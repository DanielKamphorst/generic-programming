From HoTT Require Import HoTT.

#[export] Existing Instance isgraph_forall | 0.
#[export] Existing Instance isgraph_type.

Definition twoVariableFunctorPreservesSquare
    {C1 C2 D : Type} `{Is1Cat C1} `{Is1Cat C2} `{Is1Cat D}
    (F : C1 -> C2 -> D) `{!Is0Functor (uncurry F), !Is1Functor (uncurry F)}
    {a1 a1' b1 b1' : C1} {a2 a2' b2 b2' : C2}
    {s1 : a1 $-> a1'} {s2 : a2 $-> a2'}
    {f1 : a1 $-> b1} {f2 : a2 $-> b2} {f1' : a1' $-> b1'} {f2' : a2' $-> b2'}
    {t1 : b1 $-> b1'} {t2 : b2 $-> b2'}
    (w1 : Square f1 f1' s1 t1)
    (w2 : Square f2 f2' s2 t2)
    : Square
      (fmap11 F f1 f2) (fmap11 F f1' f2') (fmap11 F s1 s2) (fmap11 F t1 t2) :=
  @fmap_square _ _ _ _ _ _ _ _ _ _
    (a1, a2) (a1', a2') (b1, b2) (b1', b2')
    (s1, s2) (t1, t2) (f1, f2) (f1', f2')
    (uncurry F) _ _
    (w1, w2).

#[export] Instance productIs0Functor : Is0Functor (uncurry prod).
Proof.
  constructor; exact (fun A B => uncurry functor_prod).
Defined.

#[export] Instance productIs1Functor : Is1Functor (uncurry prod).
Proof.
  constructor; try reflexivity.
  exact (fun A B f g w a => path_prod' (fst w (fst a)) (snd w (snd a))).
Defined.

#[export] Instance underlyingFamilyIs0Functor
  (C D : Type) `{Is1Cat C} `{Is1Cat D}
  : Is0Functor (fun11_fun C D).
Proof.
  constructor; exact (fun F G => trans_nattrans F G).
Defined.

Definition eval {A B : Type} (a : A) : (A -> B) -> B := fun f => f a.

#[export] Instance evalIs0Functor {I : Type} (C : Type) `{IsGraph C} (i : I)
  : Is0Functor (eval (B := C) i).
Proof.
  constructor; exact (fun c d f => f i).
Defined.

Definition pairing {A B X : Type} (f : X -> A) (g : X -> B) : X -> A * B :=
  prod_coind f g.

Definition copairing {A B X : Type} (f : A -> X) (g : B -> X) : A + B -> X :=
  sum_ind (fun _ => X) f g.

#[export] Instance pairingIs0Functor
  {C D E : Type} `{IsGraph C} `{IsGraph D} `{IsGraph E}
  (F : E -> C) `{!Is0Functor F}
  (G : E -> D) `{!Is0Functor G}
  : Is0Functor (pairing F G).
Proof.
  constructor; exact (fun e e' => pairing (fmap F) (fmap G)).
Defined.

Definition productOfTwoFunctors {C : Type} (F G : C -> Type) : C -> Type :=
  uncurry prod o pairing F G.

Definition coproductOfFunctors {I C : Type} (F : I -> (C -> Type))
    : C -> Type :=
  fun c => {i : I & F i c}.

#[export] Instance coproductOfFunctorsIs0Functor {I C : Type} `{IsGraph C}
  (F : I -> (C -> Type)) `{forall i : I, Is0Functor (F i)}
  : Is0Functor (coproductOfFunctors F).
Proof.
  constructor; exact (fun c d f => functor_sigma idmap (fun i => fmap (F i) f)).
Defined.

Record Poly := makePoly
  { positions : Type
  ; directions : positions -> Type
  }.

Definition Ext (p : Poly) : Type -> Type :=
  coproductOfFunctors (fun i => opyon (directions p i)).

Record LaxMonoidalFunctor := makeLaxMonoidalFunctor
  { underlyingFunctor :> Fun11 Type Type
  ; μ
    : NatTrans
      (uncurry prod o functor_prod underlyingFunctor underlyingFunctor)
      (underlyingFunctor o uncurry prod)
  ; η : Unit -> underlyingFunctor Unit
  }.

Record MonoidalNaturalTransformation (F G : LaxMonoidalFunctor) :=
  makeMonoidalNaturalTransformation
    { underlyingNaturalTransformation :> NatTrans F G
    ; compatibilityWithProduct A B
      : μ G (A, B)
        o fmap11 prod
          (underlyingNaturalTransformation A)
          (underlyingNaturalTransformation B)
      == underlyingNaturalTransformation (A * B) o μ F (A, B)
    ; compatibilityWithUnit : η G == underlyingNaturalTransformation Unit o η F
    }.

Arguments compatibilityWithUnit    {F G}.
Arguments compatibilityWithProduct {F G}.

#[export] Instance LaxMonoidalFunctorIsGraph : IsGraph LaxMonoidalFunctor.
Proof.
  constructor; exact MonoidalNaturalTransformation.
Defined.

Definition identityLaxMonoidalFunctor : LaxMonoidalFunctor :=
  makeLaxMonoidalFunctor fun11_id (nattrans_id (uncurry prod)) idmap.

Definition compositeOfTwoLaxMonoidalFunctors (G F : LaxMonoidalFunctor)
    : LaxMonoidalFunctor :=
  makeLaxMonoidalFunctor
    (fun11_compose G F)
    (nattrans_comp
      (nattrans_postwhisker G (μ F))
      (nattrans_prewhisker (μ G) (functor_prod F F)))
    (fmap G (η F) o η G).

#[export] Instance underlyingFunctorIs0Functor : Is0Functor underlyingFunctor.
Proof.
  constructor; exact underlyingNaturalTransformation.
Defined.

Definition eval' (A : Type) : LaxMonoidalFunctor -> Type :=
  eval A o fun11_fun Type Type o underlyingFunctor.

Class Traversable (T : Type -> Type) `{!Is0Functor T} := makeTraversable
  { τ (F : LaxMonoidalFunctor) A : T (F A) -> F (T A)
  ; τNaturalityIn1 A : Is1Natural (T o eval' A) (eval' (T A)) (fun F => τ F A)
  ; τNaturalityIn2 (F : LaxMonoidalFunctor) : Is1Natural (T o F) (F o T) (τ F)
  ; unitarity A : τ identityLaxMonoidalFunctor A == idmap
  ; linearity F G A
    : τ (compositeOfTwoLaxMonoidalFunctors G F) A == fmap G (τ F A) o τ G (F A)
  }.

Arguments τ              T {_ _}.
Arguments τNaturalityIn1 T {_ _}.
Arguments τNaturalityIn2 T {_ _}.
Arguments unitarity      T {_ _}.
Arguments linearity      T {_ _}.

Definition equivalencePreservesTraversability
  {S T : Type -> Type} `{Traversable S} `{!Is0Functor T}
  (φ : NatEquiv S T)
  : Traversable T.
Proof.
  snrapply makeTraversable.
  - exact (fun F A => fmap F (φ A) o τ S F A o (φ (F A))^-1).
  - exact (fun A F G α =>
      isnat (natequiv_inverse _ _ φ) (α A)
      $@v τNaturalityIn1 S A F G α
      $@v isnat_tr α (φ A)
    ).
  - exact (fun F A B f =>
      isnat (natequiv_inverse _ _ φ) (fmap F f)
      $@v τNaturalityIn2 S F A B f
      $@v fmap_square F (isnat φ f)
    ).
  - refine (fun A => _ $@ cate_isretr (φ A)).
    exact (φ A $@L unitarity S A $@R (φ A)^-1).
  - exact (fun F G A =>
      whiskerTL (f := (φ (G (F A)))^-1) (
      whiskerBL (f := emap G (natequiv_inverse _ _ φ (F A))) (
      whiskerBR (f := fmap (G o F) (φ A)) (
      linearity S F G A)))
      $@vR (fmap_comp G _ _ $@ (fmap_comp G _ _ $@R _))
    ).
Defined.

#[export] Instance traversableFunctorsAreClosedUnderΣ {I : Type}
  (T : I -> (Type -> Type))
  `{forall i : I, Is0Functor  (T i)}
  `{forall i : I, Traversable (T i)}
  : Traversable (coproductOfFunctors T).
Proof.
  snrapply makeTraversable.
  - exact (fun F A =>
      sig_ind _ (fun i => fmap F (exist (fun i => T i A) i) o τ (T i) F A)
    ).
  - exact (fun A F G α => sig_ind _ (fun i =>
      τNaturalityIn1 (T i) A F G α
      $@v isnat_tr α (exist (fun i => T i A) i))
    ).
  - exact (fun F A B f => sig_ind _ (fun i =>
      τNaturalityIn2 (T i) F A B f
      $@v
        fmap_square F (
        Build_Square
          (f01 := exist _ i)
          (f21 := exist _ i)
          (f10 := fmap (T i) f)
          (f12 := fmap (coproductOfFunctors T) f) (
        Id (A := _ -> _) _)))
    ).
  - exact (fun A => sig_ind _ (fun i =>
      exist (fun i => T i A) i $@L unitarity (T i) A)
    ).
  - exact (fun F G A => sig_ind _ (fun i =>
      linearity (T i) F G A
      $@v
        fmap_square G (
        Build_Square (f01 := exist _ i) (f21 := fmap F (exist _ i)) (
        Id _)))
    ).
Defined.

#[export] Instance traversableFunctorsAreClosedUnderProducts
  (S T : Type -> Type) `{Traversable S} `{Traversable T}
  : Traversable (productOfTwoFunctors S T).
Proof.
  snrapply makeTraversable.
  - exact (fun F A => μ F (S A, T A) o fmap11 prod (τ S F A) (τ T F A)).
  - exact (fun A F G α =>
      twoVariableFunctorPreservesSquare prod
        (τNaturalityIn1 S A F G α)
        (τNaturalityIn1 T A F G α)
      $@v compatibilityWithProduct α (S A) (T A)
    ).
  - exact (fun F A B f =>
      twoVariableFunctorPreservesSquare prod
        (τNaturalityIn2 S F A B f)
        (τNaturalityIn2 T F A B f)
      $@v isnat (μ F) (a := (S A, T A)) (a' := (S B, T B)) (fmap S f, fmap T f)
    ).
  - exact (fun A => fmap22 prod _ _ _ _ (unitarity S A) (unitarity T A)).
  - exact (fun F G A =>
      whiskerTL (f := fmap11 prod (τ S G (F A)) (τ T G (F A))) (
      whiskerBR (f := fmap G (μ F (S A, T A))) (
      isnat (μ G) (a := (S (F A), T (F A))) (a' := (F (S A), F (T A)))
        (τ S F A, τ T F A)))
      $@vL fmap22 prod _ _ _ _ (linearity S F G A) (linearity T F G A)
      $@vR fmap_comp G _ _
    ).
Defined.

Definition zeroExponentRule `{Funext} : NatEquiv (opyon Empty) (const Unit).
Proof.
  snrapply Build_NatEquiv.
  - exact (fun X => equiv_inverse (equiv_empty_rec X)).
  - intro; reflexivity.
Defined.

Definition oneExponentRule `{Funext} : NatEquiv (opyon Unit) idmap.
Proof.
  snrapply Build_NatEquiv.
  - exact (fun X => equiv_inverse (equiv_unit_rec X)).
  - intro; reflexivity.
Defined.

Definition exponentProductRule `{Funext} (A B : Type)
  : NatEquiv (opyon (A + B)) (productOfTwoFunctors (opyon A) (opyon B)).
Proof.
  snrapply Build_NatEquiv.
  - exact (fun X => equiv_inverse (equiv_sum_ind (fun _ => X))).
  - intro; reflexivity.
Defined.

#[export] Instance Δ1IsTraversable : Traversable (const Unit).
Proof.
  snrapply makeTraversable.
  - exact (fun F _ => η F).
  - exact (fun A F G α => compatibilityWithUnit α).
  - exact (fun F A B f => (fmap_id F Unit)^$ $@R η F).
  - reflexivity.
  - reflexivity.
Defined.

#[export] Instance y0IsTraversable `{Funext} : Traversable (opyon Empty) :=
  equivalencePreservesTraversability (natequiv_inverse _ _ zeroExponentRule).

#[export] Instance idIsTraversable : Traversable idmap.
Proof.
  snrapply makeTraversable.
  - exact (fun F A => idmap).
  - intros A F G α; reflexivity.
  - intros F A B f; reflexivity.
  - reflexivity.
  - exact (fun F G A => (fmap_id G (F A))^$).
Defined.

#[export] Instance y1IsTraversable `{Funext} : Traversable (opyon Unit) :=
  equivalencePreservesTraversability (natequiv_inverse _ _ oneExponentRule).

#[export] Instance yFinIsTraversable `{Funext} (n : nat)
  : Traversable (opyon (Fin n)).
Proof.
  induction n.
  - exact y0IsTraversable.
  - exact (
      equivalencePreservesTraversability
      (natequiv_inverse _ _ (exponentProductRule (Fin n) Unit))
    ).
Defined.

Class Finite (A : Type) := makeFinite
  { cardinality : nat
  ; finiteness : A <~> Fin cardinality
  }.

Arguments cardinality A {_}.
Arguments finiteness  A {_}.

#[export] Instance yIsTraversable `{Funext} (A : Type) `{Finite A}
    : Traversable (opyon A) :=
  equivalencePreservesTraversability
    (S := opyon (Fin (cardinality A))) (T := opyon A)
    (natequiv_opyon_equiv _ _ (finiteness A)).

Class Finitary (p : Poly) := finitarity i :> Finite (directions p i).

Corollary finitaryPolynomialFunctorIsTraversable `{Funext}
  (p : Poly) `{Finitary p}
  : Traversable (Ext p).
Proof.
  exact _.
Defined.

#[export] Instance optionIs0Functor : Is0Functor option.
Proof.
  constructor.
  exact (fun A B f a' =>
    match a' with
    | Some a => Some (f a)
    | None   => None
    end
  ).
Defined.

#[export] Instance optionIs1Functor : Is1Functor option.
Proof.
  constructor; try (intros; intros []; reflexivity).
  intros A B f g w; rapply option_rect; try reflexivity.
  exact (fun a => ap Some (w a)).
Defined.

Definition optionLaxMonoidalFunctor : LaxMonoidalFunctor.
Proof.
  refine (makeLaxMonoidalFunctor (Build_Fun11 _ _ option) _ Some).
  snrapply Build_NatTrans.
  - exact (fun A a' =>
      match a' with
      | (Some a1, Some a2) => Some (a1, a2)
      | _                  => None
      end
    ).
  - intros A B f [[] []]; reflexivity.
Defined.

#[export] Instance emptyTypeIsFinite : Finite Empty := makeFinite Empty 0 1.
#[export] Instance unitTypeIsFinite : Finite Unit :=
  makeFinite Unit 1 (sum_empty_l Unit)^-1.

Fixpoint familyOfFiniteTypesIsClosedUnderCoproducts (m n : nat)
    : Fin m + Fin n <~> Fin (m + n) :=
  match m with
  | O       => sum_empty_l (Fin n)
  | succ m' =>
      (familyOfFiniteTypesIsClosedUnderCoproducts m' n +E 1)
      oE (equiv_sum_assoc (Fin m') (Fin n) Unit)^-1
      oE (1 +E equiv_sum_symm Unit (Fin n))
      oE equiv_sum_assoc (Fin m') Unit (Fin n)
  end.

#[export] Instance finiteTypesAreClosedUnderCoproducts
    (A B : Type) `{Finite A} `{Finite B}
    : Finite (A + B) :=
  makeFinite (A + B) _ (
    familyOfFiniteTypesIsClosedUnderCoproducts (cardinality A) (cardinality B)
    oE (finiteness A +E finiteness B)
  ).

Notation List := list.

Definition recList {A X : Type} (x1 : X) (x2 : A -> X -> X) : List A -> X :=
  list_rect (fun _ => X) x1 (fun a _ => x2 a).

Fixpoint ListMap {A B : Type} (f : A -> B) (l : List A) : List B :=
  match l with
  | nil       => nil
  | cons a l' => cons (f a) (ListMap f l')
  end.

#[export] Instance ListIs0Functor : Is0Functor List.
Proof.
  constructor; exact @ListMap.
Defined.

Definition ListPositions : Type := List Unit.

Fixpoint ListDirections (l : ListPositions) : Type :=
  match l with
  | nil       => Empty
  | cons _ l' => Unit + ListDirections l'
  end.

Definition ListPolynomial : Poly := makePoly ListPositions ListDirections.

#[export] Instance ListPolynomialIsFinitary : Finitary ListPolynomial.
Proof.
  intro l; induction l; exact _.
Defined.

Notation List' := (Ext ListPolynomial).
Definition nil' {A : Type} : List' A := (nil; Empty_rec).
Definition cons' {A : Type} (a : A) (l' : List' A) : List' A :=
  (cons tt l'.1; copairing (fun _ => a) l'.2).

Definition indList' `{Funext} {A : Type} (X : List' A -> Type)
  (x1 : X nil')
  (x2 : forall (a : A) (l' : List' A), X l' -> X (cons' a l'))
  : forall l' : List' A, X l'.
Proof.
  refine (sig_ind _ (fix f l : forall (a : ListDirections l -> A), X (l; a) :=
    match l with
    | nil        => fun a => transport (X o exist _ nil) (contr a) x1
    | cons tt l' => fun a =>
        transport (X o exist _ (cons tt l'))
        _
        (x2 (a (inl tt)) (l'; a o inr) (f l' (a o inr)))
    end
  )).
  apply path_forall; intros [[] |]; reflexivity.
Defined.

Definition recList' {A X : Type} (x1 : X) (x2 : A -> X -> X) : List' A -> X :=
  sig_ind _ (fix f (l : ListPositions) : (ListDirections l -> A) -> X :=
    match l with
    | nil       => fun _ => x1
    | cons _ l' => fun a => x2 (a (inl tt)) (f l' (a o inr))
    end
  ).

Definition asList `{Funext} : NatEquiv List' List.
Proof.
  snrapply Build_NatEquiv.
  - intro A; srapply equiv_adjointify.
    + exact (recList' nil (@cons _)).
    + exact (recList nil' cons').
    + rapply list_rect.
      * reflexivity.
      * exact (fun a l w => ap (cons a) w).
    + rapply indList'.
      * reflexivity.
      * exact (fun a l' w => ap (cons' a) w).
  - intros A B f.
    rapply indList'.
    + reflexivity.
    + exact (fun a l' w => ap (cons (f a)) w).
Defined.

#[export] Instance ListIsTraversable `{Funext} : Traversable List :=
  equivalencePreservesTraversability asList.

Inductive Tree (A : Type) : Type :=
  | leaf : Tree A
  | node : Tree A -> A -> Tree A -> Tree A.

Arguments leaf {A}.
Arguments node {A}.

Definition recTree {A X : Type} (x1 : X) (x2 : X -> A -> X -> X)
    : Tree A -> X :=
  Tree_rect A (fun _ => X) x1 (fun _ x a _ => x2 x a).

Fixpoint TreeMap {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
  match t with
  | leaf         => leaf
  | node t1 a t2 => node (TreeMap f t1) (f a) (TreeMap f t2)
  end.

#[export] Instance TreeIs0Functor : Is0Functor Tree.
Proof.
  constructor; exact @TreeMap.
Defined.

Definition TreePositions : Type := Tree Unit.
Fixpoint TreeDirections (t : TreePositions) : Type :=
  match t with
  | leaf         => Empty
  | node t1 _ t2 => TreeDirections t1 + Unit + TreeDirections t2
  end.

Definition TreePolynomial : Poly := makePoly TreePositions TreeDirections.

#[export] Instance TreePolynomialIsFinitary : Finitary TreePolynomial.
Proof.
  intro t; induction t; exact _.
Defined.

Notation Tree' := (Ext TreePolynomial).
Definition leaf' {A : Type} : Tree' A := (leaf; Empty_rec).
Definition node' {A : Type} (t1' : Tree' A) (a : A) (t2' : Tree' A) : Tree' A :=
  (node t1'.1 tt t2'.1; copairing (copairing t1'.2 (fun _ => a)) t2'.2).

Definition indTree' `{Funext} {A : Type}
  (X : Tree' A -> Type)
  (x1 : X leaf')
  (x2 : forall t1', X t1' -> forall a t2', X t2' -> X (node' t1' a t2'))
  : forall t', X t'.
Proof.
  refine (
    sig_ind _ (fix f (t : TreePositions) : forall a, X (t; a) :=
      match t with
      | leaf          => fun a => transport (X o exist _ leaf) (contr a) x1
      | node t1 tt t2 => fun a => transport (X o exist _ (node t1 tt t2)) _
          (x2 _ (f t1 (a o inl o inl)) (a (inl (inr tt))) _ (f t2 (a o inr)))
      end
    )
  ).
  apply path_forall; intros [[| []] |]; reflexivity.
Defined.

Definition recTree' {A X : Type} (x1 : X) (x2 : X -> A -> X -> X)
    : Tree' A -> X :=
  sig_ind _ (fix f (t : TreePositions) : (TreeDirections t -> A) -> X :=
    match t with
    | leaf         => fun _ => x1
    | node t1 _ t2 => fun a =>
        x2 (f t1 (a o inl o inl)) (a (inl (inr tt))) (f t2 (a o inr))
    end
    ).

Definition asTree `{Funext} : NatEquiv Tree' Tree.
Proof.
  snrapply Build_NatEquiv.
  - intro A; srapply equiv_adjointify.
    + exact (recTree' leaf node).
    + exact (recTree leaf' node').
    + rapply Tree_rect.
      * reflexivity.
      * exact (fun t1 w1 a t2 w2 =>
          ap011 (fun t1' t2' => node t1' a t2') w1 w2
        ).
    + rapply indTree'.
      * reflexivity.
      * exact (fun t1 w1 a t2 w2 =>
          ap011 (fun t1' t2' => node' t1' a t2') w1 w2
        ).
  - intros A B f.
    rapply indTree'.
    + reflexivity.
    + exact (fun t1 w1 a t2 w2 =>
        ap011 (fun t1' t2' => node t1' (f a) t2') w1 w2
      ).
Defined.

#[export] Instance TreeIsTraversable `{Funext} : Traversable Tree :=
  equivalencePreservesTraversability asTree.

Context `{Funext}.
Open Scope list_scope.
Open Scope nat_scope.

Eval compute in
  τ List optionLaxMonoidalFunctor nat
    (Some 2 :: Some 4 :: Some 8 :: Some 16 :: nil).
Eval compute in
  τ List optionLaxMonoidalFunctor nat
    (Some 2 :: Some 4 :: None :: Some 16 :: nil).

Eval compute in
  τ Tree optionLaxMonoidalFunctor nat (
    node
      (node leaf (Some 2) (node leaf (Some 4) leaf))
      (Some 8)
      (node leaf (Some 16) leaf)
  ).
Eval compute in
  τ Tree optionLaxMonoidalFunctor nat (
    node
      (node leaf (Some 2) (node leaf None leaf))
      (Some 8)
      (node leaf (Some 16) leaf)
  ).
