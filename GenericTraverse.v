Require Import
  HoTT.HoTT
  GenericZipAndTraverse.PolynomialFunctors
  GenericZipAndTraverse.LaxMonoidalFunctors.

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

#[export] Instance ProductIs1Functor : Is1Functor (uncurry prod).
Proof.
  constructor; try reflexivity.
  exact (fun A B f g w a => path_prod' (fst w (fst a)) (snd w (snd a))).
Defined.

Definition ProductOfTwoFunctors (F G : Type -> Type) : Type -> Type :=
  fun A => F A * G A.

#[export] Instance ProductOfTwoFunctorsIs0Functor
  (F G : Type -> Type) `{!Is0Functor F} `{!Is0Functor G}
  : Is0Functor (ProductOfTwoFunctors F G).
Proof.
  constructor.
  exact (fun A B f => functor_prod (fmap F f) (fmap G f)).
Defined.

Class Traversable (T : Type -> Type) `{!Is0Functor T} := makeTraversable
  { τ (F : LaxMonoidalFunctor) (A : Type) : T (F A) -> F (T A)
  ; naturality1 (A : Type)
    : Is1Natural
      (T o ApplyLaxMonoidalFunctorTo A)
      (ApplyLaxMonoidalFunctorTo (T A))
      (fun F => τ F A)
  ; naturality2 (F : LaxMonoidalFunctor) : Is1Natural (T o F) (F o T) (τ F)
  ; unitarity (A : Type) : τ IdentityLaxMonoidalFunctor A == idmap
  ; linearity (F G : LaxMonoidalFunctor) (A : Type)
    : τ (CompositeOfTwoLaxMonoidalFunctors G F) A == fmap G (τ F A) o τ G (F A)
  }.

Arguments τ           T {_ _}.
Arguments naturality1 T {_ _}.
Arguments naturality2 T {_ _}.
Arguments unitarity   T {_ _}.
Arguments linearity   T {_ _}.

Class IsFiniteType (A : Type) := makeIsFiniteType
  { cardinality : nat
  ; equivalenceToStandardFiniteType : A <~> Fin cardinality
  }.

Arguments cardinality                     A {_}.
Arguments equivalenceToStandardFiniteType A {_}.

#[export] Instance StandardFiniteTypeIsFinite (n : nat)
    : IsFiniteType (Fin n) :=
  makeIsFiniteType (Fin n) n 1.

#[export] Instance EmptyTypeIsFinite : IsFiniteType Empty :=
  StandardFiniteTypeIsFinite 0.

#[export] Instance UnitTypeIsFinite : IsFiniteType Unit :=
  makeIsFiniteType Unit 1 (sum_empty_l Unit)^-1.

Fixpoint FinPreservesSum (m n : nat) : Fin m + Fin n <~> Fin (m + n) :=
  match m with
  | O       => sum_empty_l (Fin n)
  | succ m' =>
      (FinPreservesSum m' n +E 1)
      oE (equiv_sum_assoc (Fin m') (Fin n) Unit)^-1
      oE (1 +E equiv_sum_symm Unit (Fin n))
      oE equiv_sum_assoc (Fin m') Unit (Fin n)
  end.

#[export] Instance coproductOfTwoFiniteTypesIsFinite
    (A B : Type) `{IsFiniteType A} `{IsFiniteType B}
    : IsFiniteType (A + B) :=
  makeIsFiniteType (A + B) _ (
    FinPreservesSum (cardinality A) (cardinality B)
    oE (equivalenceToStandardFiniteType A +E equivalenceToStandardFiniteType B)
  ).

Class IsFinitePolynomial (p : Polynomial) :=
  DirectionIsFiniteType i :> IsFiniteType (Direction p i).

#[export] Instance ListPolynomialIsFinitePolynomial : IsFinitePolynomial List'.
Proof.
  exact (fun _ => _).
Defined.

#[export] Instance TreePolynomialIsFinitePolynomial : IsFinitePolynomial Tree'.
Proof.
  intro t; induction t; exact _.
Defined.

#[export] Instance equivalencePreservesTraversability
  {S T : Type -> Type} `{!Is0Functor S} `{Traversable T}
  (φ : NatEquiv S T)
  : Traversable S.
Proof.
  snrapply makeTraversable.
  - exact (fun F A => fmap F (φ A)^-1 o τ T F A o φ (F A)).
  - exact (fun A F G α =>
      isnat φ (α A)
      $@v naturality1 T A F G α
      $@v isnat_tr α (φ A)^-1
    ).
  - exact (fun F A B f =>
      isnat φ (fmap F f)
      $@v naturality2 T F A B f
      $@v fmap_square F (isnat (natequiv_inverse _ _ φ) f)
    ).
  - refine (fun A => _ $@ cate_issect (φ A)).
    exact ((φ A)^-1 $@L unitarity T A $@R φ A).
  - exact (fun F G A =>
      whiskerTL (f := φ (G (F A))) (
      whiskerBL (f := emap G (φ (F A))) (
      whiskerBR (f := fmap (G o F) (φ A)^-1) (
      linearity T F G A)))
      $@vR (fmap_comp G _ _ $@ (fmap_comp G _ _ $@R _))
    ).
Defined.

#[export] Instance idIsTraversable : Traversable idmap.
Proof.
  snrapply makeTraversable.
  - exact (fun F A => idmap).
  - intros A F G α; reflexivity.
  - intros F A B f; reflexivity.
  - reflexivity.
  - exact (fun F G A => (fmap_id G (F A))^$).
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

#[export] Instance traversableFunctorsAreClosedUnderBinaryProducts
  (S T : Type -> Type) `{Traversable S} `{Traversable T}
  : Traversable (ProductOfTwoFunctors S T).
Proof.
  snrapply makeTraversable.
  - exact (fun F A => μ F (S A, T A) o fmap11 prod (τ S F A) (τ T F A)).
  - exact (fun A F G α =>
      twoVariableFunctorPreservesSquare prod
        (naturality1 S A F G α)
        (naturality1 T A F G α)
      $@v compatibilityWithProduct α (S A) (T A)
    ).
  - exact (fun F A B f =>
      twoVariableFunctorPreservesSquare prod
        (naturality2 S F A B f)
        (naturality2 T F A B f)
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

#[export] Instance traversableFunctorsAreClosedUnderCoproducts {I : Type}
  (T : I -> (Type -> Type))
  `{forall i : I, Is0Functor  (T i)}
  `{forall i : I, Traversable (T i)}
  : Traversable (CoproductOfFunctors T).
Proof.
  snrapply makeTraversable.
  - exact (fun F A =>
      sig_ind _ (fun i => fmap F (exist (fun i => T i A) i) o τ (T i) F A)
    ).
  - exact (fun A F G α => sig_ind _ (fun i =>
      naturality1 (T i) A F G α
      $@v isnat_tr α (exist (fun i => T i A) i))
    ).
  - exact (fun F A B f => sig_ind _ (fun i =>
      naturality2 (T i) F A B f
      $@v
        fmap_square F (
        Build_Square
          (f01 := exist _ i)
          (f21 := exist _ i)
          (f10 := fmap (T i) f)
          (f12 := fmap (CoproductOfFunctors T) f) (
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
  : NatEquiv (opyon (A + B)) (ProductOfTwoFunctors (opyon A) (opyon B)).
Proof.
  snrapply Build_NatEquiv.
  - exact (fun X => equiv_inverse (equiv_sum_ind (fun _ => X))).
  - intro; reflexivity.
Defined.

#[export] Instance y0IsTraversable `{Funext} : Traversable (opyon Empty) :=
  equivalencePreservesTraversability zeroExponentRule.

#[export] Instance y1IsTraversable `{Funext} : Traversable (opyon Unit) :=
  equivalencePreservesTraversability oneExponentRule.

#[export] Instance yFinIsTraversable `{Funext} (n : nat)
  : Traversable (opyon (Fin n)).
Proof.
  induction n.
  - exact y0IsTraversable.
  - exact (
      equivalencePreservesTraversability (exponentProductRule (Fin n) Unit)
    ).
Defined.

#[export] Instance yIsTraversable `{Funext} (A : Type0) `{IsFiniteType A}
    : Traversable (opyon A) :=
  equivalencePreservesTraversability
    (S := opyon A) (T := opyon (Fin (cardinality A)))
    (natequiv_opyon_equiv _ _
      (equiv_inverse (equivalenceToStandardFiniteType A))).

#[export] Instance finitaryPolynomialFunctorIsTraversable `{Funext}
    (F : Type0 -> Type)
    `{IsPolynomialFunctor F}
    `{IsFinitePolynomial (polynomial F)}
    : Traversable F :=
  equivalencePreservesTraversability (equivalenceToExtension F).

#[export] Instance ListIsTraversable `{Funext} : Traversable List :=
  finitaryPolynomialFunctorIsTraversable List.

#[export] Instance TreeIsTraversable `{Funext} : Traversable Tree :=
  finitaryPolynomialFunctorIsTraversable Tree.

Context `{Funext}.
Open Scope list_scope.
Open Scope nat_scope.

Eval compute in
  τ List MaybeLaxMonoidalFunctor nat
    (some 2 :: some 4 :: some 8 :: some 16 :: nil).
Eval compute in
  τ List MaybeLaxMonoidalFunctor nat
    (some 2 :: some 4 :: none :: some 16 :: nil).

Eval compute in
  τ Tree MaybeLaxMonoidalFunctor nat (
    node
      (node leaf (some 2) (node leaf (some 4) leaf))
      (some 8)
      (node leaf (some 16) leaf)
  ).
Eval compute in
  τ Tree MaybeLaxMonoidalFunctor nat (
    node
      (node leaf (some 2) (node leaf none leaf))
      (some 8)
      (node leaf (some 16) leaf)
  ).
