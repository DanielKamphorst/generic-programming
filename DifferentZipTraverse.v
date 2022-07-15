Require Import HoTT.HoTT.

Definition emptySumIs0 X : {i : Empty & X i} <~> Empty.
  refine (equiv_sigma_contr X).
  exact (Empty_ind _).
Defined.

Record Arena (n : nat) : Type := makeArena
  { positions : Type
  ; directions : positions -> Fin n -> Type
  }.

Arguments positions {n}.
Arguments directions {n}.

Definition constantArena n A := makeArena n A (fun _ _ => Empty).

Definition coproductOfTwoArenas {n} (p q : Arena n) := makeArena n
  (positions p + positions q)
  (sum_ind _ (directions p) (directions q)).

Definition productOfTwoArenas {n} (p q : Arena n) := makeArena n
  (positions p * positions q)
  (fun i j => directions p (fst i) j + directions q (snd i) j).

Definition fixedPointPositions {n} (p : Arena n.+1) : Type :=
  W (positions p) (fun i => directions p i fin_last).

Fixpoint fixedPointDirections {n} (p : Arena n.+1) (i : fixedPointPositions p)
    : Fin n -> Type :=
  let (i', t) := i in fun j =>
    directions p i' (fin_incl j)
    + {a : directions p i' fin_last & fixedPointDirections p (t a) j}.

Definition fixedPoint {n} (p : Arena n.+1) :=
  makeArena n (fixedPointPositions p) (fixedPointDirections p).

Fixpoint projectionArenaDirections {n} : Fin n.+1 -> Fin n.+1 -> Type :=
  match n with
  | O    => fun _ _ => Unit
  | S n' => fun i j =>
      match i, j with
      | inr _,  inr _  => Unit
      | inl i', inl j' => projectionArenaDirections i' j'
      | _, _           => Empty
      end
  end.

Definition projectionArena {n} (i : Fin n.+1) :=
  makeArena n.+1 Unit (fun _ => projectionArenaDirections i).

Class Finite' (X : Type) := makeFinite'
  { cardinality : nat
  ; finiteness : X <~> Fin cardinality
  }.

Arguments cardinality X {_}.
Arguments finiteness X {_}.

Class Finitary {n} (p : Arena n) := finitarity i j :> Finite' (directions p i j).

#[export] Instance emptySetIsFinite : Finite' Empty := makeFinite' _ 0 1.
#[export] Instance singletonIsFinite : Finite' Unit :=
  makeFinite' _ 1 (sum_empty_l _)^-1.

Fixpoint FinPreservesCoproducts (m n : nat) : Fin m + Fin n <~> Fin (m + n) :=
  match m with
  | O    => sum_empty_l _
  | S m' =>
      (FinPreservesCoproducts m' n +E 1)
      oE (equiv_sum_assoc _ _ _)^-1
      oE (1 +E equiv_sum_symm _ _)
      oE equiv_sum_assoc _ _ _
  end.

Fixpoint FinPreservesSums (m : nat) (n : Fin m -> nat) {struct m}
  : Finite' {i : Fin m & Fin (n i)}.
Proof.
  destruct m.
  - refine (makeFinite' _ 0 _).
    apply emptySumIs0.
  - refine (makeFinite' _
      (cardinality {i : Fin m & Fin (n (fin_incl i))} + n fin_last) _).
    refine (
      _
      oE (finiteness {i : Fin m & Fin (n (fin_incl i))}
        +E equiv_contr_sigma _)
      oE equiv_sigma_sum _ _ _
    ).
    apply FinPreservesCoproducts.
Defined.

Definition isosPreserveFiniteness X Y (f : X <~> Y) `{Finite' X} : Finite' Y :=
  makeFinite' _ (cardinality X) (finiteness X oE f^-1).

#[export] Instance sumPreservesFiniteness I X
  `{Finite' I} `{forall i, Finite' (X i)}
  : Finite' {i : I & X i}.
Proof.
  apply (isosPreserveFiniteness
    {i : Fin (cardinality I) & Fin (cardinality (X ((finiteness I)^-1 i)))}
    {i : I & X i}).
  - refine (
      equiv_functor_sigma_id (fun i => (finiteness (X i))^-1)
      oE equiv_functor_sigma_pb (finiteness I)^-1
        (Q := fun i => Fin (cardinality (X i)))
    ).
  - exact (FinPreservesSums
      (cardinality I)
      (fun i => cardinality (X ((finiteness I)^-1 i)))).
Defined.

#[export] Instance coproductPreservesFiniteness X Y `{Finite' X} `{Finite' Y}
    : Finite' (X + Y) := makeFinite' _
  (cardinality X + cardinality Y)
  (FinPreservesCoproducts _ _ oE (finiteness _ +E finiteness _)).

#[export] Instance coproductPreservesFinitarity {n}
    (p q : Arena n) `{Finitary _ p} `{Finitary _ q}
    : Finitary (coproductOfTwoArenas p q) :=
  sum_ind _ finitarity finitarity.

#[export] Instance productPreservesFinitarity {n}
    (p q : Arena n) `{Finitary _ p} `{Finitary _ q}
    : Finitary (productOfTwoArenas p q).
Proof.
  intros [i j] k.
  apply coproductPreservesFiniteness; apply finitarity.
Defined.

#[export] Instance projectionsAreFinitary {n} (i : Fin n.+1)
  : Finitary (projectionArena i).
Proof.
  intros j k.
  induction n as [| n' h].
  - exact _.
  - destruct i as [i' |], k as [k' |]; try exact _.
    exact (h i' j k').
Defined.

#[export] Instance constantsAreFinitary n A : Finitary (constantArena n A) :=
  fun _ _ => _.

#[export] Instance fixedPointPreservesFinitarity {n}
  (p : Arena n.+1) `{Finitary _ p}
  : Finitary (fixedPoint p).
Proof.
  refine (W_rect _ _ _ _).
  refine (fun i t h j => _).
Defined.

Inductive P : Type :=
  | firstProjection : P
  | secondProjection : P
  | constant : Type -> P
  | product : P -> P -> P
  | coproduct : P -> P -> P.

Fixpoint denotation (p : P) : Arena 2 :=
  match p with
  | firstProjection  => projectionArena fin_zero
  | secondProjection => projectionArena (fsucc fin_zero)
  | constant A       => constantArena 2 A
  | product p1 p2    => productOfTwoArenas (denotation p1) (denotation p2)
  | coproduct p1 p2  => coproductOfTwoArenas (denotation p1) (denotation p2)
  end.

#[export] Instance pIsFinitary p : Finitary (denotation p).
Proof.
  induction p; exact _.
Defined.

Definition eval {n} (p : Arena n) (X : Fin n -> Type) : Type :=
  {i : positions p & forall j : Fin n, directions p i j -> X j}.

Definition evalMap {n} (p : Arena n) {X Y} (f : forall j, X j -> Y j)
    : eval p X -> eval p Y :=
  functor_sigma idmap (fun i =>
  functor_forall_id (fun j =>
  functor_arrow idmap (f j))).

Definition optionMap {X Y} (f : X -> Y) : option X -> option Y :=
  option_rect _ (Some o f) None.

Definition μ {X Y} : option X * option Y -> option (X * Y) :=
  prod_ind _ (option_rect _ (optionMap o pair) (fun _ => None)).

Fixpoint traverseFiniteProduct {n : nat}
    : forall X : Fin n -> Type
    , (forall i, option (X i)) -> option (forall i, X i) :=
  match n
  return
    forall X : Fin n -> Type, (forall i, option (X i)) -> option (forall i, X i)
  with
  | O    => fun X _ => Some (Empty_ind _)
  | S n' => fun X f => optionMap (sum_ind_uncurried _) (μ
      ( traverseFiniteProduct (X o fin_incl) (f o fin_incl)
      , optionMap (@Unit_ind (X o inr)) (f fin_last)
      ))
  end.

Definition traverseSum I X : {i : I & option (X i)} -> option {i : I & X i} :=
  sig_ind _ (fun i => optionMap (exist _ i)).

Definition asFinitaryArena {n} (p : Arena n) `{Finitary _ p} := makeArena n
  (positions p)
  (fun i j => Fin (cardinality (directions p i j))).

Definition finitaryPolynomialIso {n} (p : Arena n) `{Finitary _ p} X
    : eval p X -> eval (asFinitaryArena p) X :=
  functor_sigma idmap (fun i => functor_forall_id (fun j =>
    functor_arrow (finiteness (directions p i j))^-1 idmap)).

Definition finitaryPolynomialIsoInv {n} (p : Arena n) `{Finitary _ p} X
    : eval (asFinitaryArena p) X -> eval p X :=
  functor_sigma idmap (fun i => functor_forall_id (fun j =>
    functor_arrow (finiteness (directions p i j)) idmap)).

Definition traverse {n} (p : Arena n) X `{Finitary _ p}
    : eval p (option o X) -> option (eval p X) :=
  optionMap (finitaryPolynomialIsoInv p X)
  o traverseSum _ (fun i => forall j, directions (asFinitaryArena p) i j -> X j)
  o functor_sigma idmap (fun i =>
      traverseFiniteProduct _
      o functor_forall_id (fun j => traverseFiniteProduct (fun _ => X j)))
  o finitaryPolynomialIso p (option o X).

Definition ListArena := fixedPoint (denotation (coproduct
  (constant Unit)
  (product firstProjection secondProjection))).

Fixpoint asList' {A} (t : positions ListArena)
  : (forall j : Fin 1, directions ListArena t j -> A) -> list A.
Proof.
  destruct t as [[[] | [[] []]] t'].
  - exact (fun _ => nil).
  - exact (fun a => cons
      (a (@fin_last 0) (inl (inl tt)))
      (asList' _ (t' (inr tt)) (fun j d => a j (inr (inr tt; d))))).
Defined.

Definition asList {A} : eval ListArena (fun _ => A) -> list A :=
  sig_ind _ asList'.

Fixpoint asListInv {A} (l : list A) : eval ListArena (fun _ => A).
  destruct l as [| a l'].
  - exact
      ( w_sup _ _ (inl tt) Empty_rec
      ; fun j => sum_ind _ (Empty_ind _) (sig_ind _ (Empty_ind _))
      ).
  - exact
      ( w_sup _ _ (inr (tt, tt)) (fun _ => (asListInv A l').1)
      ; fun j => sum_ind _
          (fun _ => a)
          (sig_ind _ (fun _ => (asListInv A l').2 j))
      ).
Defined.

Definition traverseList {A} : list (option A) -> option (list A) :=
  optionMap asList o traverse _ _ o asListInv.

Open Scope list_scope.
Eval compute in traverseList (Some true :: Some false :: Some false :: nil).
Eval compute in traverseList (Some true :: None :: Some false :: nil).

Definition sumsCommuteWithPullbacks {I} {A B C : I -> Type}
    (f : forall i, A i -> C i)
    (g : forall i, B i -> C i)
    : {i : I & Pullback (f i) (g i)}
    <~> Pullback (functor_sigma idmap f) (functor_sigma idmap g) :=
  equiv_sigma_pullback _ _ _ _
  oE equiv_functor_sigma_pb (equiv_pr1 (fun i => {i' : I & i = i'}))^-1.

Definition productsCommuteWithPullbacks `{Funext} {I} {A B C : I -> Type}
    (f : forall i, A i -> C i)
    (g : forall i, B i -> C i)
    : Pullback (functor_forall_id f) (functor_forall_id g)
    <~> (forall i, Pullback (f i) (g i)) :=
  equiv_sig_coind _ _ oE equiv_functor_sigma_id (fun a =>
    equiv_sig_coind _ _ oE equiv_functor_sigma_id (fun b => equiv_apD10 _ _ _)).

Definition polynomialFunctorsPreservePullbacks `{Funext} {n} (p : Arena n)
    {A B C : Fin n -> Type}
    (f : forall j, A j -> C j)
    (g : forall j, B j -> C j)
    : eval p (fun j => Pullback (f j) (g j))
    <~> Pullback (evalMap p f) (evalMap p g) :=
  sumsCommuteWithPullbacks _ _
  oE equiv_functor_sigma_id (fun i =>
    (productsCommuteWithPullbacks _ _)^-1
    oE equiv_functor_forall_id (fun j =>
      (productsCommuteWithPullbacks _ _)^-1)).

Definition unzip `{Funext} {n} (p : Arena n) {A B : Fin n -> Type}
  : eval p (fun j => A j * B j)
  <~> Pullback
    (evalMap p (fun j (_ : A j) => tt))
    (evalMap p (fun j (_ : B j) => tt)) :=
  polynomialFunctorsPreservePullbacks p (fun _ _ => tt) (fun _ _ => tt)
  oE equiv_functor_sigma_id (fun i => equiv_functor_forall_id (fun j =>
    equiv_functor_arrow' 1 (equiv_pullback_unit_prod _ _)^-1)).

Context `{Funext}.
Eval compute in @asList (Bool * nat) ((unzip ListArena)^-1 (asListInv (true :: false :: false :: nil); asListInv (3 :: 4 :: 1 :: nil); idpath)) % nat.

Eval compute in asList (pullback_pr1 (unzip ListArena (asListInv ((Some tt, true) :: (None, true) :: (Some tt, false) :: nil)))).

Fixpoint denotation' (p : P) (A : Type) : Arena 1 :=
  match p with
  | firstProjection  => constantArena 1 A
  | secondProjection => projectionArena fin_zero
  | constant I'      => constantArena 1 I'
  | product p1 p2    => productOfTwoArenas (denotation' p1 A) (denotation' p2 A)
  | coproduct p1 p2  =>
      coproductOfTwoArenas (denotation' p1 A) (denotation' p2 A)
  end.

Fixpoint splitPosition `{Funext} {p A} {struct p}
  : positions (denotation' p A)
  <~>
    { i : positions (denotation p)
    & directions (denotation p) i fin_zero -> A
    }.
Proof.
  refine (
    match p with
    | firstProjection  => (equiv_contr_sigma _)^-1 oE equiv_unit_rec _
    | secondProjection => equiv_inverse (equiv_pr1 _)
    | constant I'      => equiv_inverse (equiv_pr1 _)
    | product p1 p2    =>
        equiv_functor_sigma_id (fun i => equiv_sum_distributive _ _ _)
        oE _
        oE (splitPosition _ p1 A *E splitPosition _ p2 A)
    | coproduct p1 p2  =>
        (equiv_sigma_sum _ _ _)^-1
        oE (splitPosition _ p1 A +E splitPosition _ p2 A)
    end
  ); make_equiv.
Defined.

Fixpoint directionsEq `{Funext} p A {struct p}
    : forall i
    , directions  (denotation' p A) i fin_last
      = directions (denotation p) (splitPosition i).1 fin_last :=
  match p with
  | firstProjection  => fun _ => idpath
  | secondProjection => fun _ => idpath
  | constant I'      => fun _ => idpath
  | product p1 p2    => fun i => ap011 sum
      (directionsEq p1 A (fst i))
      (directionsEq p2 A (snd i))
  | coproduct p1 p2  => sum_ind _ (directionsEq p1 A) (directionsEq p2 A)
  end.

Definition W' (p : Arena 1) : Type :=
  W (positions p) (fun i => directions p i fin_last).

Fixpoint h p A (t : W' (denotation' p A))
  : { j : positions (fixedPoint (denotation p))
    & directions (fixedPoint (denotation p)) j fin_last -> A
    }.
Proof.
  refine (let (i, t') := t in
    ( w_sup _ _
        (pr1 (splitPosition i))
        (pr1 o h p A o t' o (transport idmap (directionsEq p A i))^-1)
    ; sum_ind _ (pr2 (splitPosition i)) (sig_ind _ (pr2 o h p A o t' o _))
    )).
Defined.

Fixpoint hInv' p A (j : positions (fixedPoint (denotation p)))
  : (directions (fixedPoint (denotation p)) j fin_last -> A)
  -> W' (denotation' p A).
Proof.
  destruct j as [i j'].
  exact (fun f => w_sup _ _ (splitPosition^-1 (i; f o inl)) (
    sig_ind (fun _ => W' (denotation' p A)) (hInv' p A)
    o sig_coind
      (X := directions (denotation p) i fin_last)
      (A := fun _ => W (positions (denotation p)) _)
      _
      j'
      ((sig_ind _)^-1 (f o inr))
    o transport idmap (directionsEq p A (splitPosition^-1 (i; f o inl))
        @ ap (fun i' => directions (denotation p) i' fin_last)
          (ap pr1 (eisretr splitPosition (i; f o inl))))
  )).
Defined.

Definition hInv p A
    : { j : positions (fixedPoint (denotation p))
      & directions (fixedPoint (denotation p)) j fin_last -> A
      }
    -> W' (denotation' p A) :=
  sig_ind _ (hInv' p A).
