Require Import HoTT.HoTT.

Definition φ {X : Type} {A B C : X -> Type}
  {f : forall x : X, A x -> C x}
  {g : forall x : X, B x -> C x}
  : { s : forall x : X, A x
    & {t : forall x : X, B x & functor_forall_id f s == functor_forall_id g t}
    }
  <~> (forall x : X, Pullback (f x) (g x)).
Proof.
  srapply equiv_adjointify.
  - exact (fun '(s; t; α) x => (s x; t x; α x)).
  - exact (fun h => (fun x => (h x).1; fun x => (h x).2.1; fun x => (h x).2.2)).
  - reflexivity.
  - reflexivity.
Defined.

Record Poly (J : Type) := makePoly
  { positions : Type
  ; directions : positions -> J -> Type
  }.

Arguments positions {J}.
Arguments directions {J}.

Definition eval {J} (p : Poly J) (X : J -> Type) : Type :=
  {i : positions p & forall j : J, directions p i j -> X j}.

Definition evalMap {J} (p : Poly J) {X Y : J -> Type}
    (f : forall j : J, X j -> Y j)
    : eval p X -> eval p Y :=
  functor_sigma idmap (fun i =>
    functor_forall_id (fun j =>
      functor_arrow idmap (f j))).

Definition W' (p : Poly (Fin 1)) : Type :=
  W (positions p) (fun i => directions p i fin_last).

Fixpoint code (n : nat) : Fin n -> Fin n -> Type :=
  match n with
  | O    => Empty_rec
  | S n' => fun j1 j2 =>
      match j1, j2 with
      | inr _  , inr _   => Unit
      | inl j1', inl j2' => code n' j1' j2'
      | _, _             => Empty
      end
  end.

Definition projectionPolynomial {n} (j : Fin n) : Poly (Fin n) :=
  makePoly (Fin n) Unit (fun _ => code n j).

Definition constantPolynomial {J} (A : Type) : Poly J :=
  makePoly J A (fun _ _ => Empty).

Definition productOfTwoPolynomials {J} (p q : Poly J) : Poly J :=
  makePoly J
    (positions p * positions q)
    (fun i j => directions p (fst i) j + directions q (snd i) j).

Definition coproductOfTwoPolynomials {J} (p q : Poly J) : Poly J :=
  makePoly J
    (positions p + positions q)
    (sum_ind _ (directions p) (directions q)).

Definition fixedPointPositions (p : Poly (Fin 2)) : Type :=
  W' (makePoly (Fin 1) (positions p) (fun i _ => directions p i fin_last)).

Fixpoint fixedPointDirections (p : Poly (Fin 2)) (t : fixedPointPositions p)
    : Type :=
  match t with
  | w_sup i t' =>
      directions p i fin_zero
      + {a : directions p i fin_last & fixedPointDirections p (t' a)}
  end.

Definition fixedPointPolynomial (p : Poly (Fin 2)) : Poly (Fin 1) :=
  makePoly (Fin 1)
    (fixedPointPositions p)
    (fun t _ => fixedPointDirections p t).

Inductive Representation : Type :=
  | projection1 : Representation
  | projection2 : Representation
  | constant : Type -> Representation
  | product : Representation -> Representation -> Representation
  | coproduct : Representation -> Representation -> Representation.

Fixpoint denotation (r : Representation) : Poly (Fin 2) :=
  match r with
  | projection1     => projectionPolynomial fin_zero
  | projection2     => projectionPolynomial fin_last
  | constant A      => constantPolynomial A
  | product   r1 r2 => productOfTwoPolynomials (denotation r1) (denotation r2)
  | coproduct r1 r2 => coproductOfTwoPolynomials (denotation r1) (denotation r2)
  end.

Definition unzip `{Funext} {J} (p : Poly J) {A B : J -> Type}
  : eval p (fun j => A j * B j)
  <~> Pullback (pr1 : eval p A -> positions p) (pr1 : eval p B -> positions p).
Proof.
  refine (
    _
    oE equiv_functor_sigma'
      (equiv_pr1 (fun i => {i' : positions p & i = i'}))^-1
      (Q := fun x =>
        (forall j : J, directions p (pullback_pr1 x) j -> A j)
        * (forall j : J, directions p (pullback_pr2 x) j -> B j))
      (fun i =>
        (equiv_prod_coind _ _)^-1
        oE equiv_functor_forall_id (fun j => (equiv_prod_coind _ _)^-1))
  ).
  make_equiv.
Defined.

Definition productsCommuteWithPullbacks `{Funext} {X : Type} {A B C : X -> Type}
    (f : forall x : X, A x -> C x)
    (g : forall x : X, B x -> C x)
    : (forall x : X, Pullback (f x) (g x))
    <~> Pullback (functor_forall_id f) (functor_forall_id g) :=
  equiv_functor_sigma_id (fun s => equiv_functor_sigma_id (fun t =>
    equiv_path_forall _ _))
  oE φ^-1.

Definition coproductsCommuteWithPullbacks {I : Type} {A B C : I -> Type}
    (f : forall i : I, A i -> C i)
    (g : forall i : I, B i -> C i)
    : {i : I & Pullback (f i) (g i)}
    <~> Pullback (functor_sigma idmap f) (functor_sigma idmap g) :=
  equiv_sigma_pullback idmap idmap f g
  oE equiv_functor_sigma_pb (equiv_pr1 (fun i => {i' : I & i = i'}))^-1.

Definition polynomialFunctorsPreservePullbacks `{Funext} {J} (p : Poly J)
    {A B C : J -> Type}
    (f : forall j : J, A j -> C j)
    (g : forall j : J, B j -> C j)
    : eval p (fun j => Pullback (f j) (g j))
    <~> Pullback (evalMap p f) (evalMap p g) :=
  coproductsCommuteWithPullbacks _ _
  oE equiv_functor_sigma_id (fun i =>
    productsCommuteWithPullbacks _ _
    oE equiv_functor_forall_id (fun j => productsCommuteWithPullbacks _ _)).
