From HoTT Require Import HoTT.

Record Poly (J : Type) := makePoly
  { positions : Type
  ; directions : positions -> J -> Type
  }.

Arguments positions {J}.
Arguments directions {J}.

Definition eval1 (p : Poly Unit) (X : Type) : Type :=
  {i : positions p & directions p i tt -> X}.

Definition eval1Map p {X Y} (f : X -> Y) : eval1 p X -> eval1 p Y :=
  functor_sigma idmap (fun i => functor_arrow idmap f).

Definition W' (p : Poly Unit) : Type :=
  W (positions p) (fun i => directions p i tt).

Definition curryPoly (p : Poly (Fin 2)) (A : Type) : Poly Unit :=
  makePoly Unit
    {i : positions p & directions p i fin_zero -> A}
    (fun i _ => directions p i.1 fin_last).

Definition ẆPositions (p : Poly (Fin 2)) : Type :=
  W' (makePoly Unit (positions p) (fun i _ => directions p i fin_last)).

Fixpoint ẆDirections (p : Poly (Fin 2)) (t : ẆPositions p) : Type :=
  match t with
  | w_sup i t' =>
      directions p i fin_zero
      + {a : directions p i fin_last & ẆDirections p (t' a)}
  end.

Definition Ẇ (p : Poly (Fin 2)) : Poly Unit :=
  makePoly Unit (ẆPositions p) (fun i _ => ẆDirections p i).

Definition sup' {p : Poly (Fin 2)} {A : Type}
    (i : positions (curryPoly p A))
    (t : directions (curryPoly p A) i tt -> eval1 (Ẇ p) A)
    : eval1 (Ẇ p) A :=
  (w_sup _ _ i.1 (pr1 o t); sum_ind _ i.2 (sig_ind _ (pr2 o t))).

Definition supInv' {p : Poly (Fin 2)} {A : Type}
    : eval1 (Ẇ p) A -> eval1 (curryPoly p A) (eval1 (Ẇ p) A) :=
  sig_ind _ (fun t =>
    match t return (ẆDirections p t -> A) -> _ with
    | w_sup i t' => fun a =>
        ((i; a o inl); sig_coind _ t' (fun d => a o inr o exist _ d))
    end).

#[export] Instance supIsEquivalence' `{Funext} (p : Poly (Fin 2)) (A : Type)
  : IsEquiv (sig_ind _ (@sup' p A)).
Proof.
  apply (isequiv_adjointify _ supInv').
  - exact (sig_ind _ (fun t =>
      match t with
      | w_sup i t' => fun a =>
          ap (exist _ (w_sup _ _ i t')) (eisretr (sum_ind_uncurried _) a)
      end)).
  - reflexivity.
Defined.

Definition recẆ (p : Poly (Fin 2)) (A : Type) {X : Type}
    (x : forall i, (directions (curryPoly p A) i tt -> X) -> X)
    : eval1 (Ẇ p) A -> X :=
  sig_ind _ (fix f t :=
    match t with
    | w_sup i t' =>
        sig_ind _ x
        o eval1Map (curryPoly p A) (sig_ind _ f)
        o supInv'
        o exist _ (w_sup _ _ i t')
    end).

Definition indẆ `{Funext} (p : Poly (Fin 2)) (A : Type)
    (X : eval1 (Ẇ p) A -> Type)
    (x : forall i t, (forall a, X (t a)) -> X (sup' i t))
    : forall t, X t :=
  sig_ind _ (fix f t :=
    match t with
    | w_sup i t' => fun a =>
        eisretr (sig_ind _ sup') (w_sup _ _ i t'; a)
        # x _ _ (sig_ind _ f o pr2 (supInv' (w_sup _ _ i t'; a)))
    end).

Definition asW (p : Poly (Fin 2)) A : eval1 (Ẇ p) A -> W' (curryPoly p A) :=
  recẆ p A (w_sup _ _).

Definition asẆ (p : Poly (Fin 2)) A : W' (curryPoly p A) -> eval1 (Ẇ p) A :=
  W_rect _ _ _ (fun i _ => sup' i).

#[export] Instance asWIsEquivalence `{Funext} p A : IsEquiv (asW p A).
Proof.
  apply (isequiv_adjointify _ (asẆ p A)).
  - exact (W_rect _ _ _ (fun i _ h => ap (w_sup _ _ i) (path_forall _ _ h))).
  - exact (indẆ p A _ (fun i t h => ap (sup' i) (path_forall _ _ h))).
Defined.

Definition projectionPolynomial {J : Type} `{DecidablePaths J} (j : J)
    : Poly J :=
  makePoly J Unit (fun _ j' => if dec (j = j') then Unit else Empty).

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

Definition ListRep : Representation :=
  coproduct (constant Unit) (product projection1 projection2).

Notation List := list.
Notation List' A := (W' (curryPoly (denotation ListRep) A)) (only parsing).

Definition nil' {A : Type} : List' A := w_sup _ _ (inl tt; Empty_rec) Empty_rec.
Definition cons' {A : Type} (a : A) (l : List' A) : List' A :=
  w_sup _ _ (inr (tt, tt); fun _ => a) (fun _ => l).

Fixpoint recList' (A : Type) {X : Type} (x1 : X) (x2 : A -> X -> X)
    (l : List' A)
    : X :=
  match l with
  | w_sup (inl _; _) _  => x1
  | w_sup (inr _; a) l' => x2 (a (inl tt)) (recList' A x1 x2 (l' (inr tt)))
  end.

Definition terminalObjectEquivalence `{Funext} (A X : Type) `{Contr X}
    : A <~> (X -> A) :=
  equiv_adjointify
    (fun a _ => a)
    (fun a => a (center X))
    (fun a => path_forall _ _ (fun x => ap a (contr x)))
    (fun _ => idpath).

#[export] Instance contractibleTypePlusZeroIsContractible (A : Type) `{Contr A}
    : Contr (A + Empty) :=
  contr_equiv' A (sum_empty_r A)^-1.

Definition indList' `{Funext} (A : Type) (X : List' A -> Type)
    (x1 : X nil') (x2 : forall a l, X l -> X (cons' a l))
    : forall l : List' A, X l.
  refine (W_rect _ _ _ (sig_ind _ (sum_ind _ _ _))).
  - exact (fun 'tt a l _ =>
      ( ap
        (fun a' => w_sup _
          (fun i => directions (curryPoly (denotation ListRep) A) i tt)
          (inl tt; a')
          Empty_rec)
        (contr a)
      @ ap (w_sup _ _ (inl tt; a)) (contr l)
      )
      # x1).
  - exact (fun '(tt, tt) a l h =>
      ( ap
        (fun a' => w_sup _ _ (inr (tt, tt); a') (fun _ => l (inr tt)))
        (eisretr (terminalObjectEquivalence A (Unit + Empty)) a)
      @ ap
        (w_sup _ _ (inr (tt, tt); a))
        (eisretr (terminalObjectEquivalence (List' A) (Empty + Unit)) l)
      )
      # x2 (a (inl tt)) (l (inr tt)) (h (inr tt))).
Defined.

Definition asList {A : Type} : List' A -> List A := recList' A nil (@cons _).
Definition asList' {A : Type} : List A -> List' A :=
  list_rect _ nil' (fun a _ => cons' a).

#[export] Instance asListIsEquivalence `{Funext} A : IsEquiv (@asList A).
Proof.
  apply (isequiv_adjointify _ asList').
  - rapply list_rect.
    + exact idpath.
    + exact (fun a _ h => ap (cons a) h).
  - rapply indList'.
    + exact idpath.
    + exact (fun a _ h => ap (cons' a) h).
Defined.

Definition eval {J} (p : Poly J) (X : J -> Type) : Type :=
  {i : positions p & forall j : J, directions p i j -> X j}.

Definition asEndoFunctor (p : Poly Unit) (A : Type)
    : eval p (fun _ => A) -> eval1 p A :=
  functor_sigma idmap (fun i a => a tt).

Definition asEndoFunctorInv (p : Poly Unit) (A : Type)
    : eval1 p A -> eval p (fun _ => A) :=
  functor_sigma idmap (fun _ => @Unit_ind _).

#[export] Instance asEndoFunctorIsEquivalence `{Funext} (p : Poly Unit) A
  : IsEquiv (asEndoFunctorInv p A).
Proof.
  srapply isequiv_functor_sigma.
  refine (fun i => _).
  rapply isequiv_unit_ind.
Defined.

Definition asTree {A : Type}
    : List A -> eval (Ẇ (denotation ListRep)) (fun _ => A) :=
  asEndoFunctorInv _ _ o asẆ (denotation ListRep) A o asList'.

Definition asTreeInv {A : Type}
    : eval (Ẇ (denotation ListRep)) (fun _ => A) -> List A :=
  asList o asW (denotation ListRep) A o asEndoFunctor _ _.
