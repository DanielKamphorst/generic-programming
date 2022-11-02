From HoTT Require Import HoTT.

Record Poly (J : Type) := makePoly
  { positions : Type
  ; directions : positions -> J -> Type
  }.

Arguments positions {J}.
Arguments directions {J}.

Definition Ext1 (p : Poly Unit) (X : Type) : Type :=
  {i : positions p & directions p i tt -> X}.

#[export] Instance Ext1Is0Functor (p : Poly Unit) : Is0Functor (Ext1 p) :=
  Build_Is0Functor _ _ _ _
    (Ext1 p)
    (fun X Y f => functor_sigma idmap (fun i => functor_arrow idmap f)).

Definition curryPoly (p : Poly (Fin 2)) (A : Type) : Poly Unit :=
  makePoly Unit
    {i : positions p & directions p i fin_zero -> A}
    (fun '(i; _) _ => directions p i fin_last).

Definition W' (p : Poly Unit) : Type :=
  W (positions p) (fun i => directions p i tt).

Definition ẆPositions (p : Poly (Fin 2)) : Type :=
  W' (makePoly Unit (positions p) (fun i _ => directions p i fin_last)).

Fixpoint ẆDirections (p : Poly (Fin 2)) (t : ẆPositions p) : Type :=
  match t with
  | w_sup i t' =>
      directions p i fin_zero
      + {d : directions p i fin_last & ẆDirections p (t' d)}
  end.

Definition Ẇ (p : Poly (Fin 2)) : Poly Unit :=
  makePoly Unit (ẆPositions p) (fun t _ => ẆDirections p t).

Definition sup {p : Poly Unit} : Ext1 p (W' p) <~> W' p := issig_W _ _.

Definition sup' `{Funext} {p : Poly (Fin 2)} {A : Type}
  : Ext1 (curryPoly p A) (Ext1 (Ẇ p) A) <~> Ext1 (Ẇ p) A.
Proof.
  refine (
    equiv_functor_sigma_pb sup
    oE equiv_functor_sigma_id (fun it => equiv_sum_ind _)
    oE _
    oE equiv_functor_sigma_id (fun ia => equiv_functor_sigma_id (fun t =>
      equiv_sig_ind _))
    oE equiv_functor_sigma_id (fun ia => (equiv_sig_coind _ _)^-1)
  ).
  make_equiv.
Defined.

Definition indẆ `{Funext} (p : Poly (Fin 2)) (A : Type)
    (X : Ext1 (Ẇ p) A -> Type)
    (x : forall ia t, (forall d, X (t d)) -> X (sup' (ia; t)))
    : forall t, X t :=
  sig_ind _ (fix f t :=
    match t with
    | w_sup i t' => fun a =>
        eisretr sup' (sup (i; t'); a)
        # equiv_sig_ind' _ x
          (sup'^-1 (sup (i; t'); a))
          (fun d => sig_ind _ f (pr2 (sup'^-1 (sup (i; t'); a)) d))
    end
  ).

Definition recẆ `{Funext} (p : Poly (Fin 2)) (A : Type)
    (X : Type)
    (x : forall ia, (directions (curryPoly p A) ia tt -> X) -> X)
    : Ext1 (Ẇ p) A -> X :=
  sig_ind _ (fix f t :=
    match t with
    | w_sup i t' => fun a =>
        sig_ind _ x (fmap (Ext1 (curryPoly p A)) (sig_ind _ f) (sup'^-1
          (sup (i; t'); a)))
    end
  ).

Definition fixedPointFunctorIsPolynomial `{Funext} (p : Poly (Fin 2)) (A : Type)
  : W' (curryPoly p A) <~> Ext1 (Ẇ p) A.
Proof.
  srapply equiv_adjointify.
  - exact (W_rect _ _ (fun _ => Ext1 (Ẇ p) A) (fun ia _ => sup' o exist _ ia)).
  - exact (recẆ p A (W' (curryPoly p A)) (w_sup _ _)).
  - rapply (indẆ p A); intros ia t' h.
    exact (ap (sup' o exist _ ia) (path_forall _ _ h)).
  - rapply W_rect; intros ia t h.
    exact (ap (w_sup _ _ ia) (path_forall _ _ h)).
Defined.
