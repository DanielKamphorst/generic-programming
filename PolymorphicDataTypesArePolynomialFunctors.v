From HoTT Require Import HoTT.

Record Poly := makePoly
  { positions : Type
  ; directions : positions -> Type
  }.

Definition coproductOfFunctors {I C : Type} (F : I -> C -> Type) : C -> Type :=
  fun c => {i : I & F i c}.

#[export] Instance coproductOfFunctorsIs0Functor {I C : Type} `{IsGraph C}
  (F : I -> C -> Type) `{forall i : I, Is0Functor (F i)}
  : Is0Functor (coproductOfFunctors F).
Proof.
  constructor.
  exact (fun c d f => functor_sigma idmap (fun i => fmap (F i) f)).
Defined.

Definition Ext (p : Poly) : Type -> Type :=
  coproductOfFunctors (opyon o directions p).

Class IsPolynomialFunctor (F : Type -> Type) `{!Is0Functor F} :=
  makeIsPolynomialFunctor
    { polynomial : Poly
    ; equivalenceToExtension : NatEquiv F (Ext polynomial)
    }.

Arguments makeIsPolynomialFunctor F {_}.

Inductive Tree (A : Type) : Type :=
  | leaf : Tree A
  | node : Tree A -> A -> Tree A -> Tree A.

Arguments leaf {A}.
Arguments node {A}.

Notation indTree := Tree_rect.

Definition recTree (A X : Type) (x1 : X) (x2 : X -> A -> X -> X)
    : Tree A -> X :=
  indTree A (fun _ => X) x1 (fun _ x a _ => x2 x a).

Fixpoint TreeMap {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
  match t with
  | leaf         => leaf
  | node t1 a t2 => node (TreeMap f t1) (f a) (TreeMap f t2)
  end.

#[export] Instance TreeIs0Functor : Is0Functor Tree.
Proof.
  constructor; exact @TreeMap.
Defined.

Fixpoint TreeDirections (t : Tree Unit) : Type :=
  match t with
  | leaf         => Empty
  | node t1 _ t2 => TreeDirections t1 + Unit + TreeDirections t2
  end.

Definition Tree' : Poly := makePoly (Tree Unit) TreeDirections.

Definition leaf' {A : Type} : Ext Tree' A := (leaf; Empty_rec).

Definition node' {A : Type} : Ext Tree' A -> A -> Ext Tree' A -> Ext Tree' A :=
  fun '(t1; a1) a '(t2; a2) =>
    (node t1 tt t2; sum_ind _ (sum_ind _ a1 (fun _ => a)) a2).

Definition recTree' (A X : Type) (x1 : X) (x2 : X -> A -> X -> X)
    : Ext Tree' A -> X :=
  sig_ind _ (
    fix f (t : Tree Unit) : (TreeDirections t -> A) -> X :=
      match t with
      | leaf         => fun _ => x1
      | node t1 _ t2 => fun a =>
          x2 (f t1 (a o inl o inl)) (a (inl (inr tt))) (f t2 (a o inr))
      end
  ).

Definition indTree' `{Funext} (A : Type)
    (X : Ext Tree' A -> Type)
    (x1 : X leaf')
    (x2
      : forall t1' : Ext Tree' A
      , X t1'
      -> forall (a : A) (t2' : Ext Tree' A), X t2' -> X (node' t1' a t2'))
    : forall t' : Ext Tree' A, X t' :=
  sig_ind X (
    fix f (t : Tree Unit) : forall a : TreeDirections t -> A, X (t; a) :=
      match t with
      | leaf          => fun a => transport (X o exist _ leaf) (contr a) x1
      | node t1 tt t2 => fun a => transport (X o exist _ (node t1 tt t2))
          (ap (fun a' => sum_ind _ (sum_ind _ (a o inl o inl) a') (a o inr))
              (eisretr (fun x => unit_name x) (a o inl o inr))
            @ ap (fun a' => sum_ind _ a' (a o inr))
              (eisretr (sum_ind_uncurried _) (a o inl))
            @ eisretr (sum_ind_uncurried _) a)
          (x2 _ (f t1 (a o inl o inl)) (a (inl (inr tt))) _ (f t2 (a o inr)))
      end
  ).

#[export] Instance TreeIsPolynomialFunctor `{Funext} : IsPolynomialFunctor Tree.
Proof.
  apply (makeIsPolynomialFunctor Tree Tree'), natequiv_inverse.
  snrapply Build_NatEquiv.
  - intro A; srapply equiv_adjointify.
    + exact (recTree' A (Tree A) leaf node).
    + exact (recTree A (Ext Tree' A) leaf' node').
    + rapply indTree.
      * reflexivity.
      * exact (fun t1 w1 a t2 w2 =>
          ap011 (fun t1' t2' => node t1' a t2') w1 w2
        ).
    + rapply indTree'.
      * reflexivity.
      * exact (fun t1' w1 a t2' w2 =>
          ap011 (fun t1'' t2'' => node' t1'' a t2'') w1 w2
        ).
  - intros A B f; rapply indTree'.
    + reflexivity.
    + exact (fun t1' w1 a t2' w2 =>
        ap011 (fun t1 t2 => node t1 (f a) t2) w1 w2
      ).
Defined.

Variables I J : Type.

Inductive T (A : Type) : Type :=
  c : (I -> J -> A) -> (I -> J -> T A) -> T A.

Arguments c {A}.

Notation indT := T_rect.

Definition recT (A X : Type) (x : (I -> J -> A) -> (I -> J -> X) -> X)
    : T A -> X :=
  indT A (fun _ => X) (fun a _ => x a).

Fixpoint TMap {A B : Type} (f : A -> B) (t : T A) : T B :=
  match t with
  | c a t' => c (fun i j => f (a i j)) (fun i j => TMap f (t' i j))
  end.

#[export] Instance TIs0Functor : Is0Functor T.
Proof.
  constructor; exact @TMap.
Defined.

Fixpoint TDirections (t : T Unit) : Type :=
  match t with
  | c _ t' => I * J + {i : I & {j : J & TDirections (t' i j)}}
  end.

Definition T' : Poly := makePoly (T Unit) TDirections.

Definition c' {A : Type} (a : I -> J -> A) (t' : I -> J -> Ext T' A)
    : Ext T' A :=
  ( c (fun _ _ => tt) (fun i j => pr1 (t' i j))
  ; sum_ind _
    (fun '(i, j) => a i j)
    (sig_ind _ (fun i => sig_ind _ (fun j => pr2 (t' i j))))
  ).

Definition recT' (A X : Type) (x : (I -> J -> A) -> (I -> J -> X) -> X)
    : Ext T' A -> X :=
  sig_ind _ (
    fix f (t : T Unit) : (TDirections t -> A) -> X :=
      match t with
      | c _ t' => fun a =>
          x (fun i j => a (inl (i, j)))
            (fun i j => f (t' i j) (a o inr o exist _ i o exist _ j))
      end
  ).

Definition indT' `{Funext} (A : Type)
    (X : Ext T' A -> Type)
    (x
      : forall (a : I -> J -> A) (t' : I -> J -> Ext T' A)
      , (forall (i : I) (j : J), X (t' i j))
      -> X (c' a t'))
    : forall t' : Ext T' A, X t' :=
  sig_ind _ (
    fix f (t : T Unit) : forall a : TDirections t -> A, X (t; a) :=
      match t with
      | c u t' => fun a =>
          path_sigma' _
            (ap (fun u' => c u' t') (contr u))
            ((transport_compose
                (fun t'' => TDirections t'' -> A)
                (fun u' => c u' t')
                (contr u)
                (sum_ind _ (a o inl) (a o inr)))^
              @ transport_const (contr u) (sum_ind _ (a o inl) (a o inr))
              @ eisretr (sum_ind_uncurried _) a)
          # x (fun i j => a (inl (i, j))) _
              (fun i j => f (t' i j) (a o inr o exist _ i o exist _ j))
      end
  ).

#[export] Instance TIsPolynomialFunctor `{Funext} : IsPolynomialFunctor T.
Proof.
  apply (makeIsPolynomialFunctor T T'), natequiv_inverse.
  snrapply Build_NatEquiv.
  - intro A; srapply equiv_adjointify.
    + exact (recT' A (T A) c).
    + exact (recT A (Ext T' A) c').
    + rapply indT.
      exact (fun a t w =>
        ap (c a) (path_forall _ _ (fun i => path_forall _ _ (fun j => w i j)))
      ).
    + rapply indT'.
      exact (fun a t' w =>
        ap (c' a) (path_forall _ _ (fun i => path_forall _ _ (fun j => w i j)))
      ).
  - intros A B f; rapply indT'.
    exact (fun a t' w =>
      ap (c (fun i j => f (a i j)))
        (path_forall _ _ (fun i => path_forall _ _ (fun j => w i j)))
    ).
Defined.
