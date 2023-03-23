From HoTT Require Import HoTT.

Record Polynomial := makePolynomial
  { Position : Type
  ; Direction : Position -> Type
  }.

Definition CoproductOfFunctors {I : Type} (F : I -> (Type -> Type))
    : Type -> Type :=
  fun A => {i : I & F i A}.

#[export] Instance CoproductOfFunctorsIs0Functor {I : Type}
  (F : I -> (Type -> Type)) `{forall i : I, Is0Functor (F i)}
  : Is0Functor (CoproductOfFunctors F).
Proof.
  constructor.
  exact (fun A B f => functor_sigma idmap (fun i => fmap (F i) f)).
Defined.

Definition Extension (p : Polynomial) : Type -> Type :=
  CoproductOfFunctors (opyon o Direction p).

Class IsPolynomialFunctor (F : Type -> Type) `{!Is0Functor F} :=
  makeIsPolynomialFunctor
    { polynomial : Polynomial
    ; equivalenceToExtension : NatEquiv F (Extension polynomial)
    }.

Arguments makeIsPolynomialFunctor F {_}.
Arguments polynomial              F {_ _}.
Arguments equivalenceToExtension  F {_ _}.

Notation List := list.
Notation indList := @list_rect.
Arguments cons {A}.

Definition recList (A X : Type) (x1 : X) (x2 : A -> X -> X) : List A -> X :=
  indList A (fun _ => X) x1 (fun a _ => x2 a).

#[export] Instance ListIs0Functor : Is0Functor List.
Proof.
  constructor.
  exact (fun A B f => recList A (List B) nil (fun a l => cons (f a) l)).
Defined.

Definition List' : Polynomial := makePolynomial nat Fin.
Definition nil' {A : Type} : Extension List' A := (O; Empty_rec).
Definition cons' {A : Type} : A -> Extension List' A -> Extension List' A :=
  fun a '(n; f) => (succ n; sum_ind _ f (fun _ => a)).

Definition recList' (A X : Type) (x1 : X) (x2 : A -> X -> X)
    : Extension List' A -> X :=
  sig_ind _ (
    fix f (n : nat) : (Fin n -> A) -> X :=
      match n with
      | O       => fun _ => x1
      | succ n' => fun a => x2 (a (inr tt)) (f n' (a o inl))
      end
  ).

Definition indList' `{Funext} (A : Type0)
    (X : Extension List' A -> Type)
    (x1 : X nil')
    (x2 : forall (a : A) (l' : Extension List' A), X l' -> X (cons' a l'))
    : forall l' : Extension List' A, X l' :=
  sig_ind _ (
    fix f (n : nat) : forall a : Fin n -> A, X (n; a) :=
      match n with
      | O       => fun a => transport (X o exist _ 0) (contr a) x1
      | succ n' => fun a => transport (X o exist _ (succ n'))
          (ap (fun a' => sum_ind _ (a o inl) a')
              (eisretr (fun x => unit_name x) (a o inr))
            @ eisretr (sum_ind_uncurried _) a)
          (x2 (a (inr tt)) _ (f n' (a o inl)))
      end
  ).

#[export] Instance ListIsPolynomialFunctor `{Funext} : IsPolynomialFunctor List.
Proof.
  apply (makeIsPolynomialFunctor List List'), natequiv_inverse.
  snrapply Build_NatEquiv.
  - intro A; srapply equiv_adjointify.
    + exact (recList' A (List A) nil cons).
    + exact (recList A (Extension List' A) nil' cons').
    + rapply indList.
      * reflexivity.
      * exact (fun a l w => ap (cons a) w).
    + rapply indList'.
      * reflexivity.
      * exact (fun a l' w => ap (cons' a) w).
  - intros A B f; rapply indList'.
    + reflexivity.
    + exact (fun a l' w => ap (cons (f a)) w).
Defined.

Inductive Tree (A : Type) : Type :=
  | leaf : Tree A
  | node : Tree A -> A -> Tree A -> Tree A.

Arguments leaf {A}.
Arguments node {A}.

Notation indTree := Tree_rect.

Definition recTree (A X : Type) (x1 : X) (x2 : X -> A -> X -> X)
    : Tree A -> X :=
  indTree A (fun _ => X) x1 (fun _ x a _ => x2 x a).

#[export] Instance TreeIs0Functor : Is0Functor Tree.
Proof.
  constructor.
  exact (fun A B f =>
    recTree A (Tree B) leaf (fun t1 a t2 => node t1 (f a) t2)
  ).
Defined.

Fixpoint TreeDirection (t : Tree Unit) : Type :=
  match t with
  | leaf         => Empty
  | node t1 _ t2 => TreeDirection t1 + Unit + TreeDirection t2
  end.

Definition Tree' : Polynomial := makePolynomial (Tree Unit) TreeDirection.
Definition leaf' {A : Type} : Extension Tree' A := (leaf; Empty_rec).
Definition node' {A : Type}
    : Extension Tree' A -> A -> Extension Tree' A -> Extension Tree' A :=
  fun '(t1; f1) a '(t2; f2) =>
    (node t1 tt t2; sum_ind _ (sum_ind _ f1 (fun _ => a)) f2).

Definition recTree' (A X : Type) (x1 : X) (x2 : X -> A -> X -> X)
    : Extension Tree' A -> X :=
  sig_ind _ (
    fix f (t : Tree Unit) : (TreeDirection t -> A) -> X :=
      match t with
      | leaf         => fun _ => x1
      | node t1 _ t2 => fun a =>
          x2 (f t1 (a o inl o inl)) (a (inl (inr tt))) (f t2 (a o inr))
      end
  ).

Definition indTree' `{Funext} (A : Type)
    (X : Extension Tree' A -> Type)
    (x1 : X leaf')
    (x2 : forall t1', X t1' -> forall a t2', X t2' -> X (node' t1' a t2'))
    : forall t' : Extension Tree' A, X t' :=
  sig_ind X (
    fix f (t : Tree Unit) : forall a : TreeDirection t -> A, X (t; a) :=
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
    + exact (recTree A (Extension Tree' A) leaf' node').
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
