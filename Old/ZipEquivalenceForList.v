From HoTT Require Import HoTT.

Notation List := list.
Notation eqN := (equiv_inverse equiv_path_nat).

Fixpoint length {A : Type} (l : List A) : nat :=
  match l with
  | nil       => 0
  | cons _ l' => succ (length l')
  end.

Definition List' (A B : Type) : Type :=
  {l1 : List A & {l2 : List B & code_nat (length l1) (length l2)}}.

Definition nil' {A B : Type} : List' A B := (nil; nil; tt).
Definition cons' {A B : Type} : A * B -> List' A B -> List' A B :=
  fun '(a, b) '(l1; l2; c) => (cons a l1; cons b l2; c).

Definition indList' (A B : Type) (X : List' A B -> Type)
    (x1 : X nil')
    (x2 : forall (ab : A * B) (l' : List' A B), X l' -> X (cons' ab l'))
    : forall l' : List' A B, X l' :=
  sig_ind _ (fix f l1 :=
    match l1 with
    | nil        => sig_ind _ (fun l2 =>
        match l2 return (forall c, X (nil; l2; c)) with
        | nil        => fun 'tt => x1
        | cons b l2' => Empty_ind _
        end)
    | cons a l1' => sig_ind _ (fun l2 =>
        match l2 return (forall c, X (cons a l1'; l2; c)) with
        | nil        => Empty_ind _
        | cons b l2' => fun c => x2 (a, b) (l1'; l2'; c) (f l1' (l2'; c))
        end)
    end).

Definition zip' {A B : Type} : List' A B <~> List (A * B).
Proof.
  srapply equiv_adjointify.
  - exact (indList' A B _ nil (fun ab _ => cons ab)).
  - exact (list_rect _ nil' (fun ab _ => cons' ab)).
  - rapply list_rect.
    + reflexivity.
    + exact (fun ab _ w => ap (cons ab) w).
  - rapply indList'.
    + reflexivity.
    + exact (fun ab _ w => ap (cons' ab) w).
Defined.

Definition zip {A B : Type}
    : Pullback (@length A) (@length B) <~> List (A * B) :=
  zip'
  oE equiv_functor_sigma_id (fun l1 => equiv_functor_sigma_id (fun l2 => eqN)).

Open Scope nat_scope.
Open Scope list_scope.

Eval compute in zip (false :: true :: false :: nil; 2 :: 4 :: 6 :: nil; idpath).
Eval compute in zip^-1 ((0, true) :: (1, false) :: (2, true) :: nil).
