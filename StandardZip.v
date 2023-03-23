From HoTT Require Import HoTT.

Notation List := list.
Notation indList := @list_rect.

Definition recList (A X : Type) (x1 : X) (x2 : A -> X -> X) : List A -> X :=
  indList A (fun _ => X) x1 (fun a _ => x2 a).

Fixpoint length {A : Type} (l : List A) : nat :=
  match l with
  | nil       => 0
  | cons a l' => succ (length l')
  end.

Definition List' (A B : Type) : Type :=
  {l1 : List A & {l2 : List B & code_nat (length l1) (length l2)}}.

Definition nil' {A B : Type} : List' A B := (nil; nil; tt).
Definition cons' {A B : Type} : A * B -> List' A B -> List' A B :=
  fun '(a, b) '(l1; l2; c) => (cons a l1; cons b l2; c).

Definition indList' (A B : Type)
    (X : List' A B -> Type)
    (x1 : X nil')
    (x2 : forall (ab : A * B) (l' : List' A B), X l' -> X (cons' ab l'))
    : forall l' : List' A B, X l' :=
  sig_ind _ (
    fix f (l1 : List A) : forall l2c, X (l1; l2c) :=
      match l1 with
      | nil        => sig_ind _ (fun l2 =>
          match l2 return forall c, X (nil; l2; c) with
          | nil        => fun 'tt => x1
          | cons b l2' => fun c => Empty_rec c
          end)
      | cons a l1' => sig_ind _ (fun l2 =>
          match l2 return forall c, X (cons a l1'; l2; c) with
          | nil        => fun c => Empty_rec c
          | cons b l2' => fun c => x2 (a, b) (l1'; l2'; c) (f l1' (l2'; c))
          end)
      end
  ).

Definition recList' (A B X : Type) (x1 : X) (x2 : A * B -> X -> X)
    : List' A B -> X :=
  indList' A B (fun _ => X) x1 (fun ab _ => x2 ab).

Definition asList {A B : Type} : List' A B <~> List (A * B).
Proof.
  srapply equiv_adjointify.
  - exact (recList' A B (List (A * B)) nil (@cons _)).
  - exact (recList (A * B) (List' A B) nil' cons').
  - rapply (indList (A * B)).
    + reflexivity.
    + exact (fun ab _ w => ap (cons ab) w).
  - rapply (indList' A B).
    + reflexivity.
    + exact (fun ab _ w => ap (cons' ab) w).
Defined.

Definition zip {A B : Type}
    : Pullback (@length A) (@length B) <~> List (A * B) :=
  asList
  oE equiv_functor_sigma_id (fun l1 =>
     equiv_functor_sigma_id (fun l2 =>
     equiv_path_nat^-1)).

Notation unzip := zip^-1.

Open Scope list_scope.
Open Scope nat_scope.

Eval compute in
  zip (0 :: 2 :: 4 :: 8 :: nil; false :: true :: false :: true :: nil; idpath).

Eval compute in
  unzip ((0, true) :: (1, false) :: (2, true) :: (3, false) :: nil).
