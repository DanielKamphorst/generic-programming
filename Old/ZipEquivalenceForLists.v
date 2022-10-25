From HoTT Require Import HoTT.

Notation List := list.

Fixpoint length {A : Type} (l : List A) : nat :=
  match l with
  | nil       => 0
  | cons _ l' => succ (length l')
  end.

Definition List' (A B : Type) : Type :=
  {l : List A & {l' : List B & code_nat (length l) (length l')}}.

Definition nil' {A B : Type} : List' A B := (nil; nil; tt).
Definition cons' {A B : Type} (x : A * B) (l : List' A B) : List' A B :=
  (cons (fst x) l.1; cons (snd x) l.2.1; l.2.2).

Fixpoint unzip' {A B : Type} (l : List (A * B)) : List' A B :=
  match l with
  | nil      => nil'
  | cons x l => cons' x (unzip' l)
  end.

Definition zip' {A B : Type} : List' A B -> List (A * B) :=
  sig_ind _ (fix zip'' (l1 : List A)
      : {l2 : List B & code_nat (length l1) (length l2)} -> List (A * B) :=
    match l1 with
    | nil        => sig_ind _ (fun l2 =>
        match l2 return code_nat (length nil) (length l2) -> _ with
        | nil        => fun _ => nil
        | cons b l2' => Empty_rec
        end)
    | cons a l1' => sig_ind _ (fun l2 =>
        match l2 return code_nat (length (cons a l1')) (length l2) -> _ with
        | nil        => Empty_rec
        | cons b l2' => fun c => cons (a, b) (zip'' l1' (l2'; c))
        end)
    end).

#[export] Instance zipIsEquivalence' (A B : Type) : IsEquiv (@zip' A B).
Proof.
  apply (isequiv_adjointify zip' unzip').
  - exact (fix h l :=
      match l with
      | nil       => idpath
      | cons x l' => ap (cons x) (h l')
      end).
  - refine (sig_ind _ (fix h l1 :=
      match l1 with
      | nil        => sig_ind _ (fun l2 =>
          match l2 with
          | nil        => _
          | cons b l2' => _
          end)
      | cons a l1' => sig_ind _ (fun l2 =>
          match l2 with
          | nil        => _
          | cons b l2' => _
          end)
      end))
    ; try exact (Empty_ind _).
    + exact (fun 'tt => idpath).
    + exact (fun c => ap (cons' (a, b)) (h l1' (l2'; c))).
Defined.

Notation eqN := (equiv_inverse equiv_path_nat).

Definition zip {A B : Type}
    : Pullback (@length A) (@length B) <~> List (A * B) :=
  Build_Equiv _ _ zip' _
  oE equiv_functor_sigma_id (fun _ => equiv_functor_sigma_id (fun _ => eqN)).

Open Scope list_scope.
Open Scope nat_scope.

Eval compute in zip (false :: true :: false :: nil; 2 :: 4 :: 6 :: nil; idpath).
Eval compute in zip^-1 ((0, true) :: (1, false) :: (2, true) :: nil).
