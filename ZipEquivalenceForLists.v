From HoTT Require Import HoTT.

Notation List := list.

Definition succIsInjective {m n : nat} : (succ m = succ n) -> (m = n) :=
  @path_nat m n o (@path_nat (succ m) (succ n))^-1.

Fixpoint length {A : Type} (l : List A) : nat :=
  match l with
  | nil       => 0
  | cons _ l' => succ (length l')
  end.

Notation List' A B := (Pullback (@length A) (@length B)) (only parsing).
Definition nil' {A B : Type} : List' A B := (nil; nil; idpath).
Definition cons' {A B : Type} (x : A * B) (l : List' A B) : List' A B :=
  (cons (fst x) l.1; cons (snd x) l.2.1; ap succ l.2.2).

Fixpoint unzip {A B : Type} (l : List (A * B))
    : Pullback (@length A) (@length B) :=
  match l with
  | nil            => (nil; nil; idpath)
  | cons (a, b) l' =>
      ( cons a (unzip l').1
      ; cons b (unzip l').2.1
      ; ap succ (unzip l').2.2
      )
  end.

Definition zip {A B : Type}
    : Pullback (@length A) (@length B) -> List (A * B) :=
  sig_ind _ (fix zip' (l1 : List A)
      : {l2 : List B & length l1 = length l2} -> List (A * B) :=
    match l1 with
    | nil        => sig_ind _ (fun l2 =>
        match l2 return (length nil = length l2) -> List (A * B) with
        | nil      => fun _ => nil
        | cons _ _ => fun w => Empty_rec (path_nat^-1 w)
        end)
    | cons a l1' => sig_ind _ (fun l2 =>
        match l2 return (length (cons a l1') = length l2) -> List (A * B) with
        | nil        => fun w => Empty_rec (path_nat^-1 w)
        | cons b l2' => fun w => cons (a, b) (zip' l1' (l2'; succIsInjective w))
        end)
    end).

#[export] Instance zipIsEquivalence (A B : Type) : IsEquiv (@zip A B).
Proof.
  apply (isequiv_adjointify zip unzip).
  - exact (fix h l :=
      match l with
      | nil            => idpath
      | cons (a, b) l' => ap (cons (a, b)) (
          ap (fun w => zip ((unzip l').1; (unzip l').2.1; w)) (center _)
          @ h l')
      end).
  - refine (sig_ind _ (fix h l1 :=
      match l1 with
      | nil        => sig_ind _ (fun l2 =>
          match l2 with
          | nil      => _
          | cons _ _ => _
          end)
      | cons a l1' => sig_ind _ (fun l2 =>
          match l2 with
          | nil        => _
          | cons b l2' => _
          end)
      end))
    ; try exact (fun w => Empty_rec (path_nat^-1 w)).
    + exact (fun _ => ap (fun w' => (nil; nil; w')) (center _)).
    + exact (fun w =>
        ap (cons' (a, b)) (h l1' (l2'; succIsInjective w))
        @ ap (fun w' => (cons a l1'; cons b l2'; w')) (center _)).
Defined.
