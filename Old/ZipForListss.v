Require Import HoTT.HoTT HoTT.Classes.implementations.list.

Open Scope nat_scope.

Fixpoint code (m n : nat) : Type :=
  match m, n with
  | 0, 0         => Unit
  | m'.+1, n'.+1 => code m' n'
  | _, _         => Empty
  end.

Fixpoint r (n : nat) : code n n :=
  match n with
  | 0     => tt
  | n'.+1 => r n'
  end.

Definition encode (m n : nat) (p : m = n) : code m n := p # r m.
Fixpoint decode (m n : nat) : code m n -> m = n :=
  match m, n with
  | 0, 0         => fun _ => idpath
  | m'.+1, n'.+1 => ap S o decode m' n'
  | _, _         => Empty_rec
  end.

Fixpoint encodeIsARetractionOfDecode m n : encode m n o decode m n == idmap :=
  match m, n with
  | 0, 0         => fun _ => path_contr _ _
  | m'.+1, n'.+1 => fun c =>
      (transport_compose _ S _ _)^ @ encodeIsARetractionOfDecode m' n' c
  | _, _         => Empty_ind _
  end.

Definition encode' m n : (m = n) <~> code m n.
Proof.
  srapply (equiv_adjointify _ (decode m n) (encodeIsARetractionOfDecode m n)).
  - intro p; destruct p.
    induction m as [| m' q].
    + reflexivity.
    + exact (ap (ap S) q).
Defined.

Definition SIsIso {m n} : m = n <~> m.+1 = n.+1 :=
  (encode' m.+1 n.+1)^-1 oE encode' m n.

#[export] Instance zeroIsZeroIsContractible : Contr (0 = 0) :=
  contr_equiv' _ (encode' 0 0)^-1.

Definition nil' {A B} : Pullback (@length A) (@length B) :=
  (nil; nil; center (0 = 0)).

Definition cons' {A B}
    : A * B
    -> Pullback (@length A) (@length B)
    -> Pullback (@length A) (@length B) :=
  fun '(a, b) '(l; l'; p) => (a :: l; b :: l'; SIsIso p).

Fixpoint recList'' {A B X} (xnil' : X) (xcons' : A * B -> X -> X) (l1 : list A)
    : {l2 : list B & length l1 = length l2} -> X :=
  match l1 with
  | nil      => fun _ => xnil'
  | a :: l1' => sig_ind _ (fun l2 =>
      match l2 with
      | nil      => fun _ => xnil'
      | b :: l2' => fun p : length (a :: l1') = length (b :: l2') =>
          xcons' (a, b) (recList'' xnil' xcons' l1' (l2'; SIsIso^-1 p))
      end)
  end.

Definition recList' {A B X} (xnil' : X) (xcons' : A * B -> X -> X)
    : Pullback (@length A) (@length B) -> X :=
  sig_ind _ (recList'' xnil' xcons').

Definition zipLists {A B} : Pullback (@length A) (@length B) -> list (A * B) :=
  recList' nil (@cons _).

Definition unzipList {A B}
    : list (A * B) -> Pullback (@length A) (@length B) :=
  list_rect _ nil' (fun ab _ => cons' ab).

Eval compute in zipLists (2 :: 4 :: 8 :: nil; true :: false :: true :: nil; idpath).
Eval compute in (unzipList ((0, false) :: (1, true) :: (2, false) :: nil)).1.
Eval compute in (unzipList ((0, false) :: (1, true) :: (2, false) :: nil)).2.1.

Definition uniqList' {A B X}
  (xnil' : X) (xcons' : A * B -> X -> X)
  (f : Pullback (@length A) (@length B) -> X)
  (p : f nil' = xnil')
  (q : forall ab ll', f (cons' ab ll') = xcons' ab (f ll'))
  : f == recList' xnil' xcons'.
Proof.
  refine (sig_ind _ (list_rect _ _ _)).
  - refine (sig_ind _ (list_rect _ (fun _ => ap f (path_sigma' _ idpath (path_sigma' _ idpath (path_contr _ _))) @ p) _)).
    refine (fun b l' h r => Empty_rec (encode' _ _ r)).
  - refine (fun a l h => sig_ind _ (list_rect _ _ _)).
    + refine (fun r => Empty_rec (encode' _ _ r)).
    + refine (fun b l' _ r => ap (fun p' => f (a :: l; b :: l'; p')) (eisretr SIsIso r)^ @ q (a, b) (l; l'; SIsIso^-1 r) @ ap (xcons' (a, b)) (h (l'; SIsIso^-1 r))).
Defined.
