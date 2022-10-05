From HoTT Require Import HoTT.

Notation List := list.

Fixpoint code {A : Type} (l1 l2 : List A) : Type :=
  match l1, l2 with
  | nil       , nil         => Unit
  | cons a l1', cons a' l2' => (a = a') * code l1' l2'
  | _, _                    => Empty
  end.

Fixpoint codeIsReflexive {A : Type} (l : List A) : code l l :=
  match l with
  | nil       => tt
  | cons a l' => (idpath, codeIsReflexive l')
  end.

Definition encode {A : Type} {l l' : List A} (w : l = l') : code l l' :=
  w # codeIsReflexive l.

Fixpoint decode {A : Type} {l1 l2 : List A} : code l1 l2 -> (l1 = l2).
  refine (
    match l1, l2 with
    | nil       , nil         => fun _ => idpath
    | cons a l1', cons a' l2' => _
    | _, _                    => Empty_rec
    end).
  intros [[] c]; exact (ap (cons a) (decode _ l1' l2' c)).
Defined.

Definition eqList {A : Type} {l l' : List A} : (l = l') <~> code l l'.
Proof.
  apply (equiv_adjointify encode decode).
  - generalize l, l'.
    refine (fix h l1 l2 :=
      match l1, l2 with
      | nil       , nil         => fun 'tt => idpath
      | cons a l1', cons a' l2' => _
      | _, _                    => Empty_ind _
      end).
    intros [[] c]; exact (
      (transport_compose (code (cons a l1')) (cons a) _ _)^
      @ transport_prod (decode c) (idpath, codeIsReflexive l1')
      @ path_prod' (transport_const (decode c) idpath) (h l1' l2' c)
    ).
  - generalize l, l'.
    refine (fix h l1 l2 :=
      match l1, l2 with
      | nil       , nil         => fun 'idpath => idpath
      | cons a l1', cons a' l2' => _
      | _, _                    => fun w => Empty_rec (encode w)
      end).
    intros []; exact (ap (ap (cons a)) (h l1' l1' idpath)).
Defined.

Fixpoint ListMap {A B : Type} (f : A -> B) (l : List A) : List B :=
  match l with
  | nil       => nil
  | cons a l' => cons (f a) (ListMap f l')
  end.

Definition List' {A B C : Type} (f : A -> C) (g : B -> C) : Type :=
  {l : List A & {l' : List B & code (ListMap f l) (ListMap g l')}}.

Definition nil' {A B C : Type} {f : A -> C} {g : B -> C} : List' f g :=
  (nil; nil; tt).

Definition cons' {A B C : Type} {f : A -> C} {g : B -> C}
    (x : Pullback f g) (l : List' f g)
    : List' f g :=
  (cons x.1 l.1; cons x.2.1 l.2.1; (x.2.2, l.2.2)).

Fixpoint unzip' {A B C : Type} {f : A -> C} {g : B -> C}
    (l : List (Pullback f g))
    : List' f g :=
  match l with
  | nil       => nil'
  | cons x l' => cons' x (unzip' l')
  end.

Definition zip' {A B C : Type} {f : A -> C} {g : B -> C}
    : List' f g -> List (Pullback f g) :=
  sig_ind _ (fix zip'' (l1 : List A)
      : {l2 : List B & code (ListMap f l1) (ListMap g l2)}
      -> List (Pullback f g) :=
    match l1 with
    | nil        => sig_ind _ (fun l2 =>
        match l2 return code (ListMap f nil) (ListMap g l2) -> _ with
        | nil      => fun _ => nil
        | cons _ _ => Empty_rec
        end)
    | cons a l1' => sig_ind _ (fun l2 =>
        match l2 return code (ListMap f (cons a l1')) (ListMap g l2) -> _ with
        | nil        => Empty_rec
        | cons b l2' => fun c => cons (a; b; fst c) (zip'' l1' (l2'; snd c))
        end)
    end).

#[export] Instance zipIsEquivalence' (A B C : Type) (f : A -> C) (g : B -> C)
  : IsEquiv (zip' (f := f) (g := g)).
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
    + exact (fun c => ap (cons' (a; b; fst c)) (h l1' (l2'; snd c))).
Defined.

Definition zip {A B C : Type} {f : A -> C} {g : B -> C}
    : Pullback (ListMap f) (ListMap g) <~> List (Pullback f g) :=
  Build_Equiv _ _ zip' _
  oE equiv_functor_sigma_id (fun _ => equiv_functor_sigma_id (fun _ => eqList)).

Open Scope list_scope.
Open Scope nat_scope.

Eval compute in
  zip (f := succ) (g := idmap)
    (0 :: 2 :: 4 :: 6 :: nil; 1 :: 3 :: 5 :: 7 :: nil; idpath).
Eval compute in
  (zip (f := negb) (g := idmap))^-1
    ((false; true; idpath) :: (true; false; idpath) :: nil).
