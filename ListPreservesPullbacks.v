From HoTT Require Import HoTT.

Notation List := list.

Fixpoint ListMap {A B : Type} (f : A -> B) (l : List A) : List B :=
  match l with
  | nil       => nil
  | cons a l' => cons (f a) (ListMap f l')
  end.

#[export] Instance ListIs0Functor : Is0Functor List :=
  Build_Is0Functor _ _ _ _ List (@ListMap).

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

Fixpoint decode {A : Type} {l1 l2 : List A} : code l1 l2 -> (l1 = l2) :=
  match l1, l2 with
  | nil       , nil         => fun _ => idpath
  | cons a l1', cons a' l2' =>
      prod_ind
        (fun _ : (a = a') * code l1' l2' => cons a l1' = cons a' l2')
        (fun 'idpath c => ap (cons a) (decode c))
  | _, _                    => Empty_rec
  end.

Definition eqList (A : Type) {l l' : List A} : (l = l') <~> code l l'.
Proof.
  apply (equiv_adjointify encode decode).
  - generalize l, l'.
    refine (fix h l1 l2 :=
      match l1, l2 with
      | nil       , nil         => fun 'tt => idpath
      | cons a l1', cons a' l2' => _
      | _, _                    => Empty_ind _
      end
    ).
    intros [[] c]; exact (
      (transport_compose (code (cons a l1')) (cons a) _ _)^
      @ transport_prod (decode c) (idpath, codeIsReflexive l1')
      @ path_prod' (transport_const (decode c) idpath) (h l1' l2' c)
    ).
  - generalize l, l'.
    refine (fix h l1 l2 :=
      match l1, l2 with
      | nil       , nil         => fun 'idpath => idpath
      | cons a l1', cons a' l2' => fun 'idpath => _
      | _, _                    => fun w => Empty_rec (encode w)
      end
    ).
    exact (ap (ap (cons a)) (h l1' l1' idpath)).
Defined.

Definition List' {A B C : Type} (f : A -> C) (g : B -> C) : Type :=
  {l1 : List A & {l2 : List B & code (fmap List f l1) (fmap List g l2)}}.

Definition nil' {A B C : Type} {f : A -> C} {g : B -> C} : List' f g :=
  (nil; nil; tt).

Definition cons' {A B C : Type} {f : A -> C} {g : B -> C}
    : Pullback f g -> List' f g -> List' f g :=
  fun '(a; b; w) '(l1; l2; c) => (cons a l1; cons b l2; (w, c)).

Definition indList' {A B C : Type} (f : A -> C) (g : B -> C)
    (X : List' f g -> Type)
    (x1 : X nil')
    (x2 : forall (abw : Pullback f g) l', X l' -> X (cons' abw l'))
    : forall l' : List' f g, X l' :=
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
        | cons b l2' => fun '(w, c) =>
            x2 (a; b; w) (l1'; l2'; c) (f l1' (l2'; c))
        end)
    end).

Definition zip' {A B C : Type} (f : A -> C) (g : B -> C)
  : List' f g <~> List (Pullback f g).
Proof.
  srapply equiv_adjointify.
  - exact (indList' f g _ nil (fun abw _ => cons abw)).
  - exact (list_rect _ nil' (fun abw _ => cons' abw)).
  - rapply list_rect.
    + reflexivity.
    + exact (fun abw _ w' => ap (cons abw) w').
  - rapply indList'.
    + reflexivity.
    + exact (fun abw _ w' => ap (cons' abw) w').
Defined.

Definition zip {A B C : Type} (f : A -> C) (g : B -> C)
    : Pullback (fmap List f) (fmap List g) <~> List (Pullback f g) :=
  zip' f g
  oE equiv_functor_sigma_id (fun l1 => equiv_functor_sigma_id (fun l2 =>
    eqList C)).

Open Scope nat_scope.
Open Scope list_scope.

Eval compute in
  zip succ idmap (0 :: 2 :: 4 :: 6 :: nil; 1 :: 3 :: 5 :: 7 :: nil; idpath).
Eval compute in
  (zip negb idmap)^-1 ((false; true; idpath) :: (true; false; idpath) :: nil).
