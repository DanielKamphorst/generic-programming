Require Import HoTT.HoTT.

Fixpoint ListMap {A B} (f : A -> B) (l : list A) : list B :=
  match l with
  | nil       => nil
  | cons a l' => cons (f a) (ListMap f l')
  end.

Definition sup {A} : Unit + A * list A <~> list A.
Proof.
  srapply equiv_adjointify.
  - exact (sum_ind _ (unit_name nil) (prod_ind _ (@cons _))).
  - exact (list_rect _ (inl tt) (fun a l _ => inr (a, l))).
  - refine (list_rect _ _ _); reflexivity.
  - refine (sum_ind _ (Unit_ind _) _); reflexivity.
Defined.

Definition equalityOfNonEmptyLists {A} (a a' : A) (l l' : list A)
    : (a = a') * (l = l') <~> (cons a l = cons a' l') :=
  (equiv_ap' sup^-1 (cons a l) (cons a' l'))^-1
  oE equiv_path_sum _ _
  oE equiv_path_prod _ _.

Fixpoint zip' {A B C} {f : A -> C} {g : B -> C} (l1 : list A)
    : {l2 : list B & ListMap f l1 = ListMap g l2} -> list (Pullback f g) :=
  match l1 with
  | nil        => fun _ => nil
  | cons a l1' => sig_ind _ (list_rect _ (fun _ => nil) (fun b l2' _ w =>
      let (w1, w2) := (equalityOfNonEmptyLists _ _ _ _)^-1 w
      in cons (a; b; w1) (zip' l1' (l2'; w2))))
  end.

Definition zip {A B C} {f : A -> C} {g : B -> C}
    : Pullback (ListMap f) (ListMap g) -> list (Pullback f g) :=
  sig_ind _ zip'.

Fixpoint unzip {A B C} {f : A -> C} {g : B -> C} (l : list (Pullback f g))
    : Pullback (ListMap f) (ListMap g) :=
  match l with
  | nil                => (nil; nil; idpath)
  | cons (a; b; w1) l' =>
      let '(l1; l2; w2) := unzip l'
      in (cons a l1; cons b l2; equalityOfNonEmptyLists _ _ _ _ (w1, w2))
  end.
