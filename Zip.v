From HoTT Require Import HoTT.

#[export] Existing Instance isgraph_forall | 0.

Definition Σ (I : Type) : (I -> Type) -> Type := sig.

#[export] Instance ΣIs0Functor (I : Type) : Is0Functor (Σ I).
Proof.
  constructor; exact (fun A B => functor_sigma idmap).
Defined.

#[export] Instance ΣIs1Functor (I : Type) : Is1Functor (Σ I).
Proof.
  constructor; try reflexivity.
  exact (fun A B f g w a => ap (exist _ (pr1 a)) (w (pr1 a) (pr2 a))).
Defined.

Definition coproductOfFunctors {I C : Type} (F : I -> (C -> Type))
    : C -> Type :=
  fun c => {i : I & F i c}.

#[export] Instance coproductOfFunctorsIs0Functor {I C : Type} `{IsGraph C}
  (F : I -> (C -> Type)) `{forall i : I, Is0Functor (F i)}
  : Is0Functor (coproductOfFunctors F).
Proof.
  constructor; exact (fun c d f => fmap (Σ I) (fun i => fmap (F i) f)).
Defined.

#[export] Instance coproductOfFunctorsIs1Functor {I C : Type} `{Is1Cat C}
  (F : I -> (C -> Type))
  `{forall i : I, Is0Functor (F i)}
  `{forall i : I, Is1Functor (F i)}
  : Is1Functor (coproductOfFunctors F).
Proof.
  constructor.
  - exact (fun c d f g w => fmap2 (Σ I) (fun i => fmap2 (F i) w)).
  - exact (fun c         => fmap2 (Σ I) (fun i => fmap_id (F i) c)).
  - exact (fun c d e f g => fmap2 (Σ I) (fun i => fmap_comp (F i) f g)).
Defined.

Definition φ {A B C X : Type} {f : A -> C} {g : B -> C}
  : {s : X -> A & {t : X -> B & f o s == g o t}} <~> (X -> Pullback f g).
Proof.
  srapply equiv_adjointify.
  - intros [s [t α]]; exact (fun x => (s x; t x; α x)).
  - exact (fun h =>
      (pullback_pr1 o h; pullback_pr2 o h; pullback_commsq f g o h)
    ).
  - reflexivity.
  - reflexivity.
Defined.

Definition yPreservesPullbacks `{Funext} (X : Type) {A B C : Type}
    {f : A -> C} {g : B -> C}
    : (X -> Pullback f g) <~> Pullback (fmap (opyon X) f) (fmap (opyon X) g) :=
  equiv_functor_sigma_id (fun s =>
  equiv_functor_sigma_id (fun t =>
  equiv_path_forall _ _))
  oE φ^-1.

Definition coproductsCommuteWithPullbacks {I : Type} {A B C : I -> Type}
    (f : A $-> C) (g : B $-> C)
    : {i : I & Pullback (f i) (g i)}
    <~> Pullback (fmap (Σ I) f) (fmap (Σ I) g) :=
  equiv_sigma_pullback idmap idmap f g
  oE equiv_functor_sigma_pb (equiv_pr1 (fun i => {i' : I & i = i'}))^-1.

Record Poly := makePoly
  { positions : Type
  ; directions : positions -> Type
  }.

Definition Ext (p : Poly) : Type -> Type :=
  coproductOfFunctors (fun i => opyon (directions p i)).

Definition ExtPreservesPullbacks `{Funext} (p : Poly) {A B C : Type}
    (f : A -> C) (g : B -> C)
    : Ext p (Pullback f g) <~> Pullback (fmap (Ext p) f) (fmap (Ext p) g) :=
  coproductsCommuteWithPullbacks _ _
  oE equiv_functor_sigma_id (fun i => yPreservesPullbacks (directions p i)).

Definition unzip `{Funext} (p : Poly) {A B : Type}
  : Ext p (A * B)
  <~> Pullback
    (fmap (Ext p) (fun _ : A => tt))
    (fmap (Ext p) (fun _ : B => tt)) :=
  ExtPreservesPullbacks p (const tt) (const tt)
  oE emap (Ext p) (equiv_inverse (equiv_pullback_unit_prod A B)).

Definition copairing {A B X : Type} (f : A -> X) (g : B -> X) : A + B -> X :=
  sum_ind (fun _ => X) f g.

Notation List := list.

Definition recList {A X : Type} (x1 : X) (x2 : A -> X -> X) : List A -> X :=
  list_rect (fun _ => X) x1 (fun a _ => x2 a).

Fixpoint ListMap {A B : Type} (f : A -> B) (l : List A) : List B :=
  match l with
  | nil       => nil
  | cons a l' => cons (f a) (ListMap f l')
  end.

#[export] Instance ListIs0Functor : Is0Functor List.
Proof.
  constructor; exact @ListMap.
Defined.

Definition ListPositions : Type := List Unit.

Fixpoint ListDirections (l : ListPositions) : Type :=
  match l with
  | nil       => Empty
  | cons _ l' => Unit + ListDirections l'
  end.

Definition ListPolynomial : Poly := makePoly ListPositions ListDirections.

Notation List' := (Ext ListPolynomial).
Definition nil' {A : Type} : List' A := (nil; Empty_rec).
Definition cons' {A : Type} (a : A) (l' : List' A) : List' A :=
  (cons tt l'.1; copairing (fun _ => a) l'.2).

Definition indList' `{Funext} {A : Type} (X : List' A -> Type)
  (x1 : X nil')
  (x2 : forall (a : A) (l' : List' A), X l' -> X (cons' a l'))
  : forall l' : List' A, X l'.
Proof.
  refine (sig_ind _ (fix f l : forall (a : ListDirections l -> A), X (l; a) :=
    match l with
    | nil        => fun a => transport (X o exist _ nil) (contr a) x1
    | cons tt l' => fun a =>
        transport (X o exist _ (cons tt l'))
        _
        (x2 (a (inl tt)) (l'; a o inr) (f l' (a o inr)))
    end
  )).
  apply path_forall; intros [[] |]; reflexivity.
Defined.

Definition recList' {A X : Type} (x1 : X) (x2 : A -> X -> X) : List' A -> X :=
  sig_ind _ (fix f (l : ListPositions) : (ListDirections l -> A) -> X :=
    match l with
    | nil       => fun _ => x1
    | cons _ l' => fun a => x2 (a (inl tt)) (f l' (a o inr))
    end
  ).

Definition asList {A : Type} : List' A -> List A := recList' nil (@cons _).
Definition asListInv {A : Type} : List A -> List' A := recList nil' cons'.

Definition asListEquivalence `{Funext} : NatEquiv List' List.
Proof.
  snrapply Build_NatEquiv.
  - intro A; apply (equiv_adjointify asList asListInv).
    + rapply list_rect.
      * reflexivity.
      * exact (fun a l w => ap (cons a) w).
    + rapply indList'.
      * reflexivity.
      * exact (fun a l' w => ap (cons' a) w).
  - intros A B f.
    rapply indList'.
    + reflexivity.
    + exact (fun a l' w => ap (cons (f a)) w).
Defined.

Inductive Tree (A : Type) : Type :=
  | leaf : Tree A
  | node : Tree A -> A -> Tree A -> Tree A.

Arguments leaf {A}.
Arguments node {A}.

Definition recTree {A X : Type} (x1 : X) (x2 : X -> A -> X -> X)
    : Tree A -> X :=
  Tree_rect A (fun _ => X) x1 (fun _ x a _ => x2 x a).

Fixpoint TreeMap {A B : Type} (f : A -> B) (t : Tree A) : Tree B :=
  match t with
  | leaf         => leaf
  | node t1 a t2 => node (TreeMap f t1) (f a) (TreeMap f t2)
  end.

#[export] Instance TreeIs0Functor : Is0Functor Tree.
Proof.
  constructor; exact @TreeMap.
Defined.

Definition TreePositions : Type := Tree Unit.
Fixpoint TreeDirections (t : TreePositions) : Type :=
  match t with
  | leaf         => Empty
  | node t1 _ t2 => TreeDirections t1 + Unit + TreeDirections t2
  end.

Definition TreePolynomial : Poly := makePoly TreePositions TreeDirections.

Notation Tree' := (Ext TreePolynomial).
Definition leaf' {A : Type} : Tree' A := (leaf; Empty_rec).
Definition node' {A : Type} (t1' : Tree' A) (a : A) (t2' : Tree' A) : Tree' A :=
  (node t1'.1 tt t2'.1; copairing (copairing t1'.2 (fun _ => a)) t2'.2).

Definition indTree' `{Funext} {A : Type}
  (X : Tree' A -> Type)
  (x1 : X leaf')
  (x2 : forall t1', X t1' -> forall a t2', X t2' -> X (node' t1' a t2'))
  : forall t', X t'.
Proof.
  refine (
    sig_ind _ (fix f (t : TreePositions) : forall a, X (t; a) :=
      match t with
      | leaf          => fun a => transport (X o exist _ leaf) (contr a) x1
      | node t1 tt t2 => fun a => transport (X o exist _ (node t1 tt t2)) _
          (x2 _ (f t1 (a o inl o inl)) (a (inl (inr tt))) _ (f t2 (a o inr)))
      end
    )
  ).
  apply path_forall; intros [[| []] |]; reflexivity.
Defined.

Definition recTree' {A X : Type} (x1 : X) (x2 : X -> A -> X -> X)
    : Tree' A -> X :=
  sig_ind _ (fix f (t : TreePositions) : (TreeDirections t -> A) -> X :=
    match t with
    | leaf         => fun _ => x1
    | node t1 _ t2 => fun a =>
        x2 (f t1 (a o inl o inl)) (a (inl (inr tt))) (f t2 (a o inr))
    end
  ).

Definition asTree {A : Type} : Tree' A -> Tree A := recTree' leaf node.
Definition asTreeInv {A : Type} : Tree A -> Tree' A := recTree leaf' node'.

Definition asTreeEquivalence `{Funext} : NatEquiv Tree' Tree.
Proof.
  snrapply Build_NatEquiv.
  - intro A; apply (equiv_adjointify asTree asTreeInv).
    + rapply Tree_rect.
      * reflexivity.
      * exact (fun t1 w1 a t2 w2 =>
          ap011 (fun t1' t2' => node t1' a t2') w1 w2
        ).
    + rapply indTree'.
      * reflexivity.
      * exact (fun t1 w1 a t2 w2 =>
          ap011 (fun t1' t2' => node' t1' a t2') w1 w2
        ).
  - intros A B f.
    rapply indTree'.
    + reflexivity.
    + exact (fun t1 w1 a t2 w2 =>
        ap011 (fun t1' t2' => node t1' (f a) t2') w1 w2
      ).
Defined.

Definition unzipList `{Funext} {A B : Type}
  : List (A * B)
  <~> Pullback
    (fmap List' (fun _ : A => tt) o asListInv)
    (fmap List' (fun _ : B => tt) o asListInv).
Proof.
  refine (_ oE unzip ListPolynomial oE (asListEquivalence (A * B))^-1).
  refine (
    (equiv_sigma_prod _)^-1
    oE (equiv_functor_sigma_pb
      ((asListEquivalence A)^-1 *E (asListEquivalence B)^-1))^-1
    oE equiv_sigma_prod (fun l' => _ (fst l') = _ (snd l'))
  ).
Defined.

Definition unzipTree `{Funext} {A B : Type}
  : Tree (A * B)
  <~> Pullback
    (fmap Tree' (fun _ : A => tt) o asTreeInv)
    (fmap Tree' (fun _ : B => tt) o asTreeInv).
Proof.
  refine (_ oE unzip TreePolynomial oE (asTreeEquivalence (A * B))^-1).
  refine (
    (equiv_sigma_prod _)^-1
    oE (equiv_functor_sigma_pb
      ((asTreeEquivalence A)^-1 *E (asTreeEquivalence B)^-1))^-1
    oE equiv_sigma_prod (fun l' => _ (fst l') = _ (snd l'))
  ).
Defined.

Context `{Funext}.
Open Scope list_scope.
Open Scope nat_scope.

Eval compute in
  (unzipList ((0, true) :: (1, false) :: (2, true) :: (3, false) :: nil)).1.
Eval compute in
  (unzipList ((0, true) :: (1, false) :: (2, true) :: (3, false) :: nil)).2.1.
Eval compute in
  unzipList^-1
    ( 0 :: 2 :: 4 :: 8 :: 16 :: nil
    ; false :: false :: true :: true :: false :: nil
    ; idpath
    ).

Eval compute in
  (unzipTree (
    node
      (node leaf (0, true) (node leaf (1, false) leaf))
      (2, true)
      (node leaf (3, false) leaf)
  )).1.
Eval compute in
  (unzipTree (
    node
      (node leaf (0, true) (node leaf (1, false) leaf))
      (2, true)
      (node leaf (3, false) leaf)
  )).2.1.
Eval compute in
  unzipTree^-1
    ( node (node leaf 0 (node leaf 2 leaf)) 4 (node leaf 8 leaf)
    ; node (node leaf false (node leaf true leaf)) false (node leaf true leaf)
    ; idpath
    ).
