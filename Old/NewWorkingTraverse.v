Require Import Program.

Open Scope type_scope.

Inductive Poly : Type :=
  | identity : Poly
  | constant : Set -> Poly
  | constant' : Poly
  | product : Poly -> Poly -> Poly
  | coproduct : Poly -> Poly -> Poly
  | composite : Poly -> Poly -> Poly.

Record Arena : Type :=
  { positions : Set
  ; directions : positions -> Set
  }.

Inductive W (p : Arena) : Set :=
  sup : forall i : positions p, (directions p i -> W p) -> W p.

Record Lens (p q : Arena) : Set :=
  { onPositions : positions p -> positions q
  ; onDirections
    : forall i : positions p
    , directions q (onPositions i) -> directions p i
  }.

Arguments onPositions {p q}.
Arguments onDirections {p q}.

Definition identityArena := Build_Arena unit (fun _ => unit).
Definition constantArena (A : Set) := Build_Arena A (fun _ => Empty_set).

Definition productOfTwoArenas (p q : Arena) := Build_Arena
  (positions p * positions q)
  (fun i => directions p (fst i) + directions q (snd i)).

Definition coproductOfTwoArenas (p q : Arena) := Build_Arena
  (positions p + positions q)
  (sum_rect _ (directions p) (directions q)).

Definition compositeOfTwoArenas (p q : Arena) := Build_Arena
  {i : positions p & directions p i -> positions q}
  (fun '(existT _ i j) => {d : directions p i & directions q (j d)}).

Fixpoint asArena (p' : Poly) (X : Set) : Arena :=
  match p' with
  | identity      => identityArena
  | constant A    => constantArena A
  | constant'     => constantArena X
  | product p q   => productOfTwoArenas (asArena p X) (asArena q X)
  | coproduct p q => coproductOfTwoArenas (asArena p X) (asArena q X)
  | composite p q => compositeOfTwoArenas (asArena p X) (asArena q X)
  end.

Definition verticalComposite {p q r : Arena} (g : Lens q r) (f : Lens p q) :=
  Build_Lens p r
    (onPositions g ∘ onPositions f)
    (fun i => onDirections f i ∘ onDirections g (onPositions f i)).

Definition identityLens {p : Arena} := Build_Lens p p id (fun _ => id).
Definition constantLens {A B : Set} (f : A -> B) :=
  Build_Lens (constantArena A) (constantArena B) f (fun _ => id).

Definition firstProjection {p q : Arena} :=
  Build_Lens (productOfTwoArenas p q) p fst (fun _ => inl).
Definition secondProjection {p q : Arena} :=
  Build_Lens (productOfTwoArenas p q) q snd (fun _ => inr).

Definition pairTwoLenses {p q r : Arena} (f : Lens r p) (g : Lens r q) :=
  Build_Lens r (productOfTwoArenas p q)
    (fun i => (onPositions f i, onPositions g i))
    (fun i => sum_rec _ (onDirections f i) (onDirections g i)).

Definition productOfTwoLenses {p1 p2 q1 q2 : Arena}
    (f1 : Lens p1 q1) (f2 : Lens p2 q2) := pairTwoLenses
  (verticalComposite f1 firstProjection)
  (verticalComposite f2 secondProjection).

Definition firstInclusion {p q : Arena} :=
  Build_Lens p (coproductOfTwoArenas p q) inl (fun _ => id).
Definition secondInclusion {p q : Arena} :=
  Build_Lens q (coproductOfTwoArenas p q) inr (fun _ => id).

Definition copairTwoLenses {p q r : Arena} (f : Lens p r) (g : Lens q r) :=
  Build_Lens (coproductOfTwoArenas p q) r
    (sum_rec _ (onPositions f) (onPositions g))
    (sum_rec _ (onDirections f) (onDirections g)).

Definition coproductOfTwoLenses {p1 p2 q1 q2 : Arena}
    (f1 : Lens p1 q1) (f2 : Lens p2 q2) := copairTwoLenses
  (verticalComposite firstInclusion f1)
  (verticalComposite secondInclusion f2).

Definition horizontalComposite {p p' q q' : Arena}
    (f : Lens p p') (g : Lens q q') := Build_Lens
  (compositeOfTwoArenas p q) (compositeOfTwoArenas p' q')
  (fun '(existT _ i j) => existT _
    (onPositions f i)
    (onPositions g ∘ j ∘ onDirections f i))
  (fun '(existT _ i j) '(existT _ d' e') => existT _
    (onDirections f i d')
    (onDirections g (j (onDirections f i d')) e')).

Fixpoint asArena' (p' : Poly) {X Y : Set} (f : X -> Y)
    : Lens (asArena p' X) (asArena p' Y) :=
  match p' with
  | identity      => identityLens
  | constant A    => identityLens
  | constant'     => constantLens f
  | product p q   => productOfTwoLenses (asArena' p f) (asArena' q f)
  | coproduct p q => coproductOfTwoLenses (asArena' p f) (asArena' q f)
  | composite p q => horizontalComposite (asArena' p f) (asArena' q f)
  end.

Definition asFunctor (p : Arena) : Set -> Set :=
  fun X => {i : positions p & directions p i -> X}.

Definition asFunctor' {p q : Arena} (f : Lens p q) (X : Set)
    : asFunctor p X -> asFunctor q X :=
  fun '(existT _ i g) => existT _ (onPositions f i) (g ∘ onDirections f i).

Definition asFunctor'' (p : Arena) {X Y : Set} (f : X -> Y) : asFunctor p X -> asFunctor p Y := fun '(existT _ i g) => existT _ i (f ∘ g).

Definition η {X : Set} : X -> option X := Some.

Definition μ {X Y : Set} : option X * option Y -> option (X * Y) := fun p =>
  match p with
  | (Some x, Some y) => η (x, y)
  | _                => None
  end.

Fixpoint traversePoly (p : Poly) {X Y : Set} {struct p}
    : asFunctor (asArena p (option X)) (option Y)
    -> option (asFunctor (asArena p X) Y).
  induction p.
  exact (fun '(existT _ _ oy) => option_map (fun y => existT _ tt (fun _ => y)) (oy tt)).
  exact (fun '(existT _ a _) => option_map (fun a => existT _ a (Empty_set_rec _)) (η a)).
  exact (fun '(existT _ ox _) => option_map (fun x => existT _ x (Empty_set_rec _)) ox).
  refine (fun x => option_map _ (μ (IHp1 (asFunctor' firstProjection (option Y) x), IHp2 (asFunctor' secondProjection (option Y) x)))).
  exact (fun '(existT _ i1 j1, existT _ i2 j2) => existT _ (i1, i2) (sum_rec _ j1 j2)).
  refine (sum_rec (fun _ => option (asFunctor (coproductOfTwoArenas (asArena p1 X) (asArena p2 X)) Y)) (option_map (asFunctor' (@firstInclusion (asArena p1 X) (asArena p2 X)) Y) ∘ IHp1) (option_map (asFunctor' (@secondInclusion (asArena p1 X) (asArena p2 X)) Y) ∘ IHp2) ∘ _).
  unfold asFunctor.
  cbn [positions directions asArena coproductOfTwoArenas].
  refine (fun '(existT _ i j) => _).
  induction i.
  exact (inl (existT _ a j)).
  exact (inr (existT _ b j)).
  cbn [asArena].
  refine (fun x => _).

  cut (option (asFunctor (asArena p1 X) (asFunctor (asArena p2 X) Y))).
  refine (option_map _).
  unfold asFunctor.
  cbn [positions directions compositeOfTwoArenas].
  refine (fun '(existT _ i j) => _).
  refine (existT _ (existT _ i _) _).
  refine (fun '(existT _ d d') => _).
  exact (projT2 (j d) d').

  cut (asFunctor (asArena p1 (option X)) (option (asFunctor (asArena p2 X) Y))).
  exact (traversePoly p1 X (asFunctor (asArena p2 X) Y)).

  cut (asFunctor (asArena p1 (option X)) (asFunctor (asArena p2 (option X)) (option Y))).
  refine (asFunctor'' (asArena p1 (option X)) IHp2).

  unfold asFunctor in x.
  unfold asFunctor.
  cbn [positions directions compositeOfTwoArenas asArena] in x.
  refine (existT _ (projT1 (projT1 x)) _).
  refine (fun d => _).
  induction x.
  destruct x.
  simpl in *.
  refine (existT _ (p0 d) _).
  refine (fun d' => _).
  refine (p (existT _ d d')).
Defined.

Definition cata (p : Arena) {X : Set}
    : (asFunctor p X -> X) -> (W p -> X) :=
  fun alg => W_rec _ _ (fun i g h => alg (existT _ i h)).

Definition ι (p : Poly) (X : Set) : asFunctor (asArena p X) (W (asArena p X)) -> (W (asArena p X)).
  unfold asFunctor.
  refine (sigT_rec _ _).
  exact (sup (asArena p X)).
Defined.

Definition traverse (p : Poly) (X : Set) : W (asArena p (option X)) -> option (W (asArena p X)).
  apply cata.
  refine (option_map (ι p X) ∘ @traversePoly p X (W (asArena p X))).
Defined.

Definition ListF := asArena (coproduct (constant unit) (product constant' identity)).
Definition List := W ∘ ListF.
Definition Nil {A : Set} : List A := sup (ListF A) (inl tt) (Empty_set_rec _).
Definition Cons {A : Set} : A -> List A -> List A := fun a l =>
  sup (ListF A) (inr (a, tt)) (sum_rec _ (Empty_set_rec _) (fun _ => l)).

Definition traverseList {X : Set} : List (option X) -> option (List X).
  apply traverse.
Defined.

Definition toRegularList {X : Set} : List X -> list X.
  apply cata.
  refine (sigT_rec _ _).
  refine (sum_rec _ _ _).
  exact (fun _ _ => nil).
  exact (fun '(x, _) xs => cons x (xs (inr tt))).
Defined.

Eval compute in option_map toRegularList (traverseList (Cons (Some 3) (Cons (Some 4) (Cons (Some 2) Nil)))).
Eval compute in option_map toRegularList (traverseList (Cons (Some 3) (Cons None (Cons (Some 2) Nil)))).
