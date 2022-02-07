Require Import Program.

Open Scope type_scope.

Definition Pullback {A B C : Set} (f : A -> C) (g : B -> C) :=
  {a : A & {b : B & f a = g b}}.

Definition fst' {A B C : Set} {f : A -> C} {g : B -> C} : Pullback f g -> A :=
  fun p => projT1 p.

Definition snd' {A B C : Set} {f : A -> C} {g : B -> C} : Pullback f g -> B :=
  fun p => projT1 (projT2 p).

Definition pullbackSquareCommutativity {A B C : Set} {f : A -> C} {g : B -> C}
    : forall p : Pullback f g, f (fst' p) = g (snd' p) :=
  fun p => projT2 (projT2 p).

Definition φ {X A B C : Set} {f : A -> C} {g : B -> C}
    : Pullback (fun t : X -> A => f ∘ t) (fun u : X -> B => g ∘ u)
    -> (X -> Pullback f g).
  refine (fun p x => existT _ (fst' p x) (existT _ (snd' p x) _)).
  apply (equal_f (pullbackSquareCommutativity p)).
Defined.

Record Arena : Type :=
  { positions : Set
  ; directions : positions -> Set
  }.

Record Lens (p q : Arena) : Set :=
  { onPositions : positions p -> positions q
  ; onDirections i : directions q (onPositions i) -> directions p i
  }.

Arguments onPositions {p q}.
Arguments onDirections {p q}.

Definition identityLens {p : Arena} := Build_Lens p p id (fun _ => id).

Definition compositeOfTwoLenses {p q r : Arena} (g : Lens q r) (f : Lens p q) :=
  Build_Lens p r
    (onPositions g ∘ onPositions f)
    (fun i => onDirections f i ∘ onDirections g (onPositions f i)).

Infix "∙" := compositeOfTwoLenses (at level 40).

Definition identityArena := Build_Arena unit (fun _ => unit).

Definition constantArena (A : Set) := Build_Arena A (fun _ => Empty_set).
Definition constantLens {A B : Set} (f : A -> B) :=
  Build_Lens (constantArena A) (constantArena B) f (fun _ => id).

Definition productOfTwoArenas (p q : Arena) :=
  Build_Arena
    (positions p * positions q)
    (fun i => directions p (fst i) + directions q (snd i)).

Definition π1 {p q : Arena} :=
  Build_Lens (productOfTwoArenas p q) p fst (fun _ => inl).

Definition π2 {p q : Arena} :=
  Build_Lens (productOfTwoArenas p q) q snd (fun _ => inr).

Definition pairing {p q r : Arena} (f : Lens r p) (g : Lens r q) :=
  Build_Lens r (productOfTwoArenas p q)
    (fun i => (onPositions f i, onPositions g i))
    (fun i => sum_rec _ (onDirections f i) (onDirections g i)).

Definition productOfTwoLenses {p p' q q' : Arena}
    (f : Lens p p') (g : Lens q q') :=
  pairing (f ∙ π1) (g ∙ π2).

Definition coproductOfTwoArenas (p q : Arena) :=
  Build_Arena
    (positions p + positions q)
    (sum_rect _ (directions p) (directions q)).

Definition ι1 {p q : Arena} :=
  Build_Lens p (coproductOfTwoArenas p q) inl (fun _ => id).

Definition ι2 {p q : Arena} :=
  Build_Lens q (coproductOfTwoArenas p q) inr (fun _ => id).

Definition copairing {p q r : Arena} (f : Lens p r) (g : Lens q r) :=
  Build_Lens (coproductOfTwoArenas p q) r
    (sum_rec _ (onPositions f) (onPositions g))
    (sum_rec _ (onDirections f) (onDirections g)).

Definition coproductOfTwoLenses {p p' q q' : Arena}
    (f : Lens p p') (g : Lens q q') :=
  copairing (ι1 ∙ f) (ι2 ∙ g).

Definition compositionProduct (p q : Arena) :=
  Build_Arena
    {i : positions p & directions p i -> positions q}
    (fun '(existT _ i j) => {d : directions p i & directions q (j d)}).

Definition compositionProductOfTwoLenses {p p' q q' : Arena}
    (f : Lens p p') (g : Lens q q') :=
  Build_Lens (compositionProduct p q) (compositionProduct p' q')
    (fun '(existT _ i j) => existT _
      (onPositions f i)
      (onPositions g ∘ j ∘ onDirections f i))
    (fun '(existT _ i j) '(existT _ d' e') => existT _
      (onDirections f i d')
      (onDirections g (j (onDirections f i d')) e')).

Infix "◁" := compositionProductOfTwoLenses (at level 35).

Inductive Poly : Type :=
  | identity : Poly
  | constant : Set -> Poly
  | constant' : Poly
  | product : Poly -> Poly -> Poly
  | coproduct : Poly -> Poly -> Poly
  | composite : Poly -> Poly -> Poly.

Fixpoint Sub (p' : Poly) : Set -> Arena :=
  match p' with
  | identity      => fun _ => identityArena
  | constant A    => fun _ => constantArena A
  | constant'     => fun X => constantArena X
  | product p q   => fun X => productOfTwoArenas (Sub p X) (Sub q X)
  | coproduct p q => fun X => coproductOfTwoArenas (Sub p X) (Sub q X)
  | composite p q => fun X => compositionProduct (Sub p X) (Sub q X)
  end.

Fixpoint SubMap (p' : Poly) {X Y : Set} (f : X -> Y)
    : Lens (Sub p' X) (Sub p' Y) :=
  match p' with
  | constant'     => constantLens f
  | product p q   => productOfTwoLenses (SubMap p f) (SubMap q f)
  | coproduct p q => coproductOfTwoLenses (SubMap p f) (SubMap q f)
  | composite p q => SubMap p f ◁ SubMap q f
  | _             => identityLens
  end.

Definition pullbackOfTwoCartesianLenses {p q r : Arena}
    (f : Lens p r) (g : Lens q r) :=
  Build_Arena
    (Pullback (onPositions f) (onPositions g))
    (fun '(existT _ i _) => directions r (onPositions f i)).

Inductive W (p : Arena) : Set :=
  sup : forall i : positions p, (directions p i -> W p) -> W p.

Record Algebra (p : Arena) : Type :=
  { carrier : Set
  ; structureMap i : (directions p i -> carrier) -> carrier
  }.

Arguments carrier {p}.
Arguments structureMap {p}.

Definition cata {p : Arena} (alg : Algebra p) : W p -> carrier alg :=
  W_rec p _ (fun i _ => structureMap alg i).

Definition WMap {p q : Arena} (f : Lens p q) : W p -> W q :=
  cata (Build_Algebra p
    (W q)
    (fun i g => sup q (onPositions f i) (g ∘ onDirections f i))).

Definition α (p : Poly) {A B C : Set} {f : A -> C} {g : B -> C}
    : Pullback (WMap (SubMap p f)) (WMap (SubMap p g))
    -> W (pullbackOfTwoCartesianLenses (SubMap p f) (SubMap p g)).
  refine (sigT_rec _ _).
  refine (W_rec _ _ _).
  refine (fun i t h => _).
  refine (sigT_rec _ _).
  refine (W_rec _ _ _).
  refine (fun i' t' h' => _).
  intros [=].
  inversion_sigma.
  refine (sup (pullbackOfTwoCartesianLenses (SubMap p f) (SubMap p g))
    (existT _ i (existT _ i' H1))
    (fun d => h (onDirections (SubMap p f) i d) _)).
  refine (existT _
    (t' (onDirections (SubMap p g) i' (eq_rec
      (onPositions (SubMap p f) i)
      (fun j => directions (Sub p C) j)
      d
      (onPositions (SubMap p g) i')
      H1))) _).
  assert (H2' := equal_f H2 (eq_rec
    (onPositions (SubMap p f) i)
    (fun j => directions (Sub p C) j)
    d
    (onPositions (SubMap p g) i') H1)).
  unfold "∘" in H2'.
  rewrite <- H2'.
  elim_eq_rect.
  auto.
Defined.

Definition β (p : Poly) {A B C : Set} {f : A -> C} {g : B -> C}
    : W (pullbackOfTwoCartesianLenses (SubMap p f) (SubMap p g))
    -> W (Sub p (Pullback f g)).
  refine (WMap _).
  induction p.
  cbn.
  refine (Build_Lens
    (pullbackOfTwoCartesianLenses identityLens identityLens)
    identityArena
    fst'
    _).
  cbn.
  refine (fun p _ => _).
  destruct p.
  exact tt.

  cbn.
  refine (Build_Lens
    (pullbackOfTwoCartesianLenses identityLens identityLens)
    (constantArena S)
    fst'
    _).
  cbn.
  refine (fun _ => Empty_set_rec _).

  cbn.
  refine (Build_Lens
    (pullbackOfTwoCartesianLenses (constantLens f) (constantLens g))
    (constantArena (Pullback f g))
    id
    _).
  cbn.
  refine (fun _ => Empty_set_rec _).

  cbn.
  (* Product commutes with pullbacks. *)
  admit.

  (* Coproduct *)
  admit.

  (* Composite *)
  admit.
Admitted.
  
(* https://coq.inria.fr/stdlib/Coq.Init.Specif.html#SigTNotations *)
