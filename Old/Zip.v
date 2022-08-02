Require Import HoTT.HoTT.

Open Scope path_scope.

Definition PullbackMap' {A A' B B' C C'}
    {f : A -> C} {g : B -> C}
    {f' : A' -> C'} {g' : B' -> C'}
    (α1 : A <~> A') (α2 : B <~> B') (α3 : C <~> C')
    (h : f' o α1 == α3 o f) (k : g' o α2 == α3 o g)
    : Pullback f g <~> Pullback f' g' :=
  (equiv_sigma_prod (fun p' => f' (fst p') = g' (snd p')))^-1
  oE equiv_functor_sigma' (α1 *E α2) (fun p =>
    equiv_concat_r (k (snd p))^ _
    oE equiv_concat_l (h (fst p)) _
    oE equiv_ap α3 _ _)
  oE equiv_sigma_prod _.

Record Arena : Type := makeArena
  { positions : Type
  ; directions : positions -> Type
  }.

Record Lens (p q : Arena) : Type := makeLens
  { onPositions : positions p -> positions q
  ; onDirections i : directions q (onPositions i) -> directions p i
  }.

Arguments onPositions {p q}.
Arguments onDirections {p q}.

Class Vertical {p q} (f : Lens p q) := verticality :> IsEquiv (onPositions f).

Class Cartesian {p q} (f : Lens p q) :=
  cartesianness i :> IsEquiv (onDirections f i).

Class IsArenaIsomorphism {p q} (f : Lens p q) := makeIsArenaIsomorphism
  { isoVerticality :> Vertical f
  ; isoCartesianness :> Cartesian f
  }.

Record ArenaIsomorphism p q := makeArenaIsomorphism
  { arenaIso :> Lens p q
  ; arenaIsoInvertibility : IsArenaIsomorphism arenaIso
  }.

Arguments makeArenaIsomorphism {p q}.
#[export] Existing Instance arenaIsoInvertibility.

Definition inverseOfArenaIso {p q} (f : Lens p q) `{IsArenaIsomorphism _ _ f}
  : ArenaIsomorphism q p.
Proof.
  srefine (makeArenaIsomorphism (makeLens _ _ _ _) _).
  - exact (onPositions f)^-1.
  - exact (fun j =>
      transport _ (eisretr (onPositions f) j)
      o (onDirections f ((onPositions f)^-1 j))^-1
    ).
  - split.
    + apply isequiv_inverse.
    + exact (fun _ => _).
Defined.

Definition identityLens {p : Arena} := makeLens p p idmap (fun _ => idmap).

Definition compositeOfTwoLenses {p q r} (g : Lens q r) (f : Lens p q) :=
  makeLens p r
    (onPositions g o onPositions f)
    (fun i => onDirections f i o onDirections g (onPositions f i)).

Definition compositeOfTwoArenaIsomorphisms {p q r}
  (g : ArenaIsomorphism q r) (f : ArenaIsomorphism p q)
  : ArenaIsomorphism p r.
Proof.
  refine (makeArenaIsomorphism (compositeOfTwoLenses g f) _).
  split.
  - apply isequiv_compose.
  - exact (fun _ => _).
Defined.

Definition identityArena := makeArena Unit (fun _ => Unit).

Definition constantArena A := makeArena A (fun _ => Empty).

Definition constantLens {A B} (f : A -> B) :=
  makeLens (constantArena A) (constantArena B) f (fun _ => idmap).

Definition productOfTwoArenas p q := makeArena
  (positions p * positions q)
  (fun i => directions p (fst i) + directions q (snd i)).

Definition productOfTwoLenses {p p' q q'} (f : Lens p p') (g : Lens q q') :=
  makeLens (productOfTwoArenas p q) (productOfTwoArenas p' q')
    (functor_prod (onPositions f) (onPositions g))
    (fun i => functor_sum (onDirections f (fst i)) (onDirections g (snd i))).

Definition productOfTwoArenaIsomorphisms {p p' q q'}
  (f : ArenaIsomorphism p p') (g : ArenaIsomorphism q q')
  : ArenaIsomorphism (productOfTwoArenas p q) (productOfTwoArenas p' q').
Proof.
  refine (makeArenaIsomorphism (productOfTwoLenses f g) _).
  split.
  - apply isequiv_functor_prod.
  - exact (fun _ => _).
Defined.

Definition coproductOfTwoArenas p q := makeArena
  (positions p + positions q)
  (sum_ind _ (directions p) (directions q)).

Definition coproductOfTwoLenses {p p' q q'} (f : Lens p p') (g : Lens q q') :=
  makeLens (coproductOfTwoArenas p q) (coproductOfTwoArenas p' q')
    (functor_sum (onPositions f) (onPositions g))
    (sum_ind _ (onDirections f) (onDirections g)).

#[export] Instance coproductsPreserveCartesianLenses {p p' q q'}
    (f : Lens p p') `{Cartesian _ _ f}
    (g : Lens q q') `{Cartesian _ _ g}
    : Cartesian (coproductOfTwoLenses f g) :=
  sum_ind _ cartesianness cartesianness.

Definition coproductOfTwoArenaIsomorphisms {p p' q q'}
  (f : ArenaIsomorphism p p') (g : ArenaIsomorphism q q')
  : ArenaIsomorphism (coproductOfTwoArenas p q) (coproductOfTwoArenas p' q').
Proof.
  refine (makeArenaIsomorphism (coproductOfTwoLenses f g) _).
  split.
  - apply isequiv_functor_sum.
  - exact _.
Defined.

Definition pullbackOfLenses {p q r} (f : Lens p r) (g : Lens q r) := makeArena
  (Pullback (onPositions f) (onPositions g))
  (fun i => Pushout
    (onDirections f i.1)
    (onDirections g i.2.1 o transport _ i.2.2)).

Definition π' {p q r} {f : Lens p r} {g : Lens q r} :=
  makeLens (pullbackOfLenses f g) p pullback_pr1 (fun _ => pushl).

#[export] Instance pullbacksPreserveCartesianLenses {p q r}
    (f : Lens p r) (g : Lens q r) `{Cartesian _ _ g}
    : Cartesian (π' (f := f) (g := g)) :=
  fun _ => _.

Definition φ {p q r} {f : Lens p r} {g : Lens q r} :=
  makeLens (pullbackOfLenses f g) q pullback_pr2 (fun _ => pushr).

Definition compositeOfTwoArenas p q := makeArena
  {i : positions p & directions p i -> positions q}
  (fun i => {a : directions p i.1 & directions q (i.2 a)}).

Definition compositionProductOfTwoLenses {p p' q q'}
    (f : Lens p p') (g : Lens q q') :=
  makeLens (compositeOfTwoArenas p q) (compositeOfTwoArenas p' q')
    (functor_sigma
      (onPositions f)
      (fun i => functor_arrow (onDirections f i) (onPositions g)))
    (fun i => functor_sigma
      (onDirections f i.1)
      (onDirections g o i.2 o onDirections f i.1)).

Definition compositionProductOfTwoArenaIsomorphisms `{Funext} {p p' q q'}
  (f : ArenaIsomorphism p p') (g : ArenaIsomorphism q q')
  : ArenaIsomorphism (compositeOfTwoArenas p q) (compositeOfTwoArenas p' q').
Proof.
  refine (makeArenaIsomorphism (compositionProductOfTwoLenses f g) _).
  split.
  - apply isequiv_functor_sigma.
  - exact (fun _ => _).
Defined.

Definition equalityOfPositionsOfComposites {p q}
  (i i' : positions (compositeOfTwoArenas p q))
  : {e : i.1 = i'.1 & i.2 = i'.2 o transport _ e} <~> (i = i').
Proof.
  refine (equiv_path_sigma _ _ _ oE equiv_functor_sigma_id _).
  destruct i as [i j], i' as [i' j']; cbn.
  intro e; now destruct e.
Defined.

Definition constantFunctorsPreservePullbacks (p : Arena)
  : ArenaIsomorphism p (pullbackOfLenses (@identityLens p) identityLens).
Proof.
  refine (inverseOfArenaIso π').
  split.
  - apply isequiv_pr1_contr.
  - exact (fun _ => _).
Defined.

Definition AToAPreservesPullbacks {A B C} (f : A -> C) (g : B -> C)
  : ArenaIsomorphism
      (constantArena (Pullback f g))
      (pullbackOfLenses (constantLens f) (constantLens g)).
Proof.
  srefine (makeArenaIsomorphism (makeLens _ _ _ _) _).
  - exact idmap.
  - exact (fun i =>
      onDirections (constantLens pullback_pr1) i
      o (onDirections (π' (f := constantLens f) (g := constantLens g)) i)^-1
    ).
  - split.
    + apply isequiv_idmap.
    + exact (fun _ => _).
Defined.

Definition productsCommuteWithPullbacks1 {A1 A2 B1 B2 C1 C2}
  (f1 : A1 -> C1) (f2 : A2 -> C2)
  (g1 : B1 -> C1) (g2 : B2 -> C2)
  : Pullback f1 g1 * Pullback f2 g2
  <~> Pullback (functor_prod f1 f2) (functor_prod g1 g2).
Proof.
  refine (
    equiv_functor_sigma_id (fun _ => equiv_functor_sigma_id (fun _ =>
      equiv_path_prod _ _))
    oE _
  ).
  make_equiv.
Defined.

Definition productsCommuteWithPullbacks {p p' q q' r r'}
  (f : Lens p r) (f' : Lens p' r')
  (g : Lens q r) (g' : Lens q' r') `{Cartesian _ _ g} `{Cartesian _ _ g'}
  : ArenaIsomorphism
      (productOfTwoArenas (pullbackOfLenses f g) (pullbackOfLenses f' g'))
      (pullbackOfLenses (productOfTwoLenses f f') (productOfTwoLenses g g')).
Proof.
  srefine (makeArenaIsomorphism (makeLens _ _ _ _) _).
  - apply productsCommuteWithPullbacks1.
  - exact (fun i =>
      onDirections (productOfTwoLenses π' π') i
      o (onDirections
          (π' (f := productOfTwoLenses f f') (g := productOfTwoLenses g g'))
          (productsCommuteWithPullbacks1 _ _ _ _ i))^-1
    ).
  - split.
    + apply equiv_isequiv.
    + exact (fun _ => _).
Defined.

Definition coproductsCommuteWithPullbacks1 {A1 A2 B1 B2 C1 C2}
  (f1 : A1 -> C1) (f2 : A2 -> C2)
  (g1 : B1 -> C1) (g2 : B2 -> C2)
  : Pullback f1 g1 + Pullback f2 g2
  <~> Pullback (functor_sum f1 f2) (functor_sum g1 g2).
Proof.
  refine (
    equiv_functor_sigma_id (fun _ => equiv_functor_sigma_id (fun _ =>
      equiv_path_sum _ _))
    oE _
  ).
  srapply equiv_adjointify.
  - refine (fun i =>
      ( functor_sum pullback_pr1 pullback_pr1 i
      ; functor_sum pullback_pr2 pullback_pr2 i
      ; _
      )).
    destruct i as [i | i'].
    + exact i.2.2.
    + exact i'.2.2.
  - intros [[a1 | a2] [[b1 | b2] e]]; try now elim e.
    + exact (inl (a1; b1; e)).
    + exact (inr (a2; b2; e)).
  - intros [[a1 | a2] [[b1 | b2] e]]; (reflexivity || elim e).
  - intros [[a1 [b1 e1]] | [a2 [b2 e2]]]; reflexivity.
Defined.

Definition coproductsCommuteWithPullbacks {p p' q q' r r'}
  (f : Lens p r) (f' : Lens p' r')
  (g : Lens q r) (g' : Lens q' r') `{Cartesian _ _ g} `{Cartesian _ _ g'}
  : ArenaIsomorphism
    (coproductOfTwoArenas (pullbackOfLenses f g) (pullbackOfLenses f' g'))
    (pullbackOfLenses (coproductOfTwoLenses f f') (coproductOfTwoLenses g g')).
Proof.
  srefine (makeArenaIsomorphism (makeLens _ _ _ _) _).
  - apply coproductsCommuteWithPullbacks1.
  - exact (fun i =>
      onDirections (coproductOfTwoLenses π' π') i
      o (onDirections
          (π' (f := coproductOfTwoLenses f f') (g := coproductOfTwoLenses g g'))
          (coproductsCommuteWithPullbacks1 _ _ _ _ i))^-1
    ).
  - split.
    + apply equiv_isequiv.
    + exact (fun _ => _).
Defined.

Definition representablesPreservePullbacks `{Funext} S {X Y Z}
    (f : X -> Z) (g : Y -> Z)
    : (S -> Pullback f g)
    <~> Pullback (functor_arrow (idmap : S -> S) f) (functor_arrow idmap g) :=
  equiv_functor_sigma_id (fun x =>
    equiv_functor_sigma_id (fun y => (equiv_ap10 _ _)^-1)
    oE (equiv_sig_coind _ _)^-1)
  oE (equiv_sig_coind _ _)^-1.

Definition compositionProductsCommuteWithPullbacks1 `{Funext} {p p' q q' r r'}
  (f : Lens p r) (f' : Lens p' r') `{Cartesian _ _ f}
  (g : Lens q r) (g' : Lens q' r') `{Cartesian _ _ g}
  : positions (compositeOfTwoArenas
    (pullbackOfLenses f g)
    (pullbackOfLenses f' g'))
  <~> positions (pullbackOfLenses
    (compositionProductOfTwoLenses f f')
    (compositionProductOfTwoLenses g g')).
Proof.
  refine (
    equiv_functor_sigma_id (fun i => equiv_functor_sigma_id (fun j =>
      equalityOfPositionsOfComposites _ _))
    oE _
    oE equiv_functor_sigma_id (fun i =>
      _
      oE representablesPreservePullbacks _ _ _)
  ).
  2: exact (
    PullbackMap'
      (f' := functor_arrow (onDirections f i.1) (onPositions f'))
      (g' := functor_arrow
        (onDirections g i.2.1 o transport _ i.2.2)
        (onPositions g'))
      (equiv_precompose (onDirections π' i))
      (equiv_precompose (onDirections φ i))
      (equiv_precompose (onDirections (compositeOfTwoLenses f π') i))
      (fun _ => 1)
      (fun j' => ap (compose (onPositions g' o j')) (path_forall _ _ pglue)^)
  ).
  make_equiv.
Defined.

Definition compositionProductsCommuteWithPullbacks `{Funext} {p p' q q' r r'}
  (f : Lens p r) (f' : Lens p' r') `{Cartesian _ _ f}
  (g : Lens q r) (g' : Lens q' r') `{Cartesian _ _ g} `{Cartesian _ _ g'}
  : ArenaIsomorphism
      (compositeOfTwoArenas (pullbackOfLenses f g) (pullbackOfLenses f' g'))
      (pullbackOfLenses
        (compositionProductOfTwoLenses f f')
        (compositionProductOfTwoLenses g g')).
Proof.
  srefine (makeArenaIsomorphism (makeLens _ _ _ _) _).
  - rapply compositionProductsCommuteWithPullbacks1.
  - exact (fun i =>
      onDirections (compositionProductOfTwoLenses π' π') i
      o (onDirections
          (π'
            (f := compositionProductOfTwoLenses f f')
            (g := compositionProductOfTwoLenses g g'))
          (compositionProductsCommuteWithPullbacks1 _ _ _ _ i))^-1
    ).
  - split.
    + apply equiv_isequiv.
    + exact (fun _ => _).
Defined.

Inductive Poly : Type :=
  | identity : Poly
  | constant : Type -> Poly
  | constant' : Poly
  | product : Poly -> Poly -> Poly
  | coproduct : Poly -> Poly -> Poly
  | composite : Poly -> Poly -> Poly.

Fixpoint Sub (p' : Poly) A :=
  match p' with
  | identity      => identityArena
  | constant S'   => constantArena S'
  | constant'     => constantArena A
  | product p q   => productOfTwoArenas (Sub p A) (Sub q A)
  | coproduct p q => coproductOfTwoArenas (Sub p A) (Sub q A)
  | composite p q => compositeOfTwoArenas (Sub p A) (Sub q A)
  end.

Fixpoint SubMap (p' : Poly) {A B} (f : A -> B) : Lens (Sub p' A) (Sub p' B) :=
  match p' with
  | constant'     => constantLens f
  | product p q   => productOfTwoLenses (SubMap p f) (SubMap q f)
  | coproduct p q => coproductOfTwoLenses (SubMap p f) (SubMap q f)
  | composite p q => compositionProductOfTwoLenses (SubMap p f) (SubMap q f)
  | _             => identityLens
  end.

#[export] Instance SubIsFunctorToPolyCart p {A B} (f : A -> B)
  : Cartesian (SubMap p f).
Proof.
  induction p as [| S | | p h q h' | p h q h' | p h q h']; exact (fun _ => _).
Defined.

Definition SubPreservesPullbacks `{Funext} p {A B C} (f : A -> C) (g : B -> C)
  : ArenaIsomorphism
      (Sub p (Pullback f g))
      (pullbackOfLenses (SubMap p f) (SubMap p g)).
Proof.
  induction p as [| S | | p h q h' | p h q h' | p h q h'].
  - exact (constantFunctorsPreservePullbacks identityArena).
  - exact (constantFunctorsPreservePullbacks (constantArena S)).
  - apply AToAPreservesPullbacks.
  - exact (compositeOfTwoArenaIsomorphisms
      (productsCommuteWithPullbacks _ _ _ _)
      (productOfTwoArenaIsomorphisms h h')).
  - exact (compositeOfTwoArenaIsomorphisms
      (coproductsCommuteWithPullbacks _ _ _ _)
      (coproductOfTwoArenaIsomorphisms h h')).
  - exact (compositeOfTwoArenaIsomorphisms
      (compositionProductsCommuteWithPullbacks _ _ _ _)
      (compositionProductOfTwoArenaIsomorphisms h h')).
Defined.

Notation W' p := (W (positions p) (directions p)).
Notation sup p := (issig_W (positions p) (directions p)).

Definition WRecursionPrinciple (p : Arena) {X}
    : (positions (compositeOfTwoArenas p (constantArena X)) -> X)
    -> (W' p -> X) :=
  fun s => W_rect _ _ _ (fun i _ h => s (i; h)).

Definition WMap {p q} (f : Lens p q) : W' p -> W' q :=
  WRecursionPrinciple p (sup q o onPositions (compositionProductOfTwoLenses
    f
    (@identityLens (constantArena (W' q))))).

Definition sup' `{Funext} {p q r}
    (f : Lens p r) `{Cartesian _ _ f}
    (g : Lens q r) `{Cartesian _ _ g}
    : positions (compositeOfTwoArenas
        (pullbackOfLenses f g)
        (pullbackOfLenses (constantLens (WMap f)) (constantLens (WMap g))))
    <~> Pullback (WMap f) (WMap g) :=
  PullbackMap' (sup p) (sup q) (sup r) (fun _ => idpath) (fun _ => idpath)
  oE compositionProductsCommuteWithPullbacks1
    f (constantLens (WMap f))
    g (constantLens (WMap g)).

Definition WRecursionPrinciple' `{Funext} {p q r}
    (f : Lens p r) `{Cartesian _ _ f}
    (g : Lens q r) `{Cartesian _ _ g}
    {X}
    : (positions (compositeOfTwoArenas (pullbackOfLenses f g) (constantArena X))
      -> X)
    -> (Pullback (WMap f) (WMap g) -> X) :=
  fun s => sig_ind _ (W_rect _ _ _ (fun i i' h w =>
    let i'' := (sup' f g)^-1 (sup p (i; i'); w)
    in s (i''.1; fun a => h ((onDirections π' i''.1)^-1 a) (i''.2 a).2))).

Definition WPreservesPullbacks `{Funext} {p q r}
    (f : Lens p r) `{Cartesian _ _ f}
    (g : Lens q r) `{Cartesian _ _ g}
    : W' (pullbackOfLenses f g) -> Pullback (WMap f) (WMap g) :=
  WRecursionPrinciple (pullbackOfLenses f g) (sup' f g).

Definition WPreservesPullbacksInv `{Funext} {p q r}
    (f : Lens p r) `{Cartesian _ _ f}
    (g : Lens q r) `{Cartesian _ _ g}
    : Pullback (WMap f) (WMap g) -> W' (pullbackOfLenses f g) :=
  WRecursionPrinciple' f g (sup (pullbackOfLenses f g)).

Definition WSubPreservesPullbacks `{Funext} p {A B C} (f : A -> C) (g : B -> C)
    : W' (Sub p (Pullback f g))
    -> Pullback (WMap (SubMap p f)) (WMap (SubMap p g)) :=
  WPreservesPullbacks (SubMap p f) (SubMap p g)
  o WMap (SubPreservesPullbacks p f g).

Definition WSubPreservesPullbacksInv `{Funext} p {A B C}
    (f : A -> C) (g : B -> C)
    : Pullback (WMap (SubMap p f)) (WMap (SubMap p g))
    -> W' (Sub p (Pullback f g)) :=
  WMap (inverseOfArenaIso (SubPreservesPullbacks p f g))
  o WPreservesPullbacksInv (SubMap p f) (SubMap p g).

Definition unzip `{Funext} p {A B}
    : W' (Sub p (A * B))
    -> Pullback
      (WMap (SubMap p (fun _ : A => tt)))
      (WMap (SubMap p (fun _ : B => tt))) :=
  WSubPreservesPullbacks p (const tt) (const tt)
  o WMap (SubMap p (equiv_pullback_unit_prod A B)^-1).

Definition zip `{Funext} p {A B}
    : Pullback
      (WMap (SubMap p (fun _ : A => tt)))
      (WMap (SubMap p (fun _ : B => tt)))
    -> W' (Sub p (A * B)) :=
  WMap (SubMap p (equiv_pullback_unit_prod A B))
  o WSubPreservesPullbacksInv p (const tt) (const tt).

Definition ListPolynomial :=
  coproduct (constant Unit) (product constant' identity).

Definition asList {A} : W' (Sub ListPolynomial A) -> list A :=
  WRecursionPrinciple (Sub ListPolynomial A) (sig_ind _ (sum_ind _
    (fun _ _ => nil)
    (prod_ind _ (fun a _ l => cons a (l (inr tt)))))).

Definition asListInv {A} : list A -> W' (Sub ListPolynomial A).
Proof.
  refine (list_rect _ (sup (Sub ListPolynomial A) (inl tt; Empty_rec)) _).
  exact (fun a _ l => sup (Sub ListPolynomial A)
    (inr (a, tt); sum_ind _ (Empty_ind _) (fun _ => l))).
Defined.

Context `{Funext}.

Definition input' : Pullback (WMap (SubMap ListPolynomial negb)) (WMap (SubMap ListPolynomial idmap)).
  srefine (_; _; _).
  - srefine (sup _ (_; _)).
    + exact (inr (true, tt)).
    + srefine (fun _ => sup _ (_; _)).
      * exact (inr (false, tt)).
      * srefine (fun _ => sup _ (_; _)).
        -- exact (inl tt).
        -- exact Empty_rec.
  - srefine (sup _ (_; _)).
    + exact (inr (false, tt)).
    + srefine (fun _ => sup _ (_; _)).
      * exact (inr (true, tt)).
      * srefine (fun _ => sup _ (_; _)).
        -- exact (inl tt).
        -- exact Empty_rec.
  - cbn.
    refine (ap _ _).
    apply path_forall.
    refine (sum_ind _ (Empty_ind _) (Unit_ind _)).
    unfold functor_forall.
    refine (ap _ _).
    apply path_forall.
    refine (sum_ind _ (Empty_ind _) (Unit_ind _)).
    unfold functor_forall.
    refine (ap _ _).
    apply path_contr.
Defined.

Eval compute in list.map (fun x => (pullback_pr1 x, pullback_pr2 x)) (asList (WSubPreservesPullbacksInv ListPolynomial negb idmap input')).

Eval compute in asList (((WSubPreservesPullbacks ListPolynomial negb idmap o asListInv) (cons (true; false; 1) (cons (false; true; 1) nil))).1).
