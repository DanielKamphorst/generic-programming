Require Import HoTT.HoTT.

Arguments pullback_corec {X A B C} s {g} t {f} : rename.

Open Scope path_scope.

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

Class IsArenaIsomorphism {p q} (f : Lens p q) :=
  { isoVerticality :> Vertical f
  ; isoCartesianness :> Cartesian f
  }.

Record ArenaIsomorphism p q := makeArenaIsomorphism
  { arenaIso :> Lens p q
  ; arenaIsoInvertibility : IsArenaIsomorphism arenaIso
  }.

Arguments makeArenaIsomorphism {p q}.

Definition identityLens {p} := makeLens p p idmap (fun _ => idmap).

Definition compositeOfTwoLenses {p q r} (g : Lens q r) (f : Lens p q) :=
  makeLens p r
    (onPositions g o onPositions f)
    (fun i => onDirections f i o onDirections g (onPositions f i)).

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

Definition coproductOfTwoArenas p q := makeArena
  (positions p + positions q)
  (sum_ind _ (directions p) (directions q)).

Definition coproductOfTwoLenses {p p' q q'} (f : Lens p p') (g : Lens q q') :=
  makeLens (coproductOfTwoArenas p q) (coproductOfTwoArenas p' q')
    (functor_sum (onPositions f) (onPositions g))
    (sum_ind _ (onDirections f) (onDirections g)).

Definition compositeOfTwoArenas p q := makeArena
  {i : positions p & directions p i -> positions q}
  (fun i => {a : directions p i.1 & directions q (i.2 a)}).

Definition compositionProductOfTwoLenses {p p' q q'}
    (f : Lens p p') (g : Lens q q') :=
  makeLens (compositeOfTwoArenas p q) (compositeOfTwoArenas p' q')
    (functor_sigma
      (onPositions f)
      (fun i j => onPositions g o j o onDirections f i))
    (fun i => functor_sigma
      (onDirections f i.1)
      (onDirections g o i.2 o onDirections f i.1)).

Definition pullbackOfCartesianLenses {p q r} (f : Lens p r) (g : Lens q r) :=
  makeArena
    (Pullback (onPositions f) (onPositions g))
    (directions r o onPositions f o pullback_pr1).

Definition π' {p q r} {f : Lens p r} `{Cartesian _ _ f} {g : Lens q r} :=
  makeLens (pullbackOfCartesianLenses f g) p
    pullback_pr1
    (fun i => (onDirections f i.1)^-1).

Definition φ {p q r} {f : Lens p r} {g : Lens q r} `{Cartesian _ _ g} :=
  makeLens (pullbackOfCartesianLenses f g) q
    pullback_pr2
    (fun i => (onDirections g i.2.1 o equiv_transport (directions r) i.2.2)^-1).

Definition constantFunctorsPreservePullbacks (p : Arena)
  : ArenaIsomorphism
      p
      (pullbackOfCartesianLenses (@identityLens p) identityLens).
Proof.
  srapply makeArenaIsomorphism.
  - srapply makeLens.
    + exact (pullback_corec idmap idmap (fun _ => 1)).
    + exact (onDirections identityLens).
  - split.
    + srapply isequiv_adjointify.
      * exact pullback_pr1.
      * exact (fun _ => path_sigma' _ 1 (path_contr _ _)).
      * exact (fun _ => 1).
    + exact (fun _ => _).
Defined.

Definition AToAPreservesPullbacks {A B C} (f : A -> C) (g : B -> C)
  : ArenaIsomorphism
      (constantArena (Pullback f g))
      (pullbackOfCartesianLenses (constantLens f) (constantLens g)).
Proof.
  srapply makeArenaIsomorphism.
  - srapply makeLens.
    + exact (pullback_corec pullback_pr1 pullback_pr2 (pullback_commsq f g)).
    + exact (onDirections (constantLens pullback_pr1)).
  - split.
    + exact (isequiv_idmap (Pullback f g)).
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
  (f : Lens p r) (f' : Lens p' r') `{Cartesian _ _ f} `{Cartesian _ _ f'}
  (g : Lens q r) (g' : Lens q' r')
  : ArenaIsomorphism
      (productOfTwoArenas
        (pullbackOfCartesianLenses f g)
        (pullbackOfCartesianLenses f' g'))
      (pullbackOfCartesianLenses
        (productOfTwoLenses f f')
        (productOfTwoLenses g g')).
Proof.
  srapply makeArenaIsomorphism.
  - srapply makeLens.
    + apply productsCommuteWithPullbacks1.
    + exact (fun _ => idmap).
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
  - intros [[a1 [b1 e1]] | [a2 [b2 e2]]].
    + exact (inl a1; inl b1; e1).
    + exact (inr a2; inr b2; e2).
  - intros [[a1 | a2] [[b1 | b2] e]].
    + exact (inl (a1; b1; e)).
    + elim e.
    + elim e.
    + exact (inr (a2; b2; e)).
  - intros [[a1 | a2] [[b1 | b2] e]]; (reflexivity || elim e).
  - intros [[a1 [b1 e1]] | [a2 [b2 e2]]]; reflexivity.
Defined.

Definition coproductsCommuteWithPullbacks {p p' q q' r r'}
  (f : Lens p r) (f' : Lens p' r') `{Cartesian _ _ f} `{Cartesian _ _ f'}
  (g : Lens q r) (g' : Lens q' r')
  : ArenaIsomorphism
      (coproductOfTwoArenas
        (pullbackOfCartesianLenses f g)
        (pullbackOfCartesianLenses f' g'))
      (pullbackOfCartesianLenses
        (coproductOfTwoLenses f f')
        (coproductOfTwoLenses g g')).
Proof.
  srapply makeArenaIsomorphism.
  - srapply makeLens.
    + apply coproductsCommuteWithPullbacks1.
    + intros [i | i']; exact idmap.
  - split.
    + apply equiv_isequiv.
    + intros [i | i']; exact _.
Defined.

Inductive Poly : Type :=
  | identity : Poly
  | constant : Type -> Poly
  | constant' : Poly
  | product : Poly -> Poly -> Poly
  | coproduct : Poly -> Poly -> Poly.

Fixpoint Sub (p' : Poly) A :=
  match p' with
  | identity      => identityArena
  | constant S'   => constantArena S'
  | constant'     => constantArena A
  | product p q   => productOfTwoArenas (Sub p A) (Sub q A)
  | coproduct p q => coproductOfTwoArenas (Sub p A) (Sub q A)
  end.

Fixpoint SubMap (p' : Poly) {A B} (f : A -> B)
    : Lens (Sub p' A) (Sub p' B) :=
  match p' with
  | constant'     => constantLens f
  | product p q   => productOfTwoLenses (SubMap p f) (SubMap q f)
  | coproduct p q => coproductOfTwoLenses (SubMap p f) (SubMap q f)
  | _             => identityLens
  end.

#[export] Instance SubIsFunctorToPolyCart p {A B} (f : A -> B)
  : Cartesian (SubMap p f).
Proof.
  induction p as [| S | | p h q h' | p h q h']
    ; try exact (fun _ => _).
  exact (sum_ind _ h h').
Defined.

Definition compositeOfTwoArenaIsomorphisms {p q r}
  (g : ArenaIsomorphism q r) (f : ArenaIsomorphism p q)
  : ArenaIsomorphism p r.
Proof.
  srapply makeArenaIsomorphism.
  - exact (compositeOfTwoLenses g f).
  - split.
    + srapply isequiv_compose; apply arenaIsoInvertibility.
    + refine (fun i => _).
      srapply isequiv_compose; apply arenaIsoInvertibility.
Defined.

Definition productOfTwoArenaIsomorphisms {p p' q q'} (f : ArenaIsomorphism p p') (g : ArenaIsomorphism q q') : ArenaIsomorphism (productOfTwoArenas p q) (productOfTwoArenas p' q').
Proof.
  srapply makeArenaIsomorphism.
  - exact (productOfTwoLenses f g).
  - split.
    + rapply isequiv_functor_prod; apply arenaIsoInvertibility.
    + refine (fun i => _).
      srapply isequiv_functor_sum; apply arenaIsoInvertibility.
Defined.

Definition coproductOfTwoArenaIsomorphisms {p p' q q'} (f : ArenaIsomorphism p p') (g : ArenaIsomorphism q q') : ArenaIsomorphism (coproductOfTwoArenas p q) (coproductOfTwoArenas p' q').
Proof.
  srapply makeArenaIsomorphism.
  - exact (coproductOfTwoLenses f g).
  - split.
    + rapply isequiv_functor_sum; apply arenaIsoInvertibility.
    + refine (sum_ind _ _ _); apply arenaIsoInvertibility.
Defined.

Definition SubPreservesPullbacks (p : Poly) {A B C}
  (f : A -> C) (g : B -> C)
  : ArenaIsomorphism
      (Sub p (Pullback f g))
      (pullbackOfCartesianLenses (SubMap p f) (SubMap p g)).
Proof.
  induction p as [| S | | p h q h' | p h q h'].
  - apply constantFunctorsPreservePullbacks.
  - apply constantFunctorsPreservePullbacks.
  - apply AToAPreservesPullbacks.
  - exact (compositeOfTwoArenaIsomorphisms (productsCommuteWithPullbacks _ _ _ _) (productOfTwoArenaIsomorphisms h h')).
  - exact (compositeOfTwoArenaIsomorphisms (coproductsCommuteWithPullbacks _ _ _ _) (coproductOfTwoArenaIsomorphisms h h')).
Defined.

Definition inverseOfArenaIsomorphism {p q} (f : ArenaIsomorphism p q) : ArenaIsomorphism q p.
Proof.
  srapply makeArenaIsomorphism.
  - srapply makeLens.
    + refine (onPositions f)^-1; apply arenaIsoInvertibility.
    + refine (fun j => _).
      refine (transport (directions q) (eisretr (onPositions f) j) o (onDirections f ((onPositions f)^-1 j))^-1); apply arenaIsoInvertibility.
  - split.
    + apply isequiv_inverse.
    + refine (fun _ => _).
Defined.

Notation W' p := (W (positions p) (directions p)).
Notation sup p := (issig_W (positions p) (directions p)).

Definition WRecursionPrinciple {p X}
    : (positions (compositeOfTwoArenas p (constantArena X)) -> X)
    -> (W' p -> X) :=
  fun s => W_rect _ _ _ (fun i _ f => s (i; f)).

Definition WMap {p q} (f : Lens p q) : W' p -> W' q :=
  WRecursionPrinciple (sup q o onPositions (compositionProductOfTwoLenses
    f
    (@identityLens (constantArena (W' q))))).

Definition WRecursionPrinciple' {p q r} (f : Lens p r) (g : Lens q r) X
    : (positions (compositeOfTwoArenas (pullbackOfCartesianLenses f g) (constantArena X)) -> X)
    -> (Pullback (WMap f) (WMap g) -> X).
Proof.
  cbn.
  refine (fun s => _).
  refine (sig_ind _ _).
  refine (W_rect _ _ _ _).
  intros i t h [[j u] e % (equiv_path_wtype' _ _)].
  apply s.
  refine ((i; j; e.1); _).
  refine (fun c => h (onDirections f i c) (u (onDirections g j (e.1 # c)); happly e.2 c)).
Defined.

Definition WPreservesPullbacksInv {q q' r} (f : Lens q r) (f' : Lens q' r)
    : Pullback (WMap f) (WMap f') -> W' (pullbackOfCartesianLenses f f') :=
  WRecursionPrinciple' _ _ _ (sup _).

Definition zip (p : Poly) {A B C} (f : A -> C) (g : B -> C)
    : Pullback (WMap (SubMap p f)) (WMap (SubMap p g))
    -> W' (Sub p (Pullback f g)).
Proof.
  refine (WMap (inverseOfArenaIsomorphism (SubPreservesPullbacks p f g)) o _).
  apply WPreservesPullbacksInv.
Defined.

Definition ListPolynomial :=
  coproduct (constant Unit) (product constant' identity).

Definition asList {A} : W' (Sub ListPolynomial A) -> list A.
Proof.
  refine (W_rect _ _ _ _).
  refine (sum_ind _
    (fun _ _ _ => nil)
    (fun a _ l => cons (fst a) (l (inr tt)))).
Defined.

Context `{Funext}.

(* Can we define something like equiv_list_path inductively now using wtypes? *)

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
    refine (ap _ _).
    apply path_forall.
    refine (sum_ind _ (Empty_ind _) (Unit_ind _)).
    refine (ap _ _).
    apply path_contr.
Defined.

Eval compute in list.map (fun x => (pullback_pr1 x, pullback_pr2 x)) (asList (zip ListPolynomial _ _ input')).

(*
Definition representablesPreservePullbacks `{Funext} {S X Y Z}
    {f : X -> Z} {g : Y -> Z}
    : Pullback (よ (idmap : S -> S) f) (よ idmap g) <~> (S -> Pullback f g) :=
  equiv_sig_coind _ _ oE equiv_functor_sigma_id (fun _ =>
  equiv_sig_coind _ _ oE equiv_functor_sigma_id (fun _ => equiv_ap10 _ _)).

Definition ΣAssociativity' {A B C} {f : A -> C} {g : B -> C}
    : Pullback f g <~> {p : A * B & f (fst p) = g (snd p)} :=
  equiv_sigma_prod _.

Definition PullbackMap' {A A' B B' C C'}
    {f : A -> C} {g : B -> C}
    {f' : A' -> C'} {g' : B' -> C'}
    (α1 : A <~> A') (α2 : B <~> B') (α3 : C <~> C')
    (h1 : f' o α1 == α3 o f)
    (h2 : g' o α2 == α3 o g)
    : Pullback f g <~> Pullback f' g' :=
  ΣAssociativity'^-1
  oE equiv_functor_sigma' (α1 *E α2) (fun '(a, b) =>
    equiv_concat_r (h2 b)^ _
    oE equiv_concat_l (h1 a) _
    oE equiv_ap' α3 _ _)
  oE ΣAssociativity'.

Definition AsFunctorPreservesPullbacks `{Funext} {p p' q X X' Y}
  {f : CartesianLens p q} {f' : CartesianLens p' q}
  {h : X -> Y} {h' : X' -> Y}
  : AsFunctor (pullbackOfCartesianLenses f f') (Pullback h h')
  <~> Pullback (AsFunctorMap f h) (AsFunctorMap f' h').
Proof.
  refine (
    ΣCommutesWithPullbacks'
    oE equiv_functor_sigma_id (fun i => _ oE representablesPreservePullbacks^-1)
  ).
  refine (
    ΣAssociativity'^-1
    oE _^-1
    oE ΣAssociativity'
  ).
  refine (equiv_functor_sigma_pb (equiv_precompose' (f.2 i.1) *E equiv_precompose' (f'.2 i.2.1 oE equiv_transport _ i.2.2))).
Defined.

(*
Definition AsFunctorPreservesPullbacks `{Funext} {p p' q X X' Y}
  {f : CartesianLens p q} {f' : CartesianLens p' q}
  {h : X -> Y} {h' : X' -> Y}
  : AsFunctor (pullbackOfCartesianLenses f f') (Pullback h h')
  <~> Pullback (AsFunctorMap f h) (AsFunctorMap f' h').
Proof.
  refine (
    ΣCommutesWithPullbacks'
    oE equiv_functor_sigma_id (fun i => _ oE representablesPreservePullbacks^-1)
  ).
  refine (PullbackMap'
    (equiv_precompose' (f.2 i.1))
    (equiv_precompose' (f'.2 i.2.1 oE equiv_transport _ i.2.2))
    1 _ _)^-1 % equiv; reflexivity.
Defined.
*)
*)
