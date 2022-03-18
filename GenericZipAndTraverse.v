Require Import HoTT.HoTT.

Notation funext := (path_forall _ _).
Notation よ := functor_arrow.

Open Scope path_scope.

Record Arena : Type := makeArena
  { positions : Type
  ; directions : positions -> Type
  }.

Record Lens (p q : Arena) : Type := makeLens
  { onPositions : positions p -> positions q
  ; onDirections : forall i, directions q (onPositions i) -> directions p i
  }.

Arguments onPositions {p q}.
Arguments onDirections {p q}.

Definition AsFunctor (p : Arena) (X : Type) : Type :=
  {i : positions p & directions p i -> X}.

Definition AsFunctorMap {p q} (f : Lens p q) {X Y} (h : X -> Y)
    : AsFunctor p X -> AsFunctor q Y :=
  functor_sigma (onPositions f) (fun i => よ (onDirections f i) h).

Definition identityLens {p : Arena} := makeLens p p idmap (fun _ => idmap).

Definition identityArena := makeArena Unit (fun _ => Unit).

Definition yIsPolynomial `{Funext} X : X <~> AsFunctor identityArena X :=
  (equiv_sigma_prod0 _ _)^-1
  oE (prod_unit_l _)^-1
  oE Build_Equiv _ _ (fun x _ => x) _.

Definition constantArena A := makeArena A (fun _ => Empty).

Definition constantLens {A B} (f : A -> B) :=
  makeLens (constantArena A) (constantArena B) f (fun _ => idmap).

Definition constantFunctorIsPolynomial `{Funext} A X
    : A <~> AsFunctor (constantArena A) X :=
  (equiv_sigma_prod0 _ _)^-1
  oE (1 *E equiv_empty_rec _)
  oE (prod_unit_r _)^-1.

Definition coproductOfTwoArenas p q := makeArena
  (positions p + positions q)
  (sum_ind _ (directions p) (directions q)).

Definition coproductOfTwoLenses {p p' q q'} (f : Lens p p') (g : Lens q q') :=
  makeLens (coproductOfTwoArenas p q) (coproductOfTwoArenas p' q')
    (functor_sum (onPositions f) (onPositions g))
    (sum_ind _ (onDirections f) (onDirections g)).

Definition PolyIsClosedUnderΣ p q X
    : AsFunctor p X + AsFunctor q X
    <~> AsFunctor (coproductOfTwoArenas p q) X :=
  (equiv_sigma_sum _ _ _)^-1.

Definition PolyIsClosedUnderΣNaturality `{Funext} {p p' q q' : Arena}
  (f : Lens p p') (g : Lens q q') {X Y} (h : X -> Y)
  : AsFunctorMap (coproductOfTwoLenses f g) h o PolyIsClosedUnderΣ p q X
  == PolyIsClosedUnderΣ p' q' Y
     o functor_sum (AsFunctorMap f h) (AsFunctorMap g h).
Proof.
  intros [[i s] | [j t]]; reflexivity.
Defined.

Definition productOfTwoArenas p q := makeArena
  (positions p * positions q)
  (fun i => directions p (fst i) + directions q (snd i)).

Definition productOfTwoLenses {p p' q q'} (f : Lens p p') (g : Lens q q') :=
  makeLens (productOfTwoArenas p q) (productOfTwoArenas p' q')
    (functor_prod (onPositions f) (onPositions g))
    (fun i => functor_sum (onDirections f (fst i)) (onDirections g (snd i))).

Definition PolyIsClosedUnderΠ `{Funext} p q X
  : AsFunctor p X * AsFunctor q X <~> AsFunctor (productOfTwoArenas p q) X.
Proof.
  refine (equiv_functor_sigma_id (fun i => equiv_sum_distributive _ _ _) oE _).
  make_equiv.
Defined.

Definition PolyIsClosedUnderΠNaturality `{Funext} {p p' q q' : Arena}
  (f : Lens p p') (g : Lens q q') {X Y} (h : X -> Y)
  : AsFunctorMap (productOfTwoLenses f g) h o PolyIsClosedUnderΠ p q X
  == PolyIsClosedUnderΠ p' q' Y
     o functor_prod (AsFunctorMap f h) (AsFunctorMap g h).
Proof.
  intros [[i s] [j t]].
  refine (path_sigma' _ 1 (funext _)).
  intros [a | b]; reflexivity.
Defined.

Definition compositeOfTwoArenas p q := makeArena
  {i : positions p & directions p i -> positions q}
  (fun i => {a : directions p i.1 & directions q (i.2 a)}).

Definition compositionProductOfTwoLenses {p p' q q'}
    (f : Lens p p') (g : Lens q q') :=
  makeLens (compositeOfTwoArenas p q) (compositeOfTwoArenas p' q')
    (AsFunctorMap f (onPositions g))
    (fun i => functor_sigma
      (onDirections f i.1)
      (onDirections g o i.2 o onDirections f i.1)).

Definition PolyIsClosedUnderComposition p q X
    : AsFunctor p (AsFunctor q X) <~> AsFunctor (compositeOfTwoArenas p q) X :=
  equiv_sigma_assoc _ _
  oE equiv_functor_sigma_id (fun i =>
    equiv_functor_sigma_id (fun j => equiv_sig_ind _)
    oE (equiv_sig_coind _ _)^-1).

Inductive Poly : Type :=
  | identity : Poly
  | constant : Type -> Poly
  | constant' : Poly
  | product : Poly -> Poly -> Poly
  | coproduct : Poly -> Poly -> Poly
  | composite : Poly -> Poly -> Poly.

Fixpoint Sub (p' : Poly) X : Arena :=
  match p' with
  | identity      => identityArena
  | constant A    => constantArena A
  | constant'     => constantArena X
  | product p q   => productOfTwoArenas (Sub p X) (Sub q X)
  | coproduct p q => coproductOfTwoArenas (Sub p X) (Sub q X)
  | composite p q => compositeOfTwoArenas (Sub p X) (Sub q X)
  end.

Fixpoint SubMap (p' : Poly) {X Y} (f : X -> Y) : Lens (Sub p' X) (Sub p' Y) :=
  match p' with
  | constant'     => constantLens f
  | product p q   => productOfTwoLenses (SubMap p f) (SubMap q f)
  | coproduct p q => coproductOfTwoLenses (SubMap p f) (SubMap q f)
  | composite p q => compositionProductOfTwoLenses (SubMap p f) (SubMap q f)
  | _             => identityLens
  end.

Notation W' p := (W (positions p) (directions p)).
Notation sup p := (w_sup (positions p) (directions p)).

Definition WRecursionPrinciple {p : Arena} {X}
    : (AsFunctor p X -> X) -> (W' p -> X) :=
  fun s => W_rect _ _ _ (fun i _ f => s (i; f)).

Definition WMap {p q} (f : Lens p q) : W' p -> W' q :=
  WRecursionPrinciple (sig_ind (fun _ => W' q) (sup q) o AsFunctorMap f idmap).

Definition optionMap {X Y} (f : X -> Y) : option X -> option Y :=
  option_rect _ (Some o f) None.

Definition μ X Y : option X * option Y -> option (X * Y) :=
  prod_ind _ (option_rect _ (optionMap o pair) (fun _ => None)).

Fixpoint traversePolynomialInTwoVariables `{Funext} (p' : Poly) X Y
    : AsFunctor (Sub p' (option X)) (option Y)
    -> option (AsFunctor (Sub p' X) Y) :=
  match p' with
  | identity      => optionMap (yIsPolynomial _) o (yIsPolynomial _)^-1
  | constant A    =>
      optionMap (constantFunctorIsPolynomial _ _)
      o Some
      o (constantFunctorIsPolynomial _ _)^-1
  | constant'     =>
      optionMap (constantFunctorIsPolynomial _ _)
      o (constantFunctorIsPolynomial _ _)^-1
  | product p q   =>
      optionMap (PolyIsClosedUnderΠ _ _ _)
      o μ _ _
      o functor_prod
          (traversePolynomialInTwoVariables p _ _)
          (traversePolynomialInTwoVariables q _ _)
      o (PolyIsClosedUnderΠ _ _ _)^-1
  | coproduct p q =>
      optionMap (PolyIsClosedUnderΣ _ _ _)
      o sum_ind _ (optionMap inl) (optionMap inr)
      o functor_sum
          (traversePolynomialInTwoVariables p _ _)
          (traversePolynomialInTwoVariables q _ _)
      o (PolyIsClosedUnderΣ _ _ _)^-1
  | composite p q =>
      optionMap (PolyIsClosedUnderComposition _ _ _)
      o traversePolynomialInTwoVariables p _ _
      o AsFunctorMap identityLens (traversePolynomialInTwoVariables q _ _)
      o (PolyIsClosedUnderComposition _ _ _)^-1
  end.

Definition traverse `{Funext} (p : Poly) X
    : W' (Sub p (option X)) -> option (W' (Sub p X)) :=
  WRecursionPrinciple (
    optionMap (sig_ind _ (sup (Sub p X)))
    o traversePolynomialInTwoVariables p _ _).

Definition constantFunctorPreservesPullbacks X
    : X <~> Pullback (idmap : X -> X) idmap :=
  (Build_Equiv _ _ pullback_pr1 _)^-1.

Definition productsCommuteWithPullbacks {A1 A2 B1 B2 C1 C2}
  (f1 : A1 -> C1) (f2 : A2 -> C2)
  (g1 : B1 -> C1) (g2 : B2 -> C2)
  : Pullback f1 g1 * Pullback f2 g2
  <~> Pullback (functor_prod f1 f2) (functor_prod g1 g2).
Proof.
  refine (
    equiv_functor_sigma_id (fun a => equiv_functor_sigma_id (fun b =>
      equiv_path_prod _ _))
    oE _
  ).
  make_equiv.
Defined.

Definition coproductsCommuteWithPullbacks {A1 A2 B1 B2 C1 C2}
    (f1 : A1 -> C1) (f2 : A2 -> C2)
    (g1 : B1 -> C1) (g2 : B2 -> C2)
    : Pullback (functor_sum f1 f2) (functor_sum g1 g2)
    <~> Pullback f1 g1 + Pullback f2 g2 :=
  (equiv_functor_sigma_id (fun a1 =>
      sum_empty_r _
      oE (equiv_functor_sigma_id (fun b1 => (equiv_path_sum _ _)^-1)
        +E (prod_empty_r _
          oE equiv_sigma_prod0 _ _
          oE equiv_functor_sigma_id (fun b2 =>
            (equiv_path_sum (inl (f1 a1)) (inr (g2 b2)))^-1)))
      oE equiv_sigma_sum _ _ _)
    +E equiv_functor_sigma_id (fun a2 =>
      sum_empty_l _
      oE ((prod_empty_r _
          oE equiv_sigma_prod0 _ _
          oE equiv_functor_sigma_id (fun b1 =>
            (equiv_path_sum (inr (f2 a2)) (inl (g1 b1)))^-1))
        +E equiv_functor_sigma_id (fun b2 => (equiv_path_sum _ _)^-1))
      oE equiv_sigma_sum _ _ _))
  oE equiv_sigma_sum _ _ _.

Definition PullbackMap {A A' B B' C C'}
    {f : A -> C} {g : B -> C}
    {f' : A' -> C'} {g' : B' -> C'}
    (α1 : A <~> A') (α2 : B <~> B') (α3 : C <~> C')
    (h1 : f' o α1 == α3 o f)
    (h2 : g' o α2 == α3 o g)
    : Pullback f g <~> Pullback f' g' :=
  (equiv_sigma_prod (fun p' => f' (fst p') = g' (snd p')))^-1
  oE equiv_functor_sigma' (α1 *E α2) (fun p =>
    equiv_concat_r (h2 (snd p))^ _
    oE equiv_concat_l (h1 (fst p)) _
    oE equiv_ap' α3 _ _)
  oE equiv_sigma_prod _.

Fixpoint zipPolynomialInTwoVariables `{Funext} (p' : Poly) {A1 A2 B1 B2 C1 C2}
  (f1 : A1 -> C1) (f2 : A2 -> C2)
  (g1 : B1 -> C1) (g2 : B2 -> C2)
  {struct p'}
  : AsFunctor (Sub p' (Pullback f1 g1)) (Pullback f2 g2)
  <~> Pullback
    (AsFunctorMap (SubMap p' f1) f2)
    (AsFunctorMap (SubMap p' g1) g2).
Proof.
  refine (
  match p' with
  | identity      =>
      PullbackMap (yIsPolynomial A2) (yIsPolynomial B2) (yIsPolynomial C2)
        (fun _ => idpath) (fun _ => idpath)
      oE (yIsPolynomial (Pullback f2 g2))^-1
  | constant A    =>
      PullbackMap
        (constantFunctorIsPolynomial A A2)
        (constantFunctorIsPolynomial A B2)
        (constantFunctorIsPolynomial A C2)
        _ _
      oE constantFunctorPreservesPullbacks A
      oE (constantFunctorIsPolynomial A (Pullback f2 g2))^-1
  | constant'     =>
      PullbackMap
        (constantFunctorIsPolynomial A1 A2)
        (constantFunctorIsPolynomial B1 B2)
        (constantFunctorIsPolynomial C1 C2)
        _ _
      oE (constantFunctorIsPolynomial (Pullback f1 g1) (Pullback f2 g2))^-1
  | product p q   =>
      PullbackMap
        (PolyIsClosedUnderΠ _ _ _)
        (PolyIsClosedUnderΠ _ _ _)
        (PolyIsClosedUnderΠ _ _ _)
        _ _
      oE productsCommuteWithPullbacks _ _ _ _
      oE (zipPolynomialInTwoVariables _ p _ _ _ _ _ _ _ _ _ _
        *E zipPolynomialInTwoVariables _ q _ _ _ _ _ _ _ _ _ _)
      oE (PolyIsClosedUnderΠ _ _ _)^-1
  | coproduct p q =>
      PullbackMap
        (PolyIsClosedUnderΣ _ _ _)
        (PolyIsClosedUnderΣ _ _ _)
        (PolyIsClosedUnderΣ _ _ _)
        _ _
      oE (coproductsCommuteWithPullbacks _ _ _ _)^-1
      oE (zipPolynomialInTwoVariables _ p _ _ _ _ _ _ _ _ _ _
        +E zipPolynomialInTwoVariables _ q _ _ _ _ _ _ _ _ _ _)
      oE (PolyIsClosedUnderΣ _ _ _)^-1
  | composite p q =>
      PullbackMap
        (PolyIsClosedUnderComposition _ _ _)
        (PolyIsClosedUnderComposition _ _ _)
        (PolyIsClosedUnderComposition _ _ _)
        _ _
      oE zipPolynomialInTwoVariables _ p _ _ _ _ _ _ _ _ _ _
      oE Build_Equiv _ _ (AsFunctorMap identityLens
        (zipPolynomialInTwoVariables _ q _ _ _ _ _ _ _ _ _ _)) _
      oE (PolyIsClosedUnderComposition _ _ _)^-1
  end
  ).
  - refine (fun _ => path_sigma' _ 1 (path_contr _ _)).
  - refine (fun _ => path_sigma' _ 1 (path_contr _ _)).
  - refine (fun _ => path_sigma' _ 1 (path_contr _ _)).
  - refine (fun _ => path_sigma' _ 1 (path_contr _ _)).
  - apply PolyIsClosedUnderΠNaturality.
  - apply PolyIsClosedUnderΠNaturality.
  - apply PolyIsClosedUnderΣNaturality.
  - apply PolyIsClosedUnderΣNaturality.
  - refine (fun _ => 1).
  - refine (fun _ => 1).
Defined.

(*
Definition zip `{Funext} (p : Poly) {A B C} {f : A -> C} {g : B -> C}
  : Pullback (WMap (SubMap p f)) (WMap (SubMap p g))
  -> W' (Sub p (Pullback f g)).
Proof.
  refine (sig_ind _ _).
  refine (W_rect _ _ _ _).
  induction p.
  - cbn.
    refine (Unit_ind _).
    refine (fun l1 h => _).
    refine (sig_ind _ _).
    refine (W_rect _ _ _ _).
    refine (Unit_ind _).
    refine (fun l2 _ => _).
    cbn.
    intros e % ((equiv_path_wtype' _ _)^-1).
    cbn in e.
    unfold よ in e.
    unfold functor_forall in e.
    refine (h tt (l2 tt; _)).
    refine (happly e.2 tt @ _).
    refine (ap _ _).
    refine (ap _ _).
    apply transport_const.
  - cbn.
    refine (fun x _ _ => _).
    intros [[x' t] e % ((equiv_path_wtype' _ _)^-1)].
    cbn in e.
    unfold よ in e.
    unfold functor_forall in e.
    srefine (sup (constantArena T) x Empty_rec).
  - cbn.
    refine (fun a s _ => _).
    intros [[b t] e % ((equiv_path_wtype' _ _)^-1)].
    cbn in e.
    unfold よ in e.
    unfold functor_forall in e.
    refine (sup (constantArena (Pullback f g)) (a; b; e.1) Empty_rec).
  - cbn.
    refine (prod_ind _ _).
    refine (fun i i' s h => _).
    intros [[[j j'] t] e % ((equiv_path_wtype' _ _)^-1)].
    cbn in e.
    unfold よ, functor_forall, functor_prod in e.
    cbn in e.
    Check (equiv_path_prod _ _)^-1 e.1.
    Check h.
*)

(*
Definition sup' `{Funext} {q q' r}
  (f : CartesianLens q r) (f' : CartesianLens q' r)
  : AsFunctor (pullbackOfCartesianLenses f f') (Pullback (WMap f) (WMap f'))
  <~> Pullback (WMap f) (WMap f').
Proof.
  refine (equiv_inverse _).
  refine (_ oE _).
  - refine (equiv_functor_sigma_id (fun i => (ΠCommutesWithPullbacks _ _)^-1 oE _)).
    srefine (PullbackMap' (equiv_functor_forall (P := fun _ => W' q) (onDirections f i.1) (fun _ => idmap)) (equiv_functor_forall (P := fun _ => W' q') (onDirections f' i.2.1 o transport _ i.2.2) (fun _ => idmap)) 1 _ _).
    + refine (よ (onDirections f i.1) (WMap f)).
    + refine (よ (onDirections f' i.2.1 o transport _ i.2.2) (WMap f')).
    + reflexivity.
    + reflexivity.
  - refine (_ oE _).
    2: {
      refine (equiv_functor_sigma_id (fun _ => equiv_functor_sigma_id (fun _ => (equiv_path_wtype' _ _)^-1 % equiv))).
      }.
    transparent_abstract make_equiv.
Defined.

Definition WInductionPrinciple' `{Funext} {q q' r}
  (f : CartesianLens q r) (f' : CartesianLens q' r)
  (X : Pullback (WMap f) (WMap f') -> Type)
  : (forall m : AsFunctor (pullbackOfCartesianLenses f f') (Pullback (WMap f) (WMap f'))
      , (forall b, X (m.2 b)) -> X (sup' f f' m))
  -> forall w, X w.
Proof.
  refine (fun s => _).
  refine (sig_ind _ (W_rect _ _ _ _)).
  intros i g h [[i' g'] e].
  refine
    (eisretr (sup' f f') _ # s ((sup' f f')^-1 (sup q i g; sup q' i' g'; e)) _).
  refine (fun c => _).
  Check g (onDirections f i c).
  cbn in c.
  refine (h (onDirections f i c) (g' (onDirections f' i' (((equiv_path_wtype' _ _)^-1 e).1 # c)); _)).
Defined.

Definition WRecursionPrinciple' `{Funext} {q q' r}
    (f : CartesianLens q r) (f' : CartesianLens q' r) {X}
    : (AsFunctor (pullbackOfCartesianLenses f f') X -> X)
    -> (Pullback (WMap f) (WMap f') -> X) :=
  fun s => WInductionPrinciple' _ _ _ (fun '(i; _) g => s (i; g)).

Definition WPreservesPullbacks `{Funext} {q q' r}
    (f : CartesianLens q r) (f' : CartesianLens q' r)
    : W' (pullbackOfCartesianLenses f f')
    -> Pullback (WMap f) (WMap f') :=
  WRecursionPrinciple (sup' f f').

Definition WPreservesPullbacksInv `{Funext} {q q' r}
    (f : CartesianLens q r) (f' : CartesianLens q' r)
    : Pullback (WMap f) (WMap f')
    -> W' (pullbackOfCartesianLenses f f') :=
  WRecursionPrinciple' f f' (sig_ind _ (sup _)).

Definition List A := W' (ListF A).
Definition ListMap {A B} (f : A -> B) := WMap (ListFMap f).

Definition Nil {A} := sup (ListF A) (inl tt) Empty_rec.
Definition Cons {A} : A -> List A -> List A :=
  fun a l => sup (ListF A)
    (inr (a, tt))
    (equiv_functor_arrow' (sum_empty_l Unit) 1 (fun _ => l)).

Definition ListInductionPrinciple {A} X
  : X -> (A -> X -> X) -> List A -> X.
Proof.
  refine (fun x f => _).
  refine (WRecursionPrinciple _).
  refine (sig_ind _ _).
  refine (sum_ind _ _ _).
  - refine (fun _ _ => x).
  - refine (fun '(a, tt) g => f a (g (inr tt))).
Defined.

Definition asList {A} : list A -> List A := list_rect _ Nil (fun a _ => Cons a).
Definition asListInv {A} : List A -> list A :=
  ListInductionPrinciple _ nil (@cons _).

Definition ListPreservesPullbacks `{Funext} {A B C} {f : A -> C} {g : B -> C}
  : List (Pullback f g) -> Pullback (ListMap f) (ListMap g).
Proof.
  refine (WPreservesPullbacks _ _ o WMap _).
  srefine (makeLens _ _ _ _).
  - refine (SubPreservesPullbacks _ _ _).
  - refine (sum_ind _ _ _).
    + refine (fun _ => idmap).
    + refine (fun _ => idmap).
Defined.

Definition ListPreservesPullbacksInv `{Funext} {A B C} {f : A -> C} {g : B -> C}
  : Pullback (ListMap f) (ListMap g) -> List (Pullback f g).
Proof.
  refine (WMap _ o WPreservesPullbacksInv _ _).
  srefine (makeLens _ _ _ _).
  - refine (SubPreservesPullbacks _ _ _)^-1.
  - unfold positions.
    unfold directions.
    unfold pullbackOfLenses.
    refine (sig_ind _ _).
    refine (sum_ind _ _ _).
    + refine (fun _ _ => idmap).
    + refine (fun _ _ => idmap).
Defined.
*)
