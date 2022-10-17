Require Import HoTT.HoTT.

Record Functor := makeFunctor
  { onObjects : Type -> Type
  ; onMorphisms {X Y} : (X -> Y) -> (onObjects X -> onObjects Y)
  ; preservationOfComposition {X Y Z} (f : X -> Y) (g : Y -> Z)
    : onMorphisms (g o f) = onMorphisms g o onMorphisms f
  }.

Record LaxMonoidalFunctor := makeLaxMonoidalFunctor
  { F0 :> Functor
  ; ε : Unit -> onObjects F0 Unit
  ; μ {X Y} : onObjects F0 X * onObjects F0 Y -> onObjects F0 (X * Y)
  ; μNaturality {X X' Y Y'} (f : X -> X') (g : Y -> Y')
    : onMorphisms F0 (functor_prod f g) o μ
    = μ o functor_prod (onMorphisms F0 f) (onMorphisms F0 g)
  }.

Record NaturalTransformation (F G : Functor) := makeNaturalTransformation
  { component X : onObjects F X -> onObjects G X
  ; naturality {X Y} (f : X -> Y)
    : onMorphisms G f o component X = component Y o onMorphisms F f
  }.

Arguments component {F G}.
Arguments naturality {F G} θ {X Y} : rename.

Record MonoidalNaturalTransformation (F G : LaxMonoidalFunctor) :=
  makeMonoidalNaturalTransformation
    { θ0 :> NaturalTransformation F G
    ; compatibilityWithUnit : component θ0 Unit o ε F = ε G
    ; compatibilityWithProduct X Y
      : μ G o functor_prod (component θ0 X) (component θ0 Y)
      = component θ0 (X * Y) o μ F
    }.

Arguments compatibilityWithUnit {F G} θ : rename.
Arguments compatibilityWithProduct {F G} θ : rename.

Definition pasteTogetherTwoCommutativeSquares {A B B' C C' D}
    {f : A -> B} {g : B -> C} {h : C -> D}
    {f' : A -> B'} {g'' : B' -> C'} {h' : C' -> D}
    {g' : B' -> C}
    (w1 : g' o f' = g o f) (w2 : h' o g'' = h o g')
    : h' o g'' o f' = h o g o f :=
  ap (fun k => k o f') w2 @ ap (fun k => h o k) w1.

Definition functorPreservesCommutativeTriangle (F : Functor) {X Y Z}
    {f : X -> Y} {g : Y -> Z} {h : X -> Z}
    (w : h = g o f)
    : onMorphisms F h = onMorphisms F g o onMorphisms F f :=
  ap (onMorphisms F) w @ preservationOfComposition F f g.

Definition functorPreservesCommutativeSquare (F : Functor) {X Y Y' Z}
    {f : X -> Y} {g : Y -> Z}
    {f' : X -> Y'} {g' : Y' -> Z}
    (w : g o f = g' o f')
    : onMorphisms F g o onMorphisms F f = onMorphisms F g' o onMorphisms F f' :=
  (preservationOfComposition F f g)^ @ functorPreservesCommutativeTriangle F w.

Definition identityFunctor := makeLaxMonoidalFunctor
  (makeFunctor idmap (fun _ _ => idmap) (fun _ _ _ _ _ => idpath))
  idmap
  (fun _ _ => idmap)
  (fun _ _ _ _ _ _ => idpath).

Definition compositeOfTwoFunctors (G F : Functor) := makeFunctor
  (onObjects G o onObjects F)
  (fun _ _ => onMorphisms G o onMorphisms F)
  (fun _ _ _ f g =>
    functorPreservesCommutativeTriangle G (preservationOfComposition F f g)).

Definition compositeOfTwoLaxMonoidalFunctors (G F : LaxMonoidalFunctor) :=
  makeLaxMonoidalFunctor (compositeOfTwoFunctors G F)
    (onMorphisms G (ε F) o ε G)
    (fun _ _ => onMorphisms G (μ F) o μ G)
    (fun _ _ _ _ f g => pasteTogetherTwoCommutativeSquares
      (μNaturality G (onMorphisms F f) (onMorphisms F g))
      (functorPreservesCommutativeSquare G (μNaturality F f g))).

Definition ι {I} {X : I -> Type} (i : I) : X i -> sig X := exist _ i.

Notation β := @Unit_ind.
Definition βInv X : (forall i : Unit, X i) -> X tt := fun x => x tt.

Notation σ := sum_ind_uncurried.
Definition σInv {A B} X
    : (forall i : A + B, X i)
    -> (forall a : A, X (inl a)) * (forall b : B, X (inr b)) :=
  fun x => (x o inl, x o inr).

Definition traverseSum I (F : LaxMonoidalFunctor) (X : I -> Type)
    : sig (onObjects F o X) -> onObjects F (sig X) :=
  equiv_sig_ind _ (fun i => onMorphisms F (ι i)).

Definition traverseFiniteProduct0 (F : LaxMonoidalFunctor) X
    : (forall i : Empty, onObjects F (X i))
    -> onObjects F (forall i : Empty, X i) :=
  onMorphisms F (const (Empty_ind X)) o ε F o const tt.

Definition traverseFiniteProduct1 F X
    : (forall i : Unit, onObjects F (X i))
    -> onObjects F (forall i : Unit, X i) :=
  onMorphisms F (β X) o βInv (onObjects F o X).

Fixpoint traverseFiniteProduct n (F : LaxMonoidalFunctor)
    : forall X
    , (forall i : Fin n, onObjects F (X i))
    -> onObjects F (forall i : Fin n, X i) :=
  match n with
  | O    => traverseFiniteProduct0 F
  | S n' => fun X =>
      onMorphisms F (σ X)
      o μ F
      o functor_prod
        (traverseFiniteProduct n' F (X o inl))
        (traverseFiniteProduct1 F (X o inr))
      o σInv (onObjects F o X)
  end.

Definition βNaturality `{Funext} {X Y} (f : forall i : Unit, X i -> Y i)
    : functor_forall_id f o β X = β Y o f tt :=
  path_forall _ _ (fun x =>
  path_forall (functor_forall_id f (β X x)) (β Y (f tt x)) (Unit_ind idpath)).

Definition βInvNaturality {X Y} (f : forall i : Unit, X i -> Y i)
    : f tt o βInv X = βInv Y o functor_forall_id f :=
  idpath.

Definition σNaturality `{Funext} {A B X Y} (f : forall i : A + B, X i -> Y i)
  : functor_forall_id f o σ X
  = σ Y
    o functor_prod
      (functor_forall_id (f o inl))
      (functor_forall_id (f o inr)) :=
  path_forall _ _ (fun x => path_forall _ _ (sum_ind _
    (fun a => idpath (a := f (inl a) (fst x a)))
    (fun b => idpath (a := f (inr b) (snd x b))))).

Definition σInvNaturality {A B X Y} (f : forall i : A + B, X i -> Y i)
    : functor_prod (functor_forall_id (f o inl)) (functor_forall_id (f o inr))
      o σInv X
    = σInv Y o functor_forall_id f :=
  idpath.

Definition traverseFiniteProduct0Naturality1 {F G}
    (θ : MonoidalNaturalTransformation F G) X
    : component θ (forall i, X i) o traverseFiniteProduct0 F X
    = traverseFiniteProduct0 G X o functor_forall_id (component θ o X) :=
  ap (fun f => f o const tt) (pasteTogetherTwoCommutativeSquares
    (compatibilityWithUnit θ)
    (naturality θ (const (Empty_ind X)))^).

Definition traverseFiniteProduct0Naturality2 `{Funext} (F : LaxMonoidalFunctor)
  {X Y} (f : forall i, X i -> Y i)
  : onMorphisms F (functor_forall_id f) o traverseFiniteProduct0 F X
  = traverseFiniteProduct0 F Y
    o functor_forall_id (fun i => onMorphisms F (f i)) :=
  ap (fun g => g o ε F o const tt)
    (functorPreservesCommutativeTriangle F (path_contr
      (const (Empty_ind Y))
      (functor_forall_id f o const (Empty_ind X))))^.

Definition traverseFiniteProduct0Unitarity `{Funext} X
    : traverseFiniteProduct0 identityFunctor X = idmap :=
  path_contr _ _.

Definition traverseFiniteProduct0Linearity `{Funext} F G X
  : traverseFiniteProduct0 (compositeOfTwoLaxMonoidalFunctors G F) X
  = onMorphisms G (traverseFiniteProduct0 F X)
    o traverseFiniteProduct0 G (onObjects F o X).
Proof.
  refine (ap
    (fun f => f o ε G o const tt)
    (functorPreservesCommutativeSquare G _)).
  exact (ap
    (fun f => onMorphisms F (const (Empty_ind X)) o ε F o f)
    (path_contr idmap (const tt o const (Empty_ind (onObjects F o X))))).
Defined.

Definition traverseFiniteProduct1Naturality1 {F G} θ X
    : component θ (forall i, X i) o traverseFiniteProduct1 F X
    = traverseFiniteProduct1 G X o functor_forall_id (component θ o X) :=
  pasteTogetherTwoCommutativeSquares
    (βInvNaturality (component θ o X))
    (naturality θ (β X))^.

Definition traverseFiniteProduct1Naturality2 `{Funext} (F : LaxMonoidalFunctor)
  {X Y} (f : forall i, X i -> Y i)
  : onMorphisms F (functor_forall_id f) o traverseFiniteProduct1 F X
  = traverseFiniteProduct1 F Y
    o functor_forall_id (fun i => onMorphisms F (f i)) :=
  pasteTogetherTwoCommutativeSquares
    (βInvNaturality (fun i => onMorphisms F (f i)))
    (functorPreservesCommutativeSquare F (βNaturality f)).

Definition traverseFiniteProduct1Unitarity `{Funext} X
    : traverseFiniteProduct1 identityFunctor X = idmap :=
  path_forall _ _ (eisretr (β X)).

Definition traverseFiniteProduct1Linearity F G X
  : traverseFiniteProduct1 (compositeOfTwoLaxMonoidalFunctors G F) X
  = onMorphisms G (traverseFiniteProduct1 F X)
    o traverseFiniteProduct1 G (onObjects F o X) :=
  ap (fun f => f o βInv (onObjects (compositeOfTwoLaxMonoidalFunctors G F) o X))
    (functorPreservesCommutativeTriangle G idpath).

Fixpoint traverseFiniteProductNaturality1 n {F G}
  (θ : MonoidalNaturalTransformation F G)
  : forall X
  , component θ (forall i, X i) o traverseFiniteProduct n F X
  = traverseFiniteProduct n G X o functor_forall_id (component θ o X).
Proof.
  refine (
    match n with
    | O    => traverseFiniteProduct0Naturality1 θ
    | S n' => fun X => pasteTogetherTwoCommutativeSquares
        (σInvNaturality (component θ o X))
        (pasteTogetherTwoCommutativeSquares
          _
          (pasteTogetherTwoCommutativeSquares
            (compatibilityWithProduct θ _ _)^
            (naturality θ (σ X))^))
    end
  ).
  exact (ap011 functor_prod
    (traverseFiniteProductNaturality1 n' _ _ θ (X o inl))
    (traverseFiniteProduct1Naturality1 θ (X o inr))).
Defined.

Fixpoint traverseFiniteProductNaturality2 `{Funext} n (F : LaxMonoidalFunctor)
  : forall X Y (f : forall i, X i -> Y i)
  , onMorphisms F (functor_forall_id f) o traverseFiniteProduct n F X
  = traverseFiniteProduct n F Y
    o functor_forall_id (fun i => onMorphisms F (f i)).
Proof.
  refine (
    match n with
    | O    => @traverseFiniteProduct0Naturality2 _ F
    | S n' => fun X Y f => pasteTogetherTwoCommutativeSquares
        (σInvNaturality (fun i => onMorphisms F (f i)))
        (pasteTogetherTwoCommutativeSquares
          _
          (pasteTogetherTwoCommutativeSquares
            (μNaturality F _ _)
            (functorPreservesCommutativeSquare F (σNaturality f))))
    end
  ).
  exact (ap011 functor_prod
    (traverseFiniteProductNaturality2 _ n' F _ _ (f o inl))
    (traverseFiniteProduct1Naturality2 F (f o inr))).
Defined.

Fixpoint traverseFiniteProductUnitarity `{Funext} n
    : forall X, traverseFiniteProduct n identityFunctor X = idmap :=
  match n with
  | O    => traverseFiniteProduct0Unitarity
  | S n' => fun X =>
      ap (fun f => σ X o f o σInv X)
        (ap011 functor_prod
          (traverseFiniteProductUnitarity n' (X o inl))
          (traverseFiniteProduct1Unitarity (X o inr)))
      @ path_forall _ _ (eisretr (σ X))
  end.

Fixpoint traverseFiniteProductLinearity `{Funext} n F G
  : forall X
  , traverseFiniteProduct n (compositeOfTwoLaxMonoidalFunctors G F) X
  = onMorphisms G (traverseFiniteProduct n F X)
    o traverseFiniteProduct n G (onObjects F o X).
Proof.
  refine (
    match n with
    | O    => traverseFiniteProduct0Linearity F G
    | S n' => fun X => _
    end
  ).
  refine (ap (fun f => _ o μ (compositeOfTwoLaxMonoidalFunctors G F) o f o _) (ap011 functor_prod (traverseFiniteProductLinearity _ n' F G (X o inl)) (traverseFiniteProduct1Linearity F G (X o inr))) @ ap (fun f => _ o _ o f o functor_prod (traverseFiniteProduct n' G (onObjects F o X o inl)) (traverseFiniteProduct1 G (onObjects F o X o inr)) o _) (μNaturality G (traverseFiniteProduct n' F (X o inl)) (traverseFiniteProduct1 F (X o inr)))^ @ _).
  refine (ap (fun f => f o _ o _ o _ o _) (preservationOfComposition G _ _)^ @ ap (fun f => f o _ o _ o _) (preservationOfComposition G _ _)^ @ ap (fun f => f o _ o _ o _) (functorPreservesCommutativeTriangle G _)).
  reflexivity.
Defined.

Definition traverseSumNaturality1 `{Funext} I {F G} θ X
    : component θ (sig X) o traverseSum I F X
    = traverseSum I G X o functor_sigma idmap (component θ o X) :=
  path_forall _ _ (sig_ind _ (fun i => happly (naturality θ (ι i))^)).

Definition traverseSumNaturality2 `{Funext} I (F : LaxMonoidalFunctor) {X Y}
  (f : forall i, X i -> Y i)
  : onMorphisms F (functor_sigma idmap f) o traverseSum I F X
  = traverseSum I F Y o functor_sigma idmap (fun i => onMorphisms F (f i)).
Proof.
  refine (path_forall _ _ (sig_ind _ (fun i => _))).
  cbn; unfold functor_sigma, sig_ind, pr1, pr2.
  now refine (happly (functorPreservesCommutativeSquare F _)).
Defined.

Definition traverseSumUnitarity I X
    : traverseSum I identityFunctor X = idmap :=
  idpath.

Definition traverseSumLinearity `{Funext} I F G X
  : traverseSum I (compositeOfTwoLaxMonoidalFunctors G F) X
  = onMorphisms G (traverseSum I F X) o traverseSum I G (onObjects F o X).
Proof.
  refine (path_forall _ _ (sig_ind _ (fun i => _))).
  cbn; unfold sig_ind.
  now refine (happly (functorPreservesCommutativeTriangle G _)).
Defined.

Record FinitaryArena : Type := makeFinitaryArena
  { positions' : Type
  ; directions' : positions' -> nat
  }.

Definition eval (p : FinitaryArena) := makeFunctor
  (fun X => {i : positions' p & Fin (directions' p i) -> X})
  (fun _ _ f => functor_sigma idmap (fun _ => functor_arrow idmap f))
  (fun _ _ _ _ _ => idpath).

Definition traverse (p : FinitaryArena) (F : LaxMonoidalFunctor) X
    : onObjects (compositeOfTwoFunctors (eval p) F) X
    -> onObjects (compositeOfTwoFunctors F (eval p)) X :=
  traverseSum (positions' p) F (fun i => Fin (directions' p i) -> X)
  o functor_sigma idmap (fun i =>
      traverseFiniteProduct (directions' p i) F (fun _ => X)).

Definition traverseNaturality1 `{Funext} p {F G}
  (θ : MonoidalNaturalTransformation F G) X
  : component θ (onObjects (eval p) X) o traverse p F X
  = traverse p G X o onMorphisms (eval p) (component θ X).
Proof.
  refine (pasteTogetherTwoCommutativeSquares
    _
    (traverseSumNaturality1 (positions' p) θ _)).
  exact (path_forall _ _ (sig_ind _ (fun i => happly (ap
    (fun f => ι i o f)
    (traverseFiniteProductNaturality1 (directions' p i) θ (fun _ => X)))))).
Defined.

Definition traverseNaturality2 `{Funext} p (F : LaxMonoidalFunctor) {X Y}
  (f : X -> Y)
  : onMorphisms (compositeOfTwoFunctors F (eval p)) f o traverse p F X
  = traverse p F Y o onMorphisms (compositeOfTwoFunctors (eval p) F) f.
Proof.
  refine (pasteTogetherTwoCommutativeSquares
    _
    (traverseSumNaturality2 (positions' p) F (fun i => functor_arrow idmap f))).
  exact (path_forall _ _ (sig_ind _ (fun i => happly (ap (fun g => ι i o g)
    (traverseFiniteProductNaturality2 (directions' p i) F _ _ (fun _ => f)))))).
Defined.

Definition traverseUnitarity `{Funext} p X
    : traverse p identityFunctor X = idmap :=
  ap (fun f => f o _)
    (traverseSumUnitarity (positions' p) (fun i => Fin (directions' p i) -> X))
  @ path_forall _ _ (sig_ind _ (fun i => happly (ap
    (fun f => ι i o f)
    (traverseFiniteProductUnitarity (directions' p i) (fun _ => X))))).

Definition traverseLinearity `{Funext} p F G X
  : traverse p (compositeOfTwoLaxMonoidalFunctors G F) X
  = onMorphisms G (traverse p F X) o traverse p G (onObjects F X).
Proof.
  refine (ap (fun f => f o _) (traverseSumLinearity (positions' p) F G (fun i => Fin (directions' p i) -> X)) @ _).
  refine (ap (fun f => _ o _ o f) (path_forall _ _ (sig_ind _ (fun i => happly (ap (fun f => ι i o f) (traverseFiniteProductLinearity (directions' p i) F G (fun _ => X))))) : functor_sigma idmap (fun i => traverseFiniteProduct (directions' p i) (compositeOfTwoLaxMonoidalFunctors G F) (fun _ => X)) = functor_sigma idmap (fun i => onMorphisms G (traverseFiniteProduct (directions' p i) F (fun _ => X))) o functor_sigma idmap (fun i => traverseFiniteProduct (directions' p i) G (fun _ => onObjects F X))) @ _).
  refine (ap (fun f => _ o f o _) (traverseSumNaturality2 (positions' p) G (fun i => traverseFiniteProduct (directions' p i) F (fun _ => X)))^ @ _).
  exact (ap (fun f => f o _ o _) (preservationOfComposition G _ _)^).
Defined.

Definition emptySumIs0 X : {i : Empty & X i} <~> Empty.
  refine (equiv_sigma_contr X).
  exact (Empty_ind _).
Defined.

Record Arena (n : nat) : Type := makeArena
  { positions : Type
  ; directions : positions -> Fin n -> Type
  }.

Arguments positions {n}.
Arguments directions {n}.

Definition constantArena n A := makeArena n A (fun _ _ => Empty).

Definition coproductOfTwoArenas {n} (p q : Arena n) := makeArena n
  (positions p + positions q)
  (sum_ind _ (directions p) (directions q)).

Definition productOfTwoArenas {n} (p q : Arena n) := makeArena n
  (positions p * positions q)
  (fun i j => directions p (fst i) j + directions q (snd i) j).

Definition fixedPointPositions {n} (p : Arena n.+1) : Type :=
  W (positions p) (fun i => directions p i fin_last).

Fixpoint fixedPointDirections {n} (p : Arena n.+1) (i : fixedPointPositions p)
    : Fin n -> Type :=
  let (i', t) := i in fun j =>
    directions p i' (fin_incl j)
    + {a : directions p i' fin_last & fixedPointDirections p (t a) j}.

Definition fixedPoint {n} (p : Arena n.+1) :=
  makeArena n (fixedPointPositions p) (fixedPointDirections p).

Fixpoint projectionArenaDirections {n} : Fin n.+1 -> Fin n.+1 -> Type :=
  match n with
  | O    => fun _ _ => Unit
  | S n' => fun i j =>
      match i, j with
      | inr _,  inr _  => Unit
      | inl i', inl j' => projectionArenaDirections i' j'
      | _, _           => Empty
      end
  end.

Definition projectionArena {n} (i : Fin n.+1) :=
  makeArena n.+1 Unit (fun _ => projectionArenaDirections i).

Class Finite' (X : Type) := makeFinite'
  { cardinality : nat
  ; finiteness : X <~> Fin cardinality
  }.

Arguments cardinality X {_}.
Arguments finiteness X {_}.

Class Finitary {n} (p : Arena n) := finitarity i j :> Finite' (directions p i j).

#[export] Instance emptySetIsFinite : Finite' Empty := makeFinite' _ 0 1.
#[export] Instance singletonIsFinite : Finite' Unit :=
  makeFinite' _ 1 (sum_empty_l _)^-1.

Fixpoint FinPreservesCoproducts (m n : nat) : Fin m + Fin n <~> Fin (m + n) :=
  match m with
  | O    => sum_empty_l _
  | S m' =>
      (FinPreservesCoproducts m' n +E 1)
      oE (equiv_sum_assoc _ _ _)^-1
      oE (1 +E equiv_sum_symm _ _)
      oE equiv_sum_assoc _ _ _
  end.

Fixpoint FinPreservesSums (m : nat) (n : Fin m -> nat) {struct m}
  : Finite' {i : Fin m & Fin (n i)}.
Proof.
  destruct m.
  - refine (makeFinite' _ 0 _).
    apply emptySumIs0.
  - refine (makeFinite' _
      (cardinality {i : Fin m & Fin (n (fin_incl i))} + n fin_last) _).
    refine (
      _
      oE (finiteness {i : Fin m & Fin (n (fin_incl i))}
        +E equiv_contr_sigma _)
      oE equiv_sigma_sum _ _ _
    ).
    apply FinPreservesCoproducts.
Defined.

Definition isosPreserveFiniteness X Y (f : X <~> Y) `{Finite' X} : Finite' Y :=
  makeFinite' _ (cardinality X) (finiteness X oE f^-1).

#[export] Instance sumPreservesFiniteness I X
  `{Finite' I} `{forall i, Finite' (X i)}
  : Finite' {i : I & X i}.
Proof.
  apply (isosPreserveFiniteness
    {i : Fin (cardinality I) & Fin (cardinality (X ((finiteness I)^-1 i)))}
    {i : I & X i}).
  - refine (
      equiv_functor_sigma_id (fun i => (finiteness (X i))^-1)
      oE equiv_functor_sigma_pb (finiteness I)^-1
        (Q := fun i => Fin (cardinality (X i)))
    ).
  - exact (FinPreservesSums
      (cardinality I)
      (fun i => cardinality (X ((finiteness I)^-1 i)))).
Defined.

#[export] Instance coproductPreservesFiniteness X Y `{Finite' X} `{Finite' Y}
    : Finite' (X + Y) := makeFinite' _
  (cardinality X + cardinality Y)
  (FinPreservesCoproducts _ _ oE (finiteness _ +E finiteness _)).

#[export] Instance coproductPreservesFinitarity {n}
    (p q : Arena n) `{Finitary _ p} `{Finitary _ q}
    : Finitary (coproductOfTwoArenas p q) :=
  sum_ind _ finitarity finitarity.

#[export] Instance productPreservesFinitarity {n}
    (p q : Arena n) `{Finitary _ p} `{Finitary _ q}
    : Finitary (productOfTwoArenas p q).
Proof.
  intros [i j] k.
  apply coproductPreservesFiniteness; apply finitarity.
Defined.

#[export] Instance projectionsAreFinitary {n} (i : Fin n.+1)
  : Finitary (projectionArena i).
Proof.
  intros j k.
  induction n as [| n' h].
  - exact _.
  - destruct i as [i' |], k as [k' |]; try exact _.
    exact (h i' j k').
Defined.

#[export] Instance constantsAreFinitary n A : Finitary (constantArena n A) :=
  fun _ _ => _.

#[export] Instance fixedPointPreservesFinitarity {n}
  (p : Arena n.+1) `{Finitary _ p}
  : Finitary (fixedPoint p).
Proof.
  refine (W_rect _ _ _ _).
  refine (fun i t h j => _).
Defined.

Inductive P : Type :=
  | firstProjection : P
  | secondProjection : P
  | constant : Type -> P
  | product : P -> P -> P
  | coproduct : P -> P -> P.

Fixpoint denotation (p : P) : Arena 2 :=
  match p with
  | firstProjection  => projectionArena fin_zero
  | secondProjection => projectionArena (fsucc fin_zero)
  | constant A       => constantArena 2 A
  | product p1 p2    => productOfTwoArenas (denotation p1) (denotation p2)
  | coproduct p1 p2  => coproductOfTwoArenas (denotation p1) (denotation p2)
  end.

#[export] Instance pIsFinitary p : Finitary (denotation p).
Proof.
  induction p; exact _.
Defined.

Definition asFinitaryArena (p : Arena 1) `{Finitary _ p} :=
  makeFinitaryArena (positions p) (fun i => cardinality (directions p i fin_last)).

Open Scope list_scope.

Definition ListArena := fixedPoint (denotation (coproduct
  (constant Unit)
  (product firstProjection secondProjection))).

Definition asList {A} : onObjects (eval (asFinitaryArena ListArena)) A -> list A.
  refine (sig_ind _ _).
  refine (W_rect _ _ _ _).
  intros [[] | [[] []]].
  - exact (fun _ _ _ => nil).
  - exact (fun t l a => a (inr tt) :: l (inr tt) (a o inl)).
Defined.

Definition asListInv {A} : list A -> onObjects (eval (asFinitaryArena ListArena)) A.
  refine (list_rect _ (w_sup _ _ (inl tt) Empty_rec; Empty_rec) _).
  exact (fun a _ l => (w_sup _ _ (inr (tt, tt)) (fun _ => l.1); sum_ind _ l.2 (fun _ => a))).
Defined.

Definition optionMap {X Y} (f : X -> Y) : option X -> option Y :=
  option_rect _ (Some o f) None.

Definition Maybe `{Funext} : LaxMonoidalFunctor.
  srefine (makeLaxMonoidalFunctor _ _ _ _).
  - srefine (makeFunctor option (fun _ _ f => option_rect _ (Some o f) None) (fun A B C f g => path_forall _ _ (option_rect _ _ _))).
    + now intro a.
    + reflexivity.
  - exact Some.
  - exact (fun _ _ => prod_ind _ (option_rect _ (optionMap o pair) (fun _ => None))).
  - cbn.
    refine (fun X X' Y Y' f g => _).
    apply path_forall.
    intros [[x |] [y |]]; reflexivity.
Defined.

Context `{Funext}.
Open Scope nat_scope.

Eval compute in (onMorphisms Maybe asList o traverse (asFinitaryArena ListArena) Maybe nat o asListInv) (Some 3 :: Some 1 :: Some 4 :: nil).
Eval compute in (onMorphisms Maybe asList o traverse (asFinitaryArena ListArena) Maybe nat o asListInv) (Some 3 :: None :: Some 4 :: nil).
