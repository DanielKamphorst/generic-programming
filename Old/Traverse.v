From HoTT Require Import HoTT.

#[export] Existing Instance isgraph_forall | 0.
#[export] Existing Instance isgraph_type.

Notation "×" := (uncurry prod).
Definition Π (I : Type) (A : I -> Type) : Type := forall i : I, A i.
Definition Σ (I : Type) : (I -> Type) -> Type := sig.

#[export] Instance xIs0Functor : Is0Functor × :=
  Build_Is0Functor _ _ _ _ × (fun _ _ => uncurry functor_prod).

#[export] Instance ΠIs0Functor (I : Type) : Is0Functor (Π I) :=
  Build_Is0Functor _ _ _ _ (Π I) (@functor_forall_id I).

#[export] Instance ΣIs0Functor (I : Type) : Is0Functor (Σ I) :=
  Build_Is0Functor _ _ _ _ (Σ I) (fun _ _ => functor_sigma idmap).

#[export] Instance xIs1Functor : Is1Functor ×.
Proof.
  apply Build_Is1Functor; try reflexivity.
  exact (fun A B f f' w a => path_prod' (fst w (fst a)) (snd w (snd a))).
Defined.

#[export] Instance ΠIs1Functor `{Funext} (I : Type) : Is1Functor (Π I).
Proof.
  apply Build_Is1Functor; try reflexivity.
  exact (fun A B f f' w a => path_forall _ _ (fun i => w i (a i))).
Defined.

#[export] Instance ΣIs1Functor (I : Type) : Is1Functor (Σ I).
Proof.
  apply Build_Is1Functor; try reflexivity.
  exact (fun A B f f' w a => ap (exist _ (pr1 a)) (w (pr1 a) (pr2 a))).
Defined.

Definition bifunctorPreservesSquare
    {C1 C2 D : Type} `{Is1Cat C1} `{Is1Cat C2} `{Is1Cat D}
    (F : C1 -> C2 -> D) `{!Is0Functor (uncurry F), !Is1Functor (uncurry F)}
    {a1 a1' b1 b1' : C1} {a2 a2' b2 b2' : C2}
    {s1 : a1 $-> a1'} {s2 : a2 $-> a2'}
    {f1 : a1 $-> b1} {f2 : a2 $-> b2} {f1' : a1' $-> b1'} {f2' : a2' $-> b2'}
    {t1 : b1 $-> b1'} {t2 : b2 $-> b2'}
    (w1 : Square f1 f1' s1 t1)
    (w2 : Square f2 f2' s2 t2)
    : Square
      (fmap11 F f1 f2) (fmap11 F f1' f2') (fmap11 F s1 s2) (fmap11 F t1 t2) :=
  @fmap_square _ _ _ _ _ _ _ _ _ _
    (a1, a2) (a1', a2') (b1, b2) (b1', b2')
    (s1, s2) (t1, t2) (f1, f2) (f1', f2')
    (uncurry F) _ _
    (w1, w2).

Definition multivariableFunctorPreservesSquare
    {I C D : Type} `{Is1Cat C} `{Is1Cat D}
    (F : (I -> C) -> D) `{!Is0Functor F, !Is1Functor F}
    {a a' b b' : I -> C}
    {s : a $-> a'}
    {f : a $-> b} {f' : a' $-> b'}
    {t : b $-> b'}
    : (forall i : I, Square (f i) (f' i) (s i) (t i))
    -> Square (fmap F f) (fmap F f') (fmap F s) (fmap F t) :=
  fmap_square F.

Record LaxMonoidalFunctor := makeLaxMonoidalFunctor
  { underlyingFunctor :> Fun11 Type Type
  ; μ
    : NatTrans
      (× o functor_prod underlyingFunctor underlyingFunctor)
      (underlyingFunctor o ×)
  ; η : Unit -> underlyingFunctor Unit
  }.

Record MonoidalNaturalTransformation (F G : LaxMonoidalFunctor) :=
  makeMonoidalNaturalTransformation
    { underlyingNaturalTransformation :> NatTrans F G
    ; compatibilityWithProduct A B
      : μ G (A, B)
        o fmap11 prod
          (underlyingNaturalTransformation A)
          (underlyingNaturalTransformation B)
      == underlyingNaturalTransformation (A * B) o μ F (A, B)
    ; compatibilityWithUnit : η G == underlyingNaturalTransformation Unit o η F
    }.

Arguments compatibilityWithUnit    {F G}.
Arguments compatibilityWithProduct {F G}.

Definition identityLaxMonoidalFunctor : LaxMonoidalFunctor :=
  makeLaxMonoidalFunctor fun11_id (nattrans_id ×) idmap.

Definition compositeOfTwoLaxMonoidalFunctors (G F : LaxMonoidalFunctor)
    : LaxMonoidalFunctor :=
  makeLaxMonoidalFunctor (fun11_compose G F)
    (nattrans_comp
      (nattrans_postwhisker G (μ F))
      (nattrans_prewhisker (μ G) (functor_prod F F)))
    (fmap G (η F) o η G).

#[export] Instance LaxMonoidalFunctorIsGraph : IsGraph LaxMonoidalFunctor :=
  Build_IsGraph _ MonoidalNaturalTransformation.

#[export] Instance domainOfτFAIs0FunctorialInF (I : Type)
    (T : (I -> Type) -> Type) `{!Is0Functor T}
    (A : I -> Type)
    : Is0Functor (fun F : LaxMonoidalFunctor => T (F o A)) :=
  Build_Is0Functor _ _ _ _
    (fun F : LaxMonoidalFunctor => T (F o A))
    (fun F G α => fmap T (α o A)).

#[export] Instance domainOfτFAIs0FunctorialInA (I : Type)
    (T : (I -> Type) -> Type) `{!Is0Functor T}
    (F : LaxMonoidalFunctor)
    : Is0Functor (fun A => T (F o A)) :=
  Build_Is0Functor _ _ _ _
    (fun A => T (F o A))
    (fun A B f => fmap T (fun i => fmap F (f i))).

#[export] Instance codomainOfτFAIs0FunctorialInF (I : Type)
    (T : (I -> Type) -> Type) `{!Is0Functor T}
    (A : I -> Type)
    : Is0Functor (fun F : LaxMonoidalFunctor => F (T A)) :=
  Build_Is0Functor _ _ _ _
    (fun F : LaxMonoidalFunctor => F (T A))
    (fun F G α => α (T A)).

Class Traversable {I : Type} (T : (I -> Type) -> Type) `{!Is0Functor T} :=
  makeTraversable
    { τ (F : LaxMonoidalFunctor) (A : I -> Type) : T (F o A) -> F (T A)
    ; τNaturality1 (A : I -> Type)
      : Is1Natural
        (fun F : LaxMonoidalFunctor => T (F o A))
        (fun F => F (T A))
        (fun F => τ F A)
    ; τNaturality2 (F : LaxMonoidalFunctor)
      : Is1Natural (fun A => T (F o A)) (F o T) (τ F)
    ; unitarity (A : I -> Type) : τ identityLaxMonoidalFunctor A == idmap
    ; linearity (F G : LaxMonoidalFunctor) (A : I -> Type)
      : τ (compositeOfTwoLaxMonoidalFunctors G F) A
      == fmap G (τ F A) o τ G (F o A)
    }.

Arguments makeTraversable {I} T {_}.
Arguments τ               {I} T {_ _}.
Arguments τNaturality1    {I} T {_ _}.
Arguments τNaturality2    {I} T {_ _}.
Arguments unitarity       {I} T {_ _}.
Arguments linearity       {I} T {_ _}.

#[export] Instance ΣIsTraversable (I : Type) : Traversable (Σ I).
Proof.
  srapply (makeTraversable (Σ I)).
  - exact (fun F A => sig_ind _ (fun i => fmap F (exist _ i))).
  - exact (fun A F G α => sig_ind _ (fun i => isnat_tr α (exist _ i))).
  - exact (fun F A B f => sig_ind _ (fun i =>
      fmap_square F (
      Build_Square
        (f01 := exist A i)
        (f21 := exist B i)
        (f10 := f i)
        (f12 := fmap (Σ I) f) (
      Id (A := _ -> _) _)))
    ).
  - reflexivity.
  - exact (fun F G A => sig_ind _ (fun i => fmap_comp G (exist (F o A) i) _)).
Defined.

Definition θ `{Funext} : NatEquiv (Π Empty) (const Unit) :=
  Build_NatEquiv (Π Empty) (const Unit)
    (fun A => equiv_contr_contr)
    (fun A B f => Id _).

#[export] Instance Π0IsTraversable `{Funext} : Traversable (Π Empty).
Proof.
  srapply (makeTraversable (Π Empty)).
  - exact (fun F A => fmap F (θ A)^-1 o η F o θ (F o A)).
  - exact (fun A F G α =>
      isnat θ (α o A)
      $@v Build_Square (f10 := idmap) (compatibilityWithUnit α)
      $@v isnat_tr α (θ A)^-1
    ).
  - exact (fun F A B f =>
      isnat θ (fun i => fmap F (f i))
      $@v hrefl (η F)
      $@vR fmap_id F Unit
      $@v fmap_square F (isnat (natequiv_inverse _ _ θ) f)
    ).
  - exact (fun A => eissect (θ A)).
  - exact (fun F G A =>
      whiskerTL (f := θ (G o F o A)) (
      whiskerBL (f := emap G (θ (F o A))) (
      whiskerBR (f := fmap (G o F) (θ A)^-1) (
      Build_Square (f12 := fmap G (η F)) (Id _))))
      $@vR (fmap_comp G _ _ $@ (_ $@L fmap_comp G _ _))
    ).
Defined.

#[export] Instance evaluationIs0Functorial (I : Type) (i : I)
    : Is0Functor (fun A : I -> Type => A i) :=
  Build_Is0Functor _ _ _ _ (fun A : I -> Type => A i) (fun A B f => f i).

Definition φ `{Funext} : NatEquiv (Π Unit) (fun A => A tt) :=
  Build_NatEquiv (Π Unit) (fun A => A tt)
    (fun A => equiv_inverse (Build_Equiv _ _ (@Unit_ind A) _))
    (fun A B f => Id _).

#[export] Instance Π1IsTraversable `{Funext} : Traversable (Π Unit).
Proof.
  srapply (makeTraversable (Π Unit)).
  - exact (fun F A => fmap F (φ A)^-1 o φ (F o A)).
  - exact (fun A F G α => isnat φ (α o A) $@v isnat_tr α (φ A)^-1).
  - exact (fun F A B f =>
      isnat φ (fun i => fmap F (f i))
      $@v fmap_square F (isnat (natequiv_inverse _ _ φ) f)
    ).
  - exact (fun A => eissect (φ A)).
  - exact (fun F G A =>
      whiskerTL (f := φ (G o F o A)) (
      whiskerBL (f := emap G (φ (F o A))) (
      whiskerBR (f := fmap (G o F) (φ A)^-1) (
      hrefl idmap)))
      $@vR fmap_comp G _ _
    ).
Defined.

#[export] Instance codomainOfσXIs0FunctorialInX (A B : Type)
    : Is0Functor (fun X => Π A (X o inl) * Π B (X o inr)) :=
  Build_Is0Functor _ _ _ _
    (fun X => Π A (X o inl) * Π B (X o inr))
    (fun X Y f => fmap11 prod (fmap (Π A) (f o inl)) (fmap (Π B) (f o inr))).

Definition σ `{Funext} {A B : Type}
    : NatEquiv (Π (A + B)) (fun X => Π A (X o inl) * Π B (X o inr)) :=
  Build_NatEquiv (Π (A + B)) (fun X => Π A (X o inl) * Π B (X o inr))
    (fun X => equiv_inverse (equiv_sum_ind X))
    (fun X Y f => Id _).

#[export] Instance ΠFinIsTraversable `{Funext} (n : nat)
  : Traversable (Π (Fin n)).
Proof.
  induction n; [exact _ |].
  srapply (makeTraversable (Π (Fin (succ n)))).
  - exact (fun F A =>
      fmap F (σ A)^-1
      o μ F (Π (Fin n) (A o inl), Π Unit (A o inr))
      o fmap11 prod (τ (Π (Fin n)) F (A o inl)) (τ (Π Unit) F (A o inr))
      o σ (F o A)
    ).
  - exact (fun A F G α =>
      isnat σ (α o A)
      $@v
        bifunctorPreservesSquare prod
        (τNaturality1 (Π (Fin n)) (A o inl) _ _ α)
        (τNaturality1 (Π Unit)    (A o inr) _ _ α)
      $@v compatibilityWithProduct α (Π (Fin n) (A o inl)) (Π Unit (A o inr))
      $@v isnat_tr α (σ A)^-1
    ).
  - exact (fun F A B f =>
      isnat σ (fun i => fmap F (f i))
      $@v
        bifunctorPreservesSquare prod
        (τNaturality2 (Π (Fin n)) F _ _ (f o inl))
        (τNaturality2 (Π Unit) F _ _ (f o inr))
      $@v
        isnat (μ F)
          (a  := (Π (Fin n) (A o inl), Π Unit (A o inr)))
          (a' := (Π (Fin n) (B o inl), Π Unit (B o inr)))
          (fmap (Π (Fin n)) (f o inl), fmap (Π Unit) (f o inr))
      $@v fmap_square F (isnat (natequiv_inverse _ _ σ) f)
    ).
  - intro A.
    refine (_ $@ cate_issect (σ A)).
    exact (
      (σ A)^-1
      $@L
        fmap22 prod _ _ _ _
        (unitarity (Π (Fin n)) (A o inl))
        (unitarity (Π Unit) (A o inr))
      $@R σ A
    ).
  - exact (fun F G A =>
      whiskerTL (f := σ (G o F o A)) (
      whiskerBL (f := emap G (σ (F o A))) (
      whiskerBR (f := fmap G (fmap F (σ A)^-1)) (
        whiskerTL
          (f :=
            fmap11 prod
            (τ (Π (Fin n)) G (F o A o inl))
            (τ (Π Unit) G (F o A o inr))) (
        whiskerBR (f := fmap G (μ F (Π (Fin n) (A o inl), Π Unit (A o inr)))) (
        isnat (μ G)
          (a := (Π (Fin n) (F o A o inl), Π Unit (F o A o inr)))
          (a' := (F (Π (Fin n) (A o inl)), F (Π Unit (A o inr))))
          (τ (Π (Fin n)) F (A o inl), τ (Π Unit) F (A o inr))))
        $@vL
          fmap22 prod _ _ _ _
          (linearity (Π (Fin n)) F G (A o inl))
          (linearity (Π Unit) F G (A o inr)))))
      $@vR (
        fmap_comp G _ _ $@ (_ $@L (
        fmap_comp G _ _ $@ (_ $@L
        fmap_comp G _ _))))
    ).
Defined.

Class Finite (A : Type) := makeFinite
  { cardinality : nat
  ; finiteness : A <~> Fin cardinality
  }.

Arguments cardinality A {_}.
Arguments finiteness A {_}.

#[export] Instance codomainOfψAIs0FunctorialInA (I I' : Type) (s : I' -> I)
    : Is0Functor (fun A => Π I' (A o s)) :=
  Build_Is0Functor _ _ _ _
    (fun A => Π I' (A o s))
    (fun A B f => fmap (Π I') (f o s)).

Definition ψ `{Funext} {I I' : Type} (s : I' <~> I)
    : NatEquiv (Π I) (fun A => Π I' (A o s)) :=
  Build_NatEquiv (Π I) (fun A => Π I' (A o s))
    (fun A => equiv_functor_forall_pb s)
    (fun A B f => Id _).

#[export] Instance ΠIsTraversable `{Funext} (I : Type) `{Finite I}
  : Traversable (Π I).
Proof.
  srapply (makeTraversable (Π I)).
  - exact (fun F A =>
      fmap F (ψ (finiteness I)^-1 A)^-1
      o τ (Π (Fin (cardinality I))) F (A o (finiteness I)^-1)
      o ψ (finiteness I)^-1 (F o A)
    ).
  - exact (fun A F G α =>
      isnat (ψ (finiteness I)^-1) (α o A)
      $@v τNaturality1 (Π (Fin (cardinality I))) (A o (finiteness I)^-1) _ _ α
      $@v isnat_tr α (ψ (finiteness I)^-1 A)^-1
    ).
  - exact (fun F A B f =>
      isnat (ψ (finiteness I)^-1) (fun i => fmap F (f i))
      $@v τNaturality2 (Π (Fin (cardinality I))) F _ _ (f o (finiteness I)^-1)
      $@v fmap_square F (isnat (natequiv_inverse _ _ (ψ (finiteness I)^-1)) f)
    ).
  - intro A.
    refine (_ $@ cate_issect (ψ (finiteness I)^-1 A)).
    exact (
      (ψ (finiteness I)^-1 A)^-1
      $@L unitarity (Π (Fin (cardinality I))) (A o (finiteness I)^-1)
      $@R ψ (finiteness I)^-1 A
    ).
  - exact (fun F G A =>
      whiskerTL (f := ψ (finiteness I)^-1 (G o F o A)) (
      whiskerBL (f := emap G (ψ (finiteness I)^-1 (F o A))) (
      whiskerBR (f := fmap (G o F) (ψ (finiteness I)^-1 A)^-1) (
      Build_Square (f21 := idmap) (
      linearity (Π (Fin (cardinality I))) F G (A o (finiteness I)^-1)))))
      $@vR (fmap_comp G _ _ $@ (_ $@L fmap_comp G _ _))
    ).
Defined.

Record Poly (J : Type) := makePoly
  { positions : Type
  ; directions : positions -> J -> Type
  }.

Arguments positions {J}.
Arguments directions {J}.

Definition eval {J} (p : Poly J) (X : J -> Type) : Type :=
  Σ (positions p) (fun i => Π J (fun j => Π (directions p i j) (fun _ => X j))).

#[export] Instance evalIs0Functor (J : Type) (p : Poly J)
    : Is0Functor (eval p) :=
  Build_Is0Functor _ _ _ _ (eval p) (fun X Y f =>
    fmap (Σ (positions p)) (fun i =>
    fmap (Π J) (fun j =>
    fmap (Π (directions p i j)) (fun _ =>
    f j)))).

Class Finitary {J : Type} (p : Poly J) := makeFinitary
  { finiteNumberOfVariables      :> Finite J
  ; finiteNumberOfDirections i j :> Finite (directions p i j)
  }.

Arguments makeFinitary {J}.
Arguments finiteNumberOfVariables {J} p {_}.
Arguments finiteNumberOfDirections {J} p {_}.

#[export] Instance finitaryPolynomialIsTraversable `{Funext} {J : Type}
  (p : Poly J) `{Finitary _ p}
  : Traversable (eval p).
Proof.
  srapply (makeTraversable (eval p)).
  - exact (fun F X =>
      τ (Σ (positions p))
        F (fun i => Π J (fun j => Π (directions p i j) (fun _ => X j)))
      o fmap (Σ (positions p)) (fun i =>
        τ (Π J) F (fun j => Π (directions p i j) (fun _ => X j)))
      o fmap (Σ (positions p)) (fun i =>
        fmap (Π J) (fun j =>
        τ (Π (directions p i j)) F (fun _ => X j)))
    ).
  - exact (fun X F G α =>
      multivariableFunctorPreservesSquare (Σ (positions p)) (fun i =>
      multivariableFunctorPreservesSquare (Π J) (fun j =>
      τNaturality1 (Π (directions p i j)) (fun _ => X j) _ _ α))
      $@v
        multivariableFunctorPreservesSquare (Σ (positions p)) (fun i =>
        τNaturality1 (Π J) (fun j => Π (directions p i j) (fun _ => X j)) _ _ α)
      $@v
        τNaturality1 (Σ (positions p))
          (fun i => Π J (fun j => Π (directions p i j) (fun _ => X j))) _ _ α
    ).
  - exact (fun F X Y f =>
      multivariableFunctorPreservesSquare (Σ (positions p)) (fun i =>
      multivariableFunctorPreservesSquare (Π J) (fun j =>
      τNaturality2 (Π (directions p i j)) F _ _ (fun _ => f j)))
      $@v
        multivariableFunctorPreservesSquare (Σ (positions p)) (fun i =>
        τNaturality2 (Π J) F _ _ (fun j =>
          fmap (Π (directions p i j)) (fun _ =>
          f j)))
      $@v
        τNaturality2 (Σ (positions p)) F _ _ (fun i =>
          fmap (Π J) (fun j =>
          fmap (Π (directions p i j)) (fun _ =>
          f j)))
    ).
  - exact (fun X =>
      vdeg_square (
      fmap2 (Σ (positions p)) (fun i =>
      fmap2 (Π J) (fun j =>
      unitarity (Π (directions p i j)) (fun _ => X j))))
      $@h
        vdeg_square (
        fmap2 (Σ (positions p)) (fun i =>
        unitarity (Π J) (fun j => Π (directions p i j) (fun _ => X j))))
      $@h
        vdeg_square (
        unitarity (Σ (positions p))
          (fun i => Π J (fun j => Π (directions p i j) (fun _ => X j))))
    ).
  - exact (fun F G X =>
      whiskerTL
        (f :=
          fmap (Σ (positions p)) (fun i =>
          fmap (Π J) (fun j =>
          τ (Π (directions p i j)) G (fun _ => F (X j))))) (
      ( whiskerBR
          (f :=
            fmap (Σ (positions p)) (fun i =>
            fmap G (
            τ (Π J) F (fun j => Π (directions p i j) (fun _ => X j))))) (
        multivariableFunctorPreservesSquare (Σ (positions p)) (fun i =>
        τNaturality2 (Π J) G _ _ (fun j =>
          τ (Π (directions p i j)) F (fun _ => X j))))
        $@hR
          fmap2 (Σ (positions p)) (fun i =>
          linearity (Π J) F G (fun j => Π (directions p i j) (fun _ => X j)))
      )
      $@v (
        τNaturality2 (Σ (positions p)) G _ _ (fun i =>
          fmap (Π J) (fun j => τ (Π (directions p i j)) F (fun _ => X j)))
        $@h
          τNaturality2 (Σ (positions p)) G _ _ (fun i =>
            τ (Π J) F (fun j => Π (directions p i j) (fun _ => X j)))
        $@h
          Build_Square (f10 := idmap) (
          linearity (Σ (positions p)) F G (fun i =>
            Π J (fun j => Π (directions p i j) (fun _ => X j))))))
      $@vL
        fmap2 (Σ (positions p)) (fun i =>
        fmap2 (Π J) (fun j =>
        linearity (Π (directions p i j)) F G (fun _ => X j)))
      $@vR (fmap_comp G _ _ $@ (_ $@L fmap_comp G _ _))
    ).
Defined.

Inductive Representation : Type :=
  | projection1 : Representation
  | projection2 : Representation
  | constant : Type -> Representation
  | product   : Representation -> Representation -> Representation
  | coproduct : Representation -> Representation -> Representation.

Definition projectionPolynomial {J : Type} `{DecidablePaths J} (j : J)
    : Poly J :=
  makePoly J Unit (fun _ j' => if dec (j = j') then Unit else Empty).

Definition constantPolynomial (J A : Type) : Poly J :=
  makePoly J A (fun _ _ => Empty).

Definition productOfTwoPolynomials {J : Type} (p q : Poly J) : Poly J :=
  makePoly J
    (positions p * positions q)
    (fun i j => directions p (fst i) j + directions q (snd i) j).

Definition coproductOfTwoPolynomials {J : Type} (p q : Poly J) : Poly J :=
  makePoly J
    (positions p + positions q)
    (sum_ind _ (directions p) (directions q)).

Fixpoint denotation (r : Representation) : Poly (Fin 2) :=
  match r with
  | projection1     => projectionPolynomial fin_zero
  | projection2     => projectionPolynomial fin_last
  | constant A      => constantPolynomial (Fin 2) A
  | product   r1 r2 => productOfTwoPolynomials (denotation r1) (denotation r2)
  | coproduct r1 r2 => coproductOfTwoPolynomials (denotation r1) (denotation r2)
  end.

Definition W' (p : Poly Unit) : Type :=
  W (positions p) (fun i => directions p i tt).

Definition ẆPositions (p : Poly (Fin 2)) : Type :=
  W' (makePoly Unit (positions p) (fun i _ => directions p i fin_last)).

Fixpoint ẆDirections (p : Poly (Fin 2)) (t : ẆPositions p) : Type :=
  match t with
  | w_sup i t' =>
      directions p i fin_zero + Σ (directions p i fin_last) (ẆDirections p o t')
  end.

Definition Ẇ (p : Poly (Fin 2)) : Poly Unit :=
  makePoly Unit (ẆPositions p) (fun i _ => ẆDirections p i).

#[export] Instance FinIsFinite (n : nat) : Finite (Fin n) :=
  makeFinite (Fin n) n 1.

#[export] Instance emptyTypeIsFinite : Finite Empty := FinIsFinite 0.
#[export] Instance unitTypeIsFinite : Finite Unit :=
  makeFinite Unit 1 (sum_empty_l Unit)^-1.

Fixpoint familyOfFiniteTypesIsClosedUnderCoproducts (m n : nat)
    : Fin m + Fin n <~> Fin (m + n) :=
  match m with
  | O       => sum_empty_l (Fin n)
  | succ m' =>
      (familyOfFiniteTypesIsClosedUnderCoproducts m' n +E 1)
      oE (equiv_sum_assoc (Fin m') (Fin n) Unit)^-1
      oE (1 +E equiv_sum_symm Unit (Fin n))
      oE equiv_sum_assoc (Fin m') Unit (Fin n)
  end.

#[export] Instance finiteTypesAreClosedUnderCoproducts
    (A B : Type) `{Finite A} `{Finite B}
    : Finite (A + B) :=
  makeFinite (A + B) _ (
    familyOfFiniteTypesIsClosedUnderCoproducts (cardinality A) (cardinality B)
    oE (finiteness A +E finiteness B)
  ).

Fixpoint ΣFinIsFinite (n : nat)
    : forall A : Fin n -> Type
    , (forall i : Fin n, Finite (A i)) -> Finite (Σ (Fin n) A) :=
  match n with
  | O       => fun A _ =>
      makeFinite (Σ Empty A) _ (equiv_pr1 A (H := Empty_ind _))
  | succ n' => fun A _ =>
      makeFinite (Σ (Fin (succ n')) A) _ (
        finiteness (Σ (Fin n') (A o inl) + A (inr tt))
        oE (1 +E equiv_contr_sigma (A o inr))
        oE equiv_sigma_sum (Fin n') Unit A
      )
  end.

#[export] Existing Instance ΣFinIsFinite.

#[export] Instance ΣIsFinite
    (I : Type)      `{Finite I}
    (A : I -> Type) `{forall i : I, Finite (A i)}
    : Finite (Σ I A) :=
  makeFinite (Σ I A) _ (
    finiteness (Σ (Fin (cardinality I)) (A o (finiteness I)^-1))
    oE (equiv_functor_sigma_pb (finiteness I)^-1)^-1
  ).

#[export] Instance projectionPolynomialIsFinitary
    {J : Type} `{DecidablePaths J, Finite J}
    (j : J)
    : Finitary (projectionPolynomial j) :=
  makeFinitary (projectionPolynomial j) _ (fun _ j' =>
    if dec (j = j') as w return Finite (if w then Unit else Empty)
    then _
    else _
  ).

#[export] Instance constantPolynomialIsFinitary (J A : Type) `{Finite J}
    : Finitary (constantPolynomial J A) :=
  makeFinitary _ _ _.

#[export] Instance productOfTwoFinitaryPolynomialsIsFinitary {J : Type}
    (p q : Poly J) `{Finitary _ p} `{Finitary _ q}
    : Finitary (productOfTwoPolynomials p q) :=
  makeFinitary _ _ _.

#[export] Instance coproductOfTwoFinitaryPolynomialsIsFinitary {J : Type}
    (p q : Poly J) `{Finitary _ p} `{Finitary _ q}
    : Finitary (coproductOfTwoPolynomials p q) :=
  makeFinitary (coproductOfTwoPolynomials p q) _
    (sum_ind _ (finiteNumberOfDirections p) (finiteNumberOfDirections q)).

Fixpoint denotationIsFinitary (r : Representation) : Finitary (denotation r) :=
  match r with
  | projection1     => projectionPolynomialIsFinitary fin_zero
  | projection2     => projectionPolynomialIsFinitary fin_last
  | constant A      => constantPolynomialIsFinitary (Fin 2) A
  | product   r1 r2 =>
      productOfTwoFinitaryPolynomialsIsFinitary (denotation r1) (denotation r2)
  | coproduct r1 r2 =>
      coproductOfTwoFinitaryPolynomialsIsFinitary
      (denotation r1)
      (denotation r2)
  end.

#[export] Existing Instance denotationIsFinitary.

#[export] Instance ẆIsFinitary (p : Poly (Fin 2)) `{Finitary _ p}
  : Finitary (Ẇ p).
Proof.
  apply (makeFinitary (Ẇ p) _).
  nrefine (fix f t :=
    match t with
    | w_sup i t' => fun _ => _
    end
  ).
  apply finiteTypesAreClosedUnderCoproducts.
  - exact _.
  - apply ΣIsFinite.
    + exact _.
    + exact (fun a => f (t' a) tt).
Defined.

#[export] Instance optionIs0Functor : Is0Functor option :=
  Build_Is0Functor _ _ _ _ option (fun A B f a' =>
    match a' with
    | Some a => Some (f a)
    | None   => None
    end).

#[export] Instance optionIs1Functor : Is1Functor option.
Proof.
  srapply Build_Is1Functor.
  - exact (fun A B f f' w a' =>
      match a' with
      | Some a => ap Some (w a)
      | None   => idpath
      end
    ).
  - exact (fun A a' =>
      match a' with
      | Some _ => idpath
      | None   => idpath
      end
    ).
  - exact (fun A B C f g a' =>
      match a' with
      | Some _ => idpath
      | None   => idpath
      end
    ).
Defined.

Definition optionLaxMonoidalFunctor : LaxMonoidalFunctor.
Proof.
  refine (makeLaxMonoidalFunctor (Build_Fun11 _ _ option) _ Some).
  snrapply Build_NatTrans.
  - exact (fun A a' =>
      match a' with
      | (Some a1, Some a2) => Some (a1, a2)
      | _                  => None
      end
    ).
  - exact (fun A B f a' =>
      match a' with
      | (Some _, Some _) => idpath
      | _                => idpath
      end
    ).
Defined.
