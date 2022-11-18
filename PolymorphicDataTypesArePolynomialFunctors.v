From HoTT Require Import HoTT.

#[export] Existing Instance isgraph_forall | 0.

#[export] Instance categoryOfFamiliesHasEquivs (I C : Type) `{HasEquivs C}
  : HasEquivs (I -> C).
Proof.
  srapply Build_HasEquivs.
  - exact (fun c d => forall i : I, c i $<~> d i).
  - exact (fun c d f => forall i : I, CatIsEquiv (f i)).
  - exact (fun c d f i => cate_fun (f i)).
  - exact (fun c d f i => cate_isequiv (f i)).
  - exact (fun c d f h i => Build_CatEquiv (f i) (fe := h i)).
  - exact (fun c d f h i => cate_buildequiv_fun (f i)).
  - exact (fun c d f i => cate_inv (f i)).
  - exact (fun c d f i => cate_issect (f i)).
  - exact (fun c d f i => cate_isretr (f i)).
  - exact (fun c d f g ε η i => catie_adjointify (f i) (g i) (ε i) (η i)).
Defined.

Definition ind1Equivalence `{Funext} (X : Unit -> Type)
    : X tt <~> (forall i : Unit, X i) :=
  Build_Equiv _ _ (@Unit_ind X) _.

Notation ind2 := Bool_ind.
Definition rec2 {X : Type} : X -> X -> (Bool -> X) := ind2 (fun _ => X).

#[export] Instance rec2Is0Functor {C : Type} `{Is01Cat C} (c1 : C)
  : Is0Functor (rec2 c1).
Proof.
  constructor.
  exact (fun c2 c2' => ind2 _ (Id c1)).
Defined.

#[export] Instance rec2Is1Functor {C : Type} `{Is1Cat C} (c1 : C)
  : Is1Functor (rec2 c1).
Proof.
  constructor.
  - exact (fun c2 c2' f g => ind2 _ (Id (Id c1))).
  - exact (fun c2 => ind2 _ (Id (Id c1)) (Id (Id c2))).
  - exact (fun c2 c2' c2'' f f' => ind2 _ (cat_idr (Id c1))^$ (Id (f' $o f))).
Defined.

Definition ind2Equivalence `{Funext} (X : Bool -> Type)
  : X true * X false <~> (forall i : Bool, X i).
Proof.
  srapply equiv_adjointify.
  - exact (uncurry (ind2 X)).
  - exact (fun x => (x true, x false)).
  - intro x; apply path_forall; rapply ind2; reflexivity.
  - reflexivity.
Defined.

Definition eval {A B : Type} (a : A) : (A -> B) -> B := fun f => f a.

#[export] Instance evalIs0Functor (I C : Type) `{IsGraph C} (i : I)
  : Is0Functor (eval (B := C) i).
Proof.
  constructor.
  exact (fun c d f => f i).
Defined.

#[export] Instance evalIs1Functor (I C : Type) `{Is1Cat C} (i : I)
  : Is1Functor (eval (B := C) i).
Proof.
  constructor; try reflexivity.
  exact (fun c d f g w => w i).
Defined.

Definition pairing {A B X : Type} (f : X -> A) (g : X -> B) : X -> A * B :=
  prod_coind f g.

#[export] Instance pairingIs0Functor
  {C D E : Type} `{IsGraph C} `{IsGraph D} `{IsGraph E}
  (F : E -> C) `{!Is0Functor F}
  (G : E -> D) `{!Is0Functor G}
  : Is0Functor (pairing F G).
Proof.
  constructor.
  exact (fun e e' => pairing (fmap F) (fmap G)).
Defined.

#[export] Instance pairingIs1Functor
  (C D E : Type) `{Is1Cat C} `{Is1Cat D} `{Is1Cat E}
  (F : E -> C) `{!Is0Functor F, !Is1Functor F}
  (G : E -> D) `{!Is0Functor G, !Is1Functor G}
  : Is1Functor (pairing F G).
Proof.
  constructor.
  - exact (fun e e' f g => pairing (fmap2 F) (fmap2 G)).
  - exact (prod_coind (fmap_id F) (fmap_id G)).
  - exact (fun e e' e'' f g => (fmap_comp F f g, fmap_comp G f g)).
Defined.

Definition functorPairingEquivalence
  {C D E : Type} `{HasEquivs C} `{HasEquivs D} `{IsGraph E}
  {F F' : E -> C} `{!Is0Functor F} `{!Is0Functor F'} (α : NatEquiv F F')
  {G G' : E -> D} `{!Is0Functor G} `{!Is0Functor G'} (β : NatEquiv G G')
  : NatEquiv (pairing F G) (pairing F' G').
Proof.
  snrapply Build_NatEquiv.
  - exact (prod_coind α β).
  - exact (fun e e' => prod_coind (isnat α) (isnat β)).
Defined.

#[export] Instance productIs0Functor : Is0Functor (uncurry prod).
Proof.
  constructor.
  exact (fun A B => uncurry functor_prod).
Defined.

#[export] Instance productIs1Functor : Is1Functor (uncurry prod).
Proof.
  constructor; try reflexivity.
  exact (fun A B f g w a => path_prod' (fst w (fst a)) (snd w (snd a))).
Defined.

Definition Π (I : Type) : (I -> Type) -> Type := fun A => forall i : I, A i.

#[export] Instance ΠIs0Functor (I : Type) : Is0Functor (Π I).
Proof.
  constructor.
  exact (fun A B => functor_forall_id).
Defined.

#[export] Instance ΠIs1Functor `{Funext} (I : Type) : Is1Functor (Π I).
Proof.
  constructor; try reflexivity.
  exact (fun A B f g w a => path_forall _ _ (fun i => w i (a i))).
Defined.

#[export] Instance coproductIs0Functor : Is0Functor (uncurry sum).
Proof.
  constructor.
  exact (fun A B => uncurry functor_sum).
Defined.

#[export] Instance coproductIs1Functor : Is1Functor (uncurry sum).
Proof.
  constructor; try (intros; rapply sum_ind; reflexivity).
  exact (fun A B f g => uncurry functor_sum_homotopic).
Defined.

Definition Σ (I : Type) : (I -> Type) -> Type := sig.

#[export] Instance ΣIs0Functor (I : Type) : Is0Functor (Σ I).
Proof.
  constructor.
  exact (fun A B => functor_sigma idmap).
Defined.

#[export] Instance ΣIs1Functor (I : Type) : Is1Functor (Σ I).
Proof.
  constructor; try reflexivity.
  exact (fun A B f g w a => ap (exist _ (pr1 a)) (w (pr1 a) (pr2 a))).
Defined.

Definition productOfTwoFunctors {C : Type} (F G : C -> Type) : C -> Type :=
  uncurry prod o pairing F G.

Definition coproductOfTwoFunctors {C : Type} (F G : C -> Type) : C -> Type :=
  uncurry sum o pairing F G.

Record Poly (J : Type) := makePoly
  { positions : Type
  ; directions : positions -> J -> Type
  }.

Arguments positions  {J}.
Arguments directions {J}.

Definition Ext {J} (p : Poly J) (X : J -> Type) : Type :=
  {i : positions p & forall j : J, directions p i j -> X j}.

#[export] Instance ExtIs0Functor {J} (p : Poly J) : Is0Functor (Ext p).
Proof.
  constructor.
  exact (fun X Y f =>
    fmap (Σ (positions p)) (fun i =>
    fmap (Π J) (fun j =>
    fmap (Π (directions p i j)) (const (f j))))
  ).
Defined.

Definition Ext1 (p : Poly Unit) (X : Type) : Type :=
  {i : positions p & directions p i tt -> X}.

#[export] Instance Ext1Is0Functor (p : Poly Unit) : Is0Functor (Ext1 p).
Proof.
  constructor.
  exact (fun X Y f =>
    fmap (Σ (positions p)) (fun i =>
    fmap (Π (directions p i tt)) (const f))
  ).
Defined.

#[export] Instance Ext1Is1Functor `{Funext} (p : Poly Unit)
  : Is1Functor (Ext1 p).
Proof.
  constructor; try reflexivity.
  exact (fun X Y f g w =>
    fmap2 (Σ (positions p)) (fun i =>
    fmap2 (Π (directions p i tt)) (const w))
  ).
Defined.

Class IsPolynomialFunctor {J} (F : (J -> Type) -> Type) `{!Is0Functor F} :=
  makeIsPolynomialFunctor
    { polynomial : Poly J
    ; equivalenceToExtension : NatEquiv F (Ext polynomial)
    }.

Arguments makeIsPolynomialFunctor {J} F {_}.
Arguments polynomial              {J} F {_ _}.
Arguments equivalenceToExtension  {J} F {_ _}.

Class IsPolynomialFunctor1 (F : Type -> Type) `{!Is0Functor F} :=
  makeIsPolynomialFunctor1
    { polynomial1 : Poly Unit
    ; equivalenceToExtension1 : NatEquiv F (Ext1 polynomial1)
    }.

Arguments makeIsPolynomialFunctor1 F {_}.
Arguments polynomial1              F {_ _}.
Arguments equivalenceToExtension1  F {_ _}.

Definition projection1Polynomial : Poly Bool :=
  makePoly Bool Unit (fun _ => rec2 Unit Empty).

#[export] Instance projection1IsPolynomialFunctor `{Funext}
  : IsPolynomialFunctor (eval true).
Proof.
  srapply makeIsPolynomialFunctor.
  - exact projection1Polynomial.
  - apply natequiv_inverse; snrapply Build_NatEquiv.
    + intro X; symmetry.
      exact (
        (equiv_sigma_prod0 Unit _)^-1
        oE (prod_unit_l _)^-1
        oE ind2Equivalence (fun j => rec2 Unit Empty j -> X j)
        oE (equiv_unit_rec (X true) *E equiv_empty_rec (X false))
        oE (prod_unit_r (X true))^-1
      ).
    + intro; reflexivity.
Defined.

Definition projection2Polynomial : Poly Bool :=
  makePoly Bool Unit (fun _ => rec2 Empty Unit).

#[export] Instance projection2IsPolynomialFunctor `{Funext}
  : IsPolynomialFunctor (eval false).
Proof.
  srapply makeIsPolynomialFunctor.
  - exact projection2Polynomial.
  - apply natequiv_inverse; snrapply Build_NatEquiv.
    + intro X; symmetry.
      exact (
        (equiv_sigma_prod0 Unit _)^-1
        oE (prod_unit_l _)^-1
        oE ind2Equivalence (fun j => rec2 Empty Unit j -> X j)
        oE (equiv_empty_rec (X true) *E equiv_unit_rec (X false))
        oE (prod_unit_l (X false))^-1
      ).
    + intro; reflexivity.
Defined.

Definition constantPolynomial (J A : Type) : Poly J :=
  makePoly J A (fun _ _ => Empty).

#[export] Instance constantFunctorIsPolynomialFunctor `{Funext} (J A : Type)
  : IsPolynomialFunctor (const (A := J -> Type) A).
Proof.
  srapply makeIsPolynomialFunctor.
  - exact (constantPolynomial J A).
  - apply natequiv_inverse; snrapply Build_NatEquiv.
    + exact (fun X => equiv_pr1 _).
    + intro; reflexivity.
Defined.

Definition productOfTwoPolynomials {J} (p q : Poly J) : Poly J :=
  makePoly J
    (positions p * positions q)
    (fun '(i, i') j => directions p i j + directions q i' j).

#[export] Instance polynomialFunctorsAreClosedUnderProducts `{Funext} {J}
  (F G : (J -> Type) -> Type)
  `{IsPolynomialFunctor _ F}
  `{IsPolynomialFunctor _ G}
  : IsPolynomialFunctor (productOfTwoFunctors F G).
Proof.
  srapply makeIsPolynomialFunctor.
  - exact (productOfTwoPolynomials (polynomial F) (polynomial G)).
  - refine (
      natequiv_compose
      _
      (natequiv_postwhisker
        (uncurry prod)
        (functorPairingEquivalence
          (equivalenceToExtension F)
          (equivalenceToExtension G)))
    ).
    apply natequiv_inverse; snrapply Build_NatEquiv.
    + intro X; symmetry.
      refine (
           emap (Σ _) (fun i => emap (Π _) (fun j => equiv_sum_ind _))
        oE emap (Σ _) (fun i => equiv_prod_coind _ _)
        oE _
      ).
      make_equiv.
    + intro; reflexivity.
Defined.

Definition coproductOfTwoPolynomials {J} (p q : Poly J) : Poly J :=
  makePoly J
    (positions p + positions q)
    (sum_ind _ (directions p) (directions q)).

#[export] Instance polynomialFunctorsAreClosedUnderCoproducts {J}
  (F G : (J -> Type) -> Type)
  `{IsPolynomialFunctor _ F}
  `{IsPolynomialFunctor _ G}
  : IsPolynomialFunctor (coproductOfTwoFunctors F G).
Proof.
  srapply makeIsPolynomialFunctor.
  - exact (coproductOfTwoPolynomials (polynomial F) (polynomial G)).
  - refine (
      natequiv_compose
      _
      (natequiv_postwhisker
        (uncurry sum)
        (functorPairingEquivalence
          (equivalenceToExtension F)
          (equivalenceToExtension G)))
    ).
    snrapply Build_NatEquiv.
    + exact (fun X => equiv_inverse (equiv_sigma_sum _ _ _)).
    + intros X Y f []; reflexivity.
Defined.

Inductive Description : Type :=
  | projection1 : Description
  | projection2 : Description
  | constant : Type -> Description
  | product   : Description -> Description -> Description
  | coproduct : Description -> Description -> Description.

Fixpoint denotation (d : Description) : (Bool -> Type) -> Type :=
  match d with
  | projection1     => eval true
  | projection2     => eval false
  | constant A      => const A
  | product   d1 d2 => productOfTwoFunctors (denotation d1) (denotation d2)
  | coproduct d1 d2 => coproductOfTwoFunctors (denotation d1) (denotation d2)
  end.

#[export] Instance denotationIs0Functor (d : Description)
  : Is0Functor (denotation d).
Proof.
  induction d; exact _.
Defined.

#[export] Instance denotationIs1Functor `{Funext} (d : Description)
  : Is1Functor (denotation d).
Proof.
  induction d; exact _.
Defined.

#[export] Instance denotationIsPolynomialFunctor `{Funext} (d : Description)
  : IsPolynomialFunctor (denotation d).
Proof.
  induction d; exact _.
Defined.

Definition curryPolynomial (p : Poly Bool) (A : Type) : Poly Unit :=
  makePoly Unit
    {i : positions p & directions p i true -> A}
    (fun '(i; _) _ => directions p i false).

Infix "__" := curryPolynomial (at level 11).

#[export] Instance curryFunctorIsPolynomialFunctor1 `{Funext}
  (F : (Bool -> Type) -> Type) `{IsPolynomialFunctor _ F}
  (A : Type)
  : IsPolynomialFunctor1 (F o rec2 A).
Proof.
  srapply makeIsPolynomialFunctor1.
  - exact (polynomial F __ A).
  - refine (
      natequiv_compose
      _
      (natequiv_prewhisker (equivalenceToExtension F) (rec2 A))
    ).
    snrapply Build_NatEquiv.
    + refine (fun X => _ oE emap (Σ _) (fun i => (ind2Equivalence _)^-1)).
      make_equiv.
    + intro; reflexivity.
Defined.

Record Alg {C : Type} `{IsGraph C} (F : C -> C) := makeAlg
  { carrier : C
  ; structureMap : F carrier $-> carrier
  }.

Arguments makeAlg      {C _}.
Arguments carrier      {C _ F}.
Arguments structureMap {C _ F}.

#[export] Instance AlgIsGraph {C : Type} `{Is1Cat C}
  (F : C -> C) `{!Is0Functor F}
  : IsGraph (Alg F).
Proof.
  constructor.
  exact (fun a b =>
    { f : carrier a $-> carrier b
    & Square (structureMap a) (structureMap b) (fmap F f) f
    }
  ).
Defined.

#[export] Instance AlgIs2Graph {C : Type} `{Is1Cat C}
    (F : C -> C) `{!Is0Functor F}
    : Is2Graph (Alg F) :=
  fun a b => isgraph_induced pr1.

#[export] Instance AlgIs01Cat {C : Type} `{Is1Cat C}
  (F : C -> C) `{!Is0Functor F, !Is1Functor F}
  : Is01Cat (Alg F).
Proof.
  constructor.
  - srefine (fun a => (_; _)).
    + exact (Id (carrier a)).
    + exact (hrefl (structureMap a) $@vL fmap_id F (carrier a)).
  - srefine (fun a b c g f => (_; _)).
    + exact (g.1 $o f.1).
    + exact ((f.2 $@h g.2) $@vL fmap_comp F f.1 g.1).
Defined.

#[export] Instance AlgIs1Cat {C : Type} `{Is1Cat C}
  (F : C -> C) `{!Is0Functor F, !Is1Functor F}
  : Is1Cat (Alg F).
Proof.
  srapply Build_Is1Cat.
  - exact (fun a b => is01cat_induced pr1).
  - exact (fun a b => is0gpd_induced pr1).
  - intros a b c g; constructor; intros f f'.
    exact (cat_postwhisker g.1).
  - intros a b c f; constructor; intros g g'.
    exact (fmap (cat_precomp (carrier c) f.1)).
  - intros; apply cat_assoc.
  - intros; apply cat_idl.
  - intros; apply cat_idr.
Defined.

Definition AlgMap {C : Type} `{Is1Cat C}
    {F G : C -> C} `{!Is0Functor F} `{!Is0Functor G}
    (α : NatTrans G F)
    : Alg F -> Alg G :=
  fun a => makeAlg G (carrier a) (structureMap a $o α (carrier a)).

#[export] Instance AlgMapIs0Functor {C : Type} `{Is1Cat C}
  {F G : C -> C} `{!Is0Functor F} `{!Is0Functor G}
  (α : NatTrans G F)
  : Is0Functor (AlgMap α).
Proof.
  constructor.
  exact (fun a b => fmap (Σ _) (fun f => vconcat (isnat α f))).
Defined.

#[export] Instance AlgMapIs1Functor {C : Type} `{Is1Cat C}
  {F G : C -> C} `{!Is0Functor F, !Is1Functor F} `{!Is0Functor G, !Is1Functor G}
  (α : NatTrans G F)
  : Is1Functor (AlgMap α).
Proof.
  constructor.
  - exact (fun a b f g => idmap).
  - exact (fun a => Id (Id (carrier a))).
  - exact (fun a b c f g => Id (g.1 $o f.1)).
Defined.

#[export] Instance AlgMapPreservesInitialAlgebras {C : Type} `{HasEquivs C}
  {F G : C -> C} `{!Is0Functor F, !Is1Functor F} `{!Is0Functor G, !Is1Functor G}
  (α : NatEquiv G F)
  : PreservesInitial (AlgMap α).
Proof.
  srefine (fun x h a => (_; _)).
  - exact (
      fmap (Σ _)
      (fun f w => w $@hR (compose_hV_h (structureMap a) (α (carrier a)))^$)
      (fmap (AlgMap α) (mor_initial x (AlgMap (natequiv_inverse _ _ α) a)))
    ).
  - exact (fun g =>
      mor_initial_unique x (AlgMap (natequiv_inverse _ _ α) a)
        (fmap (Σ _)
        (fun g' w => w $@hL (compose_hh_V (structureMap x) (α (carrier x)))^$)
        (fmap (AlgMap (natequiv_inverse _ _ α)) g))
    ).
Defined.

Definition morphismsFromInitialAlgebraAreUnique {C : Type} `{Is1Cat C}
    {F : C -> C} `{!Is0Functor F, !Is1Functor F}
    {a b : Alg F} `{!IsInitial a} (f g : a $-> b)
    : f $== g :=
  (mor_initial_unique a b f)^$ $@ mor_initial_unique a b g.

Definition equivalenceBetweenLeastFixedPoints {C : Type} `{HasEquivs C}
    {F : C -> C} `{!Is0Functor F, !Is1Functor F}
    (a b : Alg F) `{!IsInitial a} `{!IsInitial b}
    : carrier a $<~> carrier b :=
  cate_adjointify
    (mor_initial a b).1
    (mor_initial b a).1
    (morphismsFromInitialAlgebraAreUnique
      (mor_initial a b $o mor_initial b a)
      (Id b))
    (morphismsFromInitialAlgebraAreUnique
      (mor_initial b a $o mor_initial a b)
      (Id a)).

Notation List := list.

Definition ListDescription : Description :=
  coproduct (constant Unit) (product projection1 projection2).

Notation ListBifunctor := (denotation ListDescription).
Notation ListPolynomial := (polynomial ListBifunctor).

Definition initialListAlgebra (A : Type) : Alg (ListBifunctor o rec2 A) :=
  makeAlg _ (List A) (sum_ind _ (fun _ => nil) (uncurry (@cons A))).

Definition uniqList (A : Type) {s : Alg (ListBifunctor o rec2 A)}
  (f g : initialListAlgebra A $-> s)
  : f $== g.
Proof.
  rapply list_rect.
  - exact ((f.2 (inl tt))^ @ g.2 (inl tt)).
  - exact (fun a l w =>
      (f.2 (inr (a, l)))^
      @ ap (structureMap s o inr o pair a) w
      @ g.2 (inr (a, l))
    ).
Defined.

#[export] Instance initialListAlgebraIsInitial (A : Type)
  : IsInitial (initialListAlgebra A).
Proof.
  srefine (fun s => (_; _)).
  - srefine (_; _).
    + exact (
        list_rect _
        (structureMap s (inl tt))
        (fun a _ => structureMap s o inr o pair a)
      ).
    + intros [[] |]; reflexivity.
  - rapply uniqList.
Defined.

Definition W' (p : Poly Unit) : Type :=
  W (positions p) (fun i => directions p i tt).

Definition sup {p : Poly Unit}
    : forall i : positions p, (directions p i tt -> W' p) -> W' p :=
  w_sup (positions p) (fun i => directions p i tt).

Definition initialWAlgebra (p : Poly Unit) : Alg (Ext1 p) :=
  makeAlg _ (W' p) (equiv_sig_ind' _ sup).

Definition uniqW `{Funext} (p : Poly Unit) {a : Alg (Ext1 p)}
  (f g : initialWAlgebra p $-> a)
  : f $== g.
Proof.
  rapply W_rect.
  exact (fun i t h =>
    (f.2 (i; t))^
    @ ap (structureMap a o exist _ i) (path_forall _ _ h)
    @ g.2 (i; t)
  ).
Defined.

#[export] Instance initialWAlgebraIsInitial `{Funext} (p : Poly Unit)
  : IsInitial (initialWAlgebra p).
Proof.
  srefine (fun s => (_; _)).
  - srefine (_; _).
    + exact (W_rect _ _ _ (fun i _ => structureMap s o exist _ i)).
    + intro; reflexivity.
  - rapply uniqW.
Defined.

Definition asWType `{Funext} {A : Type} : List A -> W' (ListPolynomial __ A) :=
  (mor_initial
    (initialListAlgebra A)
    (AlgMap (equivalenceToExtension1 (ListBifunctor o rec2 A))
      (initialWAlgebra (ListPolynomial __ A)))).1.

Definition asWTypeInv `{Funext} {A : Type}
    : W' (ListPolynomial __ A) -> List A :=
  (mor_initial (A := Alg (ListBifunctor o rec2 A))
    (AlgMap (equivalenceToExtension1 (ListBifunctor o rec2 A))
      (initialWAlgebra (ListPolynomial __ A)))
    (initialListAlgebra A)).1.

Definition ẆPositions (p : Poly Bool) : Type :=
  W' (makePoly Unit (positions p) (fun i _ => directions p i false)).

Fixpoint ẆDirections (p : Poly Bool) (t : ẆPositions p) : Type :=
  match t with
  | w_sup i t' =>
      directions p i true + {d : directions p i false & ẆDirections p (t' d)}
  end.

Definition Ẇ (p : Poly Bool) : Poly Unit :=
  makePoly Unit (ẆPositions p) (fun t _ => ẆDirections p t).

Definition supE {p : Poly Unit} : Ext1 p (W' p) <~> W' p := issig_W _ _.

Definition sup' `{Funext} {p : Poly Bool} {A : Type}
  : Ext1 (p __ A) (Ext1 (Ẇ p) A) <~> Ext1 (Ẇ p) A.
Proof.
  refine (
    equiv_functor_sigma_pb supE
    oE emap (Σ _) (fun it => equiv_sum_ind _)
    oE _
    oE emap (Σ _) (fun ia => emap (Σ _) (fun t => equiv_sig_ind _))
    oE emap (Σ _) (fun ia => (equiv_sig_coind _ _)^-1)
  ).
  make_equiv.
Defined.

Definition initialẆAlgebra `{Funext} (p : Poly Bool) (A : Type)
    : Alg (Ext1 (p __ A)) :=
  makeAlg (Ext1 (p __ A)) (Ext1 (Ẇ p) A) sup'.

Definition indẆ `{Funext} (p : Poly Bool) (A : Type)
    (X : Ext1 (Ẇ p) A -> Type)
    (x : forall ia t, (forall d, X (t d)) -> X (sup' (ia; t)))
    : forall t : Ext1 (Ẇ p) A, X t :=
  sig_ind _ (fix f t :=
    match t with
    | w_sup i t' => fun a =>
        eisretr sup' (sup i t'; a)
        # equiv_sig_ind' _ x
          (sup'^-1 (sup i t'; a))
          (fun d => sig_ind _ f (pr2 (sup'^-1 (sup i t'; a)) d))
    end
  ).

Definition recẆ `{Funext} (p : Poly Bool) (A : Type)
    (X : Type)
    (x : forall ia, (directions (p __ A) ia tt -> X) -> X)
    : Ext1 (Ẇ p) A -> X :=
  sig_ind _ (fix f t :=
    match t with
    | w_sup i t' => fun a =>
        sig_ind _ x
        (fmap (Ext1 (p __ A)) (sig_ind _ f) (sup'^-1 (sup i t'; a)))
    end
  ).

Definition recẆ' `{Funext} (p : Poly Bool) (A : Type)
  (x : Alg (Ext1 (p __ A)))
  : initialẆAlgebra p A $-> x.
Proof.
  srefine (_; _).
  - exact (recẆ p A (carrier x) (fun ia => structureMap x o exist _ ia)).
  - rapply sig_ind; reflexivity.
Defined.

Definition uniqẆ `{Funext} (p : Poly Bool) (A : Type) {a : Alg (Ext1 (p __ A))}
  (f g : initialẆAlgebra p A $-> a)
  : f $== g.
Proof.
  rapply indẆ.
  exact (fun i t h =>
    (f.2 (i; t))^
    @ ap (structureMap a o exist _ i) (path_forall _ _ h)
    @ g.2 (i; t)
  ).
Defined.

#[export] Instance initialẆAlgebraIsInitial `{Funext}
    (p : Poly Bool) (A : Type)
    : IsInitial (initialẆAlgebra p A) :=
  fun x => (recẆ' p A x; fun f => uniqẆ p A (recẆ' p A x) f).

Definition asẆ `{Funext} (p : Poly Bool) (A : Type)
    : W' (p __ A) -> Ext1 (Ẇ p) A :=
  (mor_initial (initialWAlgebra (p __ A)) (initialẆAlgebra p A)).1.

Definition asẆInv `{Funext} (p : Poly Bool) (A : Type)
    : Ext1 (Ẇ p) A -> W' (p __ A) :=
  (mor_initial (initialẆAlgebra p A) (initialWAlgebra (p __ A))).1.

Context `{Funext}.
Open Scope list_scope.
Open Scope nat_scope.

Eval compute in asWTypeInv (asẆInv ListPolynomial nat (fmap (Ext1 (Ẇ ListPolynomial)) S (asẆ ListPolynomial nat (asWType (0 :: 2 :: 4 :: 8 :: nil))))).
