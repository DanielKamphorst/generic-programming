Require Import HoTT.HoTT.

Record Arena (n : nat) := makeArena
  { positions : Type
  ; directions : positions -> Fin n -> Type
  }.

Arguments positions {n}.
Arguments directions {n}.

Record Lens {n} (p q : Arena n) := makeLens
  { onPositions : positions p -> positions q
  ; onDirections i j : directions q (onPositions i) j -> directions p i j
  }.

Arguments makeLens {n}.
Arguments onPositions {n p q}.
Arguments onDirections {n p q}.

Definition idLens {n} (p : Arena n) := makeLens p p idmap (fun _ _ => idmap).

Definition eval {n} (p : Arena n) (X : Fin n -> Type) : Type :=
  {i : positions p & forall j : Fin n, directions p i j -> X j}.

Definition evalMap {n} {p q : Arena n} (φ : Lens p q) {X Y : Fin n -> Type}
    (f : forall j : Fin n, X j -> Y j)
    : eval p X -> eval q Y :=
  functor_sigma
    (onPositions φ)
    (fun i => functor_forall_id (fun j =>
      functor_arrow (onDirections φ i j) (f j))).

Definition evalEquality `{Funext} {n} (p : Arena n) (X : Fin n -> Type)
    (x x' : eval p X)
    : { w : x.1 = x'.1
      & x.2 = (fun j => x'.2 j o transport (fun i => directions p i j) w)
      }
    <~> (x = x') :=
  equiv_path_sigma_contra _ x x'
  oE equiv_functor_sigma_id (fun w => equiv_concat_r
    (path_forall _ _ (fun j => (
      transport_forall_constant w^ x'.2 j
      @ path_forall _ _ (fun a =>
          transport_arrow_toconst w^ (x'.2 j) a
          @ ap (fun w' => x'.2 j (w' # a)) (inv_V w)))^))
    _).

Definition productsCommuteWithPullbacks `{Funext} I {A B C : I -> Type}
    (f : forall i : I, A i -> C i)
    (g : forall i : I, B i -> C i)
    : (forall i : I, Pullback (f i) (g i))
    <~> Pullback (functor_forall_id f) (functor_forall_id g) :=
  equiv_functor_sigma_id (fun a =>
    equiv_functor_sigma_id (fun b => (equiv_apD10 _ _ _)^-1)
    oE (equiv_sig_coind _ _)^-1)
  oE (equiv_sig_coind _ _)^-1.


Definition polynomialFunctorsPreservePullbacks `{Funext} {n} (p : Arena n)
  {A B C : Fin n -> Type}
  (f : forall j : Fin n, A j -> C j)
  (g : forall j : Fin n, B j -> C j)
  : eval p (fun j => Pullback (f j) (g j))
  <~> Pullback (evalMap (idLens p) f) (evalMap (idLens p) g).
Proof.
  refine (
    equiv_functor_sigma_id (fun x => equiv_functor_sigma_id (fun x' =>
      evalEquality p C _ _))
    oE _
    oE equiv_functor_sigma_id (fun i =>
      equiv_functor_sigma_id (fun a =>
        equiv_functor_sigma_id (fun iw => (equiv_functor_sigma_pb (
          equiv_functor_forall_id (fun j => equiv_precompose' (
            equiv_transport (fun i' => directions p i' j) iw.2))))^-1)
        oE (equiv_sigma_prod0 _ _)^-1
        oE (equiv_contr_unit^-1 *E 1)
        oE (prod_unit_l _)^-1)
      oE productsCommuteWithPullbacks (Fin n) _ _
      oE equiv_functor_forall_id (fun j =>
        productsCommuteWithPullbacks (directions p i j) _ _))
  ).
  make_equiv.
Defined.

Definition unzipPoly `{Funext} {n} (p : Arena n) {A B : Fin n -> Type}
  : eval p (fun j => A j * B j)
  <~> Pullback
    (evalMap (idLens p) (fun j (_ : A j) => tt))
    (evalMap (idLens p) (fun j (_ : B j) => tt)) :=
  polynomialFunctorsPreservePullbacks p _ _
  oE equiv_functor_sigma_id (fun i => equiv_functor_forall_id (fun j =>
    equiv_functor_arrow' 1 (equiv_pullback_unit_prod _ _)^-1)).

Definition W' (p : Arena 1) : Type :=
  W (positions p) (fun i => directions p i fin_last).

Definition fixedPointPositions (p : Arena 2) : Type :=
  W' (makeArena 1 (positions p) (fun i _ => directions p i fin_last)).

Fixpoint fixedPointDirections (p : Arena 2) (t : fixedPointPositions p)
    : Fin 1 -> Type :=
  fun _ => let 'w_sup i t' := t in
    directions p i fin_zero
    + {a : directions p i fin_last & fixedPointDirections p (t' a) fin_last}.

Definition fixedPoint (p : Arena 2) : Arena 1 :=
  makeArena 1 (fixedPointPositions p) (fixedPointDirections p).

(* Second Method *)
Definition eval1 (p : Arena 1) X : Type :=
  {i : positions p & directions p i fin_last -> X}.

Definition eval1Map {p q : Arena 1} (φ : Lens p q) {X Y} (f : X -> Y)
    : eval1 p X -> eval1 q Y :=
  functor_sigma
    (onPositions φ)
    (fun i => functor_arrow (onDirections φ i fin_last) f).

Record Algebra (p : Arena 1) := makeAlgebra
  { carrier : Type
  ; structureMap : eval1 p carrier -> carrier
  }.

Arguments carrier {p}.
Arguments structureMap {p}.

Definition AlgebraMorphism {p} (a a' : Algebra p) :=
  { f : carrier a -> carrier a'
  & structureMap a' o eval1Map (idLens p) f == f o structureMap a
  }.

Definition idAlgebraMorphism {p} (a : Algebra p) : AlgebraMorphism a a :=
  (idmap; fun _ => idpath).

Definition compositeOfTwoAlgebraMorphisms {p} {a a' a'' : Algebra p}
    (g : AlgebraMorphism a' a'') (f : AlgebraMorphism a a')
    : AlgebraMorphism a a'' :=
  (g.1 o f.1; fun x => g.2 (eval1Map (idLens p) f.1 x) @ ap g.1 (f.2 x)).

Definition sup (p : Arena 1) : eval1 p (W' p) <~> W' p :=
  issig_W (positions p) (fun i => directions p i fin_last).

Definition initialAlgebra (p : Arena 1) := makeAlgebra p (W' p) (sup p).

Fixpoint indW (p : Arena 1) {X : W' p -> Type}
    (s : forall (m : eval1 p (W' p)) (x : forall a, X (m.2 a)), X (sup p m))
    (t : W' p)
    : X t :=
  let 'w_sup i t' := t in s (i; t') (indW p s o t').

Definition recW {p} (a : Algebra p) : AlgebraMorphism (initialAlgebra p) a :=
  (indW p (fun m x => structureMap a (m.1; x)); fun _ => idpath).

Definition uniqW `{Funext} {p} {a : Algebra p}
    (f g : AlgebraMorphism (initialAlgebra p) a)
    : f.1 == g.1 :=
  indW p (fun m h =>
    (f.2 m)^
    @ ap (structureMap a o exist _ m.1) (path_forall _ _ h)
    @ g.2 m).

Definition WMap {p q : Arena 1} (φ : Lens p q) :=
  recW (makeAlgebra p (W' q) (sup q o eval1Map φ idmap)).

Definition curryArena (p : Arena 2) A := makeArena 1
  {i : positions p & directions p i fin_zero -> A}
  (fun i _ => directions p i.1 fin_last).

Definition curryArenaMap (p : Arena 2) {A B} (f : A -> B) := makeLens
  (curryArena p A) (curryArena p B)
  (functor_sigma idmap (fun _ => functor_arrow idmap f))
  (fun _ _ => idmap).

Definition asΠ `{Funext} {X : Fin 2 -> Type}
  : X fin_zero * X fin_last <~> (forall i : Fin 2, X i).
Proof.
  apply (equiv_adjointify
    (fun x => sum_ind _
      (sum_ind _ (Empty_ind _) (Unit_ind (fst x)))
      (Unit_ind (snd x)))
    (fun x : (forall i, X i) => (x fin_zero, x fin_last))).
  - intro x.
    apply path_forall.
    intros [[[] | []] | []]; reflexivity.
  - reflexivity.
Defined.

Definition asΠ' `{Funext} : Type * Type <~> (Fin 2 -> Type) := asΠ.
Definition asΠMap' `{Funext} {X1 X2 Y1 Y2}
    : (X1 -> Y1) * (X2 -> Y2)
    <~> (forall i, asΠ' (X1, X2) i -> asΠ' (Y1, Y2) i) :=
  asΠ.

Definition curryingEquivalence `{Funext} (p : Arena 2) (X : Fin 2 -> Type)
  : eval1 (curryArena p (X fin_zero)) (X fin_last) <~> eval p X.
Proof.
  refine (equiv_functor_sigma_id (fun i => asΠ) oE _).
  make_equiv.
Defined.

Definition sup' `{Funext} (p : Arena 2) {A B C} (f : A -> C) (g : B -> C)
    : eval1 (curryArena p (Pullback f g))
        (Pullback (WMap (curryArenaMap p f)).1 (WMap (curryArenaMap p g)).1)
    <~> Pullback (WMap (curryArenaMap p f)).1 (WMap (curryArenaMap p g)).1 :=
  (equiv_sigma_prod (fun t => _ (fst t) = _ (snd t)))^-1
  oE equiv_functor_sigma'
    ((sup (curryArena p A) oE (curryingEquivalence p _)^-1)
      *E (sup (curryArena p B) oE (curryingEquivalence p _)^-1))
    (fun t => equiv_ap'
      (sup (curryArena p C) oE (curryingEquivalence p _)^-1)
      (evalMap (idLens p) (asΠMap' (f, (WMap (curryArenaMap p f)).1)) (fst t))
      (evalMap (idLens p) (asΠMap' (g, (WMap (curryArenaMap p g)).1)) (snd t)))
  oE equiv_sigma_prod _
  oE polynomialFunctorsPreservePullbacks p _ _
  oE curryingEquivalence p _.

Definition initialAlgebra' `{Funext} (p : Arena 2) {A B C}
    (f : A -> C) (g : B -> C) :=
  makeAlgebra (curryArena p (Pullback f g))
    (Pullback (WMap (curryArenaMap p f)).1 (WMap (curryArenaMap p g)).1)
    (sup' p f g).

Fixpoint indW'' `{Funext} (p : Arena 2) {A B C} (f : A -> C) (g : B -> C) {X}
    (s : forall (m : eval1 _ _) (x : forall a, X (m.2 a)), X (sup' p f g m))
    (t : W' (curryArena p A))
    : forall t', X (t; t') :=
  fun t' => eisretr (sup' p f g) (t; t') # s
    ((sup' p f g)^-1 (t; t'))
    (sig_ind _ (indW'' p f g s) o ((sup' p f g)^-1 (t; t')).2).

Definition indW' `{Funext} (p : Arena 2) {A B C} (f : A -> C) (g : B -> C) {X}
    (s : forall (m : eval1 _ _) (x : forall a, X (m.2 a)), X (sup' p f g m))
    : forall t, X t :=
  sig_ind _ (indW'' p f g s).

Fixpoint recW'' `{Funext} {p : Arena 2} {A B C} {f : A -> C} {g : B -> C}
    (a : Algebra (curryArena p (Pullback f g)))
    (t : W' (curryArena p A))
    : { t' : W' (curryArena p B)
      & (WMap (curryArenaMap p f)).1 t = (WMap (curryArenaMap p g)).1 t'
      }
    -> carrier a :=
  structureMap a
  o eval1Map (idLens (curryArena p (Pullback f g))) (sig_ind _ (recW'' a))
  o (sup' p f g)^-1
  o exist _ t.

Definition recW' `{Funext} {p : Arena 2} {A B C} {f : A -> C} {g : B -> C}
  (a : Algebra (curryArena p (Pullback f g)))
  : AlgebraMorphism (initialAlgebra' p f g) a.
Proof.
  now refine
    ( sig_ind _ (recW'' a)
    ; fun x => ap _ (eissect (sup' p f g) x)^ @ _
    ).
Defined.

Definition uniqW' `{Funext} {p : Arena 2} {A B C} {f : A -> C} {g : B -> C}
    {a : Algebra (curryArena p (Pullback f g))}
    (s t : AlgebraMorphism (initialAlgebra' p f g) a)
    : s.1 == t.1 :=
  indW' p f g (fun m h =>
    (s.2 m)^
    @ ap (structureMap a o exist _ m.1) (path_forall _ _ h)
    @ t.2 m).

Definition zip `{Funext} (p : Arena 2) {A B C} (f : A -> C) (g : B -> C) :=
  recW' (initialAlgebra (curryArena p (Pullback f g))).

Definition unzip `{Funext} (p : Arena 2) {A B C} (f : A -> C) (g : B -> C) :=
  recW (initialAlgebra' p f g).

Definition zipIsIso `{Funext} (p : Arena 2) {A B C} (f : A -> C) (g : B -> C)
    : IsEquiv (zip p f g).1 :=
  isequiv_adjointify (zip p f g).1 (unzip p f g).1
    (uniqW
      (compositeOfTwoAlgebraMorphisms (zip p f g) (unzip p f g))
      (idAlgebraMorphism (initialAlgebra (curryArena p (Pullback f g)))))
    (uniqW'
      (compositeOfTwoAlgebraMorphisms (unzip p f g) (zip p f g))
      (idAlgebraMorphism (initialAlgebra' p f g))).

Definition zip' `{Funext} (p : Arena 2) {A B}
    : Pullback
      (WMap (curryArenaMap p (fun _ : A => tt))).1
      (WMap (curryArenaMap p (fun _ : B => tt))).1
    -> W' (curryArena p (A * B)) :=
  (WMap (curryArenaMap p (equiv_pullback_unit_prod A B))).1
  o (zip p (fun _ : A => tt) (fun _ : B => tt)).1.

Definition unzip' `{Funext} (p : Arena 2) {A B}
    : W' (curryArena p (A * B))
    -> Pullback
      (WMap (curryArenaMap p (fun _ : A => tt))).1
      (WMap (curryArenaMap p (fun _ : B => tt))).1 :=
  (unzip p (fun _ : A => tt) (fun _ : B => tt)).1
  o (WMap (curryArenaMap p (equiv_pullback_unit_prod A B)^-1)).1.

Open Scope list_scope.

Definition ListArena := 
  makeArena 2 (Unit + Unit) (sum_ind _ (fun _ _ => Empty) (fun _ _ => Unit)).

Definition asList {A} : eval (fixedPoint ListArena) (fun _ => A) -> list A.
Proof.
  refine (sig_ind _ _).
  refine (W_rect _ _ _ _).
  cbn.
  intros [[] | []].
  - exact (fun _ _ _ => nil).
  - cbn.
    refine (fun t l a => a (inr tt) (inl tt) :: l tt _).
    intros [[] | []].
    refine (a (inr tt) o inr o exist _ tt).
Defined.

Definition asListInv {A} : list A -> eval (fixedPoint ListArena) (fun _ => A).
Proof.
  refine (list_rect _ _ _).
  - unfold eval.
    refine (w_sup _ _ (inl tt) Empty_rec; _).
    intros [[] | []] [[] | [[] _]].
  - intros a _ l.
    unfold eval.
    refine (w_sup _ _ (inr tt) (fun _ => l.1); _).
    cbn.
    refine (fun _ => _).
    refine (sum_ind _ _ _).
    + refine (fun _ => a).
    + refine (sig_ind _ _).
      refine (fun _ => l.2 fin_last).
Defined.

Context `{Funext}.
Open Scope nat_scope.

Eval compute in asList (unzipPoly (fixedPoint ListArena) (asListInv ((0, false) :: (1, true) :: (2, false) :: nil))).1.
Eval compute in asList (unzipPoly (fixedPoint ListArena) (asListInv ((0, false) :: (1, true) :: (2, false) :: nil))).2.1.
Eval compute in @asList (nat * Bool) ((unzipPoly (fixedPoint ListArena))^-1 (asListInv (1 :: 2 :: 4 :: 8 :: 16 :: nil); asListInv (true :: false :: true :: false :: true :: nil); idpath)).

Definition asList' {A} : W' (curryArena ListArena A) -> list A :=
  (recW (makeAlgebra (curryArena ListArena A) (list A) (sig_ind _ (sig_ind _ (sum_ind _ (fun _ _ _ => nil) (fun _ a l => a tt :: l tt)))))).1.

Definition asListInv' {A} : list A -> W' (curryArena ListArena A).
  refine (list_rect _ (w_sup _ _ (inl tt; Empty_rec) Empty_rec) _).
  exact (fun a _ t => w_sup _ _ (inr tt; fun _ => a) (fun _ => t)).
Defined.

Context `{Funext}.
Eval compute in asList' (pullback_pr1 (unzip' ListArena (asListInv' ((true, 0) :: (false, 2) :: (false, 4) :: nil)))).
Eval compute in asList' (pullback_pr2 (unzip' ListArena (asListInv' ((true, 0) :: (false, 2) :: (false, 4) :: nil)))).

Axiom someAxiom : (WMap (curryArenaMap ListArena (fun _ : nat => tt))).1 (asListInv' (2 :: 4 :: 8 :: 16 :: nil)) = (WMap (curryArenaMap ListArena (fun _ : Bool => tt))).1 (asListInv' (true :: false :: true :: false :: nil)).

Eval compute in asList' (zip' ListArena (asListInv' (2 :: 4 :: 8 :: 16 :: nil); asListInv' (true :: false :: true :: false :: nil); someAxiom)).

Open Scope type_scope.

Definition someIso `{Funext} (p : Arena 2) A
  : eval1 (curryArena p A) (eval1 (fixedPoint p) A) <~> eval1 (fixedPoint p) A.
Proof.
  srefine (_ oE _ oE equiv_functor_sigma_id (fun i => equiv_functor_sigma_id (fun t => equiv_sig_ind _) oE (equiv_sig_coind _ _)^-1)).
  - exact {it : eval1 (makeArena 1 (positions p) (fun i _ => directions p i fin_last)) (W' (makeArena 1 (positions p) (fun i _ => directions p i fin_last))) & (directions p it.1 fin_zero -> A) * ({a : directions p it.1 fin_last & directions (fixedPoint p) (it.2 a) fin_last} -> A)}.
  - refine (_ oE equiv_functor_sigma_id (fun it => equiv_sum_ind _)).
    make_equiv.
  - make_equiv.
Defined.

Fixpoint fixedPointIso' `{Funext} (p : Arena 2) A (t : positions (fixedPoint p))
    : (directions (fixedPoint p) t fin_last -> A) -> W' (curryArena p A) :=
  let 'w_sup i f := t in
    sup _
    o eval1Map (idLens (curryArena p A)) (sig_ind _ (fixedPointIso' p A))
    o (someIso p A)^-1
    o exist _ (sup _ (i; f)).

Definition fixedPointIso `{Funext} (p : Arena 2) A
    : eval1 (fixedPoint p) A -> W' (curryArena p A) :=
  sig_ind _ (fixedPointIso' p A).

Fixpoint fixedPointIsoInv `{Funext} (p : Arena 2) A (t : W' (curryArena p A))
    : eval1 (fixedPoint p) A :=
  let 'w_sup i f := t
  in someIso p A (eval1Map (idLens (curryArena p A)) (fixedPointIsoInv p A) (i; f)).

Definition test1 `{Funext} (p : Arena 2) (A : Type) : fixedPointIso p A == sup _ o eval1Map (idLens (curryArena p A)) (sig_ind _ (fixedPointIso' p A)) o (someIso p A)^-1.
  intros [[i f] g].
  reflexivity.
Defined.

Definition test2 `{Funext} (p : Arena 2) (A : Type) : fixedPointIsoInv p A == someIso p A o eval1Map (idLens (curryArena p A)) (fixedPointIsoInv p A) o (sup _)^-1.
  intros [i f].
  reflexivity.
Defined.

Fixpoint fixedPointIsoIsRetraction `{Funext} (p : Arena 2) A
    (t : W' (curryArena p A))
    : fixedPointIso p A (fixedPointIsoInv p A t) = t.
refine (let 'w_sup i f := t in _).
Check test1 p A.
refine (ap (fixedPointIso p A) (test2 p A (w_sup (positions (curryArena p A)) (fun i0 : positions (curryArena p A) => directions (curryArena p A) i0 fin_last) i f)) @ test1 p A (someIso p A (eval1Map (idLens (curryArena p A)) (fixedPointIsoInv p A) ((sup (curryArena p A))^-1 (w_sup (positions (curryArena p A)) (fun i0 : positions (curryArena p A) => directions (curryArena p A) i0 fin_last) i f)))) @ _).
refine (ap (sup (curryArena p A) o eval1Map (idLens (curryArena p A)) (sig_ind (fun _ : {t0 : positions (fixedPoint p) & directions (fixedPoint p) t0 fin_last -> A} => W (positions (curryArena p A)) (fun i0 : positions (curryArena p A) => directions (curryArena p A) i0 fin_last)) (fixedPointIso' p A))) (eissect (someIso p A) (eval1Map (idLens (curryArena p A)) (fixedPointIsoInv p A) ((sup (curryArena p A))^-1 (w_sup (positions (curryArena p A)) (fun i0 : positions (curryArena p A) => directions (curryArena p A) i0 fin_last) i f)))) @ _).
Check ap (sup (curryArena p A) o eval1Map (idLens (curryArena p A)) (sig_ind (fun _ : {t0 : positions (fixedPoint p) & directions (fixedPoint p) t0 fin_last -> A} => W (positions (curryArena p A)) (fun i0 : positions (curryArena p A) => directions (curryArena p A) i0 fin_last)) (fixedPointIso' p A)) o eval1Map (idLens (curryArena p A)) (fixedPointIsoInv p A)) (eissect (sup (curryArena p A)) (i; f)).
refine (ap (sup (curryArena p A) o eval1Map (idLens (curryArena p A)) (sig_ind (fun _ : {t0 : positions (fixedPoint p) & directions (fixedPoint p) t0 fin_last -> A} => W (positions (curryArena p A)) (fun i0 : positions (curryArena p A) => directions (curryArena p A) i0 fin_last)) (fixedPointIso' p A)) o eval1Map (idLens (curryArena p A)) (fixedPointIsoInv p A)) (eissect (sup (curryArena p A)) (i; f)) @ _).
refine (ap (sup (curryArena p A)) (path_sigma' _ idpath (path_forall _ _ (fun a => fixedPointIsoIsRetraction _ p A (f a))))).
Defined.

Fixpoint fixedPointIsoIsSection' `{Funext} (p : Arena 2) A
  (t : positions (fixedPoint p))
  : forall g, fixedPointIsoInv p A (fixedPointIso p A (t; g)) = (t; g).
Proof.
  refine (let 'w_sup i f := t in _).
  unfold positions, directions.
  refine (fun g => _).
  refine (ap (fixedPointIsoInv p A) (test1 p A (w_sup (positions p) (fun i0 : positions p => directions p i0 fin_last) i f; g)) @ _).
  refine (test2 p A (sup (curryArena p A)
       (eval1Map (idLens (curryArena p A))
          (sig_ind
             (fun
                _ : {t0 : positions (fixedPoint p) &
                    directions (fixedPoint p) t0 fin_last -> A} =>
              W (positions (curryArena p A))
                (fun i0 : positions (curryArena p A) =>
                 directions (curryArena p A) i0 fin_last))
             (fixedPointIso' p A))
          ((someIso p A)^-1
             (w_sup (positions p)
                (fun i0 : positions p => directions p i0 fin_last) i f; g)))) @ _).
  refine (ap (someIso p A o eval1Map (idLens (curryArena p A)) (fixedPointIsoInv p A)) (eissect (sup (curryArena p A)) (eval1Map (idLens (curryArena p A)) (sig_ind (fun _ : {t0 : positions (fixedPoint p) & directions (fixedPoint p) t0 fin_last -> A} => W (positions (curryArena p A)) (fun i0 : positions (curryArena p A) => directions (curryArena p A) i0 fin_last)) (fixedPointIso' p A)) ((someIso p A)^-1 (w_sup (positions p) (fun i0 : positions p => directions p i0 fin_last) i f; g)))) @ _).
  Print sig_coind_uncurried.
  Check fixedPointIsoIsSection' _ p A.
  apply (moveR_equiv_M' (someIso p A) (eval1Map (idLens (curryArena p A)) (fixedPointIsoInv p A)
       (eval1Map (idLens (curryArena p A))
          (sig_ind
             (fun
                _ : {t0 : positions (fixedPoint p) &
                    directions (fixedPoint p) t0 fin_last -> A} =>
              W (positions (curryArena p A))
                (fun i0 : positions (curryArena p A) =>
                 directions (curryArena p A) i0 fin_last))
             (fixedPointIso' p A))
          ((someIso p A)^-1
             (w_sup (positions p)
                (fun i0 : positions p => directions p i0 fin_last) i f; g)))) (w_sup (positions p) (fun i0 : positions p => directions p i0 fin_last) i f;
  g)).
  refine (path_sigma' _ idpath _).
  cbn.
  apply path_forall.
  refine (fun a => fixedPointIsoIsSection' _ p A (f a) (g o inr o exist _ a)).
Defined.

Definition fixedPointIsoIsSection `{Funext} (p : Arena 2) A
  : fixedPointIsoInv p A o fixedPointIso p A == idmap.
Proof.
  refine (sig_ind _ _).
  apply fixedPointIsoIsSection'.
Defined.

Definition fixedPointIsoIsIso `{Funext} p A : IsEquiv (fixedPointIso p A) :=
  isequiv_adjointify _ (fixedPointIsoInv p A) (fixedPointIsoIsRetraction p A) (fixedPointIsoIsSection p A).
