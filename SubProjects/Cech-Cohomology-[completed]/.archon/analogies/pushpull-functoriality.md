# Analogy: does Mathlib supply the functoriality of `p ↦ p_* p^* F`, or should the project keep hand-rolling `pushPullMap`/`pushPullMap_comp`?

## Mode
api-alignment

## Slug
pushpull

## Iteration
001

## Question
Does Mathlib already provide the functoriality of `p ↦ p_* p^* F` (or `p ↦ p_* p^*`)
for sheaves of modules on schemes, so we should NOT hand-roll `pushPullMap` /
`pushPullMap_comp`? (1) Is there a pseudofunctor→functor "straightening" giving an honest
`Functor (Over X)ᵒᵖ ⥤ X.Modules` for a fixed `F`? (2) Is there a Mathlib idiom for the
cosimplicial object obtained by applying a (pseudo)functor to the simplicial nerve of a
cover arrow, letting the project build `CechNerve` from `coverCechNerve` WITHOUT first
assembling `G` and its `map_comp`? (3) If hand-rolled is right, is the `pushPullMap`
DEFINITION shape (two over-triangle `eqToHom` transports) the problem — would routing
through the adjunction transpose / `homEquiv` give a transport-light `map_comp` provable
by `pseudofunctor_associativity` without the defeq wall?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean:157-181` — `pushPullObj`, `pushPullMap`.
- `…:210-265` — `pushPullMap_id` (closed; template).
- `…:267-471` — the `pushPullMap_comp` recipe + dead-ends; bricks `pushPull_unit_mate`,
  `pushPull_unit_comp`, `pushforwardComp_hom_app_id`, `rawPushPullMap`, `pushPullMap_eq_raw`,
  `pushPull_transport_cancel`.
- `…:83-91` — `CechNerve` (the `sorry`); `…:124-135` — `coverArrow`, `coverCechNerve`.

## Mathlib infrastructure that exists (verified)

- `AlgebraicGeometry.Scheme.Modules.pseudofunctor : Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Adj Cat)`
  in `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`. Packages *both* the covariant
  (pushforward, right-adjoint) and contravariant (pullback, left-adjoint) functorialities,
  with full coherence: `pullbackComp`, `pushforwardComp`, `pullbackId`, `pushforwardId`,
  `pseudofunctor_associativity` (the pentagon), `pseudofunctor_left/right_unitality`.
- KEY: the pentagon/unitors are stated **only on the pullback (left-adjoint) side**
  (`pseudofunctor_associativity : (pullbackComp …).inv ≫ … = eqToHom _`). The
  pushforward-side coherences are *derived* via the mate calculus, NOT stated directly.
- `Scheme.Modules.conjugateEquiv_pullbackComp_inv :
   conjugateEquiv ((adj g).comp (adj f)) (adj (f≫g)) (pullbackComp f g).inv = (pushforwardComp f g).hom`
   and `conjugateEquiv_pullbackId_hom` — the bridges turning pullback-side comparison isos
   into pushforward-side ones.
- `Scheme.Modules.pushforwardComp_hom_app_app : ((pushforwardComp f g).hom.app M).app U = 𝟙 _` by `rfl`
   — the pushforward pseudofunctor is **strict** (its comparison 2-cells are identities on the nose).
- `CategoryTheory.conjugateEquiv` (`Mathlib/CategoryTheory/Adjunction/Mates.lean`): for
  `adj₁ : L₁⊣R₁`, `adj₂ : L₂⊣R₂`, the bijection `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)` (the mate/conjugate).
- **`CategoryTheory.conjugateEquiv_comp`** (same file): `conjugateEquiv adj₁ adj₂ α ≫
  conjugateEquiv adj₂ adj₃ β = conjugateEquiv adj₁ adj₃ (β ≫ α)`. This is *mate-of-composite =
  composite-of-mates* — the abstract functoriality identity the project is re-deriving by hand.
  Supporting: `conjugateEquiv_id`, `unit_conjugateEquiv`, `conjugateEquiv_apply_app`.
- `CategoryTheory.Pseudofunctor.Grothendieck` (`Mathlib/CategoryTheory/Bicategory/Grothendieck.lean`):
  the Grothendieck construction, but ONLY for `Pseudofunctor (LocallyDiscrete 𝒮) Cat`, and it
  builds the **total fibered category**, not the fixed-`F` functor on the base. Does NOT apply.
- `CategoryTheory.Over.lift` (`Mathlib/CategoryTheory/Comma/Over/Basic.lean`): lifts `D : J ⥤ T`
  with a cocone `D ⟶ const X` to `J ⥤ Over X` — the clean plumbing for the simplicial→over-X step.

## Decisions identified

### Decision: (Q1) Is there a pseudofunctor→functor straightening giving `G` for fixed `F`?

- **Mathlib idiom**: NONE. The only straightening of a pseudofunctor in Mathlib is
  `Pseudofunctor.Grothendieck` / `CoGrothendieck` (`Mathlib/CategoryTheory/Bicategory/Grothendieck.lean`),
  which (a) requires the target bicategory to be `Cat` (the project's lands in `Adj Cat`), and
  (b) produces the *total category* `∫P` of a fibration, not the "evaluate at a fixed object,
  vary the base map" functor `(Over X)ᵒᵖ ⥤ X.Modules`. There is no "fixed-object section" or
  "pointwise functor of a pseudofunctor" construction. Over-category pushforwards that *do*
  exist (`CategoryTheory.Over.pullback`, `ExponentiableMorphism.pushforward`,
  `LocallyCartesianClosed`) are the *topos/slice* pullback-pushforward, unrelated to the
  *module* pushforward `Scheme.Modules.pushforward`.
- **Project's path**: hand-roll `pushPullObj` + `pushPullMap` + functor laws.
- **Gap**: no idiom exists; project's path is the only option.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL. The hand-roll is genuine missing infrastructure,
  NOT a parallel API. Keep building it.

### Decision: (Q2) Can `CechNerve` be built from `coverCechNerve` without assembling `G`?

- **Mathlib idiom**: the simplicial→cosimplicial passage has clean plumbing —
  `coverCechNerve : SimplicialObject.Augmented Scheme` carries the augmentation
  `coverCechNerve.left ⟶ const X`, so `Over.lift` lifts it to `SimplexCategoryᵒᵖ ⥤ Over X`;
  then `(·).op ⋙ G : SimplexCategory ⥤ X.Modules` is exactly the (augmented) cosimplicial
  object. BUT this composition **requires `G` to be a genuine `Functor`** — i.e. it consumes
  `pushPullMap_comp`. Mathlib has no construction that applies a pseudofunctor to a Čech nerve
  and emits a cosimplicial object while dodging functoriality; functoriality is unavoidable
  somewhere.
- **Project's path**: build `G`, then compose (`relativeCechComplexOfNerve` already does the
  rest, coherence-free).
- **Gap**: identical to the only available route; the obstacle (`pushPullMap_comp`) is
  genuinely on the critical path. There is no Mathlib shortcut.
- **Verdict**: PROCEED. `pushPullMap_comp` IS the rate-limiter, as diagnosed — do not expect a
  bypass; invest in proving it (see Q3).

### Decision: (Q3) Is the `pushPullMap` DEFINITION shape the problem? Mate route vs. pushforward-side pentagon grind.

- **Mathlib idiom**: the **mate / conjugate calculus**. Mathlib structures pushforward
  (right-adjoint) functoriality as the *conjugate* of pullback (left-adjoint) functoriality —
  this is the whole design of `Scheme.Modules.pseudofunctor` (pentagon stated on pullback only;
  `conjugateEquiv_pullbackComp_inv` bridges to pushforward). The composition law of any
  right-adjoint-valued contravariant functor is an instance of `conjugateEquiv_comp`
  (*mate-of-composite = composite-of-mates*), reduced — via injectivity of the `conjugateEquiv`
  bijection — to a *pullback-side* identity, which is exactly `pseudofunctor_associativity`.
- **Project's path**: the current proof fights the pentagon on the **pushforward side** with
  `erw`/`reassoc_of%`/`congr`, which `whnf`-explodes `pullbackComp` into its raw
  `TwoSquare.equivNatTrans`/`mateEquiv` mate definition (the documented dead-end). The two
  over-triangle `eqToHom` transports in `pushPullMap` are a *secondary* irritant (already
  dodged by `rawPushPullMap` + `subst`); the *primary* friction is staying on the pushforward
  side at all.
- **Gap**: divergent-with-cost. The project already discovered the correct entry points —
  `pushPull_unit_mate` (= `unit_conjugateEquiv` of the composite adjunction +
  `conjugateEquiv_pullbackComp_inv`) and `pushPull_unit_comp` — but then *leaves* the mate
  algebra to grind a pushforward-side whiskered pentagon. The cost of not committing to the
  mate route: repeated `erw` `whnf` blow-ups, ~5 stalled iters.
- **Verdict**: ALIGN_WITH_MATHLIB (on the proof/definition shape). Commit fully to the mate
  route.

## Recommendation

Keep the hand-rolled `G` (Q1: Mathlib has no straightening; Q2: functoriality is unavoidable
and on the critical path). But **refactor the proof of `pushPullMap_comp` to live entirely in
the mate/conjugate algebra**, never on the pushforward side:

1. Recognize `pushPullMap F g` (for `g : Y₂ ⟶ Y₁`, `p₂ = a ≫ p₁`) as `(conjugateEquiv …
   χ_g).app F` whiskered/evaluated, where `χ_g` is the *pullback-side* comparison built from
   `(pullbackComp a p₁).inv` and the unit — i.e. the leg already isolated in
   `pushPull_unit_mate` / `conjugateEquiv_pullbackComp_inv`. The pushforward strictness
   `pushforwardComp_hom_app_app = 𝟙` (by `rfl`) means every pushforward-side comparison is a
   definitional identity, so nothing nontrivial lives there.
2. Prove `pushPullMap_comp` by applying **`conjugateEquiv_comp`** (mate-of-composite), reducing
   it — via `Equiv`/`conjugateEquiv` injectivity — to the *pullback-side* identity
   `χ_{g≫h} = χ_h ≫ χ_g`. That identity is **`Scheme.Modules.pseudofunctor_associativity
   (f := h.left) (g := g.left) (h := Y₁.hom)`** used as a clean `rw`/`simp` (it is stated
   syntactically on `pullbackComp`/`pullbackId` *hom isos*, so it fires without `erw` and never
   unfolds the raw `mateEquiv` definition).

The key alignment claim: the pentagon the project keeps losing on the pushforward side is
*already proven in Mathlib on the pullback side* (`pseudofunctor_associativity`), and the
mate-functoriality lemma `conjugateEquiv_comp` is the legal bridge. The defeq wall is an
artifact of doing the transport on the wrong (pushforward) side; the mate route stays in the
`conjugateEquiv` `≃`-algebra where composition is a clean algebraic identity. The bricks
`pushPull_unit_mate`, `pushPull_unit_comp`, `pushforwardComp_hom_app_id` the project already
built are exactly the right scaffolding — finish the route rather than reverting to a
pushforward-side `erw` grind.

If a clean `conjugateEquiv`-mate *definition* of `pushPullMap` proves awkward to retrofit under
the frozen object `pushPullObj`, the minimal-change version is: keep `rawPushPullMap` +
`subst`, but after clearing the over-triangles, discharge the residual pentagon by rewriting
the goal into `conjugateEquiv` form (`pushPull_unit_comp` + `conjugateEquiv_pullbackComp_inv`)
and closing with `conjugateEquiv_comp` + `pseudofunctor_associativity` + `Equiv.injective` —
deliberately avoiding `erw`/`congr` on any `pullbackComp` term.
