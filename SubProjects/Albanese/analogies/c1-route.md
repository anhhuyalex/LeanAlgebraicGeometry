# Analogy: Mathlib idiom for the Picard group of a scheme as units of a monoidal-category skeleton

## Slug
c1-route

## Iteration
108

## Question

What is the canonical Mathlib idiom for defining the **Picard group of a
scheme as the units of a monoidal category of `O_X`-modules**, and is that
idiom executable today against the project's already-shipped
`MonoidalCategory (X.Modules)` / `BraidedCategory (X.Modules)` chain
(which transitively depends on the deferred `instIsMonoidal_W` sorry for
`(W X).IsMonoidal`)?

## Project artifact(s)

- `AlgebraicJacobian/Picard/LineBundle.lean:85-122` — current
  `LineBundle X := CommRing.Pic Γ(X, ⊤)` and `Pic.pullback` via
  `CommRing.Pic.mapRingHom`.
- `AlgebraicJacobian/Modules/Monoidal.lean:166-194` — the deferred
  `instIsMonoidal_W` sorry plus the `instMonoidalCategoryStruct` and
  `instMonoidalCategory` instances that transitively consume it.
- `AlgebraicJacobian/Picard/Functor.lean:108-174` — `quotMap` and
  `PicardFunctor`, parametric in `Pic.pullback`.
- `AlgebraicJacobian/Picard/FunctorAb.lean` — additive-group flavor
  of the same construction.

## Decisions identified

The directive's single design question compresses four orthogonal decisions.

### Decision A: name of the "invertible-objects" type

- **Mathlib idiom**: there is **no type literally named
  `MonoidalCategory.Invertible`** in Mathlib b80f227. The canonical idiom is
  `(Skeleton C)ˣ` — the **units of the (skeleton's) monoid structure on the
  objects of a (braided) monoidal category**. Specifically:
  - `CategoryTheory.Skeleton.instMonoid` (`Mathlib.CategoryTheory.Monoidal.Skeleton:60`)
    promotes `Skeleton C` to `Monoid` from `[MonoidalCategory C]`.
  - `CategoryTheory.Skeleton.instCommMonoid` (`...:80`) promotes it to
    `CommMonoid` from `[BraidedCategory C]`.
  - `(Skeleton C)ˣ` is then automatically `CommGroup` from `instCommGroupUnits`.
  - The ring precedent (`CommRing.Pic`,
    `Mathlib.RingTheory.PicardGroup:407-408`) defines
    `def CommRing.Pic (R) := Shrink (Skeleton (SemimoduleCat R))ˣ`.

  Why Mathlib chose this: skeleton-level units neatly factor the
  *non-categorical* equational content (groupy laws on iso-classes) from
  the *categorical* content (associator/unitor/braiding witnesses). The
  `Shrink` wrapper handles universe issues (`SemimoduleCat R`'s skeleton
  lives in `u+1` a priori; Mathlib proves it is `Small.{u}` via the
  finite-presentation classifier).

- **Project's proposed path** (`STRATEGY.md` "Phase C1" §): refactor
  `LineBundle X` to "`MonoidalCategory.Invertible (X.Modules)`". This name
  **does not denote any Mathlib declaration**; it is a placeholder that
  must be resolved to the actual idiom.

- **Gap**: divergent-and-wrong (a literal `MonoidalCategory.Invertible`
  does not exist; the strategy text needs to commit to the correct name).
  Easy to fix at refactor-spec time.

- **Verdict**: **ALIGN_WITH_MATHLIB**. Refactor target should be
  `(Skeleton X.Modules)ˣ` (or `Shrink (Skeleton X.Modules)ˣ` if a
  universe-size issue arises), mirroring `CommRing.Pic`.

### Decision B: dependency on the deferred `instIsMonoidal_W` sorry

- **Mathlib idiom**: `(Skeleton C)ˣ` as a `CommGroup` requires
  `[BraidedCategory C]` (to get `CommMonoid (Skeleton C)`).
  - For the project, `BraidedCategory (X.Modules)` is obtained transitively
    via `Localization.Monoidal.Braided` (`Mathlib.CategoryTheory.Localization.Monoidal.Braided:118-123`,
    `instance : BraidedCategory (LocalizedMonoidal L W ε)`), which assumes
    `[W.IsMonoidal]` and `[BraidedCategory C₀]` (in fact, the project's
    `PresheafOfModules` side is `SymmetricCategory`,
    `Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal:145`).
  - `[W.IsMonoidal]` for the sheafification `W X` is the project's
    `instIsMonoidal_W` at `AlgebraicJacobian/Modules/Monoidal.lean:166-173`,
    whose body is a `sorry` for the upstream gap on `stalk_tensorObj`
    (varying-ring `R₀`).

- **Project's proposed path**: refactor C1's `LineBundle` to depend on
  the `CommGroup` of `(Skeleton X.Modules)ˣ`, accepting that it transitively
  consumes the deferred `instIsMonoidal_W` sorry.

- **Gap**: divergent-with-cost (vs. the strategy text framing
  "3 named Mathlib gaps at end-state"). The strategy text's C1 promotion
  trigger claims the project's terminal sorry-set is 3 (or 4 with L1802)
  named items. After C1 promotion, **every Lean term referencing
  `LineBundle X`, `Pic X`, `Pic.pullback`, or `PicardFunctor` would
  type-check by drawing on `BraidedCategory (X.Modules)`, hence
  transitively on the `instIsMonoidal_W` sorry**. The terminal sorry-set
  is unchanged in *count* (the sorry is already in the named set), but the
  *transitive reach* of the sorry expands dramatically:
    - **Pre-C1 promotion**: `instIsMonoidal_W` is referenced by
      `instMonoidalCategoryStruct` / `instMonoidalCategory` (`Modules/Monoidal.lean`)
      and nothing else in the project's main proof DAG actually uses
      these instances. The sorry is "dormant" in the sense that no
      downstream proof obligation explicitly consumes it.
    - **Post-C1 promotion**: `instIsMonoidal_W` becomes a *load-bearing*
      transitive dependency of `LineBundle`, `Pic`, `Pic.pullback`,
      `PicardFunctor`, `PicardFunctorAb`, and the `Jacobian`/`AbelJacobi`
      arc whose protected signatures consume `Pic`. The C1 LineBundle
      can be *constructed*, but every fact about it that requires the
      `CommGroup`/`Monoid` instances is conditional on this sorry.

  This expansion is **not dishonest** (the sorry is named and surfaced),
  but it is *materially different* from the strategy text's portrayal,
  which suggests C1 is "unblocked" by `instIsMonoidal_W`.

- **Cost**: the project's bookkeeping language should change. The end-state
  framing must say (in `STRATEGY.md`): "the four named Mathlib gaps...
  `instIsMonoidal_W` (load-bearing for the C1 Picard group on non-affine
  schemes); ..." rather than treating it as cosmetically present.
  Additionally, `lean_verify` runs on `Pic.pullback`,
  `PicardFunctor`-derived theorems, and `PicardFunctorAb` will surface
  `sorryAx` in their axiom chains post-C1, which they do not surface
  today.

- **Verdict**: **ALIGN_WITH_MATHLIB with disclosure cost**. The Mathlib
  route requires `BraidedCategory C`; the project's `BraidedCategory
  (X.Modules)` is genuinely sorry-conditional. Re-classify
  `instIsMonoidal_W` from "dormant deferred gap" to "load-bearing
  deferred gap" in the strategy text and in the end-state honest-accounting
  paragraph (cf. the C3-JacobianWitness disclosure pattern).

### Decision C: pull-back functoriality on `LineBundle`

- **Mathlib idiom (analogous to `CommRing.Pic.mapRingHom`)**: a monoidal
  functor `F : C ⥤ D` induces a monoid homomorphism `Skeleton C →* Skeleton D`
  via `Skeleton.monoidHom` (`Mathlib.CategoryTheory.Monoidal.Skeleton:111`),
  which restricts to `(Skeleton C)ˣ →* (Skeleton D)ˣ` via `Units.map`.
  - The categorical pull-back functor for sheaves of modules is
    `AlgebraicGeometry.Scheme.Hom.pullback f : Y.Modules ⥤ X.Modules`
    (`Mathlib.AlgebraicGeometry.Modules.Sheaf:167-168`,
    delegating to `SheafOfModules.pullback`).
  - To use `Skeleton.monoidHom`, we need a `Functor.Monoidal` instance on
    that pullback functor.

- **Mathlib status of this instance**: **MISSING**. A search across
  `Mathlib.AlgebraicGeometry.Modules.*`,
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.*`, and
  `Mathlib.Algebra.Category.ModuleCat.Presheaf.*` finds no
  `Functor.Monoidal` instance for any pullback on `SheafOfModules` /
  `PresheafOfModules`. Mathlib *does* have
  `(pushforward₀OfCommRingCat F R).Monoidal` for the presheaf-side
  pushforward (`...Presheaf/PushforwardZeroMonoidal:33`), but the
  pullback-side monoidality is absent.

- **Project's proposed path**: C1 refactor would need to derive
  `Pic.pullback` from a categorical pull-back functor. Without a
  `(SheafOfModules.pullback _).Monoidal` instance, the project must either
  (i) build one (a *fifth* Mathlib gap-fill, scope-comparable to building
  the `instMonoidalCategory` infrastructure itself), or (ii) define
  `Pic.pullback` more concretely — e.g. as `Units.map (Skeleton.monoidHom ...)`
  modulo a manual monoidality lemma, or by directly producing
  `(Skeleton Y.Modules)ˣ → (Skeleton X.Modules)ˣ` via
  `pullback.obj` + ad-hoc μ/ε witnesses.

- **Gap**: NEEDS_MATHLIB_GAP_FILL. **This is the largest hidden cost**
  in the C1 promotion as currently scoped. The strategy's "5-8 iters
  / 200-300 LOC" estimate for C1 plausibly does not include building
  `Functor.Monoidal (X.Hom.pullback f)`, which on its own is
  multi-iter / multi-hundred-LOC work analogous to the
  `instIsMonoidal_W` chain (modulo that the pullback functor between
  sheafifications presents differently from the localization picture
  — Mathlib's `SheafOfModules.pullback` is *not* a localization functor).

- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**, with a recommended detour:
  define `Pic.pullback` directly via `pullback.obj` on representatives,
  manually witnessing `pullback (M ⊗ N) ≅ pullback M ⊗ pullback N` as
  the proof obligation. Equivalently, the C1 refactor should produce
  this iso as a stand-alone lemma `SheafOfModules.pullback_tensorObj`
  (or accept a *second* named deferred sorry as the price of the
  refactor).

### Decision D: how to register an inhabitant of `LineBundle X`

- **Mathlib idiom**: `CommRing.Pic.mk : Type → Pic R`
  (`Mathlib.RingTheory.PicardGroup:437-441`) takes a `Module R M`
  with a `Module.Invertible R M` typeclass and produces
  `Pic R = Shrink (Skeleton (SemimoduleCat R))ˣ` via
  `Units.mkOfMulEqOne ⟦.of R M'⟧ ⟦.of R (Dual R M')⟧` plus
  a soundness proof.
  - The typeclass `Module.Invertible R M` (`...:78`) is defined as
    "the canonical map `Mᵛ ⊗[R] M → R` is bijective". This requires the
    duality theory of modules — a CommSemiring-level construction.

- **Project-side analog requirement**: to register an `M : X.Modules`
  as an element of `LineBundle X = (Skeleton X.Modules)ˣ`, the project
  must provide a "scheme-side invertibility" witness. Mathlib has no
  `SheafOfModules.Invertible` typeclass; the most direct route is to
  invoke `Units.mkOfMulEqOne` on `⟦M⟧, ⟦M⁻¹⟧` with a manual proof
  `M ⊗ M⁻¹ ≅ 𝟙_` in `X.Modules`.

- **Gap**: NEEDS_MATHLIB_GAP_FILL or PROCEED-by-construction.
  - On affine `X = Spec R`: a Mathlib-aligned bridge would derive
    `Module.Invertible R M ⇒ Sheaf-side invertibility of `M~``, but the
    `~`-functor's monoidal structure (matching presheaf-tensor of
    `Tilde` modules with module tensor) is not packaged as a
    `Functor.Monoidal` instance in Mathlib b80f227 (and `Tilde` is at
    the `ModuleCat` level, not directly at `SheafOfModules`).
  - On general `X`: there is no pre-existing typeclass, so each
    inhabitant must be hand-rolled with its tensor-inverse witness.

- **Verdict**: **PROCEED** for the C1 refactor (i.e. accept that the
  framework will not initially ship a typeclass interface for "this
  sheaf of modules is invertible"; inhabitants will be `mkOfMulEqOne`-ed
  by hand). A future iter (post-C1, outside the project's autonomous
  scope) could add `SheafOfModules.Invertible` as the scheme-side
  analog of `Module.Invertible`.

## Recommendation

**The C1 promotion is the mathematically right move and is consistent with
Mathlib's idiom**, but the strategy text's portrayal materially understates
the costs. Two cost lines are missing from the "5-8 iters / 200-300 LOC"
estimate:

1. **Disclosure cost**: `instIsMonoidal_W` re-classifies from
   "dormant deferred gap" to "load-bearing deferred gap" — every C1+
   theorem about `Pic`, `Pic.pullback`, `PicardFunctor`, and the
   downstream Jacobian arc transitively depends on it. This is honest
   accounting but requires the end-state framing to acknowledge it
   alongside the existing `JacobianWitness` disclosure (`STRATEGY.md`
   §"Honest assessment").
2. **`Functor.Monoidal` on `SheafOfModules.pullback` is a Mathlib gap**.
   The project would need either (a) to build the monoidal-functor
   structure on the categorical pullback (multi-iter, multi-hundred
   LOC), or (b) to construct `Pic.pullback` by an ad-hoc route producing
   the iso `pullback (M ⊗ N) ≅ pullback M ⊗ pullback N` directly, or
   (c) accept a *named additional sorry*
   (`SheafOfModules.pullback_tensorObj`) at the cost of expanding the
   named-gap surface from 4 to 5. **This is the dominant uncosted
   line-item** in the C1 promotion as currently scoped.

If the plan agent fires C1 next iter, the refactor directive must:

- Rename the target from `MonoidalCategory.Invertible (X.Modules)` to
  `(Skeleton X.Modules)ˣ` (or `Shrink (...)`ˣ` if a universe-size
  hiccup arises during the prover round).
- Commit upfront to one of routes (a)/(b)/(c) for `Pic.pullback`.
  Route (c) is the smallest-scope move (mirrors the project's existing
  `instIsMonoidal_W` deferral pattern), but it expands the named-gap
  surface by 1.
- Update `STRATEGY.md` end-state framing to surface
  `instIsMonoidal_W` as load-bearing for C1 / C2 / D / E, mirroring the
  `JacobianWitness` disclosure.

If those costs are unacceptable, the alternative is to **stay on the
defer-L1802-as-named-Mathlib-gap path** (escape-valve menu option (i))
and let C1 promotion remain pending — neither route shrinks the
named-gap surface below the present count.
