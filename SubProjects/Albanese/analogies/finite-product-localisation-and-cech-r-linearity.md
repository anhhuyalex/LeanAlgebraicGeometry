# Analogy: finite-product localisation and post-hoc R-linearity of the Čech differential

## Slug
finite-prod-loc

## Iteration
106

## Questions

(Q1) Does Mathlib have a product-localisation commutation
`LocalizedModule (powers a) (∏ᶜ_x M_x) ≅ ∏ᶜ_x LocalizedModule (powers a) M_x`
for finite products in `ModuleCat k` (or `ModuleCat R`), and the matching
`IsLocalizedModule.Pi` typeclass instance? If yes, name them; if no,
characterize the gap.

(Q2) Is there a Mathlib idiom for proving R-linearity of an alternating
sum of categorical morphisms `∑ (-1)^i • (Pi.lift_thing_i ≫ eqToHom)`
that avoids the per-summand pattern-match-on-anonymous-closure approach?
For example a `Preadditive` / `Linear k` -level lemma, or a `Cech` /
`simplicialNerve` instance, or a project-side reformulation that makes
R-linearity flow from typeclass structure rather than an explicit
alternating-sum proof?

## Project artifact(s)

- `AlgebraicJacobian/Cohomology/BasicOpenCech.lean:1683-1786` —
  `h_K₀_exact` block: `f_R`, `g_R`, `h_loc_X_i`, `h_loc_exact` (L1783
  sorry), followed by `exact_of_localized_span` to close `h_K₀_exact`.
- `AlgebraicJacobian/Cohomology/BasicOpenCech.lean:836-1121` — body of
  `cechCofaceMap_pi_smul` with the iter-099/103/107 scaffold; L1120
  sorry preceded by `have h_iter104 := cechCofaceMap_summand_family_R_linear hU s₀ n hn i r' y'`.
- `AlgebraicJacobian/Cohomology/BasicOpenCech.lean:454-477` —
  `cechCofaceMap_summand_family` (named morphism family, iter-102).
- `AlgebraicJacobian/Cohomology/BasicOpenCech.lean:494-595` —
  `cechCofaceMap_summand_family_R_linear` (50-LOC binder-level proof of
  per-summand R-linearity, closed iter-104).
- `AlgebraicJacobian/Cohomology/StructureSheafModuleK.lean:180-228` —
  `toModuleKPresheaf : (Opens C.left.toTopCat)ᵒᵖ ⥤ ModuleCat.{u} k` and
  its sheaf bundling `toModuleKSheaf`.

## Decisions identified

### Decision Q1a: product-localisation commutation `IsLocalizedModule.pi`

- **Mathlib idiom**: `IsLocalizedModule.pi`. Cite:
  `Mathlib.RingTheory.TensorProduct.IsBaseChangePi:93`.

  ```lean
  instance pi {ι : Type*} [Finite ι]
      {M M' : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, AddCommMonoid (M' i)]
      [∀ i, Module R (M i)] [∀ i, Module R (M' i)]
      (f : ∀ i, M i →ₗ[R] M' i) [∀ i, IsLocalizedModule S (f i)] :
      IsLocalizedModule S (.pi fun i ↦ f i ∘ₗ .proj i)
  ```

  Plus the binary sibling `IsLocalizedModule.prodMap` at L77 of the
  same file. Both are derived from
  `IsBaseChange.pi` / `IsBaseChange.prodMap` via the
  `isLocalizedModule_iff_isBaseChange` adapter, which means the
  underlying `IsLocalizedModule (LinearMap.pi …)` instance is
  definitionally a base-change statement — exactly the universal
  property "localisation commutes with finite products".

  Why Mathlib chose this: localisation = base change against
  `Localization S`; base change of modules commutes with finite limits
  in `ModuleCat R` (a categorical fact); finite products in `ModuleCat
  R` are the dependent `∀ i, M' i`-types via `ModuleCat.piIsoPi`. The
  instance is a typeclass so consumers don't have to invoke it by hand.

- **Project's current path**: the iter-069 docstring at
  `BasicOpenCech.lean:1583` describes "the
  product-localisation commutation `LocalizedModule (powers f) (∏ᶜ_x M_x) ≅
  ∏ᶜ_x LocalizedModule (powers f) M_x` holds". The sorry at L1783
  (`h_loc_exact`) is supposed to be closed by this commutation plus
  `h_a₀_fun f`. As of iter-106 no call site has been written.

- **Gap**: identical (modulo `LinearMap.pi`-vs-`Pi.lift` repackaging).
  The Mathlib instance covers the `LinearMap.pi`-flavoured product;
  bridging to `Limits.Pi.lift`-flavoured product in `ModuleCat k`
  proceeds via `ModuleCat.piIsoPi : (∏ᶜ Z) ≅ ModuleCat.of k (∀ i, Z i)`
  (`Mathlib.Algebra.Category.ModuleCat.Products`), which the project
  already uses (the `e₁`, `e₂`, `e₃` `LinearEquiv` handles at
  `BasicOpenCech.lean:1615-1617`).

- **Cost of divergence (if project rebuilds the pi-localisation instead
  of importing)**: redundant ~50-LOC infrastructure that Mathlib already
  ships. None — just align.

- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision Q1b: per-coord localisation premise

- **Mathlib idiom**: two-step bridge.
  1. `IsAffineOpen.isLocalization_of_eq_basicOpen`
     (`Mathlib/AlgebraicGeometry/AffineScheme.lean:716`) gives
     `IsLocalization.Away f Γ(X, V)` whenever `V = X.basicOpen f` and
     `V ≤ U` for affine `U` (algebra structure installed via
     `(X.presheaf.map i.op).hom.toAlgebra`).
  2. `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmonoid`
     (`Mathlib.Algebra.Module.LocalizedModule.IsLocalization`) upgrades
     an `IsLocalization` algebra map to an `IsLocalizedModule` instance
     on the algebra's `toLinearMap`.

- **Project's current path**: the iter-069 docstring lists
  "Step 3: for each `f ∈ ↑s₀`, identify the localisation of `K₀.X i` at
  `f` with the `↑s₀`-indexed slice-cover term at the same degree" and
  uses `localizedModuleIsLocalizedModule` (L1768-1775) as a *stand-in*
  by working with `LocalizedModule` directly rather than going via the
  slice cover. This means the project has bypassed the natural
  per-coord identification with `Γ(V_x ⊓ D(f.1))`.

- **Gap**: divergent-with-cost. The current project path sidesteps the
  slice-cover identification, so `h_loc_exact`'s closure cannot
  consume `h_a₀_fun f` directly — there's no Mathlib lemma
  ``IsLocalizedModule.linearMap_pi → LocalizedModule.map (...) f_R``
  that bypasses the slice-cover identification.

  The bridge has to go: `slice-cover.f at coord n` (R-linear in
  `ModuleCat k`) = `LinearMap.pi (per-coord restriction)` ∘
  `K₀.f at coord n` (under suitable identification), then identify
  `LocalizedModule.map (powers f.1) f_R` with the LHS via
  `IsLocalizedModule.iso` and uniqueness.

- **Cost of divergence**: zero new Mathlib gap, but ~50 LOC of project
  glue to build the per-coord algebra structures, install the
  `IsLocalization.Away` instances on the slice factors, and bridge to
  the `IsLocalizedModule` form via the Mathlib adapter.

- **Verdict**: ALIGN_WITH_MATHLIB (the iter-069 docstring already
  outlines this; the project just needs to write it).

### Decision Q1c: transporting `Function.Exact` across the localisation iso

- **Mathlib idiom**: `IsLocalizedModule.iso`
  (`Mathlib.Algebra.Module.LocalizedModule.Basic`) gives
  `LocalizedModule S M ≃ₗ[R] M'` whenever `IsLocalizedModule S f`. The
  pair `IsLocalizedModule.linearMap_ext` / `IsLocalizedModule.ext`
  provides extensionality. For `Function.Exact` transport across a
  `LinearEquiv`, `LinearEquiv.exact_iff_exact` (search: `LinearEquiv +
  Function.Exact`) is the canonical move.

- **Project's current path**: not yet written; the sorry at L1783 is
  raw.

- **Gap**: identical to Mathlib's intended use. No divergence.

- **Verdict**: PROCEED (no Mathlib precedent dictates the exact glue
  shape; the project just writes it).

### Decision Q2a: post-hoc R-linearity certification

- **Mathlib idiom**: the canonical idiom in Mathlib is to **build the
  complex in the right category in the first place** rather than
  certify R-linearity post hoc. `cechComplexFunctor : (Cᵒᵖ ⥤ A) ⥤
  CochainComplex A ℕ` (`Mathlib.CategoryTheory.Sites.SheafCohomology.Cech:65`)
  works for any `A` with the requisite limits — in particular for
  `A := ModuleCat R`, giving a Čech complex of **R-modules** whose
  differentials are R-linear by construction.

  `CategoryTheory.Linear R (ModuleCat R)` is canonical: hom-sets in
  `ModuleCat R` ARE the R-modules of R-linear maps; composition and
  addition commute with the R-action by definition.

  But `Linear R (ModuleCat k)` does **NOT** hold for `R ≠ k` in
  general: a `k`-linear map between `R`-modules-over-`k` need not be
  R-linear. There is no `Linear R`-instance on `ModuleCat k`, nor any
  Mathlib lemma "alternating sum of R-linear maps in
  `Hom_{ModuleCat k}(M, N)` is R-linear", because the hom-set isn't an
  R-module to start with.

  `AlgebraicTopology.alternatingCofaceMapComplex` lives over
  `Preadditive C` (`Mathlib.AlgebraicTopology.AlternatingFaceMapComplex`)
  and inherits nothing more — it neither requires nor exposes a
  `Linear R`-structure.

- **Project's current path**: build `cechCochain C (toModuleKSheaf C) 𝒰`
  in `CochainComplex (ModuleCat k) ℕ` and prove R-linearity of the
  differential post hoc via the iter-099+ alternating-sum scaffolding
  (`alternating_sum_pi_smul_aux`, `alternating_sum_pi_smul_aux_sum_comp`,
  `alternating_zsmul_pi_smul_aux_sum_comp`, the named family
  `cechCofaceMap_summand_family` + its R-linearity at iter-102/104).

  The 7-iter-stuck blocker at L1120 is *bridging* the iter-104
  binder-level R-linearity proof to the call-site anonymous-closure
  form of the K₀ differential.

- **Gap**: divergent-with-cost. Mathlib's idiom is "build in
  `ModuleCat R` if you need R-linearity"; the project's `ModuleCat k`
  + post-hoc-certify path has produced 7 consecutive failed iters
  because the categorical infrastructure (`Pi.lift`, alternating sum,
  `eqToHom`) is precisely tuned to preserve `Preadditive`/`Linear k`
  structure but obstinately whnf-reduces anonymous closures in ways
  that defeat the elaborator when tactics try to extract per-summand
  R-linearity.

  The cost is *exactly* the 7 stuck iters: post-hoc R-linearity
  certification on a `ModuleCat k`-valued Čech differential is a
  Mathlib gap **created by the project's design choice**, not a
  pre-existing Mathlib gap that needs filling.

- **Verdict**: ALIGN_WITH_MATHLIB at the architectural level. Two
  feasible paths (see Recommendation below).

### Decision Q2b: tactical bridging via `change` to named family

- **Mathlib idiom**: no Mathlib precedent for this micro-level
  reformulation (Mathlib doesn't run into it because of Q2a's
  architectural choice).

- **Project's current path**: the iter-099 attack route through
  `alternating_sum_pi_smul_aux_sum_comp`/`alternating_zsmul_pi_smul_aux_sum_comp`
  tries to apply the structural lemma at the *call site* via
  Miller-pattern unification, with `G := fun i ↦ (anonymous closure)`
  baked into the `?G` placeholder. The unifier fails because the
  anonymous closure under whnf has nested `Pi.lift` bodies that the
  elaborator cannot decompose.

- **Gap**: divergent-and-wrong (in the sense that the project keeps
  pursuing this route despite consistent failure).

- **Cost**: 7 consecutive stuck iters and counting.

- **Verdict**: PROCEED only if a fundamentally different micro-tactic
  (e.g. body-level `set F := cechCofaceMap_summand_family s₀ n` followed
  by `change ... = ∑ i ∈ Finset.univ, (-1)^↑i • F i ≫ eqToHom ⋯` at the
  *top* of the body — before any of the unfolds at L998-L1007 — so
  that the named family is what the unfolds reduce against) is
  attempted. **If this also fails, fall back to Q2a Path A
  (architectural refactor)**.

## Recommendation

### For Q1 (`h_loc_exact` sorry at BasicOpenCech.lean:1783)

**ALIGN_WITH_MATHLIB**. The closure recipe is:

```
1. For each f ∈ s₀ and each x : Fin (n+1) → ↑s₀:
   a. V_x := ∏ᶜ_a basicOpenCover ↑s₀ (x a) is affine
      (basicOpenCover_finset_inf'_isAffineOpen, iter-057).
   b. V_x ⊓ D(f.1) = D(f.1|_{V_x}) where f.1|_{V_x} is the
      image of f.1 under R = Γ(C.left, U) → Γ(C.left, V_x).
   c. IsAffineOpen.isLocalization_of_eq_basicOpen on (V_x, f.1|_{V_x})
      gives IsLocalization.Away (f.1|_{V_x}) Γ(C.left, V_x ⊓ D(f.1)).
   d. instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmonoid
      upgrades to IsLocalizedModule (powers f.1) of the algebra-induced
      LinearMap Γ(V_x) → Γ(V_x ⊓ D(f.1)).
2. IsLocalizedModule.pi packages these per-coord instances into
   IsLocalizedModule (powers f.1) of LinearMap.pi(per-coord-restriction),
   for free as a typeclass instance.
3. Identify this LinearMap.pi with the slice-cover Čech differential
   at degree n by extensionality (LinearMap.pi_ext' is one option).
4. Use IsLocalizedModule.iso + LinearEquiv.exact_iff to transport
   h_a₀_fun f (slice-cover exactness) to exactness of the localised
   K₀ differential.
```

**LOC**: ~80-120 LOC of glue. Strategy-critic's ~80 LOC estimate is
valid at the low end of this range — bridging step 1d (per-coord
algebra + IsLocalization.Away + adapter) is the bulk of the work.

### For Q2 (`cechCofaceMap_pi_smul` sorry at BasicOpenCech.lean:1120)

**MATHLIB_GAP_CONFIRMED via the project's choice of `ModuleCat k`**. Two
viable paths:

**Path B (tactical, ~30-50 LOC, RECOMMENDED FIRST)**: at the very top
of `cechCofaceMap_pi_smul`'s body — **before** the
`dsimp only [scK₀, K₀, …]` at L998 — `set` the named family:

```lean
let F := cechCofaceMap_summand_family s₀ n
```

then after the dsimp+simp unfolds at L998-L1007, attempt a single
`change`-pivot rewriting the goal's `∑ i, (-1)^↑i • Pi.lift_thing_anonymous_i ≫ eqToHom`
into `∑ i, (-1)^↑i • F i ≫ eqToHom`. Because `F` was defined as the
named extraction of that same `Pi.lift_thing`, the equality is by
`rfl` at the elaborator level — provided the dsimp+simp chain hasn't
whnf-reduced past the named family.

If the `change` succeeds, `alternating_sum_pi_smul_aux` applies with
`G := fun i ↦ F i ≫ eqToHom`-binder form and per-summand R-linearity
from `cechCofaceMap_summand_family_R_linear` becomes a direct
binder-level invocation.

**Critical experiment**: have iter-107+'s prover run `lean_multi_attempt`
with `["set F := cechCofaceMap_summand_family s₀ n", "change ∑ i, ...", "exact alternating_sum_pi_smul_aux ..."]`
at L998 (BEFORE the dsimp) and at L1014 (AFTER the dsimp+simp+show
chain). One of the two positions should land a defeq for the
`change`. If neither does, fall back to Path A.

**Path A (architectural, ~150-250 LOC, FALLBACK)**: refactor the
local-to-global proof to operate on a `ModuleCat R`-valued Čech
complex.

```
1. Define toModuleKPresheaf_R : (Opens.subType (≤ U))ᵒᵖ ⥤ ModuleCat R
   where R := Γ(C.left, U). The presheaf restricts toModuleKPresheaf
   to opens contained in U, with each section module the (R-module
   image of the) original Γ(C.left, V) under the restriction
   R-algebra structure.

2. Define K₀_R := cechCochain_R := (cechComplexFunctor with A :=
   ModuleCat R) on the basic-open cover restricted to ≤ U.

3. Identify K₀ = (ModuleCat.restrictScalars (algebraMap k R)).mapHomologicalComplex K₀_R
   (R is a k-algebra via the structure morphism k → Γ(C.left, ⊤) →
   Γ(C.left, U) = R; the restriction-scalars functor is k-linear).

4. R-linearity of K₀.f is INTRINSIC to K₀_R.f's type (it's a
   morphism in ModuleCat R, so R-linear by definition). The
   restrictScalars functor preserves linearity, so K₀.f (which IS
   K₀_R.f with k-restricted view) is R-linear when viewed through
   the R-module structure transported back to K₀.X_i via the
   forgetful.

5. The iter-099+ alternating-sum infrastructure
   (alternating_sum_pi_smul_aux, etc.) becomes redundant: it was
   only needed because R-linearity was being certified post-hoc.

6. cechCofaceMap_pi_smul and h_loc_exact both close via the
   restrictScalars + IsLocalizedModule.pi route directly on K₀_R,
   without any post-hoc pattern-matching.
```

LOC: ~150-250. Eliminates the 7-iter-stuck pattern but is a deep
restructuring.

**Recommended sequencing for iter-107+**:
- iter-107 prover: attempt Path B (tactical `change`) with the
  `lean_multi_attempt` probe described above. Time-box at 1 iter.
- iter-108 (if Path B fails): plan agent dispatches a refactor subagent
  to execute Path A on a feature branch.

## Caveats

- **Path B depends on a `rfl`-defeq** between the post-unfold goal
  shape and the named family. The iter-099 → iter-103 prover history
  documents multiple positions in the proof where Lean's whnf reducer
  destroys the named-family head symbol; if `set F` is shadowed before
  the dsimp/simp chain bakes the unfolds into the goal, the `change`
  will fail. The probe should test BOTH "set BEFORE dsimp" and "set
  AFTER dsimp" positions.

- **Path A requires re-doing the `e_i` / `h_mod_pi_i` letI scaffolding**
  inside `h_K₀_exact` — the current scaffolding (BasicOpenCech.lean:
  1605-1694) builds R-module structures by hand on `∀ i, Z_i i`-types.
  Under Path A these instances become free: the morphism in `ModuleCat R`
  already carries the R-module structure. The refactor would simplify
  the proof considerably *if* the bridge to `ModuleCat k` via
  restrictScalars composes cleanly with the project's existing
  `cechCochain` / `cechComplexFunctor` API.

- **Both paths preserve the strategy-critic's broader plan**: Q1's
  recipe (`IsLocalizedModule.pi` + slice-cover identification +
  `LinearEquiv.exact_iff`) is independent of which Q2 path closes
  `cechCofaceMap_pi_smul`. Path A removes the need for `cechCofaceMap_pi_smul`
  entirely; Path B closes it directly.

- **Mathlib has the building blocks for both Q1 and Q2 Path A**:
  - `Mathlib.RingTheory.TensorProduct.IsBaseChangePi:93` —
    `IsLocalizedModule.pi`.
  - `Mathlib.Algebra.Module.LocalizedModule.IsLocalization` —
    `instIsLocalizedModuleToLinearMapToAlgHomOfIsLocalizationAlgebraMapSubmonoid`.
  - `Mathlib.Algebra.Module.LocalizedModule.Basic` —
    `IsLocalizedModule.iso`, `IsLocalizedModule.linearMap_ext`.
  - `Mathlib.AlgebraicGeometry.AffineScheme:716` —
    `IsAffineOpen.isLocalization_of_eq_basicOpen`.
  - `Mathlib.Algebra.Category.ModuleCat.RestrictScalars` (and
    `.../ChangeOfRings.lean`) — the `restrictScalars` functor for
    Path A.
  - `Mathlib.RingTheory.LocalProperties.Exactness:211` —
    `exact_of_localized_span`, already the closer in the project's
    L1786 step.

- **Both paths share the same `exact_of_localized_span` consumer at
  L1786**; they differ only in HOW `h_loc_exact` is produced and HOW
  R-linearity of `f_R`/`g_R` is established.

## Related analogies
- [[cech-koszul-precedent]] — iter-059 audit of Čech /
  extra-degeneracy / `exact_of_isLocalized_span` precedents. The
  present analogy refines that file's "Step 2 localized identification
  (~60-100 LOC)" estimate with the concrete `IsLocalizedModule.pi`
  call and confirms the per-coord adapter chain (`IsLocalization.Away`
  → `instIsLocalizedModule...AlgebraMapSubmonoid` → `IsLocalizedModule.pi`).

---
*Iteration: 106*
