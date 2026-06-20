# Analogy: internal-hom-commutes-with-restriction along an open immersion (`dual_restrict_iso`)

## Mode
api-alignment

## Slug
ts231ih

## Iteration
231

## Question
For an open immersion `j : U ↪ X`, does Mathlib already provide (or have a directly
reusable shadow of) the natural iso of presheaves-of-modules
`j_*(ℋom_{𝒪_U}(L, 𝒪_U)) ≅ ℋom_{𝒪_X}(j_*L, 𝒪_X)`? Is the project building a parallel
API it should instead align to? And is the planner's claim that "on `V ⊆ U` both sides
are literally equal" plausible, or an underestimate of a real coherence obstruction?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1353` — `InternalHom.internalHom`
  (project-local slice/end internal hom for `PresheafOfModules`).
- `…:1406` — `dual M := internalHom M (𝟙_ …)`.
- `…:2121–2188` — `exists_tensorObj_inverse` + the `dual_restrict_iso` residual block.
- `…:2366` — `overSliceSheafEquiv` (the shared SHEAF-level, fixed-value-cat root).

## Decisions identified

### Decision A: Is there a Mathlib `PresheafOfModules` internal hom (or `MonoidalClosed`) to align to?

- **Mathlib idiom**: **absent.** `loogle MonoidalClosed (PresheafOfModules _)` → 0 hits;
  `loogle`/`leansearch` for a module-valued internal hom on `PresheafOfModules` /
  `SheafOfModules` return only the hom-*type* `PresheafOfModules.Hom`
  (`Mathlib.Algebra.Category.ModuleCat.Presheaf`), the unit `PresheafOfModules.unit` and
  `unitHomEquiv`. There is no internal-hom *object*, no `Closed`/`MonoidalClosed`
  instance. The closest shape is `CategoryTheory.Sites.SheafHom` (`presheafHom`/`sheafHom`,
  `Mathlib.CategoryTheory.Sites.SheafHom`) — but it is **Type-valued** (hom-SET) and its
  own `## TODO` asks to "turn `presheafHom`/`sheafHom` into bifunctors"; it has no
  module refinement and no pullback/pushforward-compat lemma (confirmed iter-229).
- **Project's path**: project-local `InternalHom.internalHom` (module-valued slice/end),
  correctly shaped like `Sites.SheafHom` but refined to `ModuleCat`-over-`𝒪(V)`.
- **Gap**: divergent-and-absent — there is nothing in Mathlib to align to.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL.** The project is NOT building an avoidable
  parallel; the module-valued internal hom is genuinely missing upstream.

### Decision B: Is there a Mathlib lemma `f_*`/`f^*` ⊗ internal-hom compat (the `dual_restrict_iso` itself)?

- **Mathlib idiom**: **absent.** No `pushforward`/`pullback`-commutes-with-internal-hom
  lemma exists (there is no internal hom to state it about). Mathlib *does* have the
  surrounding adjunction infrastructure that a from-scratch build can lean on:
  - `PresheafOfModules.pushforward` with full pseudofunctor coherence:
    `pushforwardId`, `pushforwardComp`, `pushforward_assoc`, `pushforwardCompToPresheaf`,
    `pushforward_obj_obj` (`= restrictScalars (φ.app X) ∘ pushforward₀Obj …`)
    (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward`).
  - `SheafOfModules.PullbackConstruction.adjunction` — the sheaf-level `f^* ⊣ f_*`
    (`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`).
  - `ModuleCat.restrictScalars_isEquivalence_of_ringEquiv` (a ring ISO ⇒ `restrictScalars`
    is an EQUIVALENCE) — the project's `restrictScalarsEquivalenceOfRingEquiv`
    (`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`). This is the decisive
    single-ring shadow: for an open immersion the structure map `β = j.appIso` is a
    *sectionwise ring iso*, so the value-category transport is an equivalence, not a
    one-way functor.
  - `TopologicalSpace.Opens.overEquivalence U : Over U ≌ Opens ↥U` — the per-open slice
    reindexing (`Mathlib.Topology.Sheaves.Over`), with the file's own `## TODO` being
    exactly "continuity ⇒ sheaf-category equivalence" (iter-229 finding).
- **Gap**: divergent-and-absent — the compat lemma must be hand-built, but on top of the
  above, not from zero.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL.**

### Decision C (feasibility audit): is the planner's "literally equal on `V ⊆ U`" claim correct?

- **Claim**: both sides are LITERALLY equal on `V ⊆ U`, so the target is near-definitional
  rather than a 150–300 LOC build.
- **Empirical reality** (iter-230 binding probe, `lean_goal`/`change` confirmed): the
  residual `(pushforward β).obj (dual M) ≅ dual ((pushforward β).obj M)` is a genuine
  **iso, not a `rfl`**. Two irreducible mismatches make it non-definitional:
  1. **Indexing**: the LHS value at `V` is computed over `Over_U (j.opensFunctor V)`,
     the RHS over `Over_X V`. These slice categories are *equivalent* (via
     `overEquivalence` / a per-`V` `Over_Y V ≌ Over_X (jV)`), not equal.
  2. **Scalars**: LHS module is over `𝒪_U(jV)`, RHS over `𝒪_X(V)`. These rings are
     *isomorphic* via `β = j.appIso`, not equal; the per-`V` action
     (`internalHomObjModule`) is exactly what a value-category-FIXED equivalence
     (`overSliceSheafEquiv`) does NOT transport — the "module fibration" cost.
- **Verdict on the claim**: **the planner is UNDERESTIMATING.** This is the standard
  `f^* ℋom(A,B) ≅ ℋom(f^*A, f^*B)` for an open immersion (flat/iso base change) — a real
  natural iso, NOT a definitional equality. Thinness of `Opens` does NOT trivialise it
  here (unlike the Type-valued sheaf root `overSliceSheafEquiv`) precisely because the
  slice presheaves carry the `𝒪(V)`-module structure that subsingleton-elimination cannot
  reach. The ~150–300 LOC estimate is plausible.
- **Mitigating lever the build SHOULD use** (and which makes it the *favorable* case): the
  target N is the structure sheaf `𝟙_ = 𝒪`, and `𝒪_X`, `𝒪_U` agree on opens `≤ U`, so the
  codomain mismatch collapses; and `β` is a ring ISO, so `restrictScalars β` is an
  EQUIVALENCE (`restrictScalars_isEquivalence_of_ringEquiv`), giving an invertible
  transport. So the iso *exists cleanly* — it is iso-base-change, the good case — but it
  still must be assembled (slice equiv + ring-iso restrictScalars + naturality in `V`).

## Recommendation
Mathlib has no internal hom for `PresheafOfModules`/`SheafOfModules` and therefore no
pushforward-commutes-with-internal-hom lemma; the project's construction is genuine
gap-fill, not an avoidable parallel API — there is nothing upstream to align to
(Decisions A, B → NEEDS_MATHLIB_GAP_FILL). The planner's "literally equal" framing is
wrong (Decision C): the residual is a real natural iso (`f^* ℋom ≅ ℋom(f^*-,f^*-)` for an
open immersion), confirmed non-`rfl` by the iter-230 probe, and its honest cost is the
150–300 LOC slice-comparison build — though it is the *favorable* iso-base-change case
because the codomain is `𝒪` (agrees on `≤ U`) and `β` is a ring iso (so `restrictScalars β`
is an equivalence via `restrictScalars_isEquivalence_of_ringEquiv`). If the build is
sanctioned, anchor it on: per-`V` `Over_Y V ≌ Over_X (jV)` (shadow of
`Opens.overEquivalence`), `restrictScalars`-along-`β`-as-equivalence, and Mathlib's
`pushforward` pseudofunctor coherence (`pushforwardComp`/`pushforward_obj_obj`) — do NOT
expect `overSliceSheafEquiv` (fixed-value-cat, sheaf-level) to discharge it. Otherwise
this confirms the iter-230 escalation: the divisor/`Pic⁰` (Abel–Jacobi) fork is the
cheaper route and the decision is the USER's.
