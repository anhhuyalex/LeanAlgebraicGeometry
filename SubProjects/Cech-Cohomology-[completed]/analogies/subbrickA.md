# Analogy: Sub-brick A — identifying `Γ(V, pushPullObj F Y_p) ≅ ∏_σ Γ(U_σ ∩ V, F)`

## Mode
api-alignment

## Slug
subbrickA

## Iteration
055

## Question
For the evaluated-at-`V` augmented Čech section complex (`V ≤ coverOpen 𝒰 i`), identify
degreewise and on differentials
`Γ(V, pushPullObj F Y_p) ≅ ∏_{σ : Fin(p+1)→I} Γ(U_σ ∩ V, F)`.
(Q1) Does Mathlib give "sections of a module sheaf over a coproduct scheme = product
of sections"? (Q2) Does Mathlib identify pullback-of-a-module-sheaf-along-an-open-
immersion with restriction, with definitional sections?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean:135` — `pushPullObj F Y = (pushforward Y.hom).obj ((pullback Y.hom).obj F)`.
- `…/CechHigherDirectImage.lean:552,561,599` — `coverCechNerveOver` / `…Aug` / `CechNerve`; degree-`p` object is `∐_σ U_σ` with structure map `q_p = Sigma.desc (fun σ ↦ j_σ)`, `j_σ : U_σ = ⋂_k coverOpen 𝒰 (σ k) ↪ X`.
- `…/CechAcyclic.lean:1501,1513` — `sectionCechFaceRestr` / `sectionCech_objD_apply`: the existing product-of-presheaf-sections + alternating-restriction-sum machinery (`sectionCechProductEquiv`).
- `…/QcohRestrictBasicOpen.lean:113,248,283` — project ALREADY uses `restrictFunctor`/`restrictFunctorIsoPullback`/`restrict_obj`/`restrictFunctorComp`.

## Decisions identified

### Decision: Q2 — pullback along an open immersion = restriction (sections)

- **Mathlib idiom**: For an open immersion `f : X ⟶ Y`, `Scheme.Modules.restrictFunctor f : Y.Modules ⥤ X.Modules` (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:319`) is the "better-defeq" model of pullback, with:
  - `restrict_obj` (`Sheaf.lean:328`): `Γ(M.restrict f, U) = Γ(M, f ''ᵁ U)` — **`rfl`** sections identification.
  - `restrict_map` (`Sheaf.lean:331`): the restriction maps are `rfl`-equal to `M.presheaf.map (f.opensFunctor.map i).op`.
  - `restrictFunctorIsoPullback f : restrictFunctor f ≅ pullback f` (`Sheaf.lean:371`) — the bridge to the actual `Scheme.Modules.pullback` that `pushPullObj` uses.
  - `restrictFunctorComp` (`Sheaf.lean:392`), `restrictFunctorId`, `restrictFunctorCongr` for the bookkeeping.
  Why Mathlib chose it: `restrictFunctor` is literally `SheafOfModules.pushforward` along `f.opensFunctor`, so its object sections are `Γ(M, f ''ᵁ U)` by `rfl` — exactly the defeq the consumer wants — while `pullback` (a sheafification-of-a-left-adjoint) has no such defeq. Mathlib keeps both and ships the iso.
- **Project's current path**: `pushPullObj` is built on raw `Scheme.Modules.pullback Y.hom`. The project ALREADY adopts the `restrictFunctorIsoPullback` idiom in `QcohRestrictBasicOpen.lean:113–114,248,283–286` to convert `pullback`-along-an-open-immersion to `restrict`, with `restrict_obj` for sections.
- **Gap**: identical — Mathlib's idiom is the right one and the project already uses it elsewhere.
- **Verdict**: PROCEED (reuse the established project pattern: `restrictFunctorIsoPullback` + `restrict_obj`).

### Decision: Q1 — sections of a module sheaf over a coproduct scheme = product

- **Mathlib idiom**: only *binary* and only at the structure-sheaf / general-`TopCat.Sheaf` level:
  - `Scheme.coprodPresheafObjIso` (`Mathlib/AlgebraicGeometry/Limits.lean:476`): `(X ⨿ Y).presheaf.obj (op U) ≅ X.presheaf.obj (op (inl⁻¹U)) ⨯ Y.presheaf.obj (op (inr⁻¹U))` — **structure sheaf, binary**.
  - `TopCat.Sheaf.isProductOfDisjoint` (`Mathlib/Topology/Sheaves/SheafCondition/PairwiseIntersections.lean:430`): for disjoint `U ⊓ V = ⊥`, `F(U ⊔ V) ≅ F(U) ⨯ F(V)` — **general `TopCat.Sheaf C X`, binary, same space**.
  - `Scheme.sigmaMk` (`Limits.lean:246`): `(Σ i, f i) ≃ₜ ∐ f` — indexed coproduct of scheme *spaces*, but **no section decomposition**.
  There is **no indexed (`σ`-family) version, and none for `SheafOfModules`/`X.Modules`**.
- **The off-the-shelf escape that shrinks the gap**: `SheafOfModules.evaluation R X` **preserves all limits** (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Limits.lean:85,108`), and `X.Modules = SheafOfModules X.ringCatSheaf` `HasLimits` (`Sheaf.lean:50`). So if the degree-`p` object is recognised as a *product in `X.Modules`*, then `Γ(V, ∏_σ N_σ) ≅ ∏_σ Γ(V, N_σ)` is FREE. This turns "sections over a coproduct OPEN" (no API) into "sections of a product MODULE" (off-the-shelf).
- **The single irreducible new lemma**: package the coproduct as a product at the module level —
  `pushPullObj F Y_p ≅ ∏_σ pushPullObj F (Over.mk j_σ)` in `X.Modules`,
  equivalently `(q_p)_* (q_p)^* F ≅ ∏_σ (j_σ)_* (j_σ)^* F` for `q_p = Sigma.desc (fun σ ↦ j_σ)`.
  This is the disjoint-union/coproduct sheaf decomposition (a module on `∐_σ U_σ` is the product of its restrictions to the components, which ARE disjoint on the coproduct space even though the `U_σ ⊆ X` overlap).
- **Cost of divergence**: must be built. Port path: lift the binary `isProductOfDisjoint`/`coprodPresheafObjIso` argument to (i) finite-indexed `σ`, (ii) `SheafOfModules`. The lift to modules goes through `Scheme.Modules.toPresheaf` which is **faithful, reflects isos, and preserves limits** (`Sheaf.lean:75–78`) plus `M.presheaf.IsSheaf` (`Sheaf.lean:126`): build a module-linear comparison map, check it is an iso on the underlying `Ab`-presheaf via the sheaf condition over the disjoint component cover, transport back. NOTE the degree-`p` object identification `(coverCechNerveOver 𝒰).obj [p] = ∐_σ U_σ` (fibre powers of the open immersions = intersection opens) is its own geometric bookkeeping, separate from this sheaf-theoretic gap.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (one lemma; everything around it is off-the-shelf).

### Decision: route the DIFFERENTIAL through the existing `sectionCechProductEquiv` machinery?

- **Mathlib/project idiom**: `CechAcyclic.lean` already proves `sectionCech_objD_apply` (`:1513`): read through `sectionCechProductEquiv`, the cosimplicial coface differential IS the alternating sum `∑ᵢ (-1)ⁱ • (presheaf restriction `sectionCechFaceRestr`)`. That is the exact shape `SectionCechModule.dDiff` consumes.
- **Recommendation**: YES — express Sub-brick A's degreewise iso so it lands in the shape `∏_{σ} Γ(coverInterOpen 𝒰 σ ⊓ V, F)` and route the differential-match through `sectionCech_objD_apply` rather than rebuilding the alternating-sum bookkeeping. The only genuinely NEW work is the degreewise *object* iso (Q1 gap + Q2 off-the-shelf + evaluation-preserves-products); the differential is reuse.
- **Verdict**: DIVERGE? no — ALIGN with the existing project API (reuse `sectionCech_objD_apply`).

## Recommendation

Decompose Sub-brick A's degreewise iso `Γ(V, pushPullObj F Y_p) ≅ ∏_σ Γ(U_σ ∩ V, F)` into a
`\uses`-chain with exactly ONE new-infra leaf:

1. `pushforward_obj_obj` (`Sheaf.lean:156`, `rfl`): `Γ(V, (q_p)_* N) = Γ(q_p⁻¹V, N)`. **off-the-shelf**
2. **[NEW]** `pushPullObj F Y_p ≅ ∏_σ pushPullObj F (Over.mk j_σ)` (coproduct→product at module level). Scope a prover lane: port binary `isProductOfDisjoint`/`coprodPresheafObjIso` to indexed + `SheafOfModules` via `toPresheaf` (faithful/reflects-iso/preserves-limits) + `IsSheaf`.
3. `evaluation` preserves products (`Sheaf/Limits.lean:85`): `Γ(V, ∏_σ N_σ) ≅ ∏_σ Γ(V, N_σ)`. **off-the-shelf**
4. `restrictFunctorIsoPullback` (`Sheaf.lean:371`): `(j_σ)^*F ≅ F.restrict j_σ`. **off-the-shelf, already used in `QcohRestrictBasicOpen.lean`**
5. `restrict_obj` (`Sheaf.lean:328`, `rfl`) + `opensRange`/`image_preimage`: `Γ(j_σ⁻¹V, F.restrict j_σ) = Γ(U_σ ∩ V, F)`. **off-the-shelf**

Then chain to the existing `CechAcyclic.lean` machinery: land in `∏_σ Γ(coverInterOpen 𝒰 σ ⊓ V, F)`
and reuse `sectionCech_objD_apply` for the differential. Four of five leaves are off-the-shelf
(two `rfl`), Q2 is already an adopted project pattern, and only leaf #2 needs a dedicated prover lane.
