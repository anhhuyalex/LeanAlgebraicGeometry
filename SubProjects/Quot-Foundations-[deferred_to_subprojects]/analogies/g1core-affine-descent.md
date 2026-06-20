# Analogy: realising G1-core `isLocalizedModule_basicOpen_of_isQuasicoherent` (QC affine descent)

## Mode
api-alignment

## Slug
g1core-descent

## Iteration
028

## Question
Build, axiom-clean, `Scheme.Modules.isLocalizedModule_basicOpen_of_isQuasicoherent`: for a
quasi-coherent `M : (Spec R).Modules` and `f : R`, the restriction `Γ(M,⊤) → Γ(M,D(f))` is
`IsLocalizedModule (Submonoid.powers f)` (Stacks 01HA / Hartshorne II.5.2). Is the planned
explicit finite-cover + flat-equalizer descent the cheapest realisation, or does Mathlib's
`Scheme.Modules`/`QuasicoherentData`/`Tilde`/`SheafOfModules` API make a shorter affine descent
cheap? Confirm the lemma names for the chosen route.

## Project artifact(s)
- `AlgebraicJacobian/Picard/QuotScheme.lean:467` — `isLocalizedModule_tilde_restrict` (built):
  restriction of `tilde N` localizes.
- `AlgebraicJacobian/Picard/QuotScheme.lean:510` — `isLocalizedModule_restrict_of_isIso_fromTildeΓ`
  (built): section-localization for `M` *given* `[IsIso M.fromTildeΓ]`.
- `AlgebraicJacobian/Picard/QuotScheme.lean:614,653` — `isIso_fromTildeΓ_of_isLocalizedModule_restrict`
  / `isIso_fromTildeΓ_iff_isLocalizedModule_restrict` (built): the **G1-assemble** glue. Everything
  downstream is now gated on this one missing keystone (G1-core), which is the directive's target.

## The decisive precedent (the heart of this consult)

Mathlib already proves the **structure-sheaf** version of this exact statement, and proves it
**not** by a finite-equalizer + flat-descent of modules:

> `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`
> (`Mathlib/AlgebraicGeometry/Morphisms/QuasiSeparated.lean:389`) [verified] — the "**Qcqs lemma**"
> of Vakil: for a qcqs scheme `X` and `f : Γ(X,U)`, `Γ(X, D(f)) ≃ Γ(X,U)_f`, i.e.
> `IsLocalization.Away f Γ(X, D(f))`.

Its proof (read in full) is the template we should copy. It assembles the *ring*
`IsLocalization.Away` from its **three pointwise axioms**, each discharged by a pointwise
existence lemma proved by **compact-open induction over the affine cover**, gluing two opens at a
time with the **sheaf condition** — never building an equalizer object, never invoking flatness:

- map_units: `IsUnit.pow _ (RingedSpace.isUnit_res_basicOpen _ f)`
  (`Mathlib/Geometry/RingedSpace/Basic.lean:161`) [verified].
- surj: `exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated` (QuasiSeparated.lean:306) [verified] —
  "every section on `D(f)` is `f^{-n}·`(a section on `U`)". Proved by
  `compact_open_induction_on` (`Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean:235`)
  [verified]: base = affine open via `IsAffineOpen.isLocalization_basicOpen`; step = glue `S` and
  affine `U` via the sheaf gluing gadget `objSupIsoProdEqLocus` + `eq_of_locally_eq'`.
- exists_of_eq: `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact` (QuasiSeparated.lean)
  [verified] — the kernel-up-to-power statement, same induction.

The target `IsLocalizedModule` unfolds to the **identical three pointwise axioms**:
`IsLocalizedModule` (`Mathlib/Algebra/Module/LocalizedModule/Basic.lean:525`) [verified] is the
class `⟨map_units, surj, exists_of_eq⟩`. So the *module* keystone is the module analogue of the
qcqs lemma, with the same proof skeleton.

## Decisions identified

### Decision: globalization method — explicit finite-equalizer/flat-descent (Route E) vs. pointwise-existence + compact-open gluing (Route F)

- **Mathlib idiom**: Route F. `isLocalization_basicOpen_of_qcqs` (QuasiSeparated.lean:389) is the
  canonical realisation of *exactly this descent* and uses pointwise existence + `compact_open_induction_on`
  + sheaf gluing. It deliberately avoids constructing a (co)equalizer object and avoids flatness.
- **Project's current path**: Route E — build `∏ N_a ⇉ ∏ N_{ab}`, localize the equalizer with
  `IsLocalization.flat` (`Mathlib/RingTheory/Flat/Localization.lean:36`) [verified], and match it to
  the equalizer for `Γ(M,D(f))`.
- **Gap**: divergent-with-cost (in-proposal, not shipped). Route E reinvents a flat-descent of a
  finite module limit that Mathlib's own qcqs proof was written to avoid. There is **no single
  Mathlib lemma** "localization commutes with a finite equalizer/limit of modules": you would chain
  `IsLocalization.flat` → `Module.Flat.lTensor`-exactness → kernel/equalizer preservation by hand —
  a genuine diagram chase. Route F replaces that entire step with the 3-field `IsLocalizedModule`
  constructor fed by two `compact_open_induction_on` lemmas, whose inductive step is the generic
  module Mayer-Vietoris `TopCat.Sheaf.isLimitPullbackCone`
  (`Mathlib/Topology/Sheaves/SheafCondition/PairwiseIntersections.lean:391`) [verified] +
  `existsUnique_gluing`/`eq_of_locally_eq'`
  (`Mathlib/Topology/Sheaves/SheafCondition/UniqueGluing.lean:180,224`) [verified], all of which hold
  for any concrete sheaf and so apply to `modulesSpecToSheaf.obj M : (Spec R).Sheaf (ModuleCat R)`.
- **Verdict**: ALIGN_WITH_MATHLIB — adopt Route F (mirror the qcqs lemma) for the globalization.

### Decision: `IsLocalizedModule` assembly — explicit `linearEquiv`/equalizer iso vs. the 3-field constructor

- **Mathlib idiom**: feed `⟨map_units, surj, exists_of_eq⟩` directly (LocalizedModule/Basic.lean:525),
  exactly as `isLocalization_basicOpen_of_qcqs` builds `IsLocalization.Away` from its three fields.
- **Project's current path**: implied construction of a section `≃ₗ` from a localized-equalizer iso.
- **Gap**: divergent-with-cost. The 3-field route never names the localized module object; map_units is
  one line (`isUnit_res_basicOpen`), and surj/exists_of_eq are the two existence lemmas.
- **Verdict**: ALIGN_WITH_MATHLIB — assemble via the 3-field constructor.

### Decision: extracting local presentations from `QuasicoherentData` (the shared, unavoidable step 1)

- **Mathlib idiom**: NONE that hands a *finite basic-open presentation cover* directly. The
  `QuasicoherentData` API (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:201`) exposes
  only: `shrink`, `localGeneratorsData`, `bind`, `ofIsIso`, `IsQuasicoherent.of_coversTop`, and
  `Presentation.map`/`Presentation.ofIsIso` to transport a presentation along the `over`/`pushforward`
  functor. No subcover extractor, no "presentation on every basic open", no affine→tilde shortcut.
  The local presentation ⟹ local tilde step is `AlgebraicGeometry.Modules.isIso_fromTildeΓ_of_presentation`
  (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean:398`) [verified], which needs a presentation of the
  module *on the affine `Spec R_g`* (obtained by transporting `(M.over (X i)).Presentation` across
  `D(g) ≅ Spec R_g`). The affine base of the tilde restriction is then free:
  `instance IsLocalizedModule (.powers f) (toOpen M (basicOpen f)).hom` (Tilde.lean:115) [verified],
  and `isLocalizedModule_tilde_restrict` (project) for sub-basic-opens.
- **Gap**: NEEDS_MATHLIB_GAP_FILL. This step (refine the QC cover to basic opens where `M ≅ tilde`,
  finite subcover by `CompactSpace (PrimeSpectrum R)`) is the prover's "heaviest unknown" and is
  **shared by BOTH routes** — it is the only access to the `M.IsQuasicoherent` hypothesis
  (`= Nonempty M.QuasicoherentData`). Route F does, however, shed two of Route E's obligations: it
  needs **no** explicit equalizer/limit object and **no** proof that the `g_a` generate the unit ideal
  (that algebraic fact was only used to identify the localized equalizer in Route E).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (irreducible; build it once, both routes need it).

### Decision: is the `over`/site machinery the right idiom, or a more direct stalk/Γ-adjunction path?

- **Mathlib idiom**: use the site `QuasicoherentData` ONLY to obtain the per-affine local tilde isos;
  do the **globalisation on the topological side** (`modulesSpecToSheaf.obj M : (Spec R).Sheaf (ModuleCat R)`)
  with the generic topological sheaf condition, exactly as the qcqs lemma works on `X.sheaf`. There is
  no shorter direct path from `M.IsQuasicoherent` to the conclusion: the stalk route (`M.stalk p = N_p`)
  computes the stalk from the same `QuasicoherentData`, so it shares step 1 and adds a colimit layer.
- **Verdict**: PROCEED — site for local data, topology for gluing; do not push the equalizer through
  the site.

## Recommendation

**Do not dispatch the prover on Route E (explicit finite-equalizer + flat descent).** Adopt
**Route F**: realise G1-core as the module analogue of `isLocalization_basicOpen_of_qcqs`.

Concretely, split G1-core into three named prover targets:

1. **map_units** (cheap, ~½ session): `IsUnit (algebraMap R (Module.End R Γ(M,D(f))) (f^n))` from
   `RingedSpace.isUnit_res_basicOpen` [verified] (the R-action on `Γ(M,D(f))` factors through the unit
   `f|_{D(f)} ∈ Γ(O,D(f))`).
2. **surj** = module port of `exists_eq_pow_mul_of_isCompact_of_isQuasiSeparated` [verified] via
   `compact_open_induction_on` [verified]; base = `M|_{D g} ≅ tilde N_g`
   (`isIso_fromTildeΓ_of_presentation` [verified] on the transported presentation) ⟹ tilde instance
   (Tilde.lean:115) [verified]; step = `TopCat.Sheaf.isLimitPullbackCone` /
   `existsUnique_gluing`/`eq_of_locally_eq'` [verified]. **[expected]** as a construction.
3. **exists_of_eq** = module port of `exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact`
   [verified], same induction. **[expected]**.

Then `isLocalizedModule_basicOpen_of_isQuasicoherent := ⟨map_units, surj, exists_of_eq⟩`
(LocalizedModule/Basic.lean:525) [verified], and the existing
`isIso_fromTildeΓ_iff_isLocalizedModule_restrict` (project) closes gap1.

The new content to build (the genuine `[expected]` work, all *ports of existing Mathlib proofs*):
the two module existence lemmas, and a module Mayer-Vietoris `objSupIsoProdEqLocus` analogue (from
`isLimitPullbackCone` + `ModuleCat`'s pullbacks `Mathlib/Algebra/Category/ModuleCat/Limits.lean:141`,
or sidestepped entirely with `existsUnique_gluing`/`eq_of_locally_eq'`). The shared step-1 cover
refinement (`QuasicoherentData` → finite basic-open tilde cover) remains the irreducible core and is
the right first prover dispatch — but built toward Route F's pointwise lemmas, not Route E's equalizer.
</content>
</invoke>
