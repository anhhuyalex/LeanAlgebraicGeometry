# Analogy: is the loc-triv chart-chase route to `pullbackTensorIso` materially cheaper than the committed general strong-monoidal pullback build?

## Mode
api-alignment

## Slug
loctriv-bridge

## Iteration
245

## Question
Adjudicate iter-243/244 ("general strong-monoidal pullback build is necessary; the
local-triviality route is blocked because `IsInvertible ⟹ IsLocallyTrivial` is
Mathlib-scale") vs analyst rpf-bridge ("the invertible-pair comparison iso is a cheap
chart-chase via the proven `IsLocallyTrivial.pullback`"). Specifically: (Q1) cost of the
forward bridge `IsInvertible M ⟹ IsLocallyTrivial M` for `Scheme.Modules`; (Q2) whether
`f^*(M⊗N) ≅ f^*M ⊗ f^*N` is provable for *locally trivial* M,N by chart-chase with no
general filtered-colimit machinery; (Q3) bottom line — is there a route restricted to the
pairs the consumer needs that is materially cheaper than the committed 20–38-iter build.

## Project artifact(s)
- `Picard/LineBundlePullback.lean:115` — `IsLocallyTrivial M` (∀x ∃ affine U, M|_U ≅ 𝒪_U).
- `Picard/LineBundlePullback.lean:130` — `OnProduct := { M // IsLocallyTrivial M }` — the
  CONSUMER carrier is `IsLocallyTrivial`, **not** `IsInvertible`.
- `Picard/LineBundlePullback.lean:156` — `IsLocallyTrivial.pullback` (pullback preserves loc
  triv). PROVEN, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`; no `sorryAx`).
- `Picard/TensorObjSubstrate.lean:168` — `IsInvertible M := ∃N, tensorObj M N ≅ 𝒪`.
- `Picard/TensorObjSubstrate.lean:425` — `tensorObj_restrict_iso` (⊗ commutes with restrict
  along open immersion). PROVEN, axiom-clean.
- `Picard/TensorObjSubstrate.lean:515` — `tensorObj_isLocallyTrivial` (⊗ of two loc-triv is
  loc-triv, via common-refinement chart-chase). PROVEN, axiom-clean.
- `Picard/TensorObjSubstrate.lean:546` — `isIso_of_isIso_restrict` (a module map that is iso
  on an open cover is a global iso, via stalk criterion). PROVEN, axiom-clean.
- `Picard/TensorObjSubstrate.lean:672` — `exists_tensorObj_inverse` (loc-triv ⟹ has ⊗
  inverse = `IsInvertible`). `sorry` (the EASY reverse direction, in progress).
- `Picard/TensorObjSubstrate.lean:902` — `pullbackObjUnitToUnit_comp` — the unit-comparison
  composition coherence via mate calculus (`conjugateEquiv_pullbackComp_inv`). PROVEN (~85 LOC).
- `Picard/TensorObjSubstrate.lean:1045` — `pullbackUnitIso` (`f^*𝒪 ≅ 𝒪` for ALL f). PROVEN,
  axiom-clean (`Opens.map f.base` is always `Final`).
- `Picard/TensorObjSubstrate.lean:1138` — `presheafPullbackOplaxMonoidal` — abstract pullback
  is oplax monoidal with canonical δ (mate of pushforward's lax structure). BUILT.
- `Picard/TensorObjSubstrate.lean:1199` — `pullbackTensorMap` (= δ_sheaf, the canonical sheaf
  map `f^*(M⊗N) ⟶ f^*M⊗f^*N`). BUILT (def, no sorry).
- `Picard/TensorObjSubstrate.lean:1147-1173` — iter-242 note: general iso-ness of δ "is a
  genuine Mathlib-scale build" blocked on the concrete inverse-image Lan model (D3 filtered
  colimit/⊗ interchange).
- `Picard/RelPicFunctor.lean:224,343` — consumer carrier is `IsLocallyTrivial`; `functorial`
  must be an `AddMonoidHom`, i.e. `g_C^*(L⊗L') ≅ g_C^*L ⊗ g_C^*L'` (= loc-triv `pullbackTensorIso`).

## Decisions identified

### Decision 1: forward bridge `IsInvertible M ⟹ IsLocallyTrivial M` (Q1)

- **Mathlib idiom**: invertibility ⟹ locally free of rank 1 lives ONLY at the
  module-over-a-ring level: `Module.Invertible R M` ⟹ `Module.Finite`/`Module.Projective`
  (`Mathlib.RingTheory.PicardGroup`); local freeness via `LocalizedModule` + finite
  presentation. The base-change stability rpf-bridge cited
  (`Module.Invertible.instLocalizationLocalizedModule`) is about localizing a module over a
  *ring*, not about `SheafOfModules`.
- **Project's path / what's needed**: lift "tensor-invertible ⟹ loc free rank 1" from a
  point's stalk `𝒪_{X,x}` to a Zariski neighborhood for `M : Scheme.Modules`.
- **Gap**: divergent-with-cost. `IsInvertible M = ∃N, M⊗N≅𝒪` supplies **no** finite-
  presentation datum for M as a `SheafOfModules` through any Mathlib lemma. There is **no**
  stalk-iso ⟹ neighborhood-iso spreading-out for `SheafOfModules`/`Scheme.Modules` at the pin
  (the project's own `isIso_of_isIso_restrict` is global-from-a-GIVEN-cover, not single-stalk
  spread-out). Realizing it = pass to stalks, prove `M_x` invertible over the local ring 𝒪_{X,x}
  (⟹ free rank 1), establish finite presentation of the sheaf, then spread out — bespoke,
  Mathlib-scale.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL — iter-243's "Mathlib-scale" assessment is CORRECT, and
  rpf-bridge's "cheap via `Module.Invertible`" is WRONG (wrong abstraction level). **BUT this
  bridge is OFF the critical path** (Decision 3): the consumer carrier is `IsLocallyTrivial`
  by definition, and only the EASY reverse direction `IsLocallyTrivial ⟹ IsInvertible`
  (`exists_tensorObj_inverse`) is used. So this gap should simply not be built.

### Decision 2: scope of `pullbackTensorIso` — general vs locally-trivial-restricted (Q2)

- **Mathlib idiom**: a left adjoint carries a canonical **oplax** monoidal structure
  (`Adjunction.leftAdjointOplaxMonoidal`, used at L1145) with comparison δ; δ is **natural**
  (`Functor.OplaxMonoidal.δ_natural`), composes via `Functor.OplaxMonoidal.comp_δ`, and has
  unit-interplay coherences (`δ_comp_η_tensorHom`, `δ_comp_tensorHom_η`). The standard way to
  prove δ is an iso on a *subclass* of objects is to reduce to the unit via naturality +
  local trivialisation, NOT to build a concrete strong-monoidal model.
- **Project's path (committed)**: build a concrete strong-monoidal inverse-image model
  (D1 done; D2 `extendScalars` strong via `distribBaseChange`; **D3** `pullback₀ = Lan` +
  the Mathlib-absent filtered-colimit/⊗ interchange) and transport δ to an iso for ALL M,N.
- **Cheaper path (chart-chase, restricted to loc-triv)**: show `pullbackTensorMap` (δ_sheaf,
  already built, L1199) is an iso via `isIso_of_isIso_restrict` (L546) on the cover
  `{f⁻¹(Uᵢ)}` where `Uᵢ` trivialises M and N on X. On `f⁻¹(Uᵢ)`: (i) δ-naturality replaces
  `M|_{Uᵢ}, N|_{Uᵢ}` by 𝒪 (free, `δ_natural`); (ii) δ on the unit pair `(𝒪,𝒪)` is an iso via
  `pullbackUnitIso` (iso for ALL f) + the `δ/η` coherences; (iii) δ commutes with the
  open-immersion base-change square `gᵢ : f⁻¹(Uᵢ) → Uᵢ` — the tensorator analog of the
  ALREADY-BUILT `pullbackObjUnitToUnit_comp`, supported by Mathlib's `comp_δ` +
  `conjugateEquiv_pullbackComp_inv`.
  - **NB the naive "both sides locally 𝒪 ⟹ isomorphic" FAILS**: loc-triv ⇏ trivial globally,
    and non-canonical local isos do not glue without sheaf-Hom gluing (`homOfLocalCompat`,
    itself an unfinished bridge). A canonical global map shown locally-iso is unavoidable —
    and δ is exactly that map, already constructed.
- **Gap**: divergent-with-cost. The committed general build pays for D3 (the filtered-colimit
  /⊗ interchange, ~400–750 LOC, the irreducible Mathlib-scale piece) that the consumer never
  consumes. The chart-chase sidesteps D2 and D3 entirely — it uses only the ABSTRACT oplax δ
  (no concrete inverse-image model) + Mathlib δ-coherences + the project's existing mate
  calculus + `isIso_of_isIso_restrict`.
- **Verdict**: ALIGN_WITH_MATHLIB (use the oplax-δ + local-reduction idiom). Estimated
  ~200–400 LOC / ~8–16 iters, vs 20–38 for the general build. Not "a few iters" (rpf-bridge
  under-scoped by ignoring coherences (ii),(iii)), but materially cheaper.

### Decision 3: is the committed general build necessary? (Q3)

- **The iter-242 "no free oplax ⇒ iso" counterexample is aimed at the wrong functor.**
  `Γ(ℙ¹,𝒪(1)) = 0` shows the **lax** tensorator of **pushforward** (right adjoint, global
  sections) fails to be iso. The consumer needs the **oplax** δ of **pullback** (left
  adjoint). Pullback PROVABLY preserves local triviality (`IsLocallyTrivial.pullback`,
  axiom-clean), so its δ IS an iso on loc-triv objects — the geometric content is local
  triviality + `pullbackUnitIso`, both already in hand. The iter-242 note priced the GENERAL
  iso and conflated it with the loc-triv iso the consumer actually needs.
- **Verdict**: the general strong-monoidal build is NOT necessary for the relative Picard
  consumer. The irreducible sub-step of the cheaper route is coherence (iii) (δ vs the
  open-immersion base-change square via mate transport) — genuine new work, but bounded,
  Mathlib-supported (`comp_δ`), and demonstrated feasible (its unit analog
  `pullbackObjUnitToUnit_comp` is done and axiom-clean).

## Recommendation

Pivot off the committed 20–38-iter general strong-monoidal pullback build. Do NOT build the
forward bridge `IsInvertible ⟹ IsLocallyTrivial` (Mathlib-scale and off-path) and do NOT build
D2/D3 (the concrete inverse-image Lan + filtered-colimit/⊗ interchange). Instead prove
`pullbackTensorIso` restricted to locally-trivial pairs by upgrading the already-built canonical
δ (`pullbackTensorMap`, L1199) to an iso via `isIso_of_isIso_restrict` over the trivialising
cover `{f⁻¹(Uᵢ)}`, using: δ-naturality (Mathlib `δ_natural`, free); δ on `(𝒪,𝒪)` iso via
`pullbackUnitIso` + Mathlib `δ_comp_η_tensorHom`/`δ_comp_tensorHom_η`; and δ-vs-base-change-square
coherence (the tensorator analog of the proven `pullbackObjUnitToUnit_comp`, backed by Mathlib
`Functor.OplaxMonoidal.comp_δ` + the project's `conjugateEquiv_pullbackComp_inv`). Decomposition:
(D1') δ sheaf-level naturality in (M,N) ~40 LOC; (D2') δ_(𝒪,𝒪) iso ~40–80 LOC; (D3') δ vs
open-immersion base-change square ~80–150 LOC; (D4') chart-chase assembly mirroring
`IsLocallyTrivial.pullback` + `tensorObj_isLocallyTrivial` ~50–100 LOC; (D5')
`IsInvertible.pullback`/group-hom wrapper ~15 LOC. Total ~200–400 LOC / ~8–16 iters.
Adversarial check passed: this route does NOT re-import the forward bridge (it lives entirely
in `IsLocallyTrivial`) and does NOT re-import the concrete inverse-image model (it uses only the
abstract oplax δ, reducing iso-ness to the unit case where `pullbackUnitIso` is unconditional).
