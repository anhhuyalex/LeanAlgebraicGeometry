# Strategy

## Goal

Formalize **Riemann–Roch in genus zero** for a smooth proper geometrically irreducible curve
`C` over a field, with zero inline `sorry` in the dependency cone of the two headline targets and
0 project axioms (kernel-only). The two headline theorems (both protected signatures):

1. **`AlgebraicGeometry.Scheme.WeilDivisor.l_eq_degree_plus_one_of_genus_zero`**
   (`thm:riemannRoch_genus_zero`) — the genus-0 Riemann–Roch formula `ℓ(D) = deg(D) + 1`.
2. **`AlgebraicGeometry.genusZero_curve_iso_P1`** (`thm:genus_zero_curve_iso_p1`) — a genus-0
   smooth proper geometrically irreducible curve over `k̄` is isomorphic to `ℙ¹`.

Primary source throughout: Hartshorne, *Algebraic Geometry*, Chapters II.6 and IV.1.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|-------------------|-------|
| S3 — skyscraper SES (`OcOfD.sheafOf_ses_single_add`). Cokernel iso body sorry-free (`asIso`). Carrier-stalk chain (binding leaf `carrierSheaf_stalk_eq` + seam A + B/B0/B1) CLOSED axiom-clean iter-016. Remaining: G2 `cokernel_stalk_at_iso_kbar` + G3 `cokernel_skyscraper_hom`(+`_isIso`) (iter-017 lane, gate-cleared) · then bridge `carrierSheaf_zero_iso_toModuleKSheaf` (Hartshorne II.6.3A, DECOMPOSED iter-017: Mathlib anchor `mem_integers_of_valuation_le_one` → section-wise =𝒪_C via Dedekind-per-chart → assembly) · then 2 ses corners by transport | ACTIVE (lead) | 2 | ~120–200 | `isIso_of_stalkFunctor_map_iso` [verified]; `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one` [verified]; `stalk_isDVR_of_smooth`/`codimOne_point_residueField_eq_kbar` (done) | bridge = last deep S3 piece (smooth-curve-chart ⇒ Dedekind + valuation=order + gluing); G2/G3 mechanical-ish (residue computation + stalkwise-iso assembly) |
| S2 — finiteness of `Hⁱ(C,𝒪_C(D))`: SES-bootstrap reduces line-bundle finiteness to the **base** `FiniteDimensional k̄ (H¹ 𝒪_C)`, a GENUINE theorem (NOT free — `genus=0` is `finrank=0` ⇏ FiniteDimensional; frozen headline supplies only `_hH1 : finrank=0`). Route (b) (DECIDED Option A): `H¹(𝒪_C) ≅ čechH1 = coker(𝒪(U)⊕𝒪(V)→𝒪(U∩V))` on a two-affine cover, then `FiniteDimensional k̄ čechH1` directly. Chapter rewritten iter-015 (fallacy killed, vestigial `serre_finiteness_mathlib_gap` excised). Fallback (a): push-forward along finite `C→ℙ¹` | NEXT | 3–4 | ~150–300 | two-affine cover affine (curve−pt); Čech=derived comparison (acyclic cover, **CRUX**); `Module.Finite` 2-of-3 | CRUX `HModule_H1_iso_cech_two_affine` rests on affine quasi-coherent `H^{>0}`-vanishing (Mathlib presence TBC when S2 active); `cech_H1_two_affine_finiteDimensional` is real curve-finiteness (Riemann inequality), NOT trivial despite "explicit cokernel" framing |
| M3-close — Euler char + RR formula → **HEADLINE #1** | BLOCKED on S1+S2+S3 | 1 | ~40–90 | χ assembly (mostly proven) | gated by substrate |
| S4 — narrow degree-1 criterion: `degree_positivePart_principal_eq_finrank` + deg φ=1 via `Ideal.sum_ramification_inertia` | NEXT | 2–3 | ~150–320 | `Ideal.sum_ramification_inertia` [verified]; "finite birational morphism onto smooth/normal proper curve ⇒ iso" [check Mathlib before dispatch] | DECIDED narrow (Hartshorne IV.1.3.5 route); full `ofFunctionFieldEmbedding`/I.6.12 NOT needed — dropped |
| M5 — RR.4 rational-curve iso (`RationalCurveIso.lean` + `AbelianVarietyRigidity.lean`) → **HEADLINE #2** | NEXT | 3–4 | ~150–350 | normalization; `finrank`; locally-quasi-finite | `phi_left_*` chain; fix `% archon:covers` before dispatch |
| S5 — `j_!` extension-by-zero ⇒ `injective_flasque` ⇒ general-`i` flasque vanishing | DEFERRED (out of headline cone) | 2 | ~150–300 | `j_!` left adjoint for `Sheaf (Opens X) (ModuleCat k)` | only needed for general-`i`, not the headlines |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|-------|----------------------|-----|-------|-------------|---------------------|----------|
| Cohomology substrate + genus | parent · — | inherited | `Cohomology/StructureSheafModuleK/*`, `Genus.lean` | sheaf-of-`k`-modules `Hⁱ`, `genus = dim H¹(𝒪_C)` | `k`-module structure on `H¹` drives Euler char | out-of-cone Čech carriers kept as compile deps, blueprint-stripped |
| FIX — false-signature corrections | 002 · 2 | ~120 | H1Vanishing, RRFormula, WeilDivisor | M2 headline `H1_skyscraperSheaf_finrank_eq_zero` axiom-clean; `euler_char_shortExact_add` true+provable; `rationalMap_order_finite_support` body closed | base-case factoring drops induction-borne `sorryAx`; relocate finiteness to explicit hyp package; finrank-level transport sidesteps TC-synth timeout | false-as-typed sigs are a planner decision, not prover-forceable; private helpers unreachable cross-file |
| M1 — `finite_order_support_affine` (Hartshorne II.6.1 ring core + AG bridge) | 004 · 4 | ~140 | WeilDivisor; ring-finiteness heart iters 003–004 | finiteness heart `finite_setOf_isPrime_height_one_mem(_or)` + AG bridge closed axiom-clean | stalk IS `IsLocalization.AtPrime` via `isAffineOpen.isLocalization_stalk` (NO explicit ring-iso); `functionField_isScalarTower` + `ordFrac_of_isUnit` | search-shape not difficulty: 2 iters lost assuming `ordFrac_ringEquiv` transport was needed |
| S1a — smooth-local ⟹ DVR (pure-algebra, Route C conormal iso) | 006 · 4 | ~90 | `SmoothRegular.lean` | conormal iso `𝔪/𝔪²≃κ⊗Ω` + `finrank cotangent=finrank Ω` + `isDiscreteValuationRing_of_smooth_dim_one` (all axiom-clean) | `kerCotangentToTensor_injective_iff`+`exact_kerCotangentToTensor_mapBaseChange`+`ker_residue`+`extendScalarsOfSurjective`; verify PRESENT/ABSENT against the actual pin, not recollection | Route R (Stacks 00TT regularity) = 3 deep absent gaps, DROPPED; `FiniteType` unsatisfiable for 1-dim local domain → `EssFiniteType` |
| S1b-core — scheme DVR-stalk substrate (chart/residue/cotangent pin + curve-dim bound) | 013 · 7 | ~260 | `SmoothStalkDVR.lean`, `ResidueFieldKbar.lean`, `CurveKrullDim.lean` | `finrank_cotangentSpace_stalk_eq_one_of_smooth` (iter-011), `residueField_eq_of_coheight_eq_one` (iter-010), `krullDim_curve_le_one` (iter-013), Cohen–Seidenberg keystone `ringKrullDim_le_of_moduleFinite_injective` | residue diamond AVOIDED via `algebraMap_residueField_surjective_of_isLocalization_atPrime`; **embedding-dimension** route (`dim R ≤ dim_κ 𝔪/𝔪²`) reuses the conormal bridge at chart maximals — beats filling a Mathlib gap | trdeg route (`dim=trdeg`/`trdeg=rankΩ`) Mathlib-ABSENT → abandoned iter-013; normality route (`smooth⟹integrally-closed`) also absent → REJECTED |
| S1b-wire — DVR-stalk substrate into `sheafOf` (codim-1 regularity) | 014 · 1 | ~40 | `OcOfD.lean` | `isDiscreteValuationRing_stalk_of_smooth` + global `instIsRegularInCodimensionOneOfSmooth`; `sheafOf` now axiom-clean | a clean consumer-side wire (1-line wrapper + per-point global instance + `inferInstance`) beats a speculative infra lane once the real ingredients land | `IsLocallyNoetherian C.left` threads from properness; place wrapper in OcOfD (needs its in-file finrank→DVR lemma), NOT SmoothStalkDVR |

## Routes

**Single route** — bottom-up formalization of the parent-inherited blueprint along the RR.1→RR.4
dependency chain; the math is classical (Hartshorne IV.1) and the Lean skeleton + detailed chapters
exist. Caveat (strategy-critic): S2/S3/S4 are *new Mathlib-grade infrastructure* (Serre finiteness,
coherent tensor-exactness, Grothendieck vanishing, function-field-determines-curve), NOT mere
sorry-filling — resourced accordingly above.

**Headline #1 H¹-path (timeless fact):** the χ-chain's skyscraper H¹-vanishing uses base-case
factoring — a direct `i=1` proof via in-file `ext_one_eq_zero_of_hom_surjective_of_injective` +
flasque-restriction surjectivity — to drop `injective_flasque`/`j_!` (S5) from the headline cone.
Headline #1 still genuinely depends on smooth⟹DVR (S1), Serre finiteness (S2), and the skyscraper
SES (S3); genus-0 H¹ (`_hH1`) remains a hypothesis of the formula.

**Parallelism:** after the shared S1 (`sheafOf` well-definedness), the headline-#1 arm (S2 + S3 +
M3-close) and the headline-#2 arm (S4 + M5) are largely disjoint and concurrently dispatchable;
they share only S1 and the `ℓ(P)=2` fact (headline #1 at `D=P` feeding M5). Do not serialize.

## Open strategic questions

- S3 carrier-stalk chain (binding leaf `carrierSheaf_stalk_eq` + seam A + B/B0/B1): CLOSED axiom-clean
  iter-016. G2/G3 cokernel leaves (`cokernel_stalk_at_iso_kbar`, `cokernel_skyscraper_hom`(+`_isIso`)) now
  UNBLOCKED → iter-017 prover lane (gate-cleared). Last deep S3 piece = bridge
  `carrierSheaf_zero_iso_toModuleKSheaf` (Hartshorne II.6.3A "algebraic Hartogs"): DECOMPOSED iter-017 into
  Mathlib anchor `mem_integers_of_valuation_le_one` [verified] → `carrierSheaf_zero_sections_eq_structureSheaf`
  (smooth-curve chart ⇒ Dedekind domain; valuation=order; codim-1 pts = prime divisors) → sheaf assembly.
  NEXT iter: scaffold its sub-lemma stubs (same file as G2/G3 → not concurrent) + prove; then ses corners.
- S2 SHARED-VANISHING NODE (blueprint-reviewer iter-016, must-do at S2 activation): `lem:grothendieck_vanishing_curve`
  (no `\lean`, used-by 4) is the SAME H²/Ext²-vanishing as the open `sorry` at RRFormula.lean:469. Pin ONE
  shared project lemma (`Subsingleton (Scheme.HModule kbar F i)` / `=0`, `2 ≤ i`, 1-dim curve), give it the
  `\lean`, retarget L469 + add the `\uses` edge. Also fix `thm:riemannRoch_genus_zero` prose (omits `_hH1`
  premise + fallacious H¹=0 step, RRFormula.tex 789–795; Lean closed, not prover-blocking). DEFER S2 dispatch until pinned.
- `sheafOf_singlePoint` blocker: dag **used-by 0** (off headline cone), blocked on OCofP `private` carriers;
  DEPRIORITISED (defer the OCofP de-privatise refactor).
- S2 CRUX (strategy-critic CHALLENGE iter-015): route (b)'s `H¹(𝒪_C) ≅ čechH1` hides a Čech=derived
  comparison for the two-affine cover (acyclic-cover / Leray). DECIDED Option A (prove the comparison) — Option B
  ("define working H¹ via the cover") cannot avoid it since `genus` is FROZEN on the Ext-based `HModule … 1`.
  The comparison rests on affine quasi-coherent `H^{>0}`-vanishing; confirm Mathlib presence (reference-retriever)
  WHEN S2 becomes active. Also `cech_H1_two_affine_finiteDimensional` is real curve-finiteness (Riemann
  inequality), not trivial. Vestigial `serre_finiteness_mathlib_gap` (∞-source) EXCISED iter-015.
- S4 (RESOLVED): "finite birational ⇒ iso" ABSENT in Mathlib (only normalization scaffold
  `instIsIsoToNormalizationOfIsIntegralHom`); S4 must BUILD the iso from the normalization universal property.
  `Ideal.sum_ramification_inertia` + `isIso_of_stalkFunctor_map_iso` VERIFIED present. Narrow degree-1⇒iso
  route (Hartshorne IV.1.3.5) stands.

## Mathlib gaps & new material

- **Gaps to fill**: **algebraic Hartogs / regular-functions-on-curve** `carrierSheaf₀ ≅ 𝒪_C` (S3 bridge;
  Mathlib anchor `mem_integers_of_valuation_le_one` exists, gap = smooth-curve-chart⇒Dedekind + valuation=order
  + sheaf gluing, ~120–200 LOC) — last deep S3 piece. (Carrier-stalk computation DONE iter-016.)
  Čech=derived comparison `H¹(𝒪_C) ≅ čechH1` + `FiniteDimensional k̄ čechH1` (S2 base, zero Mathlib
  H¹-finiteness); SES-bootstrap line-bundle finiteness (2-of-3); Grothendieck deg≥2 Ext-vanishing;
  ramification-inertia degree-1 criterion + **"finite birational ⇒ iso"** (BUILD from normalization, S4/M5);
  `j_!` extension-by-zero (out of headline cone). NOT gaps: conormal iso `𝔪/𝔪²≅κ⊗Ω` (`kerCotangentToTensor`),
  curve-dimension bound (done iter-013), codim-1 regularity wire (done iter-014).
- **New project material**: `WeilDivisor.sheafOf` (`𝒪_C(D)`), `eulerCharacteristic`/`WeilDivisor.l`,
  `lineBundleAtClosedPoint`, `morphismToP1OfGlobalSections`/`poleDivisor`, the `phi_left_*` chain,
  project instance `CompactSpace C.left` (from `QuasiCompact.compactSpace_of_compactSpace`).
