# Strategy

## Goal

Formalize **Riemann–Roch in genus zero** for a smooth proper geometrically irreducible curve
`C` over a field, together with the rational-curve isomorphism `C ≅ ℙ¹`. This subproject was
extracted from Christian Merten's Jacobian challenge (`references/challenge.lean.ref`) to isolate
the Riemann–Roch development, which in the parent was frozen behind a permanent "Route-C pause"
and is now the whole project. End-state: zero inline `sorry` in the dependency cone of the two
headline targets, 0 project axioms, kernel-only axioms.

Two headline targets:

1. **`Scheme.WeilDivisor.l_eq_degree_plus_one_of_genus_zero`** (`thm:riemannRoch_genus_zero`) —
   the genus-0 Riemann–Roch formula `ℓ(D) = deg(D) + 1`.
2. **`genusZero_curve_iso_P1`** (`thm:genus_zero_curve_iso_p1`) — a genus-0 smooth proper
   geometrically irreducible curve over `k̄` is isomorphic to `ℙ¹`.

Primary source throughout: Hartshorne, *Algebraic Geometry*, Chapters II.6 and IV.1.

## The arc (dependency chain)

**RR.1 — Weil divisors (`RiemannRoch/WeilDivisor.lean`).** The codim-1 cycle group `WeilDivisor`,
prime divisors, `IsRegularInCodimensionOne`, the valuation `order` at a prime divisor, the degree
homomorphism `divisor_degree_hom`, principal divisors, and linear equivalence. The basic divisor
*vocabulary* on which everything else rests. (Hartshorne II.6.)

**RR.2\* — the invertible sheaf `𝒪_C(D)` (`RiemannRoch/OcOfD.lean`).** `WeilDivisor.sheafOf` and
its immediate corollaries (`sheafOf_zero`, `sheafOf_singlePoint`, the single-point short exact
sequence `sheafOf_ses_single_add`). (Hartshorne II.6, p.144.)

**RR.2.H¹ — `H¹` vanishing for skyscraper sheaves (`RiemannRoch/H1Vanishing.lean`).** Flasque
sheaves and their cohomology vanishing (`HModule_flasque_eq_zero`), skyscraper sheaves are flasque,
and hence `H¹` of a closed-point skyscraper vanishes. Built on the sheaf-of-`k`-modules cohomology
substrate `Cohomology/StructureSheafModuleK`. (Hartshorne II.1 Ex.1.16, III.2.)

**RR.2 — the Riemann–Roch formula (`RiemannRoch/RRFormula.lean`).** The Euler characteristic
`eulerCharacteristic`, the `ℓ`-invariant `WeilDivisor.l`, the `χ` identity
`χ(𝒪_C(D)) = deg(D) + 1 − g` (`eulerCharacteristic_eq_degree_plus_one_minus_genus`), and the
genus-0 specialisation `l_eq_degree_plus_one_of_genus_zero`. (Hartshorne IV.1, pp.294–297.)

**RR.3 — the line bundle `𝒪_C(P)` (`RiemannRoch/OCofP.lean`).** The line bundle of a closed point,
its global sections as a Riemann–Roch space, genus-0 cohomological vanishing, and the genus-0
dimension formula `lineBundleAtClosedPoint_dim_eq_two_of_genusZero`. (Hartshorne II.6, IV.1.)

**RR.4 — the rational-curve isomorphism (`RiemannRoch/RationalCurveIso.lean`,
`AbelianVarietyRigidity.lean`).** From two global sections build a morphism to `ℙ¹`
(`morphismToP1OfGlobalSections`); compute its degree via the pole divisor
(`poleDivisor_degree_eq_finrank`); show a degree-1 morphism between smooth proper curves is an
isomorphism (`iso_of_degree_one`, via the normalization lemmas `phi_left_*`); conclude
`genusZero_curve_iso_P1`. (Hartshorne IV.1, Example 1.3.5.)

## Substrate (kept for compilation, not a goal)

- **`Cohomology/StructureSheafModuleK/*`** — the structure sheaf as a sheaf of `k`-modules and its
  `H^i`, supplying the `k`-vector-space structure on `H¹(C, 𝒪_C)` that defines `genus` and the
  Euler characteristic. Out-of-cone Čech-cohomology carrier declarations remain in the Lean as
  compile dependencies; their blueprint blocks were removed during extraction.
- **`Genus0BaseObjects/*`** — the concrete projective line `ProjectiveLineBar` and its charts,
  the encoding of `ℙ¹` used by RR.4. Three sorried substrate declarations
  (`gmScalingP1_*`, `projectiveLineBar_geomIrred`) are recorded in the extract manifest `riders`:
  their blueprint blocks lived in the dropped `AbelianVarietyRigidity.tex` chapter.

## Roadmap

Bottom-up milestone order to close the cone (158 nodes, **85 open / 16 blueprint `sorry`** at
extraction; the `StructureSheafModuleK` cohomology substrate and `genus` are already done). Each
milestone is gated on the previous one. Counts are open-nodes / `sorry`-nodes per chapter at
extraction; drive the live frontier with `leandag stats` and
`archon dag-query cone --node <seeds>`.

- **M1 — RR.1 divisor vocabulary** (`RiemannRoch/WeilDivisor.lean`, **35 open / 3 sorry**).
  The foundation everything rests on: the `order` valuation and its ring-equiv transports
  (`ord_ringEquiv`, `ordFrac_ringEquiv`, `order_neg/inv/zero/one/mul/pow`), the degree
  homomorphism (`degree_add/neg/sub/zero/single`, `divisor_degree_hom`), prime-divisor
  open-immersion descent (`primeDivisor_ext/ofOpen_point/restrictToOpen_point`), principal
  divisors (`principal_apply/one`, `principal_deg_zero`), and the positive-part / finite-support
  lemmas. Mostly small algebra-of-divisors lemmas; no deep geometry. (Hartshorne II.6.)

- **M2 — RR.2.H¹ flasque `H¹` vanishing** (`RiemannRoch/H1Vanishing.lean`, **15 open / 2 sorry**).
  Flasque sheaves are injective and have vanishing higher cohomology
  (`isFlasque_injective`, `HModule_flasque_*`, `ext_one_eq_zero_of_hom_surjective_of_injective`),
  skyscraper sheaves are flasque (`isFlasque_constant_irreducible`, the `alpha/beta` constant-sheaf
  bridge), hence `H¹` of a closed-point skyscraper vanishes. Consumes the done `StructureSheafModuleK`
  substrate. (Hartshorne II.1 Ex.1.16, III.2.)

- **M3 — RR.2\*/RR.2 the Euler characteristic and the Riemann–Roch formula**
  (`RiemannRoch/OcOfD.lean` **3 open / 3 sorry** + `RiemannRoch/RRFormula.lean` **6 open / 1 sorry**)
  → **HEADLINE #1 `l_eq_degree_plus_one_of_genus_zero`**. The invertible sheaf `𝒪_C(D)` and its
  short exact sequences (`sheafOf`, `sheafOf_zero/singlePoint/ses_single_add`); the Euler
  characteristic and its additivity on short exact sequences (`euler_char_shortExact_add`,
  `euler_char_sheafOf_*`, `euler_char_skyscraperSheaf` using M2); the `χ` identity
  `χ(𝒪_C(D)) = deg(D) + 1 − g`; the genus-0 specialisation. (Hartshorne IV.1, pp.294–297.)

- **M4 — RR.3 the line bundle `𝒪_C(P)` and its global sections** (`RiemannRoch/OCofP.lean`,
  **16 open / 3 sorry**). The carrier sheaf of a closed point (`lineBundleAtClosedPoint.*`
  carriers/submodule/trivAtBot), global sections as a Riemann–Roch space
  (`globalSections_iff`), genus-0 cohomological vanishing (`h1_vanishing_genusZero` using M2/M3),
  and the genus-0 dimension formula `lineBundleAtClosedPoint_h0_sub_h1_eq_two` /
  `…_exists_nonconstant_genusZero`. (Hartshorne II.6, IV.1.)

- **M5 — RR.4 the rational-curve isomorphism** (`RiemannRoch/RationalCurveIso.lean` +
  `AbelianVarietyRigidity.lean`, **10 open / 4 sorry**) → **HEADLINE #2 `genusZero_curve_iso_P1`**.
  The morphism to `ℙ¹` from two global sections (using M4's non-constant section); its degree via
  the pole divisor (`localParameterAtInfty`, `hom_poleDivisor`, `poleDivisor_degree_eq_finrank`);
  a degree-1 morphism between smooth proper curves is an isomorphism (`iso_of_degree_one` via the
  normalization chain `phi_left_locallyQuasiFinite_of_finrank_one` →
  `phi_left_toNormalization_isIso` → `phi_left_fromNormalization_isIso_of_smoothProper_finrank_one`,
  and `algebraMap_bijective_of_finrank_one`); conclude `genusZero_curve_iso_P1`.
  (Hartshorne IV.1, Example 1.3.5.)

**Critical path:** M1 → M2 → M3 (headline #1) → M4 → M5 (headline #2). M3's RR formula and M4's
dimension formula both consume M1+M2; M5 consumes M4's non-constant-section existence. The
`phi_left_*` normalization lemmas (M5) and the genus-0 `h⁰ − h¹` computation (M4) are the deepest
open `sorry`s and the likely rate-limiters.
