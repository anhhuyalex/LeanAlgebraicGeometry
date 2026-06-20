# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

**Zero inline `sorry` in the dependency cone of the Riemann–Roch targets + kernel-only axioms.**
This subproject was extracted from the `Algebraic-Jacobian-Challenge` project (extract on
2026-06-20) to isolate the **Riemann–Roch in genus zero** development for a smooth proper
geometrically irreducible curve. The Jacobian / Picard / Albanese / Čech higher-direct-image
machinery has been dropped; only the Riemann–Roch development and the cohomology / `ℙ¹` substrate
it imports remain. Full framing in STRATEGY.md.

## Top-level goals (extraction seeds)

The cone is driven by the Riemann–Roch chapters (RR.1 – RR.4), with two headline targets:

1. **`AlgebraicGeometry.Scheme.WeilDivisor.l_eq_degree_plus_one_of_genus_zero`**
   (`thm:riemannRoch_genus_zero`) — the Riemann–Roch formula in genus zero, `ℓ(D) = deg(D) + 1`.
2. **`AlgebraicGeometry.genusZero_curve_iso_P1`** (`thm:genus_zero_curve_iso_p1`) — a genus-`0`
   smooth proper geometrically irreducible curve over `k̄` is isomorphic to `ℙ¹`.

Supporting development, all kept whole: Weil divisors and the degree/order/principal-divisor API
(RR.1), the invertible sheaf `𝒪_C(D)` (RR.2\*), the Euler characteristic and `ℓ`-invariant (RR.2),
`H¹` vanishing for skyscraper sheaves (RR.2.H¹), and the line bundle `𝒪_C(P)` (RR.3).

## Scope at extraction (DAG snapshot)

- **158 blueprint nodes** in the closure (85 proved), **19 with `sorry`**, **0 broken `\uses{}`**.
- **3 ∞-effort substrate nodes** (`gmScalingP1_chart_agreement_cross01`, `gmScalingP1_collapse_at_zero`,
  `projectiveLineBar_geomIrred`) are intentional: their blueprint blocks lived in the dropped
  `AbelianVarietyRigidity.tex` chapter while their Lean stays in the kept `Genus0BaseObjects`
  substrate. Recorded in the extract manifest `riders` array.
- The cohomology substrate files (`Cohomology/StructureSheafModuleK/*`) are kept as compile-time
  dependencies; their out-of-cone Čech-cohomology carrier declarations remain in the Lean but
  their blueprint blocks were removed from the kept chapter.

## Open work (the prover frontier)

**85 open nodes / 16 blueprint `sorry`** at extraction (`lake build`: 7 literal `sorry`
declarations). The cohomology substrate (`StructureSheafModuleK`) and `genus` are already done.
The bottom-up milestone plan lives in **STRATEGY.md § Roadmap** (M1 → M5):

- **M1 — RR.1 divisor vocabulary** (`WeilDivisor.lean`, 35 open / 3 sorry).
- **M2 — RR.2.H¹ flasque `H¹` vanishing** (`H1Vanishing.lean`, 15 open / 2 sorry).
- **M3 — RR.2\*/RR.2 Euler char + RR formula** (`OcOfD.lean` + `RRFormula.lean`, 9 open / 4 sorry)
  → **headline #1 `l_eq_degree_plus_one_of_genus_zero`**.
- **M4 — RR.3 line bundle `𝒪_C(P)`** (`OCofP.lean`, 16 open / 3 sorry).
- **M5 — RR.4 rational-curve iso** (`RationalCurveIso.lean` + `AbelianVarietyRigidity.lean`,
  10 open / 4 sorry) → **headline #2 `genusZero_curve_iso_P1`**.

Deepest open `sorry`s / likely rate-limiters: the `phi_left_*` normalization lemmas (M5) and the
genus-0 `lineBundleAtClosedPoint_h0_sub_h1_eq_two` computation (M4).

Run `leandag stats` / `archon dag-query cone --node <seeds>` for the live frontier; the manifest
`.archon/extract-manifest.json` records the agreed seeds and closure.
