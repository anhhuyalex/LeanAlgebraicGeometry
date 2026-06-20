# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

**Zero inline `sorry` in the dependency cone of the Albanese universal property**
of the Jacobian, with kernel-only axioms. This subproject was carved from the
**Algebraic-Jacobian-Challenge** parent (extract, 2026-06-20) to isolate the
Albanese / universal-property layer and its geometric + commutative-algebra
substrate, decoupled from the parent's cohomology `Rⁱf_*` engine, FGA Picard
representability, Riemann–Roch, and differentials development.

## Top-level goal (seed)

`thm:albanese_universal_property` — the Albanese universal property of
`J := Pic⁰_{C/k}` (Milne III §6 Prop. 6.1). The label carries two nodes: the
proved `AlgebraicGeometry.Pic0.albanese_universal_property` and the still-unproven
headline `AlgebraicGeometry.Scheme.Pic.albaneseUP`.

## Scope of the cone (105 blueprint nodes)

The closure of the seed keeps, with their open obligations:

- **Albanese UP layer** — `AlbaneseUP.lean`: symmetric-power / Abel–Jacobi map,
  descent through the birational `σ`, the connecting lemma. Several supporting
  lemmas still carry `sorry` (`lem:abel_jacobi_morphism`,
  `lem:symmetric_product_*`, `lem:descent_through_birational_sigma`,
  `def:symmetric_power_curve`).
- **Rational-map extension (Milne I §3 Thm 3.2)** — `Thm32RationalMapExtension.lean`,
  `CodimOneExtension.lean`: the pure-codimension-one indeterminacy / valuative
  extension. Open: `thm:codim_one_extension`, `lem:av_codimOneFree_of_indeterminacy`,
  `lem:isReduced_of_smooth_over_field`, `lem:milne_codim1_indeterminacy`.
- **Auslander–Buchsbaum substrate** — `AuslanderBuchsbaum.lean`: `depth`,
  projective dimension, the AB formula.
- **Coheight bridge** — `CoheightBridge.lean`: coheight ↔ Krull dimension of stalks.
- **Rigidity** — `RigidityLemma.lean`: the rigidity lemma + additivity corollaries.
- **Kept slices** — `Picard/FGAPicRepresentability.lean` (pic-scheme placeholder),
  `RiemannRoch/WeilDivisor.lean` (divisor substrate), and the
  `Genus0BaseObjects/` + `Cohomology/StructureSheafModuleK/` compile-time
  substrate imported by the above.

## Honest build state

Inherited from the parent at extract time. The cone contains **12 unproven**
target nodes and **15 nodes carrying `sorry`** (the genuine remaining work).
`lake build` has **not** been re-run in the sandbox after the carve; the extract
verify gate (or `lake build`) is the authoritative kernel check. Two intentional
`sorry`-carrying riders (`gmScalingP1_chart_agreement_cross01`,
`gmScalingP1_collapse_at_zero`) survive in the imported `GmScaling.lean` with
their blueprint blocks dropped; they are recorded in the extract manifest.

## DAG snapshot (post-carve)

106 blueprint nodes (93 proved), 0 broken `\uses`, all 105 closure labels present,
0 quality regression vs the parent's recorded commit.
