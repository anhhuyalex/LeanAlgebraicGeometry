# Strategy

## Goal

Formalize the main theorems of Hausel–Hitchin (2021), "Very stable Higgs bundles, equivariant
multiplicity and mirror symmetry" (MR4411733), with Theorem 1.3 (multiplicity formula
`m_{F_E} = chi_T(Sym(T+*_E)) / chi_T(Sym(A*)) |_{t=1}`) and Corollary 1.4 (explicit product
formula `m_N = 2^{3g-3} · 3^{5g-5} · … · n^{(2n-1)(g-1)}`) as primary targets, and Theorem 1.1
(very stable ↔ closed upward flow), Theorem 1.2 (type-(1,…,1) classification by "no repeated
zero") as secondary targets. The moduli space M, Hitchin map h, and nilpotent cone N are
geometric objects unavailable in Mathlib and will be axiomatized, with proof obligations
discharged in a later geometric realization phase.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|------------|-----|-------------------|-------|
| Blueprint | ACTIVE | 0 | — | — | Complete this iter |
| BB theory | NEXT | 4–6 | ~400–600 | AlgebraicGeometry.Scheme, GroupAction, GradedAlgebra | Sumihiro theorem missing in Mathlib; needs from-scratch |
| Higgs tower | NEXT | 3–4 | ~200–350 | AlgebraicGeometry.Scheme (curves), RingTheory | Slope-stability not in Mathlib; axiomatize |
| Moduli axioms | NEXT | 2–3 | ~150–250 | AlgebraicGeometry.Scheme | M/h/N/m_F as axiom decls; no construction yet |
| Char formula | NEXT | 2–3 | ~150–250 | PowerSeries, Polynomial, LinearAlgebra | chi_T product formula; polynomial-valuedness |
| Thm 1.3 + Cor 1.4 | NEXT | 3–5 | ~200–400 | (builds on BB+Moduli axioms+Char formula) | Equivariant localization argument |
| Thm 1.2 classif. | NEXT | 3–5 | ~200–400 | Divisors, OrderZero | Hecke transform formalism; divisor zero-order |
| Mirror symmetry | PAUSED | 10–15 | ~500–900 | FourierMukai, Jacobians, HyperKahler | Far outside current Mathlib |
| Geom. realization | PAUSED | 15–25 | ~800–1500 | (all of above + stacks/coherent sheaves) | Discharge axioms; Moduli stack machinery |

Notes on parallelism: BB theory and Higgs tower are independent; they can advance in parallel.
Moduli axioms can start as soon as Blueprint is done. Char formula is independent of BB theory.

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|-------|----------------------|-----|-------|-------------|---------------------|---------|
| Init | 001 · 1 | 0 | Basic.lean | scaffold | — | — |
| Blueprint | 001 · 1 | 0 | Overview.tex | 33 nodes, 0∞, 0 isolated | axiom-first insight | Phantom prerequisites in Mathlib |

## Routes

**Axiom-first route (primary):** Declare M (semi-projective variety with T-action), h (Hitchin
map, proper, T-equivariant), N = h^{-1}(0) (the nilpotent cone as a subscheme), and m_F (the
local-ring-length multiplicity) as formal Lean `axiom` declarations or `sorry`-bodied `noncomputable def`s with stated hypotheses. Prove Thm 1.1, 1.2, 1.3, and Cor 1.4 conditionally on these axioms. The two parallel sub-lanes — BB theory (pure abstract algebraic geometry) and the Higgs bundle tower (concrete bundle definitions) — converge at lem:pushforward_locally_free.

**Geometric realization route (secondary, paused):** Build M, h, N, m_F as actual Lean objects
using algebraic geometry (coherent sheaves, moduli stacks, Hitchin fibration). Discharges the
axioms from the primary route. Unblocked only after primary route axioms are laid out: the
axiom-first approach explicitly catalogues which geometric facts need construction, so both
routes can be planned simultaneously. (The former "secondary route" circular-dependency is
resolved: the primary route no longer waits for the secondary; the secondary route consumes
the primary's axiom list as its specification.)

## Open strategic questions

- Which Lean representation for smooth projective curves? Options: abstract `CurveType` axiom,
  `AlgebraicGeometry.Scheme` with `IsSmooth + IsProjective + genus = g`, or `EllipticCurve`-style.
- For BB Prop 2.1: will Sumihiro's theorem (T-invariant affine open cover) need a from-scratch
  proof, or can it be circumvented by assuming M is affine near each fixed point?
- For chi_T product formula: is `MvPowerSeries` or `FormalMultilinearSeries` the right home in
  Mathlib for the weight-space product expansion?
- For component multiplicity m_F as local ring length: is `LocalRing.length` in Mathlib
  sufficient, or does it require a non-reduced scheme / DVR argument not yet in Mathlib?

## Mathlib gaps & new material

**Gaps to fill (build from scratch; no Mathlib namespace covers these):**
- Semi-projective variety with C*-action (BB theory foundation)
- Slope-stability of algebraic vector bundles on curves (Infrastructure)
- Sumihiro's theorem for C*-actions (required for BB Prop 2.1)
- Local ring length at generic points of non-reduced scheme components (for m_F)

**New project material (declarations the project must introduce):**
- `axiom` declarations for M, h : M → A, N, and m_F (moduli-space axioms)
- `VeryStableHiggsBundles.BBTheory` — semi-projective variety + weight decomposition
- `VeryStableHiggsBundles.CharFormula` — chi_T(Sym(V*)) product formula over weight spaces
- `VeryStableHiggsBundles.MultiplicityCore` — Cor 1.4 product formula as a pure algebra result
