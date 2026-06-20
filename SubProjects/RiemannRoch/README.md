# AlgebraicJacobian — Riemann–Roch subproject

<!-- archon:readme -->

## Project

A formalization in Lean 4 + Mathlib of **Riemann–Roch in genus zero** for a smooth, proper,
geometrically irreducible curve `C` over a field. By a smooth curve we mean a geometrically
irreducible, smooth scheme of relative dimension one over a field. This subproject was extracted
from the `Algebraic-Jacobian-Challenge` project; it keeps the self-contained Riemann–Roch
development and the cohomology / `ℙ¹` substrate it depends on, and drops the Jacobian, Picard,
Albanese and Čech higher-direct-image machinery.

The development builds, from the ground up:

- **Weil divisors** on a curve (`WeilDivisor`, prime divisors, `degree`, `order`, principal
  divisors) — RR.1;
- the **invertible sheaf `𝒪_C(D)`** of a Weil divisor — RR.2\*;
- the **Euler characteristic** `χ`, the `ℓ`-invariant, and the **Riemann–Roch formula in genus
  zero** `ℓ(D) = deg(D) + 1` (`WeilDivisor.l_eq_degree_plus_one_of_genus_zero`) — RR.2;
- **vanishing of `H¹`** for skyscraper sheaves via flasque-sheaf cohomology — RR.2.H¹;
- the line bundle **`𝒪_C(P)`** of a closed point and its global sections — RR.3;
- the **rational-curve isomorphism** `C ≅ ℙ¹` over `k̄` for a genus-`0` curve
  (`genusZero_curve_iso_P1`) — RR.4.

The genus and the `H¹(C, 𝒪_C)` `k`-vector-space structure are supplied by the sheaf-of-`k`-modules
cohomology substrate (`Cohomology/StructureSheafModuleK`); the concrete `ℙ¹` (`ProjectiveLineBar`)
is supplied by `Genus0BaseObjects`.

## References

See [`references/summary.md`](references/summary.md) for a description of each source. The
development cites Hartshorne's *Algebraic Geometry* (Chapters II.6 and IV.1) throughout.

## Structure

- `AlgebraicJacobian/Genus.lean` — definition of `genus`
- `AlgebraicJacobian/RiemannRoch/` — the Riemann–Roch development (RR.1 – RR.4):
  `WeilDivisor`, `OcOfD`, `RRFormula`, `H1Vanishing`, `OCofP`, `RationalCurveIso`
- `AlgebraicJacobian/AbelianVarietyRigidity.lean` — hosts the genus-`0` curve `≅ ℙ¹` target
  `genusZero_curve_iso_P1`
- `AlgebraicJacobian/Cohomology/StructureSheafModuleK/` — the sheaf-of-`k`-modules structure
  sheaf and `H^i`, used to define genus and the Euler characteristic
- `AlgebraicJacobian/Genus0BaseObjects/` — the concrete projective line `ProjectiveLineBar`
- `blueprint/` — leanblueprint source (build with `leanblueprint pdf` and `leanblueprint web`)
- `references/` — informal sources backing the formalization
- `.archon/` — agent state (not committed)

## How to build

```bash
lake exe cache get   # download Mathlib olean cache
lake build           # compile the project
```

## How to run the formalization loop

```bash
archon loop .
```

This launches the plan → prove → review loop and opens a dashboard.
