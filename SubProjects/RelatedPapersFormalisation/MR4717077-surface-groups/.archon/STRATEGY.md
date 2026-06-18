# Strategy

## Goal

Formalize **Theorem 1.2.1** (Landesman–Litt, arXiv:2205.15352): if
\(\rho : \pi_1(\Sigma_{g,n}) \to \mathrm{GL}_r(\mathbb{C})\) is an MCG-finite
representation with \(r < \sqrt{g+1}\), then \(\rho\) has finite image.
Secondary goals: asymptotic Putman–Wieland (Thm 1.4.1) and free-group
corollary (Cor 1.6.1).

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|-------------------|-------|
| Blueprint (DAG) | ACTIVE | 1 | 0 | none | chapter coverage complete |
| Foundations | NEXT | 4 | ~150–300 | `FundamentalGroup`, `FreeGroup` | surface group π₁(Σ_{g,n}) not in Mathlib; axiomatize as fp group |
| Elementary algebraic results | NEXT | 3 | ~200–400 | representation theory basics | Prop 2.1.1, Cor 1.6.1, Birman exact seq. |
| Deep analytic inputs (axioms) | NEXT | 2 | ~100–200 | none | 5 axioms: thm:period-map, thm:rank-bound-subsystem, thm:cohomologically-rigid-integral, thm:nah-unitarity, prop:mcg-finite-family |
| Main theorem assembly | NEXT | 4 | ~300–500 | none | connect axioms through the blueprint proof scaffold |

## Completed

| Phase | Iters | LOC | Files | Key results | Reusable techniques | Pitfalls |
|-------|-------|-----|-------|-------------|---------------------|---------|
| Init | 1 | 0 | Basic.lean | project scaffold | — | — |

## Routes

Single route: formalize main theorem via sorry-based scaffolding for the five
deep analytic inputs listed below; prove the elementary algebraic/group-theoretic
skeleton in full.

The five axioms and the rationale for each:
1. **`thm:period-map`** (Thm 5.1.6): derivative of period map as a multiplication
   map. Proved in Appendix A; requires Hodge theory / Mehta–Seshadri outside Mathlib.
2. **`thm:rank-bound-subsystem`** (Thm 1.7.1): rank bound for sub-local systems of
   R¹π°_∗ 𝕍. Proof uses Clifford-type vector bundle arguments + §6 Hodge theory.
   Axiomatizing this makes Thm 6.2.1 and Thm 7.2.1 provable from it, recovering
   both as genuine deductions in the formalization.
3. **`thm:cohomologically-rigid-integral`** (EG18/KP20b integrality): requires
   p-adic Hodge theory not in Mathlib.
4. **`thm:nah-unitarity`** ([LL22] Thm 1.2.12): a semisimple cohomologically rigid
   local system of rank < √(g+1) that underlies a VHS is unitary. Core non-abelian
   Hodge theory input; used in both the unitary case and semisimple case proofs.
5. **`prop:mcg-finite-family`** (Prop 2.1.3): lifting an MCG-finite representation
   to a local system on a versal family requires étale homotopy sequence machinery.
   Axiomatize; the converse direction (MCG-finite → comes from a family) is the
   hard direction; the easy direction (from a family → MCG-finite) is separately
   provable from the axiom.

## Open strategic questions

- Can `prop:mcg-finite-family` eventually be proved from Mathlib's algebraic
  topology? (étale path spaces / homotopy exact sequences are not yet in Mathlib)
- Once `thm:rank-bound-subsystem` is axiomatized, should a future phase attempt
  to prove it from `thm:period-map` + Clifford + vector bundle methods?

## Mathlib gaps & new material

**Gaps to fill:**
- Surface group π₁(Σ_{g,n}) as a finitely-presented group with MCG outer action
- Mapping class group Mod_{g,n} and PMod_{g,n}
- Five deep analytic axioms (see Routes above)

**New project material:**
- `MCGFinite`: predicate on representations π₁(Σ_{g,n}) → GL_r(ℂ)
- `finiteImage_of_mcgFinite`: main theorem statement
- Axioms for the five deep inputs; elementary proofs for the rest
