# Strategy

## Goal

Formalize the main results of Bhargava–Shankar–Wang "Squarefree values of polynomial discriminants I" (MR4419629, arXiv:1611.09806): **Theorem 1.1** (density of monic integer degree-n polynomials with squarefree discriminant = λ_n > 0), **Theorem 1.2** (density with maximal order = ζ(2)⁻¹), and **Corollaries 1.3–1.4** (monogenic S_n-fields lower bound; shortest vector count). The deliverable is sorry-bodied proofs of all four results with admitted sorry-axioms for the Ekedahl sieve and geometry-of-numbers tail estimates.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|-------------------|-------|
| 1 — Statements-first: density type + theorem stubs | ACTIVE | 2–3 | ~150–250 | `Filter.Tendsto`, `Nat.card`, `Polynomial.discriminant` | Density type must typecheck before Phase 2 |
| 2 — Elementary definitions | NEXT | 3–5 | ~200–400 | `ZMod`, `Polynomial.roots`, `Matrix.det` | Strong/weak divisibility encoding in Lean |
| 3 — Local densities (Yamamura) + Euler product | NEXT | 3–4 | ~200–350 | `ZMod`, `Nat.card`, `Finprod` | Yamamura formula for p=2 separately |
| 4 — Algebraic infrastructure (Q-inv, σ_m) black-box | NEXT (parallel with 3) | 2–3 | ~80–150 | `Matrix`, `LinearMap` | Sorry-axioms for Q-inv properties |
| 5 — Sieve deduction + sorry-bodied proofs | NEXT | 2–3 | ~100–200 | — | Connecting sorry-axioms to main stmts |
| 6 — Corollaries (sorry-bodied) | NEXT | 1–2 | ~80–120 | — | Monogenic/shortest-vector deduction |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|-------|----------------------|-----|-------|-------------|---------------------|----------|
| 0 — Blueprint DAG | 001 · 1 | 0 | Overview.tex | 47-block blueprint, fully wired | — | Empty Lean files |

## Routes

Single route (statements-first, sorry-bodied). Key pivot decisions made in iter-001:

1. **Density type**: use `Filter.Tendsto atTop` on the ratio sequence `n ↦ #{f ∈ S, H(f) < n} / #{f ∈ V_n(ℤ), H(f) < n}`. This is the standard Lean approach for natural density; it matches `def:natural_density` in the blueprint.
2. **Q-invariant**: black-box sorry-axioms (~80 LOC): state the key properties (transformation law, Q = m for the explicit matrices) as `sorry`-bodied lemmas; do not formalize the full determinant-of-minors construction.
3. **Ekedahl sieve / GON**: introduced as named sorry-axioms (`axiom ekedahlSieve`, `axiom geometryOfNumbersCount`) so the corollaries are sorry-bodied and Phase 6 is finite (not ∞).

Milestone sequence: (a) density type `def naturalDensity` typechecks; (b) main theorem statements `thm1_1`, `thm1_2`, `cor1_3`, `cor1_4` typecheck with sorry; (c) definitions filled bottom-up; (d) Yamamura's formula and Euler product proved; (e) sorry-axioms for sieve/GON stated; (f) full sorry-bodied proofs assembled.

## Open strategic questions

- Whether the Lean type for Yamamura's local density should use `ZMod.card` / `Nat.card` ratios or a direct `MeasureTheory.Measure` on the p-adic integers.
- Whether to later attempt a proof of the Ekedahl sieve itself (would require a separate Mathlib contribution of comparable scale to this project).

## Mathlib gaps & new material

**Gaps to fill:**
- Natural density for height-ordered polynomial families — not in Mathlib; will introduce as project definition using `Filter.Tendsto`.
- Ekedahl sieve — not in Mathlib; admitted as sorry-axiom.
- Counting G(ℤ)-orbits in cusps — not in Mathlib; admitted as sorry-axiom.
- Yamamura's local density formula — not in Mathlib; will formalize from paper.

**New project material:**
- Height function H(f) = max{|aᵢ|^{1/i}}; natural density via `Filter.Tendsto`.
- Strong/weak p²-divisibility of discriminant; sets U_m^(s), U_m^(w).
- Symmetric matrix space W_n, SO_n action, invariant polynomial f_B.
- Q-invariant black-box sorry-axioms (transformation law + explicit matrix formula).
- Embedding σ_m: sorry-bodied construction with stated properties.
- Local density λ_n(p) and Euler product λ_n = ∏_p λ_n(p).
