# Strategy

## Goal

Produce a machine-checkable Lean 4 skeleton of Belkale's paper "Rigid local systems and the multiplicative eigenvalue problem" (MR4413746): the main bijection (Theorem egregium) between rigid irreducible unitary local systems with \(n\)-th root of unity local monodromies and F-vertices of \(P_n(s)\), and Theorem KatzQ (no such rank \(>1\) systems when \(n\) is prime). All combinatorial and algebraic definitions are proved in full; proof bodies relying on moduli stacks / GW theory (\emph{named sorry-axioms below}) carry explicit \texttt{sorry}.

**Sorry-axiom set (Route B boundary):**
- `abw_inequalities` proof body — requires Mehta-Seshadri / parabolic bundle theory
- `IsFLineBundle` construction on Par\(_{n,N,S}\) — requires moduli stack machinery
- `strangeDuality_mem_polytope` proof — requires numerical strange duality
- `egregium` proof body — conditionally follows from the above axioms
- `propertyP` proof body — requires Proposition enumerative of the paper

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|------------------|-------|
| Blueprint elaboration | ACTIVE | 1 | — | — | Citation hard-fails and missing declarations need writer pass |
| Combinatorial foundations | NEXT | 4 | ~300–600 | `YoungDiagram`, `Finset`, `Matrix` | Delta_n, YoungDiagram.transpose name (verify vs `Partition.conjugate`) |
| Local systems definitions | NEXT | 3 | ~200–400 | `Matrix.GeneralLinearGroup` (`GL (Fin n) R`), `ConjClasses` | Rigidity predicate; conjugacy class representation |
| Multiplicative eigenvalue polytope | NEXT | 5 | ~400–800 | none (polyhedral definition) | GW numbers introduced abstractly; ABW as sorry-axiom |
| Strange duality map v(A) | NEXT | 3 | ~200–400 | `YoungDiagram.transpose` or `Partition.conjugate` | Map definition; combinator for the transpose operation |
| Main bijection (Theorem egregium) | NEXT | 4 | ~200–400 | sorry-axiom set above | Par-stack, christmas, fvertex-flinebundle all sorry-bounded |
| Theorem KatzQ (prime case) | NEXT | 3 | ~150–300 | `Nat.Prime` | tau_n(s) group must be declared; combinatorial scalar argument |

Note: "Combinatorial foundations" and "Local systems definitions" are **independent** and can be dispatched as **parallel** prover lanes. "Strange duality map" can begin in parallel with "Multiplicative eigenvalue polytope" (depends only on Delta_n + MonodromyData).

## Routes

**Route B (combinatorial skeleton) — active**: Formalize all combinatorial/algebraic definitions and statements completely; hold the sorry-axiom set (see ## Goal) as explicit `sorry`-bounded stubs. Delivers conditional proofs of Theorem egregium and KatzQ against the named axioms.

**Route A (full formalization) — aspirational**: Eliminate all sorry-axioms by developing moduli stack / parabolic bundle / GW theory. No active sub-phase yet; requires Mathlib upstream contributions or bespoke formalization of algebraic geometry stacks.

## Open strategic questions

- Best Lean representation for conjugacy classes: `ConjClasses (GL n C)` (coordinate-free) vs. eigenvalue tuples as `Fin n → ℝ`?
- `YoungDiagram.transpose` vs. `Partition.conjugate`: verify the exact Mathlib 4 name before building Strange duality phase.

## Mathlib gaps & new material

**Gaps to fill**:
- Gromov-Witten numbers for Grassmannians (not in Mathlib; introduce abstractly as a definition)
- Parabolic bundles / moduli stacks Par\(_{n,N,S}\) (not in Mathlib; sorry-axiom under Route B)

**New project material**:
- `MultiplicativeEigenvaluePolytope`: polytope \(P_n(s) \subset \Delta_n^s\) (set-theoretic, no moduli stacks needed for definition)
- `IsRigidIrreducible`: rigidity + irreducibility predicate
- `IsFVertex`: F-vertex predicate
- `TauGroup`: the symmetry group \(\tau_n(s)\) acting on \(P_n(s)\)
- `strangeDualityMap`: map \(\mathcal{A} \mapsto v(\mathcal{A})\) via Young diagram transposition
