# Strategy

## Goal

Formalize the main mathematical content of:

> Bojko, Lim, Moreira: *Virasoro constraints for moduli of sheaves and vertex algebras* (arXiv:2210.05266, MR4712868).

The end-state is a Lean 4 library containing:

1. **Algebraic infrastructure**: the descendent algebra `BD^X`, weight-0 descendents, pair descendent algebra, and the Virasoro operators `L_k` (k ≥ −1) satisfying the Virasoro bracket `[L_k, L_l] = (l − k) L_{k+l}` (proved).
2. **VOA framework**: the abstract vertex operator algebra typeclass (`VertexAlgebra`, `ConformalElement`, `PrimaryState`), stated with sorry bodies for the existence results depending on moduli stacks.
3. **Virasoro conjecture as a statement**: rigorous Lean statements of Conjectures 1.3 and 1.4 (Virasoro for sheaves and pairs), with abstract `VirtualFundamentalClass` hypotheses and sorry bodies — virtual fundamental classes are not in Mathlib.
4. **Main theorem statements**: Lean declarations for Theorem A (Virasoro constraints for semistable sheaves on curves and surfaces with `h^{1,0} = h^{2,0} = 0`) and Theorem B (Virasoro constraints ↔ primary states), all with sorry bodies.

*All formalized statements must match the paper's conventions: holomorphic descendent grading `deg(ch_i^HH(γ)) = 2i − p + q` for `γ ∈ H^{p,q}(X)`.*

The primary **proof target** (fully proved, no sorry) is the Virasoro bracket relation. Everything else may carry sorries in this project.

Phase 5 (rank-1 cases / Hilbert scheme proofs) is out of scope for this project and is listed under Open strategic questions.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|------------|-----|-------------------|-------|
| 1. Blueprint/DAG | COMPLETE | 0 | — | — | — |
| 2a. SuperCommAlgebra typeclass | ACTIVE | 2–3 | ~300 LOC | None (build from scratch) | Sign-rule complexity; Z/2-graded Leibniz |
| 2b. DescendentAlgebra instance | BLOCKED on 2a | 2–3 | ~200 LOC | `FreeAlgebra`, `MvPowerSeries` | Completion vs. polynomial ring trade-off |
| 2c. VirasoroOp definition | BLOCKED on 2b | 1–2 | ~150 LOC | `GradedRing` | Künneth decomposition encoding |
| 2d. Virasoro bracket proof | BLOCKED on 2c | 2–4 | ~300 LOC | None (algebraic) | Long induction on generators |
| 3. VOA axioms | ACTIVE | 3–5 | ~400 LOC | None | Formal power series over End(V) |
| 4. Statements (sorry-bodied) | BLOCKED on 2–3 | 1–2 | ~150 LOC | Abstract `VirtualFundamentalClass` | Statement precision |

Phases 2a and 3 are independent and can start in parallel.

## Routes

### Route: Bottom-up algebraic infrastructure (selected)

Build the algebraic framework first (supercommutative algebra → descendent algebra → Virasoro operators → VOA axioms), then write sorry-bodied statements for the geometric results. The primary proof goal (the Virasoro bracket relation) is purely algebraic and does not require geometric Mathlib infrastructure.

The sorry-scaffold step (sorry-bodied declarations for all four goal items, making the Lean files typecheck) is part of Phase 4 once Phase 2–3 infrastructure is in place.

## Open strategic questions

1. **Rank-1 cases (Phase 5, out of scope)**: Proving Virasoro constraints for rank-1 moduli spaces (symmetric powers of curves, Hilbert schemes of points) requires Hilbert scheme cohomology, which is absent from Mathlib. This is tracked as future work.

2. **Completion vs. polynomial ring for BD^X**: The paper defines `BD^X = SSym⟦CH^X⟧` as a completion of the free supercommutative algebra. In Lean, this can be implemented as a formal power series ring or as an explicit module structure. The choice affects the Virasoro operator definitions. Decision deferred to Phase 2b.

3. **Virtual fundamental class abstraction**: The Virasoro conjecture statements require `[M]^vir ∈ H_•(M)`. The abstract type for this will be an axiomatized typeclass `VirtualFundamentalClass`. The precise interface needed for the sorry-bodied statements must be determined in Phase 4.

## Mathlib gaps & new material

| Item | In Mathlib? | Plan |
|------|-------------|------|
| `SuperCommAlgebra` (Z/2-graded with sign) | NO | Build from scratch in Phase 2a |
| `GradedRing` / `GradedAlgebra` | YES (`Mathlib.RingTheory.GradedAlgebra.Basic`) | Reuse |
| `FreeAlgebra` | YES (`Mathlib.Algebra.FreeAlgebra`) | Reuse |
| `MvPowerSeries` (formal power series) | YES (`Mathlib.RingTheory.PowerSeries.Basic`) | Reuse for completion |
| Vertex algebra typeclass | NO | Build from scratch in Phase 3 |
| Virtual fundamental classes | NO | Axiomatize as abstract typeclass in Phase 4 |
| Hilbert scheme cohomology | NO | Out of scope |
| Joyce's vertex algebra construction | NO | Stated as sorry in Phase 3 |
