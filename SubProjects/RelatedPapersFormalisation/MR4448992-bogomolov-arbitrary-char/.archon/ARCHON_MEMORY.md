<!-- ARCHON_MEMORY.md — condensed project knowledge for all agents.
     Written by the plan agent and archon discuss. Read by all agents.

     HARD LIMITS: max 10 bullets · ~600 chars total.
     Prune before adding. Only keep what would surprise an agent reading
     the code fresh. Do NOT duplicate things obvious from the codebase.
-->

- **No abelian-scheme API in Mathlib**: `AlgebraicGeometry/Group/Abelian.lean` has only 2 commutativity theorems. `AbelianScheme`, `AbelianVariety.Trace`, and intersection numbers must all be built from scratch.
- **No Chow groups in Mathlib**: `AlgebraicGeometry.ChowGroup` does not exist. Algebraic cycles with Q-coefficients and intersection product are entirely new infrastructure.
- **Three external axioms** (sorry-marked): `thm:maninMumford` (Raynaud/Hrushovski), `lem:fundamentalInequality` (Zhang-Gubler), `thm:yamakiReduction` (Yamaki 2016a). These are admitted; all other sorries eliminated.
- **Blow-up API**: Mathlib has `AlgebraicGeometry.BlowupAlgebra`; verify it suffices for the pencil construction in §3 before Phase 3 begins.
- **Northcott**: verify Mathlib's Northcott property covers function fields (not just number fields) before Phase 5.
