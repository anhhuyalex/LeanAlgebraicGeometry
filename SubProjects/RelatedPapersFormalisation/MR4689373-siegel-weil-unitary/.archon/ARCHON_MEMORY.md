<!-- ARCHON_MEMORY.md — condensed project knowledge for all agents.
     Written by the plan agent and archon discuss. Read by all agents.

     HARD LIMITS: max 10 bullets · ~600 chars total.
     Prune before adding. Only keep what would surprise an agent reading
     the code fresh. Do NOT duplicate things obvious from the codebase.

     Good candidates: dead-end tactics, files not to touch, Mathlib gap
     coordinates, protected invariants, per-file hazards, standing routes
     to avoid, axioms that must not be accepted.

     Bad candidates: things already obvious from the code or PROGRESS.md,
     current sorry counts, task-specific details that change every iter.
-->

- `Ch_0(𝒵_ℰ^r(a))_Q` is **axiomatized** in P0 (`HSW.VirtualFundamentalClass`) — do NOT attempt to build Chow groups from scratch. Construction is P2 (`def:virtual-class-full`).
- ℓ-adic perverse sheaves are **absent from Mathlib** — P3a requires a mini-library (mini-scope: constructibility, direct image, Frobenius trace on `Herm_{2d}`). Build only what is needed.
- `Mathlib.AlgebraicGeometry.Modules.Sheaf` exists; `Mathlib.AlgebraicGeometry.VectorBundle` does **not** — use the former for locally-free sheaves.
- `def:herm-torsion-stack` is defined in `Hermitian_Springer.tex` (P3a), not Overview.tex — use this label in cross-chapter `\uses{}` of P3b/P3c.
- `Ẽ_a` sorry-body in P0 is **temporary** — discharged in P1: after Cho–Yamauchi define `Ẽ_a := ∏_v Den(T, L_v, s)`. P3b proves the trace formula using this constructive definition.
- P1 ∥ P2 ∥ P3a run in **parallel** after P0 — none depends on the others. P3c needs P3a+P3b.
- Start P0 prover with `HSW.BaseCurve` (leandag: impact 49, deps 0). Follow dependency order; `NumberTheory.FunctionField` is the Mathlib entry point.
