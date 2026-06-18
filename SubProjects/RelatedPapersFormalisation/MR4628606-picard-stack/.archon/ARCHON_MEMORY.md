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

- Algebraic stacks, operational Chow, and log geometry are absent from Mathlib; all three are axiomatized as named axioms — never try to use `AlgebraicGeometry.Scheme` as a substitute for stacks.
- `SimpleGraph` cannot represent prestable graphs (no loops, no multi-edges, no genus labels); `PrestableGraph` must be built from scratch.
- `MvPolynomial` (Mathlib) is the right tool for Pixton's formula polynomial ring.
- JPPZ 2018 formula is a permanent named axiom (`Axiom.JPPZ2018`) — it is the keystone reduction for `thm:main`; the main theorem is axiom-dependent on it until a formalization of JPPZ is available.
- Operational Chow is represented as an abstract ring (not a concrete completion/limit) — this decision is committed; do not re-open it.
- `MulAction.orbitEquiv` (Mathlib, `GroupTheory.GroupAction.Quotient`) is available for the graph automorphism quotient.
