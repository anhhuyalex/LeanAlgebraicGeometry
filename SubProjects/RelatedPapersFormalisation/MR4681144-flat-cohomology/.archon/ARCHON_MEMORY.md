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

- **No Lean decls yet**: all \lean{} names are `.TODO.` placeholders; unmatched_lean=17 is expected until Lean scaffolding runs.
- **Confirmed missing from Mathlib 4.30.0**: `CompleteIntersectionLocalRing`, fppf flat cohomology with supports, `GroupScheme` typeclass, `PerfectoidRing`, arc topology, prismatic Dieudonné theory.
- **Partials in Mathlib**: module-theoretic `LocalCohomology` exists but fppf sheaf-version must be built; `WittVector` exists; `AlgebraicGeometry.Sites` (étale, fpqc) exists.
- **Two-track strategy**: Track A = char-p case (crystalline Dieudonné, no arc/animated rings); Track B = full theorem (adds perfectoid rings, arc topology, simplicial rings, prismatic Dieudonné).
- **Animated rings encoding**: use simplicial commutative rings directly, not ∞-categories.
- **Arc covers**: algebraically defined as maps where every rank-1 valuation ring over any point lifts.
