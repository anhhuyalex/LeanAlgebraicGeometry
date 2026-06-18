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

- **Axiom-first**: sheaf machinery (perverse sheaves, IC complexes, decomp thm, nearby cycles) goes in `Axioms.lean` as named `axiom` decls; do NOT try to prove these from scratch.
- **Primary target**: crystal theorem (Thm 1.6 = `thm:crystal`) first — needs only combinatorial foundations + crystal axioms, no sheaf theory.
- **Mathlib**: `RootSystem`/`RootPairing` exist; Kashiwara crystals, arc spaces, perverse sheaves, affine Grassmannian all MISSING in Lean 4 Mathlib as of Aug 2025.
- **Blueprint**: all 21 decls in `Overview.tex`; `\lean{}` names are `MR4433079IntersectionComplexesAndUnramifiedLFactors.<CamelCase>`.
- **Namespace**: `MR4433079IntersectionComplexesAndUnramifiedLFactors` (long — plan for aliases).
- **No `conjecture` env** in `common.tex`; Conj 1.7 is stated as bold text inside `def:representation-crystal`. Add env if needed.
