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

- **Jacobian (MISSING from Mathlib):** `Mathlib.WeierstrassCurve.Jacobian` = Jacobian coordinates for elliptic curves only. `Jac(C)` as a g-dimensional abelian variety is NOT in Mathlib. Blueprint axiomatizes it via `def:jacobian_av` sorry stubs.
- **Positivity labels are camelCase:** `def:isNef`, `def:isBig`, `thm:siuCriterion`, `lem:nefFromBetti` (blueprint labels, not lean names). Use these exact strings in `\uses{}`.
- **`thm:weil_height_mathlib`:** Marked `\mathlibok`; actual Mathlib declaration name unverified — check `Mathlib.NumberTheory.Heights` before referencing in Lean.
- **`thm:arith_bezout`:** Black-box from Autissier [Théorème 3]{HauteursAlt3}; NOT in Mathlib; always a sorry stub.
- **Do NOT add `\leanok`:** Only the sync_leanok tool sets this; agents must never add it manually.
