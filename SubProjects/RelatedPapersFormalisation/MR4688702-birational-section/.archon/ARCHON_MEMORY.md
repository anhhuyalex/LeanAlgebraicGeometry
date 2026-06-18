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

- **Pure-axiom route**: no `sorry` in proof bodies; use proper `axiom` declarations for all missing infrastructure. Sorry bodies make downstream proofs vacuously admissible.
- **Reference IDs corrected (iter-002)**: Correct arXiv IDs are bv15=1204.1260, bv19=1610.07341, bv23-valuative=2210.03406, tv18=1410.1164. Old IDs 1404.7475/1412.7523 belong to unrelated papers.
- **Tate modules absent**: `Mathlib.AlgebraicGeometry.EllipticCurve.*` does NOT contain Tate modules of abelian varieties (Jacobians). Do not cite it.
- **Étale fundamental gerbes absent** from Mathlib: gerbe construction (bv15/bv19) and infinite root stack (tv18) need `axiom` declarations.
- **Parallel lanes**: once `SpecBirat` + `TBiratBirat` (steps 7–8) exist, A-path (steps 9–13) and C-path (steps 14–18) are independent — dispatch as parallel prover lanes.
- **BSC.TODO.* names**: all 38 blueprint nodes use placeholder names. Replace with actual `BSC.*` names when writing `Basic.lean` declarations.
- **example:gm-loop tooling gap**: leandag does not track `example` environments as DAG nodes. Cannot wire via `\uses{}` without broken ref. Plan agent should convert to `lemma` env.
