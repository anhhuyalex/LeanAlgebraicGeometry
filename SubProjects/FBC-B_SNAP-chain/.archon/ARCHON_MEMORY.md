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

- FBC: MATE route DEAD; seeds reached via concrete-tilde chain (per-chart 01I9→fork→separated→MV→bridge). Whole mate apparatus (`base_change_mate_{domain,codomain}_read`/`_gstar_transpose`/`_section_identity`/`_generator_trace`/`pushforward_base_change_mate_*`) is COMPILE-DEAD (seeds = bare sorry) — excise in a DEDICATED iter (sync blueprint `\uses` same iter), never alongside an FBC prover. KEEP `base_change_mate_regroupEquiv` (the (a) cancellation `(R⊗_A B)⊗_R M≅B⊗_A M`, NOT `cancelBaseChange` directly) + `base_change_map_affine_local`.
- `X.Modules`/value-ModuleCat diamond: positional `rw`/`simp`/`erw`/`comp_apply`/`hom_comp` fail → term-mode + `change`-to-nested-application.
- SNAP: carrier `AddCommGrpCat`; coherence via `Localization.Monoidal` `LocalizedMonoidal L W ε` synonym (full `MonoidalCategory(X.Modules)` DEAD). HAZARD: `⊗_loc` NOT defeq hand-built `tensorObj` → bridges object-iso-CONJUGATED via `tensorObjLocalizedIso=μ⁻¹;counit` (Option B), NOT bare `α=α^loc` (type error); Option A redefine rejected (defeq blast radius). Stalkwise DEAD.
- Build `lake build <module>` (LSP hides kernel timeouts); never `maxHeartbeats 1e6`. No LLM API key.
