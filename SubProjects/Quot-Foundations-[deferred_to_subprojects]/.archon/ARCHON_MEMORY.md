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

- FBC mate route `base_change_mate_*_legs_conj`/`_gstar_transpose` is ABANDONED; named FBC legs go via FBC-B direct (`baseChangeGammaPullbackEquiv`). Don't re-attempt the mate route.
- `X.Modules`/value-ModuleCat diamond: positional `rw`/`simp`/`erw`, `comp_apply`, `hom_comp` all fail → term-mode + `change`-to-nested-application.
- SNAP: carrier `AddCommGrpCat` not `AddCommGrp`; `P⊗Q` = `MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q`. Stalkwise DEAD. `sectionsMul_assoc_unit` = FOUR cast-mediated component Eqs (TensorPower.Basic idiom), NOT one GradedMonoid Eq/HEq.
- Build with `lake build <module>` (LSP hides kernel timeouts); never add `maxHeartbeats 1e6`. No LLM API key in env.
- Hilbert polynomial is χ (Euler char), NOT H⁰: parent `def:hilbert_polynomial` is χ-semantic; this i=0 leg does NOT formalize it (sibling cohomology leg owns it). Never build an H⁰ `Φ_s` under that label.
