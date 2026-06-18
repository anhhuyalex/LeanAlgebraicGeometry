<!-- ARCHON_MEMORY.md — condensed project knowledge for all agents.
     Written by the plan agent and archon discuss. Read by all agents.

     HARD LIMITS: max 10 bullets · ~600 chars total.
     Prune before adding. Only keep what would surprise an agent reading
     the code fresh. Do NOT duplicate things obvious from the code or PROGRESS.md.

     Good candidates: dead-end tactics, files not to touch, Mathlib gap
     coordinates, protected invariants, per-file hazards, standing routes
     to avoid, axioms that must not be accepted.

     Bad candidates: things already obvious from the code or PROGRESS.md,
     current sorry counts, task-specific details that change every iter.
-->

- 4 sorry-axioms must be tracked: [A1] noExceptionalOverZ4 (cites [Schröer 2021b] Thm 7.2), [A2] Fontaine/Abrashkin Hodge restriction, [A3] Picard scheme representability (Artin), [A4] Galois cohomology H¹(k,P).
- Picard scheme representability (A3) is NOT in Mathlib; candidate for upstream PR before or during formalization.
- Exceptional Enriques surfaces ([A1]) require a companion paper [Schröer 2021b] not yet in references/.
- All shared macros (\\ZZ, \\FF, \\Spec, \\Num, \\Br, etc.) defined in blueprint/src/macros/common.tex.
- Strategy: conditional-proof-first (sorry-axiomed skeleton first, then eliminate sorries backwards).
