<!-- ARCHON_MEMORY.md — condensed project knowledge for all agents.
     Written by the plan agent and archon discuss. Read by all agents.

     HARD LIMITS: max 10 bullets · ~600 chars total.
     Prune before adding. Only keep what would surprise an agent reading
     the code fresh. Do NOT duplicate things obvious from the codebase.
-->

- All infrastructure (perverse sheaves, MHS, non-abelian Hodge, moduli of Higgs bundles) is absent from Mathlib — use `noncomputable def ... := sorry`, NOT bare `axiom`.
- Both Lean files are scaffolding targets; all 22 declarations go in `Basic.lean` under namespace `MR4433080HitchinFibrationsAbelianSurfacesAndThePwConjecture` (abbreviate `HitchinPW` in discussion only; Lean uses the full name).
- The four main theorem lanes (PW_genus2, PW_even, oddTautPerversity, PW_iff_multiplicativity) are mutually independent once the common type scaffold exists — dispatch them as parallel provers.
- Reference source: `references/MR4433080-hitchin-pw.tex` is the definitive citation source; its line ranges 200–800 cover all main results.
