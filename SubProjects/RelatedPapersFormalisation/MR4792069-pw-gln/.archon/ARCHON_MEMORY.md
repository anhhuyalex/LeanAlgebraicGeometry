<!-- ARCHON_MEMORY.md — condensed project knowledge for all agents.
     Written by the plan agent and archon discuss. Read by all agents.

     HARD LIMITS: max 10 bullets · ~600 chars total.
     Prune before adding. Only keep what would surprise an agent reading
     the code fresh. Do NOT duplicate things obvious from the codebase.
-->

- `PerverseFiltration` and `WeightFiltration` are permanent sorry-axioms (perverse sheaves / mixed Hodge theory absent from Mathlib).
- Filtration framework: use `Mathlib.RingTheory.FilteredAlgebra.Basic` (IsModuleFiltration); NOT `Mathlib.Algebra.FilteredRing` (doesn't exist).
- Singular cohomology H^m(M_B, ℚ) is not in Mathlib; introduce as opaque ℚ-module `CohomologyGroup`.
- Paper source: `references/pw-gln-maulik-shen.tex` (LaTeX) + `.pdf` (arXiv:2209.02568, Ann. Math. 200 (2024) no. 2).
- All 8 blueprint declarations are in `blueprint/src/chapters/Overview.tex` (consolidated chapter covers both .lean files).
