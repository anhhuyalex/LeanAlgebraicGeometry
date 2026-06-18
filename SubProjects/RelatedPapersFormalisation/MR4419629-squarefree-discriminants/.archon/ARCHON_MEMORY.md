<!-- ARCHON_MEMORY.md — condensed project knowledge for all agents.
     Written by the plan agent and archon discuss. Read by all agents.

     HARD LIMITS: max 10 bullets · ~600 chars total.
     Prune before adding. Only keep what would surprise an agent reading
     the code fresh. Do NOT duplicate things obvious from the codebase.
-->

- **Density type decided**: use `Filter.Tendsto atTop` on ratio `#S_X / #V_X` where X → ∞ with H(f) < X.
- **Q-invariant strategy**: black-box sorry-axioms only (~80 LOC); do NOT attempt full determinant-of-minors construction.
- **Ekedahl sieve + GON**: admitted as named sorry-axioms (`axiom ekedahlSieve`, `axiom geometryOfNumbersCount`); corollaries sorry-bodied off these.
- **Blueprint**: Overview.tex covers both Lean files (47 blocks, 128 edges, 0 isolated, 0 ∞ effort).
- **Namespace**: `MR4419629SquarefreeValuesOfPolynomialDiscriminantsI`.
- **Approach**: statements-first — write theorem stubs that typecheck BEFORE building definitions bottom-up.
