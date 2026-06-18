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

- **SuperCommAlgebra absent from Mathlib** — `Algebra.SuperCommutative` does not exist in Mathlib4; build from scratch as a typeclass in Phase 2a.
- **Primary proof target**: `thm:virasoro-bracket` (`[L_k, L_l] = (l-k)L_{k+l}`) — purely algebraic, no geometric Mathlib infra needed.
- **Virtual fund. classes absent** — `[M]^vir ∈ H_•(M)` is not in Mathlib; formalize as abstract typeclass hypothesis.
- **Joyce vertex algebra absent** — Joyce's VOA construction from moduli stack homology is out of scope for proofs; appears as sorry/hypothesis.
- **Holomorphic descendent grading**: `deg(ch_i^HH(γ)) = 2i - p + q` for `γ ∈ H^{p,q}(X)` — non-standard; must match paper exactly.
- **One chapter covers both files**: `blueprint/src/chapters/Overview.tex` covers both Lean files via `% archon:covers` — do not create separate chapters.
