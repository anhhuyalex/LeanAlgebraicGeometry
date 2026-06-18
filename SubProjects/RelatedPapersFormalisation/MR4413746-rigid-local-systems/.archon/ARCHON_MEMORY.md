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

- Route B: five proof bodies are LOCKED sorry-axioms — `abw_inequalities`, `IsFLineBundle`, `strangeDuality_mem_polytope`, `egregium`, `propertyP`. Do NOT attempt to prove these; stub with `sorry` immediately.
- `YoungDiagram.transpose` name in Mathlib 4 is UNVERIFIED — confirm via LSP before building the Strange duality phase. May be `Partition.conjugate`.
- `LocalSystem` is a tuple of matrices (A₁,…,Aₛ) in GL(n,ℂ) with ∏Aᵢ = I, up to conjugacy — no sheaf or monodromy representation formalism needed.
- `def:par-stack` (`ParabolicStack`) is a sorry-bounded root: do not try to construct the moduli stack; axiomatize as an opaque `def` or `constant`.
- Lean file target: `MR4413746RigidLocalSystemsAndTheMultiplicativeEigenvalueProblem/Basic.lean` — all declarations go here. The namespace is `MR4413746RigidLocalSystemsAndTheMultiplicativeEigenvalueProblem`.
- DAG complete as of iter-001: 24 blueprint nodes, 55 edges, 0 ∞-effort. Blueprint is the single source of truth; do not re-elaborate declarations not in Overview.tex.
