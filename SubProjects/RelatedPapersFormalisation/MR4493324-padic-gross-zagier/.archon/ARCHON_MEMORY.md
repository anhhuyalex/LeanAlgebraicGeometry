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

- **Macro hazard**: `common.tex` defines `\cO = \mathcal{O}`; Overview.tex uses `\scO = \mathscr{O}` to avoid silent override. Do not add `\newcommand{\cO}` in any chapter. Align in a future iter.
- **Mathlib gap: Galois cohomology**: arithmetic Galois cohomology with Selmer conditions is ABSENT. `GroupCohomology.Basic` covers abstract groups only. All Selmer group constructions are new material.
- **Mathlib gap: Iwasawa algebras**: `ℤ_p⟦Γ_F⟧` is absent; `RingTheory.AdicCompletion` is insufficient. Iwasawa algebra must be built from scratch.
- **Architecture decision (settled)**: groups G, H, (G×H)' and HidaFamily are axiomatised as type-class hypotheses in all initial stubs; no concrete constructions in early phases.
- **p-adic L-function**: axiomatised from companion paper [Dis/b]; never re-proved in this project.
- **lem:NumberField_mathlib lean path**: `Mathlib.NumberTheory.NumberField.Basic.NumberField` — verify against live Mathlib in iter-002 before using as anchor.
- **Blueprint TODO placeholders**: all 25 `\lean{}` annotations use `MR4493324TheUniversalPAdicGrossZagierFormula.Basic.TODO.<name>`; prover loop must replace with real Lean names.
