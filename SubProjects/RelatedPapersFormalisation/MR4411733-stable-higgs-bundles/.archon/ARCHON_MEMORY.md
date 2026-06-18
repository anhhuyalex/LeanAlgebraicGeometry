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

- Moduli space M, Hitchin map h, nilpotent cone N, and component multiplicity m_F are unavailable in Mathlib; must be axiomatized (`axiom` decls) — do not attempt to construct them from Mathlib primitives.
- Sumihiro's theorem (T-invariant affine open cover for C*-actions) is NOT in Mathlib 4.30+; the BB proposition (Prop 2.1) needs a from-scratch algebraic proof.
- `AlgCurves`/`VecBundles` are phantom Mathlib namespaces; smooth projective curves with stability conditions must be built from scratch.
- chi_T(Sym(V*)) product formula is the algebraically independent core of Thm 1.3; can be proved in `MvPowerSeries`/`PowerSeries ℤ` without any geometry.
- All blueprint declarations use TODO placeholders `VeryStableHiggsBundles.TODO.<Name>`; rename when Lean decls are written.
- Blueprint is one cone: 1 leaf = `thm:euler_pairing_agreement`, 3 roots = semi_proj_variety / Higgs_bundle / T_pos_module.
