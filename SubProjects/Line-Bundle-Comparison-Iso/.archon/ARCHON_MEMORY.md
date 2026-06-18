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
- `exists_tensorObj_inverse` import-cycle gated (needs `dual_isLocallyTrivial`); close by MOVING the decl downstream of DualInverse (RelPicFunctor = sole code consumer), never in `TensorObjSubstrate.lean`.
- D3′ cocycle: NatTrans-level via `conjugateEquiv_comp`; never splice a `.app P` δ-square. (`d3cocycle006`)
- DUAL route COMPLETE (iter-015); if reopening DualInverse: `inv ε` whnf-times-out, use shallow `_naturality_apply` lemma + `exact`. (`dualnat006`)
- Top-level extraction of monoidal-carried content FAILS: `MonoidalCategoryStruct (PresheafOfModules X.ringCatSheaf.obj)` not globally synthesizable — keep reductions IN-PROOF (letI/unification). Killed `pullbackTensorMap_restrict_core` iter-018; same wall kills `Functor.Monoidal.transport` for open-immersion δ-iso (K1) — instead mirror closed `tensorObj_restrict_iso` (H1∘H2 in-proof) + `Adjunction.IsMonoidal.leftAdjoint_μ` mate.
- Cancel across defeq-but-not-syntactic `SheafOfModules` instances: state a generic single-`[Category C]` lemma, apply by `exact` (defeq). `rw [Category.assoc]` won't key-match; `erw` mate-whnf-bombs. (`comp_cancel_mid`, iter-015)
- AJC `extendScalars`/`pullback0`/`pullbackLanDecomposition` Lan block is DEAD code — do NOT port.
