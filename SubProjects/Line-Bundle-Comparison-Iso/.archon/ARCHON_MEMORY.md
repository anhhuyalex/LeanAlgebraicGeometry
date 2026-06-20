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
- `exists_tensorObj_inverse` MOVED to `TensorObjInverse.lean` (downstream of DualInverse) iter-023 — decoupled from K1. Close via `rem:dual_discharges_inverse`: `dual L` + glue local left-unitor contractions (`homOfLocalCompat`) + `isIso_of_isIso_restrict`. NEVER sheafify-the-eval (d.2 dead-end).
- Terminal `trivialisation_restrict_compat` STUCK 3 iters (1st green window iter-032 closed only S1=chart morphism `j=resLE`+reindex `image_preimage_of_le`). Residual = 5 per-constituent restrict-naturality squares against `j` (composite pullback+sheafification isos, NO codebase precedent): tensorObj_restrict_iso, dual_restrict_iso≫dualIsoOfIso, dual_unit_iso, tensorObj_unit_iso, + blueprint-OMITTED `uι`=restrictFunctorIsoPullback≫pullbackUnitIso. effort-broken iter-033; prove S2 (tensorObj_restrict_iso) FIRST as template. NOT a blind lane. DEAD probes: subst/rcases on `hVU:V≤U` (not eqn), `simp[restrictIsoUnitOfLE]`, `congr 1`/`Iso.eq_inv_comp`/`Hom.ext`.
- DUAL route COMPLETE; reopening DualInverse: `inv ε` whnf-times-out, use shallow `_naturality_apply` + `exact`. (`dualnat006`)
- K1 carrier diamond RESOLVED (023): defeq composite `Gβ:=pushforward₀OfCommRingCat…⋙restrictScalars β'` (`δ Gβ=μIsoβ.inv` rfl) + `hadj'`/`H1'` re-ascribed onto `presheaf⋙forget₂`; drive `simp(zeta:=false)`+`erw` (full simp / `letI`/`transport` re-ADD the diamond — dead). `hmon` IsMonoidal stays IN-PROOF; its 2 collapse IDENTITIES extract as `pushforward_{eta,mu}_appIso_collapse`, threading `pushforward₀OfCommRingCat` sections (NOT `tensor_ext`).
- K1 μ-collapse: `mu_appIso_collapse` CLOSED 031 via `private deltaConjOfMuComparison` (abstract `Type*` fvars dodge the let/whnf friction; one-line `exact`). η CLOSED 028. `IsMonoidal`/`unit_app_tensor_comp_map_δ hadj'` route is CIRCULAR (DEAD). SOLE residual = `_lhs_tmul` (per-section MATE leg, ASYMMETRIC vs `_rhs_tmul` composition — NOT a 1:1 `pushforwardComp_lax_μ` port). 4-ITER WALL: `pushforwardPushforwardAdj_unit_app_app_apply` won't key on the unit leg until `hadj'` is un-`let`/`change`d to `pushforwardPushforwardAdjunction` form. Cocycle-A: `analogies/cocycle-a.md` (rigid ExactPairing off-path — no `MonoidalCategory X.Modules`).
- Cocycle-A B1 = N-square reduced to presheaf eval-core `presheafDualUnitIso_naturality` (DualInverse.lean, eval-at-1 of `ℋom(𝟙,𝟙)`); `(dualIsoOfIso t).symm = dualIsoOfIso t.symm` is a DEAD rewrite (`Iso.self_symm_id` "pattern not found") — take `.symm` of B1 instead.
- Cancel across defeq-but-not-syntactic `SheafOfModules` instances: generic single-`[Category C]` lemma, apply by `exact` (defeq). `rw [Category.assoc]` won't key-match; `erw` whnf-bombs. (`comp_cancel_mid`)
- PARALLEL-LANE BUILD RACE on import chain Substrate→DualInverse→TensorObjInverse: a root-churning lane (any edit to Substrate, the root) starves downstream lanes of every green-build window — iter-029 lost ALL 3 lanes' work this way (proofs verified by `lean_multi_attempt` but never `lake build`-committable). Run root-churning (Substrate) lanes SOLO; only co-dispatch downstream files when the root stays green/untouched. A build-break in a SORRY-FREE decl never dispatches (plan-validate objectivesNoop drops sorry-free files — bit the L219 fix iters 029/030); apply such deterministic fixes via the `refactor` subagent in plan phase, NOT a prover lane (fixed iter-031). AJC `extendScalars`/`pullback0`/`pullbackLanDecomposition` Lan block is DEAD code — do NOT port.
