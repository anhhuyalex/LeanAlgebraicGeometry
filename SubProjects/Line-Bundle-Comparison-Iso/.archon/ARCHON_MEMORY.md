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
- **TRUST ONLY `lake build`, NEVER LSP.** LSP `lean_diagnostic`/`lean_multi_attempt` gave STALE-GREEN on the >4800-LOC root `TensorObjSubstrate.lean` for 3 iters (039–041), masking a RED root (undefined-id stub) — falsely reported seed-1 "delivered". Every close confirmed by `lake build` only.
- **SEED-1 DELIVERED iter-042** — root `TensorObjSubstrate.lean` GREEN, sorry-free, K1 PUBLIC (L4770). K1 `hδ` realized via abstract `isIso_oplaxδ_of_conj` ← δ-conjugation `pushforward_mu_appIso_collapse` (on `deltaConjOfMuComparison`) — SUPERSEDED the phantom `pullbackTensorMap_presheafDelta_eq`/`pullbackTensorComparison` (never existed). Blueprint reconciled iter-043.
- PLAN-VALIDATE TRAPS (each = a 0-dispatch iter): (1) STOP-MARKER (034+035) drops a `## Current Objectives` line whose lowercase has "do not touch/assign/work on"/"off-limits"/"no objective" → say "restrict edits to this file". (2) NO-OP SCAFFOLD (047) drops a line naming a sorry-FREE `.lean` file UNLESS that SAME line carries a scaffold keyword (scaffold|skeleton|stub out|declarations for|does not exist) — to ADD a decl to a sorry-free file, put "scaffold" + the filename on ONE line.
- KEYSTONE `conjugateEquiv_restrictFunctorComp_inv` CLOSED iter-048 (root, PUBLIC, axiom-clean): INSTANTIATE `Adjunction.leftAdjointCompIso` on `pushforwardComp` (do NOT equate with `restrictFunctorComp`); residual iso-hom eq by MAP-level merge + `Subsingleton.elim`. **NEVER `ext` a conjugate-headed goal (whnf-bomb).** Bridge **B2 `restrictFunctorIsoPullback_comp_compat` FULLY CLOSED iter-050** via fine-grained per-leg sub-lemmas: `conjugateEquiv.injective` → LHS-collapse keystone (=𝟙) → N `← conjugateEquiv_comp` splits over the FIXED `(C,D)=(X.Mod,V.Mod)` → per-leg pushforward values → cancel `pushforwardComp` → `conjugateEquiv_reindexCongr`. **`mateEquiv_hcomp/vcomp` confirmed UNNEEDED** (supersedes `b2mate045.md`). NOW: terminal engine = B1-crux `H1inv_app_eq_pullbackVal_restrict` — crosses the presheaf/sheaf SHEAFIFICATION boundary (`sheafificationCompPullback_eq_leftAdjointUniq` + `leftAdjointUniqUnitEta`, root). NEVER sheafify-the-eval; monoidal-packaging REJECTED (`MonoidalCategory X.Modules` ABSENT). If B1-crux stalls: effort-break the unit identity / mathlib-analogist cross-domain — NOT user escalation, NOT the `restrictCompReindex`→pullback refactor (that was B2's, done).
- DEAD on the squares: `restrictFunctorComp.hom.naturality` (gives MORPHISM-naturality, not immersion); subst/rcases on `hVU:V≤U`; `simp[restrictIsoUnitOfLE]`; `congr 1`/`Iso.eq_inv_comp`/`Hom.ext`.
- Cancel across defeq-but-not-syntactic `SheafOfModules ≫`/`Iso.hom`: generic single-`[Category C]` lemma applied by `exact` (defeq matches); every `rw`/`simp` of a category lemma MISSES, `erw [Category.assoc]` whnf-bombs (`comp_cancel_mid`). `have ht` via term-mode `exact`.
- K1 carrier diamond RESOLVED (023): defeq composite `Gβ:=pushforward₀OfCommRingCat⋙restrictScalars β'`; drive `simp(zeta:=false)`+`erw` (full simp/`letI`/`transport` re-ADD the diamond — dead).
- PARALLEL-LANE BUILD RACE: a root-churning (Substrate) edit starves downstream lanes of green-build windows (iter-029 lost all 3 lanes). Run root-churning lanes SOLO; co-dispatch downstream only when root frozen/green. AJC `extendScalars`/`pullback0`/`pullbackLanDecomposition` Lan block is DEAD code — do NOT port.
- DUAL route COMPLETE; reopening DualInverse: `inv ε` whnf-times-out, use shallow `_naturality_apply` + `exact` (`dualnat006`).
