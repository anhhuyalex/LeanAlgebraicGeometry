# Project Progress

## Current Stage

prover  (GR-seed cone DELIVERED iter-001; SNAP-S0 assoc chain ACTIVE. iter-017 BROKE the 4-iter ★ wall
(head-pin) ⇒ B4/B5 auto-clean + B6 base CLOSED. Sorry 7→5. iter-018/019: B6 succ stalled on the
`MonoidalPresheaf X` / `X.PresheafOfModules` whiskering-synonym diamond (iter-019 = 0-edit). **iter-019
escalation gate FIRED → iter-020 dispatched mathlib-analogist (api-alignment) `whisker-synonym`**, which
returned a **lean_run_code-VERIFIED new mechanism (route b)**: prove whisker-iso functoriality by routing
through the already-proven canonical bridges `tensorObjWhiskerRightIso_eq`/`_eq` (`rw [..._eq×n]; apply
Iso.ext; simp`) — uniformly `X.Modules`-comp, NO `MonoidalPresheaf X` re-entry, synonym diamond never
appears. Route (a) [synonym-side re-derive] = DEAD END. progress-critic iter-020 = STUCK but endorsed: a
prover round IS warranted because the mechanism is now validated (not a sixth cosmetic retry). LIVE = B6
succ (route b) + B7 (gated). comm = invertibility-gated FUTURE, no consumer.)

## Stages
- [x] init
- [x] autoformalize
- [ ] prover — GR-seed cone delivered (iter-001). SNAP-S0 assoc chain ACTIVE.
      iter-007/009 built the inherited canonical monoidal foundation; iter-011 B1; iter-012 B2/B3+B5
      assembly; iter-013 reduced B4 to ★ + `sheafification_map_unit_eq`; iter-014/016 diagnosed the
      comp-instance diamond + proved the generic coherence; **iter-017 CLOSED ★ (head-pin) ⇒ B4+B5
      auto-clean, + B6 base.** Remaining: B6 succ (braided coherence), B7 (gated on B6). χ-blocked
      nodes (QuotScheme.lean) remain DEFERRED to the cohomology leg at merge.
- [ ] polish — after SNAP assoc chain closes.

## End-state overview

**ACHIEVED (iter-001):** goal seed `AlgebraicGeometry.Grassmannian.represents` sorry-free and
axiom-clean. GR-quot representability cone (Nitsure §1/§5) delivered and merge-ready. SNAP is
self-contained, so SNAP's shape does NOT affect the delivered goal.

**iter-017 BREAKTHROUGH — the 4-iter ★ wall is broken.** ★ `tensorObjAssoc_eta_factor_sheaf` CLOSED
axiom-clean: the >4M-heartbeat `exact` failure was HEAD-MISALIGNMENT, not term size — pinning the generic
coherence's `M := LocalizedMonoidal …` (all isos explicit) + `set_option maxRecDepth 4000` closed it.
B4 + B5 became axiom-clean automatically. B6 `tensorPowAdd_assoc` BASE case CLOSED (helper
`tensorObjIso_tensorPowAdd_reindex`). Sorry 7→5.

**iter-020 — escalation gate FIRED; analogist returned a VERIFIED mechanism.** progress-critic
`snap-conv-20` = STUCK (sorry flat at 5 for 3 iters of B6-succ; iter-019 0-edit; synonym diamond recurs
≥3 iters; estimate at its 1–3 ceiling). The iter-019 gate mandated a mathlib-analogist consult BEFORE any
further prover round — dispatched `whisker-synonym` (api-alignment). Result (`analogies/whisker-synonym.md`,
end-to-end lean_run_code-VERIFIED): **route (b)** — the whisker-iso functoriality the succ case needs
(`tensorObjWhiskerRightIso (e ≪≫ f) G = … ≪≫ …`, +`_refl`, +Left analogues) is proved by routing through
the EXISTING canonical bridges `tensorObjWhiskerRightIso_eq`/`tensorObjWhiskerLeftIso_eq`
(`rw [..._eq×n]; apply Iso.ext; simp`). The bridges already absorbed the synonym crossing, so the residual
is uniformly `X.Modules`-comp with a single comp head — `comp_whiskerRight` (a `@[simp,reassoc]` lemma)
fires directly, NO `hc` bridge, NO `MonoidalPresheaf X` re-entry. **Route (a)** [re-derive on the synonym
side, the iter-019 plan] = DEAD END (re-opens the diamond). progress-critic endorsed: this prover round is
NOT the sixth cosmetic retry — it executes a structurally NEW, validated route. **Next gate (pre-committed):
if B6-succ still does NOT close with the route-(b) helpers → effort-breaker on `lem:tensorPowAdd_assoc`
(the braided-coherence residual) next iter; NO further unconstrained prover rounds.**

**Live scope = B6 succ + B7 ONLY.** comm (`sectionsMul_mul_comm`,
`tensorBraiding_self_eq_id_of_isInvertible`, `tensorPowAdd_comm`) is invertibility-gated FUTURE work with
no consumer (`GCommSemiring` unbuilt) — NOT chased this iter.

## Current Objectives

1. **`AlgebraicJacobian/Picard/SectionGradedRing.lean`** — Blueprint: `chapters/Picard_SectionGradedRing.tex`
   (`lem:tensorPowAdd_assoc` [B6, succ case, sorry @3151], `lem:sectionMul_coherent` →
   `sectionsMul_mul_assoc` [B7, sorry @3156]; axiom-clean upstream: ★ `lem:tensorObjAssoc_eta_factor_sheaf`,
   B4 `lem:tensorObjAssoc_eta_factor`, B5 `lem:tensorObjAssoc_hom_sectionsMul`, B6 base,
   `lem:tensorPowAdd_zero_right`, B1/B2/B3). `[prover-mode: prove]`

   **PRIORITY: B6 succ to closure FIRST (full budget). B7 only after B6 succ closes.**

   - **B6 succ `tensorPowAdd_assoc` (sorry @3151) — THE MUST-FIX, via the iter-020 VERIFIED route (b).**
     Base CLOSED; only `m = k+1` remains. THE recipe is `analogies/whisker-synonym.md` (api-alignment,
     iter-020, end-to-end lean_run_code-VERIFIED). **Do NOT pursue the iter-019 route-(a) [synonym-side head
     re-exposure] — the analogist proved it is a DEAD END (re-opens the `MonoidalPresheaf X` diamond).**

     **STEP 1 — build the 4 whisker-iso functoriality helpers via route (b) (VERIFIED).** Private lemmas,
     each proved by routing through the EXISTING canonical bridges, NOT by re-deriving on the synonym side:
     ```
     private lemma tensorObjWhiskerRightIso_trans {F F' F'' : X.Modules}
         (e : F ≅ F') (f : F' ≅ F'') (G : X.Modules) :
         tensorObjWhiskerRightIso (e ≪≫ f) G
           = tensorObjWhiskerRightIso e G ≪≫ tensorObjWhiskerRightIso f G := by
       rw [tensorObjWhiskerRightIso_eq, tensorObjWhiskerRightIso_eq, tensorObjWhiskerRightIso_eq]
       apply Iso.ext; simp
     -- _refl:  rw [tensorObjWhiskerRightIso_eq]; apply Iso.ext; simp
     -- tensorObjWhiskerLeftIso_trans / _refl: identical, via tensorObjWhiskerLeftIso_eq (+ whiskerLeft_comp)
     ```
     WHY it works (no synonym re-entry): the `_eq` bridges (@1928/@1979, proven axiom-clean) rewrite each
     hand-built whisker to the canonical `(tensorObjIso _ _).symm ≪≫ whiskerRightIso e G ≪≫ tensorObjIso _ _`
     in `X.Modules`; the residual is uniformly `X.Modules`-comp (single comp head, no `MonoidalPresheaf X`
     junction), so `comp_whiskerRight` (a `@[simp,reassoc]` lemma) fires under `apply Iso.ext; simp`. NO `hc`
     bridge needed. Fallback if `simp` mis-fires: `simp only [Iso.trans_hom, Iso.symm_hom,
     MonoidalCategory.whiskerRightIso_hom, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
     MonoidalCategory.comp_whiskerRight, Category.comp_id]` (left: `whiskerLeftIso_hom`/`whiskerLeft_comp`).
     These helpers stay `private` → no leandag coverage debt (consistent with the `_eq` bridges).

     **STEP 2 — restructure the succ proof; iso-level functoriality BEFORE `Iso.ext`.** The CURRENT @3145
     `simp only [tensorPowAdd, tensorObjWhiskerRightIso_eq, …]; sorry` unfolds everything to canonical FIRST
     — that is exactly WHY `rw [ih]` cannot fire (per the analogist consumer note). REPLACE it: keep
     `tensorPowAdd k _` FOLDED and rewrite the LHS at ISO level with the STEP-1 helpers
     (`rw [tensorObjWhiskerRightIso_trans, tensorObjWhiskerLeftIso_trans, …]`) so the LHS exposes
     `tensorObjWhiskerRightIso (tensorPowAdd k m') (L^m'') ≪≫ tensorPowAdd (k+m') m''`; unfold
     `tensorPowAdd (k+1+m') m''` via `k+1+m' = (k+m')+1`; then `rw [ih]`.

     **STEP 3 — close the residual canonical braided coherence** on `L^k, L, L^m', L^m''` (now uniformly
     `X.Modules`): `apply Iso.ext` then `MonoidalCategory.hexagon_forward` `[verified — BraidedCategory
     field]` + `MonoidalCategory.pentagon` `[verified]` + `whisker_exchange` `[verified]`, NO β=id (both
     bracketings = the SAME permutation — that is what separates assoc-∀L from comm). Discharge
     `Nat.succ_add`/`add_assoc` reindexers with a `subst` helper mirroring `tensorObjIso_tensorPowAdd_reindex`
     (@~3021). `maxRecDepth` OK; do NOT add `maxHeartbeats 1e6`.

     **ESCALATION GATE (pre-committed, progress-critic `snap-conv-20` = STUCK):** this is the ONE prover round
     authorized by the verified route-(b) mechanism. **If B6 succ STILL does NOT close**, write a PRECISE
     blocker to the task result — name the exact STEP (helper / `rw [ih]` mismatch / which coherence lemma
     fails) and the residual goal — and bank the compiling partial (the 4 helpers alone are real progress).
     Do NOT fabricate a pin, weaken the statement, add `maxHeartbeats 1e6`, or retry route (a). The next iter
     dispatches `effort-breaker` on `lem:tensorPowAdd_assoc` to split the braided-coherence residual.

   - **B7 `sectionsMul_mul_assoc` (sorry @3156) — STRETCH (only after B6 succ closes).** Assemble
     mirroring `sectionsMul_mul_one`: after `simp only [gMul_mul_apply]`, combine (1) B5 (axiom-clean),
     (2) a NEW μ-slide helper (whiskered-`sectionsMul` naturality with a general comparison `Γ(μ)` in
     place of a single `η` — analogue of B2/B3; build only after B6 succ), (3) B6 (now full), then
     `sectionsCast_self`.

   **Verify:** `lake build AlgebraicJacobian.Picard.SectionGradedRing` (LSP hides `(kernel) deterministic
   timeout`); `#print axioms` = `[propext, Classical.choice, Quot.sound]` on B6 (and B7 if closed), NO
   `sorryAx`. Do NOT add `maxHeartbeats 1e6` (`maxRecDepth` is acceptable for stack-depth, as on ★).
   Commit compiling closed legs; do not leave a non-compiling scaffold. comm decls stay `sorry`.

## Deferred (NOT objectives this iter)

- **comm chain (`sectionsMul_mul_comm`, `tensorBraiding_self_eq_id_of_isInvertible`, `tensorPowAdd_comm`,
  @3228/3207/3193):** invertibility-gated FUTURE work. Route in the blueprint + `analogies/invertible.md`.
  No consumer (`GCommSemiring` assembly unbuilt) → not chased until the assoc chain lands AND a
  `GCommSemiring` consumer is built.
- **RelativeTensorCoequalizer coverage debt (~15 helpers, L302–445):** PROVEN out-of-cone; lack `\lean{}`
  blocks. Deferred to a dedicated post-assoc blueprint-writer round.
- **χ-blocked (`QuotScheme.lean`, 4 sorries):** `hilbertPolynomial` (χ-semantic), `QuotFunctor`,
  `Grassmannian` functor. Need a higher-cohomology engine this i=0 leg lacks; filled from the cohomology
  leg at merge. Genuine gap; not blind-formalizable.
- **`RelativeSpec.lean`:** Route-A sibling chapter, no phase in this leg. Out of scope.
- **Out-of-cone debt:** weak `Scheme.Grassmannian.representable` skeleton; goal does not rely on it.

## Blueprint health (non-gating, deferred to merge-back)

iter-018: enriched the B6 `lem:tensorPowAdd_assoc` proof sketch to the ACCURATE braided-coherence argument
(was "pure pentagon / Mac Lane" — wrong: the def threads `tensorBraiding`; added `lem:tensorBraiding_eq` to
`\uses`) and corrected the "line bundle" over-restriction to "arbitrary L". gate12 (iter-012) PASS otherwise
holds; lvbc iter-017 reported 0 must-fix on the active cone. blueprint-reviewer skipped (see iter sidecar —
the only chapter edit is a prose enrichment derived from the prover's iter-017 VERIFIED base-case techniques,
not speculative). Dangling refs remain in DEFERRED chapters (`Cohomology_FlatBaseChange.tex`, `QuotScheme.tex`,
`GlueDescent.tex`, `RelativeSpec.tex`) + the in-file `lem:relativeTensor_as_coequalizer` ref — extraction /
out-of-cone artifacts, resolve at merge-back.

## Standing notes

- **Prover model:** `opus`.
- **Cold-build validation:** `lake build AlgebraicJacobian.Picard.SectionGradedRing` (LSP hides
  `(kernel) deterministic timeout`); do NOT add `maxHeartbeats 1e6`. `maxRecDepth` OK for stack depth.
- **No LLM API key in env** — use blueprint + Mathlib search + the analogist subagent.
- **Nothing is protected** — `archon-protected.yaml` has no active entries; the prover may add new
  `private` helpers + re-sign unprotected SNAP decls freely.
- **Merge-back discipline:** the iter-007 monoidal-localization pivot DIVERGES from the sibling by
  design. Never add `\leanok` by hand.
