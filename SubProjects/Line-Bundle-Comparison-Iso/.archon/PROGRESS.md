# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

**Zero inline `sorry` in the dependency cone of the three seed declarations + kernel-only
axioms**, for the **Line-Bundle Comparison Iso** subproject (A.1.c.sub). Seeds:
`lem:pullback_tensor_iso_loctriv` (seed-1, D4′ — DELIVERED iter-042),
`lem:dual_isLocallyTrivial` (seed-2, DUAL — DELIVERED),
`thm:rel_pic_addcommgroup_via_tensorobj` (seed-3, consumer; gated on terminal).

## Build state (iter-057 plan turn)

- **Root `TensorObjSubstrate.lean` GREEN, sorry-free, axiom-clean.** Includes the ALREADY-PROVEN
  oplax instance `presheafPullbackOplaxMonoidal` (`:1115`, via Mathlib `leftAdjointOplaxMonoidal`),
  whose `Functor.OplaxMonoidal.left_unitality_hom` is free and already consumed at `:1346`.
- **Terminal `TensorObjInverse.lean` GREEN-mod-sorry (4).** Sorries: S3 `dual_restrict_iso_restrict_compat`
  (L1099), S4a `dual_unit_iso_restrict_compat` (L1123), bridge 3 `pullbackTensorMap_left_unitality`
  (L1211), `trivialisation_restrict_compat` (L1432). S2 + S4b body + S4b inner seam are sorry-free
  (S4b inner seam closed iter-056; the whole S4b square now rides on bridge 3 alone).

## iter-057 — effort-break the tensor-flank crux + prove its chain; Cone B made prover-ready

- **progress-critic (iter-057): CHURNING** (mechanically: PARTIAL×3 in the 5-iter window, sorry flat
  3 iters). Critic's read: the churn is **structural fine-graining**, NOT accumulation-without-payoff —
  each PARTIAL proved a sub-goal and isolated the residual one level deeper, identical to the B1/B2
  plateau immediately before closure. Corrective = the effort-break, already done this iter. Critic
  also recommended (acted on): prep Cone B's blueprint in parallel (read-only blueprint, no file-split
  needed) to remove the iter-058 sequential bottleneck + disambiguate the dual blocker.
- **effort-break (Cone A / bridge 3, done this iter):** `lem:pullback_tensor_map_left_unitality`
  decomposed into a 3-link `\uses` chain (max single-node effort 1803→1226). New sub-lemmas:
  `lem:pullback_val_iso_naturality_left_unitor` (L1, RHS reconciliation),
  `lem:tensorobj_left_unitor_pullback_eq_sheafify` (L2, λ-leg),
  `lem:pullback_unit_iso_whisker_eq_sheafify_eta_whisker` (L3, η-whisker leg, hardest). Target proof
  is now a short assembly. Template oracle: `isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta`.
- **effort-break (Cone B / dual flank, done this iter):** `lem:presheafdual_pullback_restrict_natural`
  decomposed into 4 atomic sub-lemmas (θ-as-eval, dualIsoOfIso-as-precomp, the eval/restrict
  base-change atom, its sectionwise form), mirroring the proven `presheafDualUnitIso_naturality`.
  **Disambiguation result:** the dual flank uses a **separate** internal-hom construction (NOT the
  tensor δ-seam); it shares only the outer counit seam, which lives in the consumers S3/S4a.
- **Blueprint HARD GATE: PASS** (blueprint-reviewer iter057, whole-blueprint). Both Cone A and Cone B
  sub-routes clear `complete:true / correct:true`, 0 must-fix. "Cone A — prover may be dispatched now."
  Soft (no gate impact): `lem:pullback_compatible_with_tensorobj` `\lean` hint points at a non-existent
  deferred decl (repoint later); Cone A sub-1 has one unused `\uses` over-edge.

## Decision (iter-057) — SOLO fine-grained prove lane on the Cone A / bridge-3 chain; Cone B queued

- **Chosen:** one prover on `TensorObjInverse.lean`, **fine-grained mode**, formalizing the freshly
  decomposed bridge-3 chain (L1 → L2 → L3 → target) and thereby closing S4b ENTIRELY (sorry 4→3 =
  genuine net elimination, breaking the CHURNING signal). Bridge 3 was a PARTIAL with no progress on
  the reconciliation, and the blueprint is now atomic — exactly when fine-grained applies.
- **Cone B NOT a second lane this iter.** It is in the SAME Lean file → two prover lanes cannot run
  concurrently without a file split (deferred until the terminal lands, to protect the warm proof
  file). Loading it now is the "load more lanes" anti-pattern the CHURNING verdict warns against. Its
  blueprint is now prover-ready (gate cleared), so iter-058 dispatches it with no blueprint round.
- **Reversal signal:** if the fine-grained pass closes L1/L2 but stalls on L3
  (`pullback_unit_iso_whisker_eq_sheafify_eta_whisker`, the largest residual, effort 1226), re-dispatch
  the effort-breaker to split L3 into 3a (bridge-1 substitution + whisker expansion) and 3b (left-factor
  device cancellation against the wrapper) — the split is already worked out in the effort-breaker
  report. If the whole pass stalls with no new closed sub-lemma → cross-domain mathlib-analogist on
  the sheaf-transport seam (the move that unblocked the B1-crux).

## Current Objectives

1. **`AlgebraicJacobian/Picard/TensorObjInverse.lean`** — **TERMINAL lane, SOLO. Close S4b: formalize
   and prove the freshly effort-broken Cone A / bridge-3 chain.**
   Blueprint: `chapters/Picard_TensorObjSubstrate.tex` (consolidated; `% archon:covers …/TensorObjInverse.lean`).
   The HARD GATE cleared this iter; the blueprint proofs for the chain are atomic and prover-ready.
   - **Formalize + prove these three NEW sub-lemmas IN THIS FILE** (namespace
     `AlgebraicGeometry.Scheme.Modules`; suggested order L1 → L2 → L3):
     1. `pullbackValIso_naturality_leftUnitor` (`lem:pullback_val_iso_naturality_left_unitor`) — RHS
        reconciliation: `(pbv_{𝒪⊗M}).inv ≫ f^*(tensorObj_left_unitor M).hom = a_Y.map (F.map λ_{M.val}) ≫ (pbv_M).inv`.
        Naturality of `pullbackValIso f` against the sheaf morphism `(tensorObj_left_unitor M).hom`. Cleanest.
     2. `tensorObj_left_unitor_pullback_eq_sheafify` (`lem:tensorobj_left_unitor_pullback_eq_sheafify`) —
        λ-leg: `β.hom ≫ a_Y.map(pbv⊗pbv) ≫ (tensorObj_left_unitor (f^*M)).hom = a_Y.map λ_{F.obj M.val} ≫ (pbv_M).hom`
        (identifies the sheaf left unitor at `f^*M` with the sheafified presheaf unitor mod the bridge-2
        right wrapper). Uses counit + unitor naturality; reuse `tensorObj_unit_iso_eq_left_unitor`,
        `tensorObj_left_unitor_naturality` already in-file.
     3. `pullbackUnitIso_whisker_eq_sheafify_eta_whisker` (`lem:pullback_unit_iso_whisker_eq_sheafify_eta_whisker`) —
        η-whisker leg (hardest): `(tensorObjIsoOfIso (pullbackUnitIso f) 𝟙).hom ≫ (bridge-2 right wrapper)
        ∼ a_Y.map(η F ▷ F.obj M.val)`, mod `pullbackValIso`/`sheafifyUnitIso`/`β`. Consumes bridge 1
        `pullbackUnitIso_eq_sheafify_eta`. **If it churns, STOP and report — the planner re-breaks it to
        3a/3b** (split already specced in `.archon/logs/iter-057/effort-breaker-bridge3-report.md`); do
        NOT grind it whole.
   - **Then close** `pullbackTensorMap_left_unitality` (L1211, bridge 3, currently the sorry): rewritten
     proof = sheafify `hlu := Functor.OplaxMonoidal.left_unitality_hom (pullback φ') M.val`, split by
     functoriality into 3 legs + RHS, δ-leg by `pullbackTensorMap_eq_sheafify_delta` (bridge 2,
     already applied), η-leg by sub-lemma 3, λ-leg by sub-lemma 2, RHS by sub-lemma 1, cancel interior
     reconciliation pairs. **This CLOSES S4b entirely** — the inner seam
     `tensorObj_unit_iso_restrict_compat_inner` and the S4b body both already consume bridge 3
     sorry-free (iter-056), so closing bridge 3 drops the project sorry 4→3.
   - **Reuse:** the B1 seam toolkit (`pullbackValIso`, `sheafificationCompPullback`, `sheafifyUnitIso`,
     `sheafifyTensorUnitIso`, `toRingCatSheafHom` reconcile, counit naturality) + the
     `isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta` template (root :1315/:1346) which already
     sheafifies `left_unitality_hom F (𝟙_)` and handles the δ/η-whisker/λ legs for the UNIT PAIR — the
     three sub-lemmas are that handling generalized from `𝟙_` to `M.val`, kept as equalities.
   - **Hygiene (opportunistic, same file):** strip any stale "still open" labels for `hKEY` /
     `sheafPullbackUnit_forget_eq` (both PROVED).
   - **Attempt to completion.** If stuck, leave a compiling partial + name which sub-lemma is unclosed
     — NOT a fresh untouched sorry.
   - **AUTHORITATIVE = `lake build AlgebraicJacobian.Picard.TensorObjInverse` EXIT 0, NOT LSP.** Across
     the `SheafOfModules ≫` defeq-not-syntactic seam apply category lemmas TERM-MODE
     (`Eq.trans`/`congrArg`/`exact`); `rw [Category.assoc]`/`rw [Functor.map_comp]` MISS,
     `erw [Category.assoc]` whnf-bombs. `tensorObj_left_unitor_naturality` needs **`erw`** (restrict vs
     `restrictFunctor.obj` defeq). DEAD probes (do NOT retry): `restrictFunctorComp.hom.naturality`;
     subst/rcases on `hVU:V≤U`; `simp[restrictIsoUnitOfLE]`; `congr 1`/`Iso.eq_inv_comp`/`Hom.ext`;
     NEVER `ext` a conjugate goal.
   [prover-mode: fine-grained]

## Deferred this iter (NOT prover objectives)

- **S3 `dual_restrict_iso_restrict_compat` (L1099) + S4a `dual_unit_iso_restrict_compat` (L1123) =
  Cone B — NOW PROVER-READY (effort-broken + HARD-GATE cleared this iter), QUEUED iter-058.** Crux
  `lem:presheafdual_pullback_restrict_natural` decomposed into 4 atomic sub-lemmas (θ-as-eval,
  dualIsoOfIso-as-precomp, eval/restrict base-change atom, sectionwise form), mirroring the proven
  `presheafDualUnitIso_naturality`. Uses a SEPARATE internal-hom construction (not the tensor δ-seam;
  shares only the outer counit seam in S3/S4a). Deferred this iter ONLY because it is in the same Lean
  file as the active bridge-3 lane (no concurrent provers without a file split). NOT monoidality (no
  Mathlib dual-preservation API matching `f^*`); do NOT build `Functor.Monoidal` (globally false); do
  NOT reintroduce `pullbackDualMap`. iter-058 dispatches a fine-grained prover on this chain.
- **`trivialisation_restrict_compat` (L1432)** — telescope of all 5 squares; gated transitively.
- **Consumer seed-3 `PicSharp.addCommGroup_via_tensorObj` (`RelPicFunctor.lean`)** — not in Lean;
  gated on the terminal close. `map_add` ← seed-1; `map_zero` ← `pullbackUnitIso`; inverse ←
  `exists_tensorObj_inverse`.
- **Coverage / file-split debt:** ~115 isolated `lean_aux` nodes; `TensorObjSubstrate.lean` (>4800 LOC)
  split — scheduled cleanup phase after the terminal lands.
- **Extraction note:** module names / paths / labels unchanged from the parent for clean merge-back.
