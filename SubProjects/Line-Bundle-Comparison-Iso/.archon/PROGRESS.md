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
`lem:pullback_tensor_iso_loctriv` (seed-1, D4′ — **DELIVERED iter-042**),
`lem:dual_isLocallyTrivial` (seed-2, DUAL — DELIVERED),
`thm:rel_pic_addcommgroup_via_tensorobj` (seed-3, consumer; gated on terminal).

## Build state (iter-051 plan turn)

- **Terminal `TensorObjInverse.lean` GREEN-mod-sorry (6).** `lake build` EXIT 0 (iter-050), zero axioms.
  Sorries: L493 (B1-crux `H1inv_app_eq_pullbackVal_restrict`), L594/L616/L640/L656 (squares S2/S3/S4a/S4b),
  L787 (`trivialisation_restrict_compat`).
- **iter-050 outcome: Bridge B2 FULLY CLOSED** (the 044–049 multi-iter blocker, gone). fine-grained landed
  6 new axiom-clean public lemmas (5 atomic per-leg sub-lemmas + assembled `_hom` helper); B2's
  `restrictFunctorIsoPullback_comp_compat` is now sorry-free. Sorry 7→6.
- **progress-critic terminal051: CONVERGING, dispatch=OK** (8→8→7→6; helpers closed-not-accumulated;
  "conjugate telescope" blocker resolved). Proceed with the B1-crux prove lane.
- **iter-049/050 HARD STOP (B2 `_hom` survives → refactor) is SATISFIED** — `_hom` closed iter-050. It does
  NOT apply to B1-crux: B1-crux's blocker is the *sheafification boundary*, a different problem than the
  conjugate-of-comp the `restrictCompReindex`→pullback refactor would address.

## Decision (iter-051) — `prove` lane on B1-crux `H1inv_app_eq_pullbackVal_restrict` (the sole "engine" sorry)

- B2 done ⇒ B1-crux is now the next blocker; the squares ride the B1 keystone body (already sorry-free mod
  this crux) + B2. The conjugate toolkit built iter-050 (c₅, reindexCongr, whiskers, LHS-collapse keystone)
  is now available to it. B1-crux has had NO dedicated prove pass yet (iter-050 spent its budget closing B2,
  left a clean documented sorry), so this is `prove`, not fine-grained — no churn signal to fine-grain on.
- **B1-crux reversal/HARD STOP (NEW, AUTONOMOUS — distinct from the satisfied B2 one):** if B1-crux is STILL
  sorry after this round with no structural advance, do NOT re-dispatch the same recipe. Next iter pivot
  autonomously to (a) `effort-break` the crux unit-coherence identity into named sub-claims at the
  sheafification-unit seam, AND/OR (b) `mathlib-analogist` (cross-domain) on the structural shape
  "sheafification unit intertwines presheaf vs sheaf left-adjoint-uniqueness comparisons" — NOT user
  escalation (standing AUTONOMOUS directive 2026-05-31), NOT the `restrictCompReindex`→pullback refactor
  (wrong target — that addresses B2's conjugate-of-comp, already done).

## Current Objectives

1. **`AlgebraicJacobian/Picard/TensorObjInverse.lean`** — **TERMINAL lane, SOLO. Close the B1-crux engine
   sorry; then drive the dependent squares as budget permits.**
   Blueprint: `chapters/Picard_TensorObjSubstrate.tex` (consolidated; `% archon:covers …/TensorObjInverse.lean`).
   - **PRIMARY — B1-crux `H1inv_app_eq_pullbackVal_restrict` (sorry L493).** The body is already reduced
     (verified iter-045) to the isolated CRUX unit identity: after
     `apply (pullbackPushforwardAdjunction …).homEquiv … |>.injective; rw [leftAdjointUniq_inv_app];`
     `simp only [homEquiv_unit]; refine Eq.trans (unit_leftAdjointUniq_hom_app _ hadj M.val) ?_`, the
     remaining goal is `hadj.unit.app M.val = pullbackPPAdj.unit.app M.val ≫ pushforward.map (η ≫ …)`.
     **Documented route (in-code L466–492; blueprint `lem:h1inv_app_eq_pullbackval_restrict` L7132):**
     `rw [pullbackValIso, restrictFunctorIsoPullback]; simp only [Iso.trans_hom, Iso.symm_hom,`
     `Functor.mapIso_hom, Functor.map_comp]; rw [sheafificationCompPullback_eq_leftAdjointUniq]`
     (`sheafificationCompPullback_eq_leftAdjointUniq` [verified, root L1511]); then a
     `leftAdjointUniq_trans`/`conjugateEquiv_comp` coherence threading the SCPB unit leg via
     `leftAdjointUniqUnitEta` [verified, root L1531]. The new iter-050 conjugate lemmas
     (`conjugateEquiv_pullbackComp_hom`, `conjugateEquiv_reindexCongr`, the whiskers, the LHS-collapse
     `conjugateEquiv_restrictFunctorIsoPullback_hom`) are now available. This crosses the presheaf/sheaf
     sheafification boundary (`pushforwardPushforwardAdj` vs `pullbackPushforwardAdjunction` vs
     `sheafificationAdjunction`) — genuinely harder than B2's clean restrict/pullback world. **Attempt the
     body; leave attempt-backed partial progress (a compiling sub-step / helper) if genuinely stuck —
     NOT a fresh untouched sorry.**
   - **SECONDARY (only if B1-crux closes, then as budget permits):** S2 `tensorObj_restrict_iso_restrict_compat`
     (L594) and S4b `tensorObj_unit_iso_restrict_compat` (L656) — ride B1 (body now fully closed) +
     `pullbackTensorMap_restrict`/`_natural` (sorry-free D3′ cone) + B2 (done) + left-unitor. These are
     deep immersion-naturality 4-step chart-chases; one at a time.
   - **DEFER unless trivial:** S3 (L616) / S4a (L640) — dual analogue, thin-poset `subsingleton` route (b)
     UNVERIFIED; if it stalls leave a clean sorry, do NOT burn the round. `trivialisation_restrict_compat`
     (L787) — telescope of all 5 squares; only after they close.
   - **Cleanup (cheap, lean-auditor iter-050 major/minor — do while warm):** L193 section header drop the
     stale "(iter-028 stubs)" qualifier (all decls under it proved); L519 docstring qualify "sorry-free" →
     "sorry-free at this level" (transitively rides the B1-crux sorry).
   - **AUTHORITATIVE = `lake build AlgebraicJacobian.Picard.TensorObjInverse` EXIT 0, NOT LSP** (LSP gave
     stale-green for 3 iters — memory `lhs-tmul-telescope-iter037`). DEAD probes (do NOT retry):
     `restrictFunctorComp.hom.naturality φ`; `subst`/`rcases` on `hVU`; `simp[restrictIsoUnitOfLE]`;
     `congr 1`/`Iso.eq_inv_comp`/`Hom.ext`; **NEVER `ext` on a conjugate-headed goal** (whnf-bomb). Across
     the SheafOfModules `≫` defeq-not-syntactic seam use term-mode `exact` of a generic single-`[Category C]`
     lemma, NOT `rw`/`simp` of a category lemma (always misses).
   [prover-mode: prove]

## Standing deferrals

- **Consumer seed-3 `PicSharp.addCommGroup_via_tensorObj` (`RelPicFunctor.lean`)** — not in Lean; gated on
  the terminal close (seed-1 done). `map_add` ← seed-1 comparison iso; `map_zero` ← `pullbackUnitIso`;
  inverse ← `exists_tensorObj_inverse`. Blueprint `Picard_RelPicFunctor.tex` has the 2 forward `\lean{}`
  targets (non-gating "soon" — formalize when unblocked).
- **Coverage / file-split debt:** ~105 isolated `lean_aux` nodes (mostly `private` generic plumbing);
  `TensorObjSubstrate.lean` (>4800 LOC) split scheduled after the terminal lands. iter-051 cleared the 2
  freshly-flagged B2-block items (added `lem:conjugateequiv_restrictfunctorisopullback_hom` block; removed
  the dangling `pushforwardComp_reindex_telescope` `\lean{}` → exposition). Bulk deferred to the phase.
- **AJC Lan-decomposition block** — NOT ported (dead code; not in any seed cone).
- **Extraction note:** module names / paths / labels unchanged from the parent for clean merge-back.
