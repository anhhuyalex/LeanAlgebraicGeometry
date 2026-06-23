# Pending Tasks
<!-- Current open-task set, last-known state only. Per-attempt detail → iter sidecars. -->

## Seed 1 — `pullbackTensorIsoOfLocallyTrivial` (D4′) — `TensorObjSubstrate.lean` — DONE iter-042 → see task_done.md
DELIVERED: root GREEN (`lake build` EXIT 0, 8321 jobs), sorry-free. K1 `hδ` via `isIso_oplaxδ_of_conj` ←
`pushforward_mu_appIso_collapse` (δ-conjugation on `deltaConjOfMuComparison`), SUPERSEDING the phantom
`pullbackTensorMap_presheafDelta_eq`/`pullbackTensorComparison`. K1 witness PUBLIC (L4770). iters 039–041
"delivered" were LSP stale-green — `lake build` is the only authority. Blueprint reconciled iter-043.

## ROOT gap-fill — `conjugateEquiv_restrictFunctorComp_inv` (`TensorObjSubstrate.lean`) — DONE iter-048 → see task_done.md
CLOSED public, axiom-clean (lake EXIT 0). iter-046 "irreducible" verdict overturned (abstract
`leftAdjointCompIso`-on-`pushforwardComp` route; NEVER `ext` the conjugate-headed goal). Now consumable by terminal.

## Terminal — `exists_tensorObj_inverse` (`lem:tensorobj_inverse_invertible`) — `TensorObjInverse.lean` — GREEN-mod-sorry (4); ENGINE DONE, S2 + S4b-body + S4b-inner CLOSED, bridge-3 chain active (iter-057)
STATE: **B1/B2 ENGINE LAYER COMPLETE** (B2 iter-050; B1-crux iter-053). **S2 CLOSED iter-054.** **S4b BODY
closed iter-055; S4b INNER SEAM closed iter-056** — the whole S4b square now rides on ONE lemma, bridge 3
`pullbackTensorMap_left_unitality` (L1211). 4 sorries: S3 (L1099), S4a (L1123), bridge 3 (L1211),
`trivialisation_restrict_compat` (L1432).
- **iter-057 PRIMARY = close S4b via the effort-broken bridge-3 chain (Cone A).** bridge 3 effort-broken
  this iter into a 3-link chain (HARD GATE PASS): L1 `pullbackValIso_naturality_leftUnitor` (RHS
  reconciliation), L2 `tensorObj_left_unitor_pullback_eq_sheafify` (λ-leg), L3
  `pullbackUnitIso_whisker_eq_sheafify_eta_whisker` (η-whisker, hardest; pre-specced 3a/3b re-break in
  `logs/iter-057/effort-breaker-bridge3-report.md`). Fine-grained prover: prove L1→L2→L3→target. Bridges
  1/2 (`pullbackUnitIso_eq_sheafify_eta` = `pullbackEtaUnitSquare.symm`; `pullbackTensorMap_eq_sheafify_delta`
  = rfl) already CLOSED iter-056. Template `isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta` (root
  :1315/:1346). Reversal: L3 stalls → re-break to 3a/3b; whole pass stalls → cross-domain analogist on
  the sheaf-transport seam.
- **S4c** `trivialisation_uIota_restrict_compat` — CLOSED iter-041, sorry-free (transitively on B2).
- **S3** (L1099) / **S4a** (L1123) — DUAL FLANK = **Cone B**, NOW PROVER-READY (effort-broken + HARD-GATE
  cleared iter-057), QUEUED iter-058. Crux `presheafDual_pullback_restrict_natural` decomposed into 4
  atomic sub-lemmas (θ-as-eval / dualIsoOfIso-as-precomp / eval-restrict base-change atom / sectionwise
  form), mirroring proven `presheafDualUnitIso_naturality`. SEPARATE internal-hom construction (not the
  tensor δ-seam; shares only the outer counit seam in S3/S4a). Deferred this iter ONLY for same-file
  concurrency (no file split mid-proof). NOT monoidality; NOT the abandoned `pullbackDualMap`.
- **`trivialisation_restrict_compat`** (L1432) — telescope of the 5 squares; only after they close. DEAD probes:
  `restrictFunctorComp.hom.naturality φ` (morphism, iter-040); subst/rcases on `hVU:V≤U`, `simp[restrictIsoUnitOfLE]`,
  `congr 1`/`Iso.eq_inv_comp`/`Hom.ext`. `erw`/term-`exact` not `rw` ([[tensorobjinverse-red-at-source]]).
- **Cocycle `exists_tensorObj_inverse`** — CLOSED modulo `trivialisation_restrict_compat` (iter-038, green). Full
  iso-algebra reduction in-code; `have ht` uses term-mode `exact` (every `rw`/`simp` of a category lemma misses on
  the defeq-not-syntactic SheafOfModules `≫`). NEVER sheafify-the-eval (d.2 dead-end). DEAD: `rfl`, `simp
  [tensorObjIsoOfIso_trans/refl, dualIsoOfIso_trans/refl]` (iso-level, goal is `.val.app`-section level).
- **Residual B** — CLOSED iter-026. Recipe `rem:dual_discharges_inverse`. Non-critical branch (seed-3
  `map_add` rides seed-1→K1).

## Scaffold target — seed 3 `PicSharp.addCommGroup_via_tensorObj` (`RelPicFunctor.lean`)
STATE: not in Lean. Gated on seed-1 (map_add ← comparison iso) + `exists_tensorObj_inverse` (group inverse).

## Tracked debt
- Coverage: 5 iter-019 helpers are `private` generic plumbing (no node owed) except
  `sheafificationCompPullback_comp_inv` (pinned `lem:pullback_val_iso_comp_scpb`). Bulk ~99 `lean_aux`
  decls remain; scheduled `Coverage + file-split` phase.
- File-split: `TensorObjSubstrate.lean` >3600 LOC (over 1000-LOC policy) — split scheduled after the
  active seed-1 lane lands (avoid disrupting the warm file).

## Completeness audit (user-requested) — DONE
3-seed cone COMPLETE vs AJC: 108/108 nodes, cone sizes 52/36/32 exact. Diffs = AJC dead-code Lan block
(not ported) + out-of-scope Route-A. Nothing required missing.
