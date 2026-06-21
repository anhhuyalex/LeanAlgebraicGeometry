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

## Terminal — `exists_tensorObj_inverse` (`lem:tensorobj_inverse_invertible`) — `TensorObjInverse.lean` — GREEN-mod-sorry (6); B1-crux engine iter-051
STATE: **Bridge B2 FULLY CLOSED iter-050** (the 044–049 blocker, gone) — `restrictFunctorIsoPullback_comp_compat`
+ `_hom` helper sorry-free, 6 axiom-clean lemmas (5 per-leg + assembled). Sorry 7→6. The iter-049/050 HARD STOP
(B2 `_hom` survives → refactor) is SATISFIED (`_hom` closed) and does NOT apply to B1-crux. progress-critic
terminal051: **CONVERGING, dispatch=OK**.
Current 6 sorries: B1-crux `H1inv_app_eq_pullbackVal_restrict` (L493), squares S2/S3/S4a/S4b
(L594/L616/L640/L656), `trivialisation_restrict_compat` (L787).
- **iter-051 PRIMARY = B1-crux** `H1inv_app_eq_pullbackVal_restrict` (L493) — the sole "engine" sorry; squares
  ride it + B2. Body reduced (iter-045) to the isolated CRUX unit identity. Route (in-code L466–492; blueprint
  `lem:h1inv_app_eq_pullbackval_restrict`): `rw [pullbackValIso, restrictFunctorIsoPullback]; simp; rw
  [sheafificationCompPullback_eq_leftAdjointUniq]` (root L1511) → `leftAdjointUniq_trans`/`conjugateEquiv_comp`
  coherence + `leftAdjointUniqUnitEta` (root L1531) for the SCPB unit leg. Crosses the presheaf/sheaf
  SHEAFIFICATION BOUNDARY — harder than B2's clean restrict/pullback world. iter-050 conjugate toolkit (c₅,
  reindexCongr, whiskers, LHS-collapse keystone `conjugateEquiv_restrictFunctorIsoPullback_hom`) now available.
  **B1-crux HARD STOP (AUTONOMOUS): if it survives with no advance, effort-break the unit identity AND/OR
  mathlib-analogist cross-domain on "sheafification-unit intertwines presheaf/sheaf adjoint-uniqueness"; NOT user
  escalation, NOT the restrictCompReindex→pullback refactor (wrong target — that addressed B2, done).**
- **S2** (L594) — B1 (body closed) + `pullbackTensorMap_restrict`/`_natural` + B2. **S4b** (L656) — S2+S4c+left-unitor.
- **S4c** `trivialisation_uIota_restrict_compat` — CLOSED iter-041, sorry-free (transitively on B2).
- **S3** (L616) / **S4a** (L640) — dual gap, thin-poset `subsingleton` route (b) UNVERIFIED; if it stalls,
  leave clean-sorry. Route (a) full `pullbackDualMap` cone (~150–250 LOC) deferred.
- **`trivialisation_restrict_compat`** (L787) — telescope of the 5 squares; only after they close. DEAD probes:
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
