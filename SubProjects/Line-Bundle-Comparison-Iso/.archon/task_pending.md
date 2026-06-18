# Pending Tasks
<!-- Current open-task set, last-known state only. Per-attempt detail → iter sidecars. -->

## Seed 1 — `pullbackTensorIsoOfLocallyTrivial` (D4′ chart-chase) — `TensorObjSubstrate.lean` — ACTIVE
STATE: body CLOSED iter-020 (decl L4238, chart-chase sorry-free). Residual = ONE brick **K1**
`pullbackTensorMap_isIso_of_isOpenImmersion` (L4139, sole open `sorry` L4172, transitive sorryAx to
seed-1). The chart-chase (cover `{f⁻¹W}` + `isIso_of_isIso_restrict` + two `pullbackTensorMap_restrict`
splits + K2 `pullbackTensorMap_isIso_of_base_unit`) is fully assembled; it reduces D4′ to K1 at the two
open immersions `(f⁻¹W).ι`, `W.ι`.
- **K1** = `IsIso (pullbackTensorMap f M N)` for `[IsOpenImmersion f]`, ARBITRARY M,N. iter-020 tried
  `Functor.Monoidal.transport` (functor-level) → FAILED on the monoidal-carrier diamond
  (`MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj)` not synthesizable). REDIRECT (this iter):
  go through the designed entry `isIso_pullbackTensorMap_of_isIso_sheafifyDelta` → reduce to presheaf
  `IsIso (δ (pullback φ') M.val N.val)`, closed IN-PROOF mirroring the CLOSED `tensorObj_restrict_iso`
  (H1 = `pushforward β ≅ pullback φ` via `leftAdjointUniq`; H2 = `restrictScalarsMonoidalOfBijective`)
  + the adjunction-mate compatibility (`Adjunction.IsMonoidal`, cf. `presheafUnit_comp_map_eta` which
  uses `Adjunction.unit_app_unit_comp_map_η`). Do NOT retry functor-level transport.
- Pin: `AlgebraicGeometry.Scheme.Modules.pullbackTensorIsoOfLocallyTrivial`. Blueprint K1 node added
  this iter (`lem:pullback_tensor_map_isiso_open_immersion`).
- Reference: Stacks `lemma-tensor-product-pullback` (pullback strong-monoidal) — `references/stacks-modules.tex`.

## Deferred terminal — `exists_tensorObj_inverse` (`lem:tensorobj_inverse_invertible`)
STATE: the project's SOLE bare `sorry` (TensorObjSubstrate.lean:730). Import-cycle-gated: needs
`dual_isLocallyTrivial` (DualInverse.lean, which imports TensorObjSubstrate) → cannot close in
TensorObjSubstrate.lean. RESOLUTION (next phase, planned in STRATEGY): refactor-MOVE the decl to a file
downstream of DualInverse where `dual_isLocallyTrivial` is visible, repoint RelPicFunctor's import
(its `neg`/`neg_add_cancel` is the only consumer), then close the gluing proof (bridge A
`homOfLocalCompat` + B `isIso_of_isIso_restrict` [done] + C `dual_isLocallyTrivial` [done]).

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
