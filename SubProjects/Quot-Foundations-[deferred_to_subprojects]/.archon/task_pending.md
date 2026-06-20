# Pending Tasks

Current open-task set (last-known state). Per-lane detail in `iter/iter-081/{plan,objectives}.md` + PROGRESS.md.

## Active prover lanes (iter-081)

- **GrassmannianQuot.lean** — 1 sorry, `tautologicalQuotient_epi` (L2470). NOW UNBLOCKED (keystone
  `isIso_glueRestrictionHom` reached 0-sorry iter-080). Epi via joint reflection across the chart cover.
  Closing it → GrassmannianQuot 0-sorry, GR-quot route complete (`represents` already DONE iter-080).
- **SectionGradedRing.lean** — 9 scaffolded SNAP stubs (L1843–1901). Fill bricks (`sectionsCast`,
  `gradedMonoid_eq_of_cast`, GMul/GOne, 4 coherence Eqs = `sectionMul_coherent`) then build the
  `GMonoid`/`GSemiring`/`GCommSemiring`/`Gmodule` assembly instances (TensorPower.Basic idiom).
  Recipe `analogies/snap-gcomm.md` + in-file handoff L1807–1830.
- **FlatBaseChangeGlobal.lean** — 1 sorry, `baseChangeGammaPullbackEquiv` (L274). Stub landed iter-081
  from the analogist-verified sig. Proof per blueprint `thm:fbcb_global_direct` (start at
  `baseChangeGammaEquiv`; transport RHS via `gammaTopEquivEqLocus` on `F'`). RHS `B`-module =
  `restrictScalars` along `pullbackGroundRingAlg B`. Design `analogies/fbcb-pullback-equiv-sig.md`.

## Queued — NEXT iters

- **FBC-B reduction lemma** `flatBaseChange_isIso_iff_gammaTensorComparison` — left as TODO iter-081;
  needs a follow-up analogist pass (abstract pullback-square vs direct-`B` parametrization of
  `pushforwardBaseChangeMap`), then scaffold+prove.
- **FBC named-leg discharge + cleanup.** Move/fill `affineBaseChange_pushforward_iso` (FlatBaseChange.lean
  L2566) + `flatBaseChange_pushforward_isIso` (L2606) from `baseChangeGammaPullbackEquiv` (signatures
  movable), then delete the dead `base_change_mate_*` apparatus (`_legs_conj`@1802, `_gstar_transpose`@2291
  — 4 off-path sorries).
- **RelativeSpec `RepresentableBy` upgrade** (own lane): reference-retrieve Q4 tags 01LM/01LP/01LT FIRST,
  then upgrade `thm:relative_spec_univ` from `IsAffineHom`. Independent of GR-quot/SNAP.
- **QUOT-repr core** (after SNAP-S0 + RelativeSpec): `grassmannian_scheme` + `thm:grassmannian_representable`
  via rank-d locally-free quotients — χ-INDEPENDENT core only (Q1). χ Hilbert-poly / Quot-functor are OUT
  (sibling cohomology leg). QuotScheme.lean's 8 sorries are gated on this + are NOT a current lane.

## Blueprint debt (non-blocking)

- `Picard_QuotScheme.tex` `\lean{Grassmannian.representable}` UNDER-DELIVERS — strengthen or split before
  the QUOT-repr core lane.
- `Cohomology_FlatBaseChange.tex`: repoint `thm:flat_base_change_pushforward` `\uses{}` from the MV-route
  helpers to the DIRECT route once `baseChangeGammaPullbackEquiv` lands; mark/prune the 3 MV-route legacy
  helpers.
- Stale Lean docstring on `ztensor_whisker_localIso` (~L1397, dead stalk route) — fix when a prover is
  next in SectionGradedRing.lean.

## Off critical path

- **FBC mate keystone** — ABANDONED. Do NOT re-attempt `_legs_conj`/`_gstar_transpose` (cleanup-delete).
- **`def:hilbert_polynomial` / `def:quot_functor`** — χ-semantic, OUT of this leg (sibling cohomology leg).
