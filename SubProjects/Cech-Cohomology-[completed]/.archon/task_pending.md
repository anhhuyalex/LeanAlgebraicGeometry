# Pending Tasks

## iter-087 status — BUILD GATE only

All 7 kernel sorries are now LSP-clean (0 inline `sorry` tokens, resolved iters 081–085):
1. `pushPull_interLegHom_sections` — term-shrunk via `erw`, proof complete (iter-081).
2. `coreIso_comm` / `coreIso_comm_leg` / `_coface` / `_sum` — MERGE-STUB proofs restored + split
   to CSILegAux (iter-085). All LSP-green.
3. `mapAlternatingCofaceMapComplexIso` naturality — fixed via simp+rfl (iter-081).
4. `cechAugmented_to_acyclicResolutionInput` — restored (iter-081).

**Single remaining gate:** `lake build AlgebraicJacobian.Cohomology.CechToHigherDirectImage`
must succeed (olean confirmation). CSILeg further split (iter-087) into 5 files:
Leg~4.8M, Mid1~5.6M, Mid2~5.6M, Top~8M, Aux~14.4M HB — all under 10-min 46K-HB/s budget.

---

Current open obligations (last-known state). Per-attempt detail lives in iter sidecars.

> **iter-080 status. PROJECT MATHEMATICALLY COMPLETE — 0 inline `sorry` project-wide.**
> The deliverable `AlgebraicGeometry.cech_computes_higherDirectImage` (`CechToHigherDirectImage.lean`)
> is proved (iter-079). The user (iter-080) dropped the old false-as-signed protected sibling + its
> `archon-protected.yaml` entry and renamed the correct theorem to the canonical name; verified sound
> (peer AJC carries the false general signature as a `sorry`, unprotected; general form is FALSE —
> ℙ¹/O(-2), `𝒰={𝟙 X}`). `archon-protected.yaml` is now empty.

## The single remaining gate
- **Full-build + axiom-clean confirmation of the capstone cone.** The heavy cohomology cold-builds
  ~25 min (a `lake build AlgebraicJacobian.Cohomology.CechToHigherDirectImage` was launched iter-080
  plan phase; the deterministic `sync_leanok`/review-build gate also verifies). The user's large
  uncommitted `CechHigherDirectImage.lean` edit (429+/201−) is not yet independently build-verified.
  Both critics (strategy-critic + blueprint-reviewer `finish`, iter-080) named this as the one
  outstanding condition before declaring complete. If green ⟹ advance stage to **polish**.

## Polish items (non-blocking, after build confirmed)
- Reading-order cosmetic: `lem:pushforward_mapHC_cechComplexOnX`, `lem:cechAugmented_to_acyclicResolutionInput`
  appear textually after their consumer in `Cohomology_CechHigherDirectImage.tex` (DAG correct).
- Dormant `lem:tile_section_comparison` has `\leanok` with no `\lean{}` vs its UNFORMALIZED NOTE
  (review-agent's marker domain; not in the goal cone).
- Stale "sorry"-mentioning docstrings: `CechSectionIdentificationLeg.lean:15`, `CechSectionIdentification.lean:20`.
- Dead scaffolding in Leg: `pushPullLegIso`, `pushPull_leg_coherence`.
- `#print axioms cech_computes_higherDirectImage` = kernel only (confirm).

## Dead ends (do NOT retry)
Stalk-at-prime exactness for `X.Modules`; naive affine-basis section-exactness (circular = `Ȟᵖ`);
tilde/standard-cover vanishing as the `cechAugmented_exact` local discharger (wrong cover); span-cover
descent on global sections (circular); open-subscheme `j⁻¹V≅SpecΓ(j⁻¹V)` Ext transport
(restriction-injectives wall); `hacyc` via Serre vanishing on `U∩f⁻¹V` (open not affine — adjoint route
is correct, DONE); the non-augmented section complex is NOT contractible (target the AUGMENTED `D'_aug`);
`lean_run_code`/LSP "rfl" are STALE-`.olean` lies — confirm only with `lake env lean`
([[keystone-tile-reconciliation-not-rfl]]); the `↑R`-Semiring diamond — `change`(defeq) not `rw`/`simp`
([[rR-semiring-diamond-change-workaround]]).
