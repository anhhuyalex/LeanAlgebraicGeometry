# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

> ## ⚠ REOPENED 2026-06-18 — `lake build` FAILS; "PROVED iter-079" was LSP-green, not kernel-green
>
> A merge audit (into `Algebraic-Jacobian-Challenge`) found this project's `lake build` has
> **never produced oleans** for the `CechSectionIdentificationLeg → … → CechToHigherDirectImage`
> chain. The iter-079 "PROVED, 0 sorries" rested on `lean-lsp-mcp` diagnostics, which are weaker
> than the kernel. The capstone `cech_computes_higherDirectImage` is **NOT kernel-verified**.
> 7 declarations are now `sorry`-ed (proofs preserved in `MERGE-STUB-PROOF`/`MERGE NOTE`
> comments) so the project `lake build`s green; **prover is re-opened to fix them for real.**
> Stage stays **prover** (NOT polish). Worklist in `task_pending.md`; directives in `USER_HINTS.md`.

**Zero inline `sorry` project-wide; kernel-only axioms, 0 project axioms.** The deliverable is
`AlgebraicGeometry.cech_computes_higherDirectImage` (`CechToHigherDirectImage.lean`) — the separated
relative case of Stacks 02KE, with `[QuasiCompact f] [IsSeparated f] [X.IsSeparated] [S.IsSeparated]`,
`h𝒰 : ∀ i, IsAffine (𝒰.X i)`, and the per-intersection `hres` injective-resolutions family.
**PROVED iter-079, 0 sorries.** Full framing in STRATEGY.md.

## Iter-080 context — frozen decl resolved by the user; project sorry-free

The user dropped the old false-as-signed protected `cech_computes_higherDirectImage` (general
`X.OpenCover`, only `[IsSeparated f]`) and its `archon-protected.yaml` entry, and the correct sibling
was renamed to the canonical `cech_computes_higherDirectImage`. **Verified the drop is sound:** peer
`Algebraic-Jacobian-Challenge` carries that same general signature as a `sorry` (needs absent Mathlib
spectral sequences) and does **not** protect it; the general statement is FALSE (counterexample
`X=ℙ¹, 𝒰={𝟙 X}, F=O(-2)`: `Hⁱ(Č•)=0` but `R¹f_*F≠0`). **Project-wide inline `sorry` count = 0.**

This iter (plan phase):
- Reconciled the blueprint: merged the two near-duplicate comparison blocks into the single
  `lem:cech_computes_cohomology` (pinned to the live `cech_computes_higherDirectImage`) carrying the
  precise hypotheses + scope note; deleted the orphaned `..._affineCover` block. blueprint-reviewer
  `finish` = PASS (statement matches the live signature; no broken refs; clean doctor).
- strategy-critic `finish` = SOUND (deliverable TRUE + faithful to the separated relative case of 02KE;
  ℙ¹/O(-2) counterexample correct; dropping the false decl is a soundness necessity).
- Updated STRATEGY/TO_USER to the new reality.

## Current Objectives

**iter-094 — REDISPATCH of the iter-093 LegTop kernel-fix (iter-093 was dropped by the no-op trap, never ran).**
iter-093's objective was DROPPED by plan-validate (`failed_all_noop`): a 0-sorry file is treated as a
no-op UNLESS its heading line carries a scaffold keyword. The kernel error is unchanged and confirmed
in `logs/iter-092/chain-build.log`:
- `pushPull_interLegHom_sections` (line ~301): `(kernel) deterministic timeout` — the proof TERM is
  too large for the kernel under `maxHeartbeats 1600000` (prior `have`/`thin_resid5`-extraction shrink
  insufficient).
- `coreIso_comm_leg` (line ~392): `unknown constant 'pushPull_interLegHom_sections'` — pure CASCADE of
  the timeout (the failed lemma never enters the environment). Fixing #1 fixes #2.

This is the concrete blocker behind the REOPENED-2026-06-18 note: the capstone is NOT kernel-verified
because this chain link does not kernel-compile. The math is correct (blueprint PASS iter-080); this is
a kernel term-SIZE problem. Fix = DECOMPOSE (the kernel checks each decl independently and treats
cross-references as opaque; splitting an over-budget term into under-budget pieces fixes the timeout AND
keeps the file fast — directive-aligned). Oleans are present through Mid2, so the verification build only
recompiles LegTop (fast).

### 1. **CechSectionIdentificationLegTop.lean** — scaffold a new `private lemma` to split the kernel-timeout term in `pushPull_interLegHom_sections` [prover-mode: prove]
Make `lake build AlgebraicJacobian.Cohomology.CechSectionIdentificationLegTop` succeed
(kernel-clean + axiom-clean). **This file has NO `sorry` but FAILS the kernel** — the task is to
RESTRUCTURE `pushPull_interLegHom_sections` so every declaration's term checks under the existing
1600000 budget. Recipe: extract the heavy post-`congr 1` residual (the part NOT already covered by the
existing `thin_resid5` helper) into a NEW `private lemma`; the main lemma then composes the
`pls_eq`/`hstep` prefix with that opaque helper. If the first split still times out, split RECURSIVELY
(the seam is a real mathematical/structural boundary, not arbitrary). Mark every new helper `private`.
Preserve the public signatures of `pushPull_interLegHom_sections` and `coreIso_comm_leg` verbatim
(consumed by CSI/Aux). VERIFY with `lake build <module>` — the LSP is NOT authoritative for kernel
timeouts; then confirm `#print axioms coreIso_comm_leg` is sorry-free (kernel axioms only).
**Fallback (guaranteed unblock if decomposition can't bound the term this iter):** raise `maxHeartbeats`
on JUST the offending decl to the smallest passing value, tagged `-- KERNEL-BUDGET:`. Either path makes
the build progress — do not exit without one. Full file-specific guidance is in the
`/- USER (iter-093): … -/` hint above the lemma. Blueprint: `Cohomology_CechHigherDirectImage.tex`
(`lem:coreIso_comm_leg`).

Backs `lem:coreIso_comm_leg` (Stacks 01EO Čech-to-cohomology comparison, per-leg coface naturality).

## Next iter plan (after review)
- Once LegTop kernel-compiles, RE-LAUNCH the detached chain build
  (`lake build AlgebraicJacobian.Cohomology.CechToHigherDirectImage`); it will replay cache up to
  LegTop then build Aux → CSI → CechAugmentedResolution → CHDI. **Aux (`maxHeartbeats 6400000` ×2,
  heaviest) and CHDI (`4000000`) are the next kernel-timeout risks** — if either hits a
  `(kernel) deterministic timeout`, apply the SAME decomposition fix (split the offending decl so each
  piece checks independently under budget). Each kernel-timeout is one prover objective.
- Only when the WHOLE chain kernel-compiles + sync_leanok adds `\leanok` for
  `cech_computes_higherDirectImage` AND `#print axioms cech_computes_higherDirectImage` = kernel only:
  advance to **polish**. Polish cleanup: stale CSI docstring (CSI.lean:19-21 still claims a
  `coreIso_comm_leg` sorry — false); dead scaffolding (pushPullLegIso/pushPull_leg_coherence); orphan
  DAG nodes (tile_section_comparison, pushforward_commutes_restriction, used-by 0).
- **Speed (standing directive):** decomposition IS the lever — it both bounds kernel cost and lets the
  pieces build in less wall-clock. Prefer it over blind heartbeat raises (which make the slowest file
  slower). Do NOT LSP-poke to "build" — only `lake build`/`lake env lean` writes oleans (iter-092 finding).

## Deferred / standing notes
- **Frozen-signature decision RESOLVED (iter-080, by the user):** the false general decl + its protection
  are gone; the canonical name now carries the correct hypotheses. (Prior iters 077–079 left it a documented
  `sorry` because agents cannot edit a protected signature; the user removed it.)
- **Dead routes (no retry):** see STRATEGY §Routes / ARCHON_MEMORY — stalk-at-prime exactness; naive
  affine-basis section-exactness (circular); span-cover descent on global sections (circular);
  open-subscheme Ext transport (restriction-injectives wall); non-augmented section complex (not
  contractible); `hacyc` via Serre vanishing on `U∩f⁻¹V` (open not affine).
- **Build-wall:** the heavy chain cold-builds ~25+ min and may exit-137 in the prover memory cap; trust
  the review-build gate for full verification. `\leanok` owned by `sync_leanok`.
- No usable external-LLM API key in env; use subagents / LSP.
