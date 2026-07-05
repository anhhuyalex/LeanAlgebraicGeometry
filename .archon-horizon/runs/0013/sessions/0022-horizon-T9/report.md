All work is verified, committed, and documented. Here's my report.

## Summary

Completed and kernel-verified the **function-field pullback bridge `K(Y) → K(X)`** for dominant rational maps — the substrate the memory `t9-albanese-endgame-unblock-map` had tracked as a partial ("stalkPullback landed, dominant refinement documented but walled"). Both new declarations are axiom-clean, committed, and pinned in the blueprint 1-to-1. This is the substep-3 function-field functoriality on the extension-leg critical path (Milne §I.3).

## Progress
- AlgebraicJacobian/Albanese/RationalMapFunctionField.lean: added `fromFunctionField_base_eq_genericPoint` + `functionFieldPullback`, both axiom-clean `[propext, Classical.choice, Quot.sound]`; file kernel-compiles (`lake env lean`, exit 0); reachable from root (`AlgebraicJacobian.lean:103`).
- blueprint/src/chapters/Albanese_CodimOneExtension.tex: added `lem:fromFunctionField_base_eq_genericPoint` + `def:functionFieldPullback`, complete proofs, `\leanok`, honest `\uses`; labels unique.
- AlgebraicJacobian/Albanese/AlbaneseUP.lean: no change — 7 sorries remain, all gated on the missing Sym^g scheme substrate + Pic0 representability (out of scope).
- AlgebraicJacobian/Albanese/CodimOneExtension.lean: no change — the ONE Milne-3.3 sorry (`:1721`) remains; its difference map needs new RationalMap primitives (see below).

## Issues
- **Extension leg not axiom-clean.** `extend_to_av` (Thm32) still carries the Milne-3.3 `sorry` transitively. Also, CodimOneExtension imports `AuslanderBuchsbaum.lean` (15 sorries); I did not audit whether the specific AB lemmas it uses are themselves clean — an open soundness question worth a targeted axiom-check.
- **Blueprint drift (pre-existing, unfixed):** `thm:codim_one_extension`'s `\uses{cor:regular_cohen_macaulay}` + proof prose still describe the 0AVF/Cohen–Macaulay route that memory says is a phantom in the honest valuative chain. Flagged in memory bullet 20; left as consistency debt.
- I verified the changed leaf file at kernel level but did not run the full multi-thousand-job `lake build` (unnecessary: RationalMapFunctionField is Mathlib-only, imported only by the root aggregator, and compiles standalone — no downstream dependents can break).

## Why I stopped
Task not complete: the Albanese UP / endgame glue remains gated on two large greenfield sub-builds, neither one-session work.
- I carried the one concrete, completable critical-path brick to a verified, committed finish.
- The next brick (Milne 3.3 substep 1, the difference map `Φ = m∘(f×f) : X×X ⇢ G`) requires **new `RationalMap` infrastructure that mathlib lacks**: I confirmed `Birational/RationalMap.lean` exposes only `compHom` (right-compose with a morphism) — no rational-map products and no precomposition with a dominant/open morphism. Building those + the germ-definedness criterion + substep 4b is a genuine multi-session build, not finishable-and-verifiable now.
- Starting it would leave broken/half-built infrastructure — worse than a clean verified stop.

## Next
- Build the RationalMap primitives: precomposition with an open dominant morphism (needs "preimage of a dense open under an open map is dense") and a pairing into a product target; then the difference map `Φ`, the germ-definedness criterion, and substep 4b to close Milne 3.3 (`CodimOneExtension.lean:1721`).
- Independently: the UP leg needs the Sym^g scheme substrate (Milne III.3, glue `Spec((A^{⊗g})^{Sₘ})`) — the larger of the two greenfield blocks.
- Cheap follow-up: axiom-check whether the AuslanderBuchsbaum lemmas that CodimOneExtension actually uses are clean, to bound the extension leg's taint precisely.
