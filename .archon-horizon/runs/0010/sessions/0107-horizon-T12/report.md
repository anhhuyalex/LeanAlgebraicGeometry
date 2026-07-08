## Summary

**`Grassmannian.representable` is closed, axiom-clean.** The single remaining leaf of `thm:grassmannian_representable` — the Zariski sheaf axiom `Grassmannian.isZariskiSheaf` — is proved in a new 1062-line file `Picard/GrassmannianZariskiSheaf.lean`, making the entire Grassmannian representability chain (statement fix → Zariski descent of representability → sheaf axiom) sorry-free. `lean_verify` reports `[propext, Classical.choice, Quot.sound]` for both `Grassmannian.representable` and the new master theorem `grassmannian_isZariskiSheafOver`; the full project kernel build is green (8655 jobs).

The proof: chart quotient families glue by module descent over the mathlib glue datum of the open cover (`Scheme.Modules.glue` engine from `GlueDescent.lean`). The key idea that made the descent cocycle *free* is an epi-uniqueness algebra: the predicate `IsGlueIso` ("intertwines the restricted chart quotients over a common total map") admits `trans`/`symm`/`baseChange`/`cast`/`reindex` closure lemmas, gluing isomorphisms are unique because quotient maps are epi, so both C1 and the triple-overlap cocycle C2 are two-line uniqueness applications. The quotient maps glue via `glueLift` (overlap condition = one cast-coherence lemma `triangleIso_cast_coherence`), the family is packaged over the glued scheme where epi/local-freeness are native, and one `pullbackAlong` along `fromGlued⁻¹` lands it on `T`. Separation is the `Abelian.epiDesc` + cover-faithfulness pattern lifted from `GrassmannianQuot.lean`.

## Progress
- AlgebraicJacobian/Picard/GrassmannianZariskiSheaf.lean: NEW, 1062 lines, sorry-free; cover-local toolkit, IsGlueIso algebra, transition isos + C1/C2, glued family, sheaf theorem.
- AlgebraicJacobian/Picard/GrassmannianRepresentability.lean: 1 sorry -> 0; `isZariskiSheaf` now delegates to the new file; `Grassmannian.representable` axiom-clean.
- AlgebraicJacobian.lean: registered the new module in the root import list.
- blueprint/src/chapters/Picard_QuotScheme.tex: `lem:grassmannian_zariski_sheaf` proof rewritten to the Lean route + `\leanok`; `thm:grassmannian_representable` proof `\leanok` with bare-representability disclaimer; stale NOTE updated.
- Ledger: committed as 8e506aa4 (all four files content-verified in workspace.git); inbox note I-0124; memory `grassmannian-representable-closed` written, two stale memories updated.
- AlgebraicJacobian/Picard/QuotFunctorDef.lean: no change; its 5 sorries (incl. the false-as-pinned `QuotScheme`, I-0118) are the remaining T12 frontier.

## Issues
- v4.31 gotchas discovered and recorded in memory: local glue-datum defs must be `@[reducible]` (instances-transparency walls otherwise); `inv 𝒰.fromGlued` under a hom-ascription picks a divergent `catToReflQuiver` instance path and breaks `IsIso` synthesis — fixed by binding the instance as a named lemma and passing it explicitly.
- Style lints remain in the new file (unused section vars, unused simp args, `show`-vs-`change`) — consistent with existing project files, no errors.
- The blueprint theorem's smoothness/properness/Plücker refinements are still prose-only (pre-existing, disclaimed in NOTE).

## Why I stopped
Task not complete: T12's headline (full Pic representability) remains open; this session closed its deepest ready milestone (Grassmannian representability, one of the two representability endgames).
- Remaining leaves are each documented session-sized items: 4 QuotFunctorDef base-change leaves plus the QuotScheme statement repair (I-0118 trap — needs projectivity vocabulary).
- Work is committed, kernel-verified, and blueprint-reconciled; starting another deep leaf with remaining budget risked leaving broken state.

## Next
- Reuse the `IsGlueIso` skeleton verbatim for the Quot functor's sheaf axiom (same file pattern; `QuotFamily.Rel` is also epi-witnessed).
- Repair the pinned `Scheme.QuotScheme` statement per I-0118 (projective π / very ample L / coherent E) before attempting its proof.
- Adjacent tractable leaf: `HasProperSupport.of_isPullback` (annihilator pullback + properness base change), per the QuotFunctor memory.
