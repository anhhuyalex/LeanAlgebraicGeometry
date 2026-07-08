## Summary

Closed the **Zariski descent of representability** keystone of the T12 Picard-representability cone: `Scheme.representable_of_openCover` (EGA 0_I 4.5.4 / Stacks 01JJ) — previously the monolithic typed-sorry leaf of `thm:grassmannian_representable` — is now **fully proved and axiom-clean** (`[propext, Classical.choice, Quot.sound]`). The proof lives in a new 1370-line file `ZariskiDescentRepresentability.lean` that routes through mathlib's `Scheme.LocalRepresentability` (Stacks 01JJ): since `F : (Sch/S)ᵒᵖ ⥤ Type 1` is one universe too big for the mathlib theorem, I built a `Type 0` "glued point" total functor (base morphism + classifying morphisms into the local representing objects), proved it equivalent to `Σ a, F(T,a)` via the bespoke sheaf axiom, showed it is a big-Zariski sheaf with relatively-representable open-immersion charts, and translated the resulting absolute representability back to `Over S`. `Grassmannian.representable` now depends on a **single** remaining leaf (`isZariskiSheaf`), and the descent theorem is general-purpose — it will serve Quot and Pic representability directly.

## Progress
- AlgebraicJacobian/Picard/ZariskiDescentRepresentability.lean: NEW, 1370 lines, sorry-free; hosts moved `IsZariskiSheafOver`/`overRes*` plus proved `representable_of_openCover`.
- AlgebraicJacobian/Picard/GrassmannianRepresentability.lean: 2 sorries -> 1; descent leaf deleted, imports the new file; only `isZariskiSheaf` remains.
- AlgebraicJacobian.lean: registered the new module.
- blueprint/src/chapters/Picard_QuotScheme.tex: descent proof rewritten to the formalized route, `\leanok`; new `\mathlibok` node `lem:local_representability_mathlib` (Stacks 01JJ).
- Verification: `lake build` green on both modules (kernel-checked); `lean_verify` axioms clean on the theorem.
- Memory: new `zariski-descent-representability-proved` (architecture + rw-free transport discipline, opaque-glue trick); updated `grassmannian-representability-descent`.
- Inbox: I-0123 to Ground summarizing the closure and recommending `isZariskiSheaf` as next target.
- Commits: 5 semantic commits (18ce86b9, 7d6754e8, 66bc0a64, 2ffb9641, af7f2d42).

## Issues
- None open in the new work: no sorries, no lint warnings in the new file; pre-existing warnings in `SectionGradedRing.lean`/`CechAcyclic.lean` untouched.
- Recurring hazard documented in memory: `rw`/`simp` fail on goals with `Over.mk`-typed subterms; the file establishes a calc/`congrArg` discipline plus subst-based transport lemmas that future sessions should reuse.

## Why I stopped
Task not complete: T12's full endgame (`instHasPicScheme`, QuotScheme statement repair per I-0118, `isZariskiSheaf`) remains, but the session's chosen objective — closing the descent keystone — is done, verified, and committed; the remaining context budget is insufficient to responsibly start the next multi-hundred-line leaf.

## Next
- `Grassmannian.isZariskiSheaf`: module gluing via the `GlueDescent` `Scheme.Modules.glue` engine — now the sole obstruction to `Grassmannian.representable`.
- Reuse `representable_of_openCover` for the Quot and Pic representability statements (restate `QuotScheme` first per I-0118).
- QuotFunctorDef leaves (`HasProperSupport.of_isPullback`, `hilbertFunction_quotBaseMap`) remain as scoped mid-size targets.
