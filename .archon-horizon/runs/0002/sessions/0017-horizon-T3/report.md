Everything is in place: build green, axiom-clean, blueprint pinned, inbox and memory updated, no stray files. Final report:

## Summary

- Attacked `ALB.codim1` per recommendation: the Stage-6 keystone gap of `isRegularLocalRing_stalk_of_smooth` (Stacks 00TT) in `CodimOneExtension.lean`.
- **Discharged sub-gap (ii.B)** — the Stacks 00OE smooth-algebra Krull-dimension formula at closed points — and proved the **closed-point case of Stacks 00TT axiom-clean**.
- Key insight: no transcendence-degree/Noether-normalization build needed (iter-199 estimated 200–300 LOC of it); v4.31 Mathlib's `Polynomial.height_eq_height_add_one` + Krull's height theorem (`Ideal.height_le_height_add_spanFinrank_of_le`) + Jacobson instances carry the whole computation. This also supersedes the stalled iter-200 Step-3 regular-sequence lane.

## Progress

- New module `Albanese/StandardSmoothDimension.lean` (~230 LOC, Mathlib-only imports, ~8 s build): maximal ideals of `MvPolynomial ι k` have full height; `n ≤ ht m` and `n ≤ ringKrullDim Sₘ` for standard-smooth algebras; regularity glue from the cotangent bound.
- `CodimOneExtension.lean` §3.B gains Step B.d `isRegularLocalRing_localization_of_isStandardSmooth_of_bijective_residue` and B.d′ `..._of_isAlgClosed` (unconditional over k̄ via Zariski's lemma).
- All 7 new declarations `#print axioms`-clean (`propext, Classical.choice, Quot.sound`).
- Full `lake build` green (8581 jobs); sorried-decl count unchanged at 16 — no new sorries, stale Stage-6 docs rewritten honestly (docstring + sorry-body closure plan).
- Blueprint: 6 new `\leanok` nodes in `Albanese_CodimOneExtension.tex` (`subsec:codim1_substrate_lemmas`), complete proofs, labels verified; `lem:smooth_to_regular_local_ring` `\uses` extended.
- Inbox: results commented on `I-0008`; recipe + traps filed as memory `I-0027`; auto-memory updated.

## Issues

- The three CodimOneExtension sorries remain (expected): `isRegularLocalRing_stalk_of_smooth` now blocks **only on Stacks 00OF** (localization of regular local rings is regular — needs Serre's homological characterization, absent from Mathlib; large build, flagged do-not-side-quest). Milne 3.1/3.3 additionally need 0AVF and function-field pullback machinery.
- Duplication note for Ground/janitor: the old iter-200 private Step-2 lemmas (`MvPolynomial.maximalIdeal_height_*`, CodimOneExtension L647–714) are now mathematically subsumed by the public module; left in place to keep existing blueprint pins valid.
- Instance trap recorded: `letI := Ideal.Quotient.field m` must be installed before other `haveI`s on `S ⧸ m`, else `Algebra k (S ⧸ m)` synthesis breaks (transparency option does not help).
- Did not refresh the leandag cache (per `I-0010` precedent); the 6 new nodes enter the DAG on the next refresh.

## Next

- If 00OF ever lands (Mathlib or project-side), the sorry-body now contains the exact closure pattern (closed specialisation + `IsLocalization.algEquiv` + `IsRegularLocalRing.of_ringEquiv`).
- Optional cleanup: dedupe the superseded iter-200 Step-2/Step-3 lane and re-point its blueprint nodes.
- `hCP_check` (GmScaling) and the A.3/picrep-gated sorries remain the only other Albanese items; no further generic T3 session is fruitful.
