Everything is clean and committed: temp removed, no stray files, working tree clean, DifferenceMap.lean sorry-free, CodimOneExtension's only sorry is the unchanged Milne 3.3 one. Here's my report.

## Summary

Advanced the T9 critical path — Milne Lemma 3.3 (`indeterminacy_pure_codim_one_into_grpScheme`), the sole open sorry gating the Albanese extension leg — by **landing Sub-step 1 in full**: Milne's difference rational map `Φ(x,y) = f(x)·f(y)⁻¹` is now a named, verified, axiom-clean construction, and its self-product integrality input is proved end-to-end. I did **not** close the Milne 3.3 sorry itself (Sub-steps 2 and 4b are genuinely multi-session), so no new sorries were introduced.

A parallel workflow mapped the four required mathlib API areas; a second adversarial-verify workflow confirmed the construction is **sound + faithful to Milne** (orientation `fst/snd = g·h⁻¹` cross-checked against `lift_conj`) and the blueprint has **no dangling `\uses`/orphans**.

## Progress
- AlgebraicJacobian/Albanese/DifferenceMap.lean: NEW leaf (Mathlib + 2 bricks only) — `GrpObj.diff`, `grpObjDiffLeft`(+`_comp_hom`), `isOpenMap_pullback_fst/snd_self`, `differenceRationalMap`, `differenceRationalMap_compHom_over`; all axiom-clean, kernel-built.
- AlgebraicJacobian/Albanese/CodimOneExtension.lean: +`Scheme.isIntegral_pullback_self` (axiom-clean) discharging the difference map's `[IsIntegral (pullback X.hom X.hom)]` hyp; the one Milne 3.3 sorry unchanged.
- AlgebraicJacobian.lean: added `import ...Albanese.DifferenceMap`; full root build green (8660 jobs).
- blueprint/src/chapters/Albanese_CodimOneExtension.tex: +4 nodes (`def:grpObj_diff`, `lem:grpObjDiffLeft_comp_hom`, `def:rationalMap_difference`, `lem:rationalMap_difference_over`), wired into `lem:milne_codim1_indeterminacy`.

## Issues
- `differenceRationalMap`'s domain-of-definition is only guaranteed dense (built via the function-field `prod` route), not explicitly ⊇ U×U — this is exactly why Sub-step 2 (slice) is hard; recorded in memory.
- Two v4.31 gotchas cost build iterations (both fixed, documented in memory): `Over.mk _.hom` doesn't reduce at instances transparency (needs a `show`); `IrreducibleSpace (pullback …)` mis-resolves `pullback` in the `Type` category (must drive synthesis through a `Scheme`-typed application).
- Pre-existing, not mine: `linter.style.header`/overlapping-instance/line-length warnings surface when CodimOneExtension rebuilds; `I-0118` (QuotScheme) is an unrelated T12 concern.

## Why I stopped
Task not complete: the Milne 3.3 sorry `indeterminacy_pure_codim_one_into_grpScheme` remains open — this was substrate progress (Sub-step 1 + its integrality input), and closing it needs Sub-steps 2 (diagonal slice `(x,x)∈DomΦ ↔ x∈Domf`) and 4b (diagonal codim-1 Krull bound), both substantive multi-session work that I will not fake with a new sorry. Everything I added is verified green and axiom-clean; a clean stopping point.

## Next
- Sub-step 2 (slice): relate the function-field-built Φ's actual domain to the pointwise `f(x)=Φ(x,u)·f(u)` near the diagonal (group-law continuity + domain openness) — the genuine remaining frontier.
- Sub-step 4b: transport a coheight-1 pole point of X×X through Δ to a coheight-1 point of X in Z(f) (Krull bound; 4a = `PolePurity.lean` already done).
- When closing the sorry inside CodimOneExtension: `import ...Albanese.DifferenceMap`, then `haveI := Scheme.isIntegral_pullback_self X; ... differenceRationalMap f hover` — both inputs now exist.
