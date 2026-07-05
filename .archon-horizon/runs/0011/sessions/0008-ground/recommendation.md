# Orientation for Horizon — run 0011 / T13 (retire genus-0 / Route-C split)

- Useful context: the genus split is already gone from the **Lean tree** (`Genus0BaseObjects/*`, `AbelianVarietyRigidity.lean`, `genusZeroWitness`/`positiveGenusWitness` deleted; `Jacobian C` uniform). T13 is residue cleanup. Full scope map + the do-not-delete trap live in `I-0107` and memory `I-0106`.

- Relevant residue files: root `roadmap.md` (stale genus-0 lines ~66/70/72/77/112/120); `RiemannRoch/WeilDivisor.lean` (dual-purpose — `PrimeDivisor`/`RationalMap.order` feed live `Albanese/CodimOneExtension.lean`, only the `-- Route C PAUSE` degree/RR→ℙ¹ block is dead); prose in `RigidityLemma.lean:787`, `Jacobian.lean:24,182`. Doc comments in `AbelJacobi.lean`/`Genus.lean` sit outside the current write globs.

- Blueprint↔Lean mismatch to reconcile: `blueprint/src/chapters/AbelianVarietyRigidity.tex` in **both** AJC and Albanese still carries the genus-0 chapter — `% archon:covers ...Genus0BaseObjects/*.lean` (deleted), the `def:genus0_base_objects` node with ~15 `\uses` edges, and `thm:genus_zero_curve_iso_p1`; compiled `Albanese.json` shows 104 refs to the deleted `Genus0BaseObjects` files.

- Build/environment note: AJC builds green (8646 jobs, exit 0) per the run-0010 T12 reconcile; this Ground session changed no Lean, so that state stands. `RigidityLemma.lean` + its rigidity/Milne §I corollaries are live (used by the uniform Albanese construction) — only their "genus-0 base case" framing prose is stale.
