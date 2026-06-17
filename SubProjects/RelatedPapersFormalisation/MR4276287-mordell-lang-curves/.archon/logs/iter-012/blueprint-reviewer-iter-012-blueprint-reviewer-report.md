# Blueprint Review

## Tool checks
- `leandag build --json`: no broken `\uses{}` edges, no unknown labels, no isolated blueprint nodes.
- `archon blueprint-doctor --json`: no malformed refs, no `covers` problems, 22 labels defined.

## Chapter verdicts

### `blueprint/src/chapters/Overview.tex`
- complete: true
- correct: true
- Notes: this is now a prose-only overview. The stale `% archon:covers` line has already been removed, and that is the right state to keep.

### `blueprint/src/chapters/MR4276287UniformityInMordellLangForCurves_Basic.tex`
- complete: partial
- correct: false
- Findings:
  - Citation discipline is not yet compliant. `def:ambient_setup` and `lem:moduli_height_comparison` (lines 11-31) have only a descriptive `\textit{Source: ...}` sentence and no `% SOURCE:` pointer. Every later source-backed block has a `% SOURCE:` line, but the visible `\textit{Source: ...}` text is still a paraphrase instead of the required matching pointer form. This is a hard-fix formatting issue across lines 11-186.
  - The height-inequality stack is still a little too compressed for a prover-facing blueprint. `thm:nondeg_for_bd`, `thm:ht_inequality`, and `thm:ht_inequality_full` rely on the Faltings--Zhang / graph-construction input, but that object is only implicit in the prose. If the formalization is going to follow the paper route cleanly, this should either be made explicit as its own block or expanded into a more detailed proof sketch.

### `blueprint/src/chapters/MR4276287UniformityInMordellLangForCurves.tex`
- complete: partial
- correct: false
- Findings:
  - The same citation-discipline issue appears here. All four blocks have `% SOURCE:` lines, but the visible `\textit{Source: ...}` text is still descriptive instead of matching the source pointer exactly. That needs to be normalized before the chapter is safe to merge.
  - The final theorem statements are on target, but the proof sketches for `prop:premazur`, `thm:bd_rat_intro`, `thm:bd_fin_rank`, and `thm:bd_tor_intro_nf` are still one-sentence summaries. The Lean route will need the reduction chain spelled out more explicitly, especially the handoff from `prop:alg_pt_far` to the moduli-height comparison step.

## Cross-chapter notes
- The overview is correctly prose-only and should stay uncoupled from Lean coverage.
- No broken `\uses{}` edges, unknown references, malformed refs, or isolated blueprint nodes were found.
- All remaining strategy phases are represented by substantive blueprint content, so there are no zero-coverage phases and no unstarted-phase chapter proposals are needed this iter.
- The consolidated `Basic` chapter spans setup, Betti geometry, height inequality, and counting lemmas. That is acceptable for coverage, but it is the natural place to split later if the team wants more parallelism.

## Must-fix-this-iter
- Normalize citations in `blueprint/src/chapters/MR4276287UniformityInMordellLangForCurves_Basic.tex`: add `% SOURCE:` pointers to the first two blocks, and make the visible `\textit{Source: ...}` line match the pointer exactly in every source-backed block.
- Normalize citations in `blueprint/src/chapters/MR4276287UniformityInMordellLangForCurves.tex` the same way.
- Expand the height-inequality sketch in `Basic.tex` so the Faltings--Zhang / graph-construction step is explicit enough for a prover.

## Unstarted-phase proposals
- None. Every strategy phase has blueprint coverage.

## Notes for Plan Agent
- Keep the `Overview` chapter without a `covers` line.
- The dependency graph is clean, so the next writer pass should focus on citation normalization and proof-detail expansion rather than structural rewiring.
