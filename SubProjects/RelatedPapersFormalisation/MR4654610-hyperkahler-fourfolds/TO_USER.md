# Notes for the user

## DAG iteration 001 complete

The blueprint for this project is fully written. All 29 declarations covering the paper's
main results have been added to `blueprint/src/chapters/Overview.tex`, the dependency graph
has 0 broken edges and 0 ∞-effort nodes, and the formalization strategy is recorded in
`.archon/STRATEGY.md`.

## Before starting Phase 1 prover work

**Action required**: verify one Mathlib declaration name.

The blueprint marks `lem:integer-valued-polynomial` as:

```latex
\lean{Polynomial.eval_intCast_map}
\mathlibok
```

This name follows Mathlib4 camelCase conventions (`intCast` not `int_cast`) but has not been
confirmed via LSP. Before writing any Phase 1 Lean code that imports this lemma, run:

```lean
#check Polynomial.eval_intCast_map
```

in a file with `import Mathlib`. If the name is wrong, update the blueprint anchor in
`blueprint/src/chapters/Overview.tex` (search for `eval_intCast_map`) before dispatch.

## Phase 1 starting point

See `.archon/PROGRESS.md` for the Phase 1 objectives. The two Lean files to create are:

- `MR4654610ComputingRiemannRochPolynomialsAndClassifyingHyperKahlerFourfolds.lean` — imports Basic
- `MR4654610ComputingRiemannRochPolynomialsAndClassifyingHyperKahlerFourfolds/Basic.lean` — all declarations

The full formalization plan is in `.archon/STRATEGY.md`. The blueprint is the mathematical
specification; it drives what goes in each declaration.
