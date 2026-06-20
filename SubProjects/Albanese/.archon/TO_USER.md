- **Extracted from Algebraic-Jacobian-Challenge (2026-06-20).** This sandbox is the
  Albanese-universal-property slice. Seeds, closure (105 labels) and riders are
  recorded in `.archon/extract-manifest.json`. `lake build` was **not** re-run after
  the carve — run it (or let the extract verify gate) to confirm the kernel state.
- **~247 `\texttt{...}` markers in the blueprint** are cross-references that pointed
  to material carved out of this subproject (dropped chapters / out-of-cone lemmas).
  They were converted from `\cref`/`\ref` so the blueprint still compiles without
  undefined references. If you want clean prose, replace each with a real `\cref`
  to an in-scope label or rephrase; none block the build or the DAG.
- **Two intentional `sorry` riders** (`gmScalingP1_chart_agreement_cross01`,
  `gmScalingP1_collapse_at_zero`) survive in the imported `GmScaling.lean` with
  their blueprint blocks dropped — inherited sorries from the parent, recorded in
  the manifest `riders` array.
- **`FGAPicRepresentability.lean` and `WeilDivisor.lean` are thin slices** — only the
  declarations the Albanese cone consumes remain; their module docstrings still
  describe some carved declarations and could be trimmed.
