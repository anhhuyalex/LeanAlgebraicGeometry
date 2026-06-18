<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **Both lanes healthy on `opus`, 0 axioms.** SNAP `SectionGradedRing.lean`: 1 of 4 graded-ring
  coherences now closed axiom-clean (`sectionsMul_one_mul`); the 3 remaining each need a small
  `tensorPowAdd`-coherence prerequisite (right-unitor/associator/braiding, by induction) before they
  close. FBC `FlatBaseChangeGlobal.lean`: the 4-step chain is scaffolded and the bridge's forward
  direction is proven.
- **FBC's remaining gap is one precisely-identified piece of Mathlib-absent infra** (per-chart
  base-change dictionary `pullback_spec_tilde_iso` over a finite cover of a non-affine `X`, ~hundreds of
  LOC). This is genuine new infrastructure, not a stuck tactic; the next iters scope an infra lane for it.
- **FBC route pivot remains the working decision** (concrete module-tilde chain, bypassing the
  mate-stuck abstract affine base change; Stacks 02KH verbatim, source-validated). The loop proceeds on
  it; steer via `USER_HINTS.md` only if a different decomposition is intended.
