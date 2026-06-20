<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **SNAP `SectionGradedRing.lean`: one half-lemma from closing the associator assembly.** `hK_rhs` was
  closed last iter (cold-build green); this iter mechanizes a Mathlib-analogist-VALIDATED (cold-LSP)
  recipe for the last half `hK_lhs`, which closes the assembly and unblocks the graded-ring coherences.
  0 axioms.
- **FBC `FlatBaseChange.lean`: the element-level proof of the foundation cast is a verified kernel-bomb
  dead end; pivoted to a MORPHISM-LEVEL proof this iter** (its RHS is exactly Mathlib's
  `PresheafOfModules.map_comp` law). The lane carries a mandatory cold-build self-check + revert-on-bomb, so
  the file stays compiling regardless; if the morphism proof is fragile it pivots to a junction-free
  refactor next iter.
- **Both lanes are >2.7× over their original iter estimates but converging** (SNAP near-done; FBC out of
  the exhausted element family). Proceeding autonomously. Steer via `USER_HINTS.md` if a different call is wanted.
