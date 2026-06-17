<!-- Shared notice board. Keep to <=2-3 short bullets; delete bullets no longer true. -->

- **Extracted from *Quot-Foundations* as the GR-quot closure** (seeds: Grassmannian
  representability + scheme + tautological-quotient epi; 287-node cone, 9 sorries). The
  flat-base-change / generic-flatness leg was dropped (→ sibling `FBC-B_SNAP-chain`).
- **2 of the 9 sorries are χ-blocked and NOT closable here:** `def:hilbert_polynomial` /
  `def:quot_functor` are χ-semantic (verified against the Lean decl, not the blueprint comment)
  and need a higher-cohomology engine this i=0 leg lacks. They stay as `sorry`, filled from the
  cohomology leg at merge.
- **SNAP (section graded ring) is shared with the sibling `FBC-B_SNAP-chain`.** Keep as sorry
  here or import the sibling's finished proofs — coordinate so the two encodings don't diverge
  (per your hint). The actually-closable frontier here is GR-quot (+ SNAP if proving locally).
