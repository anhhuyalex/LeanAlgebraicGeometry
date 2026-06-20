---
name: ts225-blueprint-audit
description: iter-225 whole-blueprint audit results: sub-step 4 gate, chapter statuses, cross-chapter inconsistency
metadata:
  type: project
---

HARD GATE CLEARS for `lem:internal_hom_isSheaf` (`AlgebraicGeometry.Scheme.Modules.dual`): construction complete+correct+detailed enough; Lean target well-named; minor prose gap (sheafification step for descended evaluation elided) formalizable without guessing.

`lem:dual_isLocallyTrivial` and `rem:dual_discharges_inverse`: coherent with sub-step 4; no must-fix.

Standing marker hygiene (multi-`\lean{}` `sync_leanok` quirk on several dual-infra blocks): KNOWN, tracked, informational.

Cross-chapter inconsistency: `lem:rational_map_to_av_extends` has two `\lean{}` pins — old `AlgebraicGeometry.rationalMap_to_av_extends` in AbelianVarietyRigidity.tex, canonical `AlgebraicGeometry.Scheme.RationalMap.extend_to_av` in Albanese_Thm32RationalMapExtension.tex. Soon-fix: update the old pin.

6 chapters complete: partial — all in held/paused routes (Picard_QuotScheme, Picard_FlatteningStratification, Albanese_CodimOneExtension unread portion, RiemannRoch × 4). None block the active lane.

0 unstarted phases with zero blueprint coverage.

**Why:** Whole-blueprint review dispatched as pre-prover gate for sub-step 4 dispatch.
**How to apply:** Plan agent can dispatch mathlib-build prover to `lem:internal_hom_isSheaf` this iter. Brief the prover: add one sentence to the proof about the universal property of sheafification for the descended evaluation `M⊗_psh M^∨ → M⊗_X M^∨ → O_X`.
