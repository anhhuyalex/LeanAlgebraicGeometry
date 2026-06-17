# Mathlib Analogist Directive

## Mode
api-alignment

## Slug
overview-roadmap

## Design question
For the ambient setup around the height-inequality / Mordell-Lang roadmap, should the blueprint treat the data as a bundled structure (capturing the family, embeddings, heights, and non-degeneracy witness) or as separate predicates/definitions with explicit witnesses? What is the closest Mathlib idiom for the non-degeneracy hypothesis and for the Betti-map-derived rank condition?

## Project artifact(s) under question
- `blueprint/src/chapters/Overview.tex`: the only current blueprint chapter, which will need to host the roadmap and the foundational setup blocks.
- `references/MR4276287-mordell-lang-curves.tex`: especially `intro.tex`, `BettiMapForm.tex`, `SetUpHtIneq.tex`, `HtIneq.tex`, `HtIneqFinalVer.tex`, `SettingUp.tex`, `DistanceCurve.tex`, `RatPt.tex`.

## Why now
I am about to write the blueprint chapter and need to decide whether the setup should be bundled or broken into separate declarations, so the future Lean targets stay aligned with Mathlib idioms.

## Hints
Non-degeneracy is a rank condition on a Betti-map differential; the ambient data includes a family of abelian schemes, a projective embedding, and a height machine input.

## Severity expectation
high-stakes
