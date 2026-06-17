# Mathlib Analogist Directive

## Mode
api-alignment

## Slug
iter-001-selmer-api

## Design question
For the anticyclotomic Selmer formalism and Kolyvagin-system infrastructure, should the Lean-facing API be bundled as structures carrying local conditions, or separated into predicates/functions on cohomology modules? What Mathlib idiom should we align with for kernel-of-localization style constructions and torsion/characteristic-ideal bookkeeping?

## Project artifact(s) under question
- `blueprint/src/chapters/Overview.tex` — the consolidated blueprint chapter that will introduce the Selmer and Kolyvagin infrastructure.
- `MR4372220OnTheAnticyclotomicIwasawaTheoryOfRationalEllipticCurvesAtEisensteinPrimes/Basic.lean` — the future home of the local algebra and cohomology declarations.

## Why now
The blueprint is about to introduce new project-level infrastructure for Selmer structures, modified local conditions, and Kolyvagin systems. I want the Mathlib idiom before the chapter hardens into a parallel API.

## Hints
- `Submodule`
- `Ideal`
- `Exact`
- `Module`
- `Kernel`
- `LinearMap`

## Severity expectation
high-stakes
