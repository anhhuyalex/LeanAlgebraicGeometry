# Orientation — run 0010, opening Ground (session 0109-ground)

- Useful context (live Quot cone, `AJC.picrep`): `Grassmannian.representable` is closed axiom-clean (`Picard/GrassmannianZariskiSheaf.lean` + `GrassmannianRepresentability.lean`, both `sorry`-free). The remaining Quot leaves live in `Picard/QuotFunctorDef.lean` — **5 `sorry`s** at lines 380 `pullbackSlicePresentation_isFinite` (index bookkeeping), 419 `CoherentSheafFlat.of_isPullback`, 432 `HasProperSupport.of_isPullback`, 457 `hilbertFunction_quotBaseMap` (H⁰ flat base change), 844 `QuotScheme`.

- Consistency note: `thm:quot_representable` (`Picard_QuotScheme.tex:4374`) is now `\notready` (was falsely `\leanok`). Its Lean target `QuotScheme` is unproved and **false as pinned** — proper+lofinite-type over arbitrary quasi-coherent `L,E`, weaker than the correct projective+very-ample+coherent statement the blueprint holds (`I-0118`; Mathlib v4.31 lacks projectivity vocabulary, so the signature can't yet be made faithful).

- Related bricks: `CoherentSheafFlat.of_isPullback` needs the same stalk-of-pullback infrastructure as the FBC leaf `pullback_preservesFiniteLimits` (`CechHigherDirectImageUnconditional.lean`; route analysis in memory `I-0076`/`I-0083`). Functor-law and ModuleCat-hom recipes for this chapter are in memory `I-0113`/`I-0088`; hilbertPolynomial substrate in `I-0109`, 01XJ pushforward-qcoh in `I-0120`.

- Other active cones if widening scope: `AJC.fbc` (3 leaves in `CechHigherDirectImageUnconditional.lean`), `AJC.pic0av` tangent-space `tangentSpaceIso` (task T10, `Pic0AbelianVariety.lean`; attack path in `I-0061`/`I-0082`), and `ALB.codim1` gated on the single Milne 3.3 leaf `indeterminacy_pure_codim_one_into_grpScheme` (`Albanese/CodimOneExtension.lean`; chain notes in `I-0065`).
