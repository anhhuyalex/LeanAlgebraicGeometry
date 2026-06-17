# Mathlib Analogist Report

## Slug
iter-001-selmer-api

## Iteration
001

## Scope

The current blueprint and `Basic.lean` are still just a stub, so this is a forward-looking API decision. The right choice now is to match Mathlib's subobject and exactness idioms before the project grows a parallel Selmer/Kolyvagin surface.

## Verdict Summary

- Selmer local-condition packaging: `ALIGN_WITH_MATHLIB`
- Kernel-of-localization / exactness: `ALIGN_WITH_MATHLIB`
- Torsion bookkeeping: `ALIGN_WITH_MATHLIB`
- Characteristic ideals: `NEEDS_MATHLIB_GAP_FILL`

## Selmer Local Conditions

- Verdict: `ALIGN_WITH_MATHLIB`
- Mathlib idiom: use a thin structure only for the *family of local conditions* if you need one, but keep the actual mathematical objects as `Submodule`s and predicates. `Submodule` is the canonical bundled carrier for module subobjects, and Mathlib does use small record types for indexed families of submodules with axioms, e.g. `Ideal.Filtration` with `N : ℕ → Submodule R M` plus monotonicity and compatibility fields (`Mathlib/Algebra/Module/Submodule/Defs.lean:38-42`, `Mathlib/RingTheory/Filtration.lean:49-55`).
- Project recommendation: if you need a `SelmerStructure` record, make it a light parameter package of local-condition assignments. Do not make the Selmer group itself a bespoke structure. The Selmer group should be a `Submodule` or a predicate on the ambient cohomology module.
- Cost of divergence: a custom bundled Selmer object will force bridge lemmas for every `map`, `comap`, `ker`, quotient, and exactness statement. That is exactly the kind of API fragmentation Mathlib tries to avoid.

## Kernel-Of-Localization And Exactness

- Verdict: `ALIGN_WITH_MATHLIB`
- Mathlib idiom: kernel-style constructions are `Submodule`s coming from `LinearMap.ker`, and exactness is phrased as equality of `range` and `ker`. `LinearMap.ker` is defined as `comap f ⊥` (`Mathlib/Algebra/Module/Submodule/Ker.lean:58-61`), and `LinearMap.exact_iff` identifies `Exact f g` with `LinearMap.ker g = LinearMap.range f` (`Mathlib/Algebra/Exact/Basic.lean:249-251`). The short-complex API in `ModuleCat` uses the same pattern directly: `range = ker`, then a canonical map into the kernel, then homology as `ker / range` (`Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean:52-58`, `Mathlib/Algebra/Homology/ShortComplex/ModuleCat.lean:95-107`).
- Project recommendation: model localization and restriction maps as actual linear/semilinear maps, then express Selmer conditions using `ker`, `range`, `comap`, and `Exact`. If the construction is a kernel, make it a `Submodule`; if it is an exactness statement, make it a proposition about those canonical maps.
- Cost of divergence: introducing a separate kernel object or a bespoke exact-sequence wrapper will duplicate the standard `LinearMap`/`Submodule` API and make later homology-style arguments harder to state cleanly.

## Torsion Bookkeeping

- Verdict: `ALIGN_WITH_MATHLIB`
- Mathlib idiom: torsion is handled by predicates and submodules, not by a dedicated torsion object. `Submodule.torsionBy`, `Submodule.torsion'`, and `Submodule.torsion` are the canonical submodule-level definitions, while `Module.IsTorsion` is just a predicate (`Mathlib/Algebra/Module/Torsion/Basic.lean:175-225`). Rank/quotient bookkeeping is then stated in terms of those submodules, e.g. `rank_quotient_eq_of_le_torsion` and `finrank_quotient_eq_of_le_torsion` (`Mathlib/LinearAlgebra/Dimension/Torsion/Basic.lean:27-43`).
- Project recommendation: keep torsionness as a module predicate and keep the torsion subobject as a `Submodule`. Do not invent a bespoke torsion wrapper when the canonical API already gives you the lattice and quotient lemmas you will need.
- Cost of divergence: a custom torsion structure would again shadow the standard `Submodule`/`Ideal` lattice and make quotient/rank lemmas harder to reuse.

## Characteristic Ideals

- Verdict: `NEEDS_MATHLIB_GAP_FILL`
- Mathlib idiom: the right carrier is still `Ideal`, not a new wrapper type. `Ideal R` is literally implemented as `Submodule R R` (`Mathlib/RingTheory/Ideal/Defs.lean:13-20`), so ideal-valued invariants should live in the existing ideal lattice.
- Gap: Mathlib does not provide a canonical characteristic-ideal abstraction or theorem stack. That part is project-specific and must be built on top of `Ideal`.
- Project recommendation: define characteristic ideals as `Ideal`-valued functions/lemmas over the Iwasawa algebra, and keep the surrounding divisibility and equality bookkeeping as project-level theorems. Do not introduce a bespoke `CharacteristicIdeal` carrier unless you have a real semantic reason that `Ideal` cannot express.
- Cost of divergence: a wrapper type here would buy nothing and would immediately require coercions and bridge lemmas back to `Ideal`.

## Bottom Line

The Mathlib-aligned shape is: thin parameter structure for local conditions if needed, core Selmer objects as `Submodule`s and exactness statements, torsion as `Submodule`/predicate infrastructure, and characteristic ideals as `Ideal`-valued project code. The only real gap to fill is the characteristic-ideal theorem layer; the container type should still be `Ideal`.
