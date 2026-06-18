# Strategy

## Goal
Formalize Theorem D of Disegni, "The universal p-adic Gross-Zagier formula" (MR4493324, arXiv:2001.00045): the p-adic height of the universal Heegner class \(\mathscr{P}_{K^p}\) over a locally distinguished Hida family \(\mathscr{X}\) equals the cyclotomic derivative of the p-adic L-function, as an identity of \(\mathscr{K}\hat\otimes_{\mathbf{Z}_p}\Gamma_F\)-valued functionals on universal ordinary automorphic representations. Theorem B (the classical specialisation for a fixed ordinary, locally distinguished, non-exceptional \(\Pi\)) is the key prerequisite.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|------------|-----|-------------------|-------|
| Blueprint / DAG elaboration | ACTIVE | 1 | — | — | 84-page paper; most structures absent from Mathlib |
| Top-down axiom skeleton (Thms B, C, D as sorry-based stubs) | NEXT | 3 | ~200–400 | `Mathlib.NumberTheory.NumberField`, `AlgebraicGeometry.Scheme` | Lean types for all major objects must be settled first |
| Foundational structures: groups GL₂, GU(1), (G×H)', Shimura varieties | NEXT | 12 | ~800–1800 | `LinearAlgebra.UnitaryGroup`, `AlgebraicGeometry.Scheme` | (G×H)' is incoherent; Shimura variety towers not in Mathlib |
| Automorphic representations & Hida eigenvariety | NEXT | 14 | ~800–1600 | `RingTheory.AdicCompletion`, `CategoryTheory.Limits` | Hida families not in Mathlib; ordinary projector novel |
| Galois representations & Nekovář Selmer groups | NEXT | 14 | ~800–1600 | `GroupCohomology.Basic` (abstract only) | Arithmetic Galois cohomology with Selmer conditions ABSENT from Mathlib |
| Theorem B: classical p-adic Gross-Zagier for fixed Π | NEXT | 12 | ~600–1200 | Needs prior three phases | ~40-page argument; theta lift, toric periods, height comparison |
| Universal Heegner class & Theorem C | NEXT | 10 | ~500–1000 | Needs Galois + Hida phases | Arithmetic theta lift not in Mathlib; toric period integrals novel |
| Iwasawa algebra ℤ_p⟦Γ_F⟧ & completed tensor products | NEXT | 5 | ~200–400 | ABSENT from Mathlib | Literal type of Theorem D's codomain; must build from scratch |
| p-adic L-function (axiomatised from [Dis/b]) | NEXT | 3 | ~100–200 | None (axiomatised) | Only interpolation property stated; companion paper [Dis/b] is the reference |
| Main formula Theorem D & applications (E, F, G) | NEXT | 10 | ~400–800 | Needs all prior phases | p-adic interpolation from Theorem B requires control theory for Selmer over Hida |

## Routes

Primary route: **top-down axiom skeleton first** — state Theorem D in Lean using type-class hypotheses for every major structure (`HidaFamily`, `UniversalHeegnerClass`, `PAdicLFunction`, `CyclotomicHeightPairing`) and axioms for their key properties. The main formula is then a formal consequence of the axioms. Subsequent phases progressively discharge axioms with concrete constructions, bottom-up.

Architectural decision (settled): the incoherent groups G, H, (G×H)' and the Hida family will be **axiomatised as type-class hypotheses** in the initial stubs; concrete constructions come in later phases. The p-adic L-function is axiomatised from [Dis/b] and never re-proved in this project.

## Open strategic questions

- What is the correct Lean type for the Hida family \(\mathscr{X}\): a formal spectrum (`PrimeSpectrum (HeckeAlgebra ...)`) or an abstract `p`-adic analytic family parameterised by a weight space?
- Should Nekovář Selmer complexes be built on derived categories (requiring `Mathlib.Algebra.Homology.DerivedCategory`) or axiomatised as abstract functors satisfying their key properties?
- For Theorem B, which sub-result requires the most new Lean infrastructure: the toric period integrals, the Bloch-Kato exponential comparison, or the Galois cohomology input?

## Mathlib gaps & new material

**Gaps to fill:**
- Arithmetic Galois cohomology for number fields with Selmer conditions and local Tate duality (ABSENT from Mathlib — `GroupCohomology.Basic` covers abstract groups only)
- Iwasawa algebra ℤ_p⟦Γ_F⟧ and modules over it (ABSENT from Mathlib; `RingTheory.AdicCompletion` insufficient)
- Completed tensor product \(\hat\otimes_{\mathbf{Z}_p}\) of topological rings/modules
- Shimura varieties for (G×H)' with towers, Hecke correspondences, canonical models
- Ordinary eigenvariety (Hida family) for (G×H)'
- Arithmetic theta lift from GU(1) to G (Heegner class construction)
- Toric period integrals at finite and infinite places

**New project material:**
- Incoherent quaternion algebra **B** over **A**_Q with specified ramification Σ
- Nekovář Selmer complexes \(\widetilde{H}^i_f(E, V)\) and the height pairing
- Universal Heegner class \(\mathscr{P}_{K^p} \colon \Pi^{K^p,\mathrm{ord}}_{H_\Sigma}\to\widetilde{H}^1_f(E,\mathscr{V})\)
- p-adic interpolation operator \(\gamma^{\mathrm{ord}}_{H'}\) at \(p\infty\)
- Control theorems: Selmer groups vary coherently over the Hida family (Iwasawa-theoretic control)
