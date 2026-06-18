# Strategy

## Goal

Formalize the statements of the four main theorems of de Cataldo–Maulik–Shen (arXiv:1909.11885): P=W for genus 2 (Thm 1), P=W for even tautological classes (Thm 2), perversity of odd tautological classes (Thm 3), and the equivalence P=W ↔ multiplicativity (Thm 4). All four must appear as type-correct Lean declarations (sorry bodies acceptable where infrastructure is missing).

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|-------------------|-------|
| Blueprint — write full Overview chapter | ACTIVE | 0 (done this iter) | ~0 | none | — |
| Scaffolding — all type stubs + theorem decls | NEXT | 3–5 | ~300–500 | Scheme morphisms, proper maps | All 9 type stubs needed before any theorem decl |
| Definitions — fill sorry on definitions | NEXT | 5–10 | ~400–800 | AlgebraicGeometry.Morphisms, sheaf cohomology | Perverse sheaves, MHS not in Mathlib; axiomatize |
| Theorems (parallel lanes 1–4) | NEXT | 10+ | ~500–1500 | Decomp theorem, non-abelian Hodge | Very deep; most remain sorry indefinitely |

## Routes

Single route for Blueprint and Scaffolding phases. Once the common scaffold exists, the four theorem proof lanes (Thm 1 genus-2 P=W; Thm 2 even tautological; Thm 3 odd tautological; Thm 4 multiplicativity equivalence) are mutually independent and should be dispatched as parallel prover agents.

## Open strategic questions

- **axiom vs def+sorry**: For all axiomatized infrastructure (`PerverseFiltration`, `WeightFiltration`, `CharacterVariety`, `DolbeaultModuli`, `NonabelianHodgeDiffeo`, `MixedHodgeStructure`), prefer `noncomputable def ... := sorry` over bare `axiom` for blueprint visibility and easier later filling.
- How much of the moduli space geometry (Higgs bundles, character variety fibrations) can realistically be stated in Lean given current Mathlib?

## Mathlib gaps & new material

**Gaps (not in Mathlib):**
- Perverse $t$-structure / perverse sheaves / decomposition theorem
- Mixed Hodge structures and weight filtration
- Non-abelian Hodge diffeomorphism (Simpson)
- Moduli of Higgs bundles / stable sheaves on surfaces

**New project material (all required before Scaffolding):**
- `HitchinModuliDol` — Dolbeault moduli space M_Dol (axiom/sorry-def)
- `CharacterVariety` — Betti moduli space M_B (axiom/sorry-def)
- `NonabelianHodgeDiffeo` — Simpson diffeomorphism M_Dol ≅ M_B (axiom/sorry-def)
- `PerverseFiltration` — perverse filtration for a proper morphism (sorry-def)
- `WeightFiltration` — weight filtration on H*(M_B) from MHS (sorry-def)
- `HodgeTateDecomp` — Hodge–Tate pieces of H*(M_B) (sorry-def)
- `TautologicalClass` — tautological classes c(γ,k) via twisted Chern char push-forward
- `HitchinFibration` — Hitchin map M_Dol → Λ
- `taut_abelian_splitting` — splitting theorem for abelian surface moduli
