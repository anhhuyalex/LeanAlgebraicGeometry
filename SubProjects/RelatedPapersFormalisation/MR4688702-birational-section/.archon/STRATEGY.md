# Strategy

## Goal

Formalize the three main theorems from MR4688702 (Bresciani, "On the birational section conjecture with strong birationality assumptions", arXiv:2108.13397):

- **Theorem A**: Let X be a smooth curve over a field k finitely generated over Q. A Galois section of X is geometric or cuspidal if and only if it is t-birationally liftable.
- **Theorem B**: For a hyperbolic curve X over k finitely generated over Q, the following are equivalent: (i) for every finitely generated K/k every Galois section of X_K is geometric or cuspidal; (ii) for every finitely generated K/k every Galois section of X_K is birationally liftable. As a consequence, the section conjecture is equivalent to the cuspidalization conjecture.
- **Theorem C**: The birational section conjecture is equivalent to an interpolation property: for every number field k, every z ∈ S_{k(P^1)/k} and every open U ⊆ P^1, there exists open V ⊆ U and a π_1-section r of U×V\Δ → V such that r_v = ι_{U\{v}}(z) for all v ∈ V(k).

All declarations live in `MR4688702OnTheBirationalSectionConjectureWithStrongBirationalityAssumptions/Basic.lean`.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|------------------|-------|
| Blueprint | COMPLETE | 0 | N/A | None | Done: 38 DAG nodes, 66 edges, 0 ∞ — COMPLETE iter-002 |
| Axiom layer | ACTIVE | 2–3 | ~100–200 | None | References now available; 3 citation/reference clean-up items first |
| Foundations | PLANNED | 3–5 | ~300–500 | `AlgebraicGeometry`, `NumberField`, `DVR` | Étale fund. groups absent from Mathlib |
| Specialization | PLANNED | 5–8 | ~500–800 | `DVR` theory, profinite groups | Gerbes, root stacks, specialization absent |
| Main argument (A-path) | PLANNED | 4–6 | ~400–600 | Local fields, `Hilbert.Irreducibility` | Mattuck absent; Stix Thm B absent |
| Main argument (C-path) | PLANNED | 3–5 | ~300–400 | Hilbert irreducibility | Parallel to A-path once step 8 done |
| Main theorems | PLANNED | 2–3 | ~150–250 | — | Thin once A/B/C-path steps are done |

## Routes

### Route: Pure-axiom skeleton with proved implications

**Summary**: Every piece of missing Mathlib infrastructure (étale fundamental gerbes, infinite root stack, profinite fundamental group, Galois sections, specializing loops) is declared as a proper Lean 4 `axiom` with a mathematically correct type signature verified against the paper and cited references. All 18 critical-path declarations are then proved as genuine Lean `theorem`/`lemma`/`def` statements from those axioms — **no `sorry` appears in any proof body**. The final file has a bounded, explicit axiom list at the top, followed by closed proofs.

**Why pure-axiom and not sorry-bodies**: `sorry` in a definition body makes the defined term reduce to any type, so downstream proofs become trivially admissible regardless of whether they reflect the paper's logic. Proper `axiom` declarations force the prover to write type-correct logical derivations; Lean's kernel then verifies the logical skeleton is genuinely connected. This is more honest and more reusable: a future Mathlib PR replacing `axiom FamiliesExactSeq` with a proof produces a fully closed formalization at no cost.

**Critical logical path** with formalization class:
- **(A)** = will be proved as a genuine theorem from axioms
- **(AX)** = proper `axiom` declaration (missing Mathlib infrastructure)
- Steps annotated; no step is `sorry`

| # | Name | Class | Depends on | Key external fact |
|---|------|-------|------------|------------------|
| 1 | `FamiliesExactSeq` | AX | — | SGA1, exact seq for π₁ of curve family in char 0 |
| 2 | `RelGerbeLimit` | AX | 1 | Bresciani-Vistoli, arXiv:1404.7475 §3 |
| 3 | `ProrootValCrit` | AX | 2 | Bresciani-Vistoli valuative criterion (companion paper — **must retrieve**) |
| 4 | `SpecLoop` (def) | AX | 2 | Bresciani-Vistoli gerbe morphism construction |
| 5 | `UniqueLoopTorus` | AX | 4 | Mattuck's theorem + valuation finiteness argument |
| 6 | `UniqueLoopCurve` | A | 5 | Follows from 5 via Jacobian + Mattuck |
| 7 | `SpecBirat` | A | 4 | Formal from definition of b.l. + spec |
| 8 | `TBiratBirat` | A | 7 | Specialization at t=0 |
| 9 | `SpecTBirat` | A | 7, 8 | Stability of t-b.l. under specialization |
| 10 | `NFLift` | A | 6, 9 | Uses Stix Thm B (AX) + UniqueLoopCurve |
| 11 | `SimpleProp` | A | 3, 6, 10 | Key local-global argument |
| 12 | `NFFG` | AX | — | Tamagawa + Saidí-Tyler reduction (transcendence deg induction) |
| 13 | `TheoremA` | A | 11, 12 | Formal combination |
| 14 | `CuspBL`, `CuspBL2` | A | 7 | Formal from definition of cuspidal |
| 15 | `HilbertSections` | A | 2 | Hilbert irreducibility (AX) + proj limit finiteness |
| 16 | `TheoremB` | A | 13, 14 | Formal combination |
| 17 | `BiratEquiv` | A | 7 | Formal from BSC definition |
| 18 | `TheoremC` | A | 11, 15, 17 | Formal combination |

**Parallel lanes**: Once steps 7–8 (`SpecBirat`, `TBiratBirat`) are in place, the A-path (steps 9–13) and the C-path (steps 14–18, i.e., `CuspBL` → `CuspBL2` → `HilbertSections` → `BiratEquiv` → `TheoremC`) are **logically independent** and can be dispatched as parallel prover lanes in the same iteration.

**Minimum axiom set** (declarations with class AX above):
- `FamiliesExactSeq`: exact sequence `π₁(X_s) → π₁(X) → π₁(S) → 1` for a proper smooth curve family with section (SGA1 XIII 4.3)
- `RelGerbeLimit`: `Π_{X/S} = lim_{i} Φᵢ` as a cofiltered limit of proper étale gerbes (Bresciani-Vistoli arXiv:1404.7475 §3)
- `ProrootValCrit`: generic section extends over infinite root stack (Bresciani-Vistoli companion paper — **statement pending retrieval**)
- `SpecLoop`: the specializing loop `γ_z(c)` as a morphism of gerbes `BẐ → π₁(Xₛ)` (Bresciani arXiv:2108.13397 §2)
- `UniqueLoopTorus`: loop constancy for tori from valuation argument (Mattuck, Theorem 2 in p-adic Lie groups paper)
- `StixThmB`: Dirichlet density result for non-integral local points (Stix, Theorem B)
- `NFFG`: Tamagawa's étale-neighborhood proposition + Saidí-Tyler reduction to number fields
- `HilbertIrred`: Hilbert irreducibility theorem (present in Mathlib in some form; to be checked iter-002)

## Open strategic questions

- **RESOLVED (iter-001)**: axioms-vs-sorry → **pure-axiom approach adopted** (see route description above).
- **RESOLVED (iter-002)**: Bresciani-Vistoli valuative criterion paper identified and retrieved as `bv23-valuative` (arXiv:2210.03406, Theorem 3.1). The companion fundamental gerbe papers are also retrieved: `bv15-nori-gerbe` (arXiv:1204.1260) and `bv19-fund-gerbes` (arXiv:1610.07341). Note: the IDs 1404.7475 and 1412.7523 in earlier notes were **WRONG** — they belong to unrelated papers.
- **OPEN**: Confirm whether Hilbert's irreducibility theorem is available as `Mathlib.FieldTheory.Hilbert` or similar. Check in iter-002 before writing the `HilbertSections` proof.

## Mathlib gaps & new material

**Absent from Mathlib (need `axiom` declarations):**
- Profinite étale fundamental group of a curve as a profinite group — SGA1 reference needed; `Mathlib.Topology.Algebra.Profinite.Basic` has profinite group theory but no link to schemes
- Étale fundamental gerbes (Borne-Vistoli, arXiv:1204.1260 §8 and arXiv:1610.07341)
- Infinite root stack construction (Talpo-Vistoli, arXiv:1410.1164)
- Non-unique specialization of Galois sections via infinite root stacks
- Tamagawa's étale-neighborhood proposition (Tamagawa 1997, Proposition 2.8(iv))
- Koenigsmann's birational section conjecture over local fields
- Stix's Theorem B (Dirichlet density of non-integral local points)
- Saidí-Tyler reduction (BSC for NF implies BSC for f.g. extensions; arXiv:2109.05276 Theorem C)
- Mattuck's theorem (torsion finiteness in p-adic Lie groups)

**In Mathlib (verified or likely):**
- DVR theory: `Mathlib.RingTheory.DiscreteValuationRing.Basic` — VERIFIED
- Profinite group infrastructure: `Mathlib.Topology.Algebra.Profinite.Basic` — VERIFIED (but no scheme fundamental group link)
- Projective limits of topological groups: `Mathlib.Topology.Algebra.Group.Basic` (general) — VERIFIED
- Number fields and completions: `Mathlib.NumberTheory.NumberField` — VERIFIED
- Hilbert's irreducibility theorem: `Mathlib.FieldTheory.Hilbert` or similar — **to verify iter-002**

**Absent for stated purpose:**
- Tate modules of abelian varieties (Jacobians): **not in Mathlib**. `Mathlib.AlgebraicGeometry.EllipticCurve.*` covers elliptic curves but does not contain Tate modules of general abelian varieties. The `UniqueLoopCurve` proof via Mattuck requires the Jacobian Tate module; this is fully absent and must be `axiom`-ized.
