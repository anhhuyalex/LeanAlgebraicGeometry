# Strategy

## Goal

Formalize **Theorem: There is no Enriques surface over the integers** (Schröer, arXiv:2004.07025 / MR4513142): the fiber category \(\mathcal{M}_{\mathrm{Enr}}(\mathbb{Z})\) is empty, i.e., there is no smooth proper family of Enriques surfaces over \(\mathrm{Spec}(\mathbb{Z})\).

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|-------------------|-------|
| Blueprint elaboration | ACTIVE | 2–3 | — | — | 15 sections; Sections 3–14 not yet blueprinted |
| Conditional proof skeleton (sorry-axiomed stubs for all gaps) | NEXT | 3–5 | ~200–400 | `AlgebraicGeometry.Scheme`, scheme morphisms | Clarifies which gaps are load-bearing |
| Axiom: exceptional Enriques (cite [Schröer 2021b], Thm 7.2) | NEXT | 1 | ~50 | — | External citation; sorry-axiom until companion paper formalized |
| Axiom: Fontaine/Abrashkin Hodge-number restriction | NEXT | 1 | ~50 | — | Not in Mathlib; sorry-axiom with tracking comment |
| Defs: Enriques surface, Picard scheme (Artin representability) | NEXT | 5–10 | ~400–600 | Algebraic spaces not in Mathlib | Picard scheme representability is the hardest item |
| Defs: étale group schemes, Galois cohomology H¹(k,P) | NEXT | 5–8 | ~300–500 | GroupCohomology (abstract groups only) | Galois cohomology for group schemes not in Mathlib |
| Sections 1–2: local systems of numerical classes + contractions | NEXT | 5–8 | ~300–500 | Picard groups, étale schemes | Depends on Galois cohomology |
| Sections 3–5: curves of canonical type, families | NEXT | 5–10 | ~500–800 | Genus-one fibrations | New material; not in Mathlib |
| Sections 6–9: rational elliptic surfaces, point counting, Jacobian | NEXT | 10–15 | ~600–1000 | Weil conjectures (partial), Mordell–Weil | Weil conjectures for surfaces missing in Mathlib |
| Sections 10–11: classification + possible configurations | NEXT | 8–12 | ~600–1000 | Weierstrass models over 𝔽₂[t] | 11 explicit Weierstrass equations |
| Sections 12–13: elimination of I₄* and III* fibers | NEXT | 6–10 | ~400–600 | — | Combinatorial; many subcases |
| Section 14: restricted configurations | NEXT | 5–8 | ~300–500 | — | Combinatorial analysis of pairs of fibrations |
| Section 15: main theorem assembly | NEXT | 3–5 | ~100–200 | — | Depends on all prior phases |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|-------|----------------------|-----|-------|-------------|---------------------|----------|
| Init | 001 · 1 | 0 | Basic.lean | Empty stubs | — | — |

## Routes

**Chosen route: Conditional-proof-first (strongly recommended).** The strategy-critic identified that following the paper bottom-up without first building the proof skeleton risks investing in infrastructure that is not on the critical path. The adopted approach:
1. Build sorry-axiomed stubs for all 15 theorem/lemma declarations immediately (the proof skeleton).
2. Identify which sorry-axioms are truly load-bearing vs. potentially avoidable.
3. Work backwards, eliminating sorries in dependency order.
4. For Picard scheme representability and Galois cohomology H¹: consider upstreaming to Mathlib as the project progresses; track as named sorry-axioms until then.

**Explicit sorry-axiom tracking (4 items — must eliminate before project is done):**
- `[SORRY-AXIOM A1]` — Exceptional Enriques surfaces: citing [Schröer 2021b], Thm 7.2. Elimination path: formalize the relevant fragment of that companion paper, or find the result in Mathlib.
- `[SORRY-AXIOM A2]` — Fontaine/Abrashkin Hodge-number restriction: no smooth proper scheme over ℤ with \(h^{i,j} \neq 0\) for \(i \neq j\), \(i+j \leq 3\). Elimination path: formalize [Fontaine 1993] fragment or [Abrashkin 1990] fragment; this is a deep p-adic Hodge theory result.
- `[SORRY-AXIOM A3]` — Picard scheme representability (Artin 1969, Thm 7.3): the Picard functor of a flat proper algebraic space is representable. Elimination path: formalize Artin representability for this setting; candidate for Mathlib PR.
- `[SORRY-AXIOM A4]` — Galois cohomology H¹(k, P) for group schemes P over a field k (including norm maps and finite-order cohomology classes). Elimination path: build the required fragment inside the project; candidate for Mathlib PR under `GroupCohomology`.

## Open strategic questions

- Should Picard scheme representability (A3) and Galois cohomology (A4) be upstreamed to Mathlib as standalone PRs, or built inside the project? Decision deferred until the proof skeleton confirms they are load-bearing.
- How to organize the 15 sections into Lean files beyond the current stub (currently one file)?
- Are Weierstrass models over \(\mathbb{F}_2[t]\) and their classification in Mathlib? (Probably not.)

## Mathlib gaps & new material

**Gaps to fill (sorry-axioms A1–A4 above, plus):**
- Genus-one fibrations (elliptic + quasielliptic) and Kodaira classification
- Weil conjectures for surfaces (partial in Mathlib — Riemann hypothesis for curves present)

**New project material:**
- `Num_{X/k}` — local system of numerical classes
- `IsEnriquesSurface` — Enriques surface over a field or algebraically closed field
- `IsFamilyOfEnriquesSurfaces` — family over a ring
- `HasConstantPicardScheme` — constant Picard scheme condition
- `IsExceptionalEnriquesSurface` — Ekedahl–Shepherd-Barron exceptional condition
