# Strategy

## Goal

Formalize the main purity theorem for flat cohomology (Cesnavicius–Scholze, MR4681144): for a Noetherian local complete intersection ring \((R, \mathfrak{m})\) and a commutative finite flat \(R\)-group scheme \(G\), the flat cohomology \(H^i_{\mathfrak{m}}(R, G) = 0\) for \(i < \dim(R)\). As corollaries, establish Gabber's conjectures: torsion \(\mathrm{Pic}(U_R) = 0\) for CI of \(\dim \ge 3\), and \(\mathrm{Br}(R) \cong \mathrm{Br}(U_R)\) for CI of \(\dim \ge 4\).

**Route decision (iter 001)**: Pursue both tracks in parallel. Track A targets the positive-characteristic special case (regular or LCI \(\mathbb{F}_p\)-algebra) avoiding animated rings and arc topology; Track B builds toward the full theorem. Track A produces meaningful results sooner; Track B produces the stated goal.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|-------------------|-------|
| Blueprint elaboration | ACTIVE | 1–2 | ~0 | — | Large mathematical scope |
| [A] Complete intersection predicate + fppf flat cohomology with supports | NEXT | 10–20 | ~800–1500 | `AlgebraicGeometry.Sites.Fppf` (exists), `LocalCohomology` (module-theoretic exists) | Must build sheaf-cohomology-with-supports in fppf topology from scratch; no `GroupScheme` or `AlgebraicGeometry.Cohomology` in Mathlib |
| [A] Finite flat group schemes over a ring | NEXT | 8–15 | ~600–1200 | `Mathlib.AlgebraicGeometry.Sites.Fppf` | No `GroupScheme` typeclass in Mathlib; must build from commutative Hopf algebras |
| [A] Crystalline Dieudonné theory (positive char.) | NEXT | 20–35 | ~2000–4000 | Witt vectors (`WittVector`), `PerfectClosure` | Very large; needed for positive-characteristic key formula; no existing Mathlib formalization |
| [A] Purity for smooth/regular \(\mathbb{F}_p\)-LCI (Track A goal) | NEXT | 10–15 | ~800–1500 | depends on above | Requires crystalline Dieudonné theory; no arc topology or animated rings needed |
| [B] Perfectoid rings (integral, \(\mathbb{Z}_p\)-algebras) | NEXT | 20–35 | ~2000–4000 | `RingTheory.Perfectoid.Untilt` (exists, partial) | No `PerfectoidRing` definition in Mathlib; scope comparable to Lean perfectoid project |
| [B] Arc topology and p-complete arc covers | NEXT | 10–20 | ~1000–2000 | `AlgebraicGeometry.Sites` | Encoding: define arc cover as a map of rings where every rank-1 valuation ring over a point of Spec(A) lifts; build arc sheaves as a Grothendieck topology; no Mathlib formalization |
| [B] Simplicial commutative rings & derived quotients | NEXT | 15–25 | ~1500–3000 | `Mathlib.AlgebraicTopology.SimplicialObject` | Encode animated rings as simplicial commutative rings (no ∞-category quotienting needed for the algebraic statements); derived tensor product \(A \otimes^{\mathbf{L}}_{\mathbb{Z}[X]} \mathbb{Z}\) via explicit simplicial resolution |
| [B] p-adic continuity & excision for simplicial rings | NEXT | 10–15 | ~800–1500 | depends on simplicial ring phase | Follows from positive-characteristic key formula and animated deformation theory |
| [B] Prismatic Dieudonné theory for perfectoids | NEXT | 30–50 | ~4000–8000 | — | Largest single gap; required for arc descent and the general key formula; may need to wait for upstream Mathlib development or be done as a standalone sub-project |
| [B] Arc descent + perfectoid purity | NEXT | 15–25 | ~1500–3000 | depends on arc topology + prismatic | Requires both arc topology and prismatic Dieudonné theory |
| [B] André's lemma + main LCI reduction (full theorem) | NEXT | 10–20 | ~1000–2000 | depends on all B phases | Final reduction; straightforward once perfectoid purity is established |
| Gabber conjectures corollaries | NEXT | 5–10 | ~400–800 | `Mathlib.Algebraic.BrauerGroup` (partial?) | Follows from main theorem (or Track A result for char-\(p\) case) |

## Routes

**Track A — positive characteristic special case** (actionable now): Prove purity for regular/LCI \(\mathbb{F}_p\)-algebras using crystalline Dieudonné theory (positive-characteristic key formula). No arc topology, no animated rings, no perfectoid rings needed. Milestones: (i) fppf flat cohomology with supports; (ii) finite flat group schemes; (iii) crystalline Dieudonné theory and key formula; (iv) purity for LCI \(\mathbb{F}_p\)-algebras.

**Track B — full theorem** (long-term): Extend to mixed characteristic via perfectoid rings, arc topology, prismatic Dieudonné theory, and simplicial ring deformation theory. Track B reuses all Track A infrastructure. Milestones after Track A: (v) perfectoid rings; (vi) arc covers and arc sheaves; (vii) simplicial commutative rings + derived quotients; (viii) prismatic Dieudonné theory; (ix) perfectoid purity and arc descent; (x) André's lemma reduction.

## Open strategic questions

- When should Track B prismatic Dieudonné theory begin — in parallel with Track A or only after Track A is complete?
- Should the project coordinate with or wait for upstream Mathlib formalization of perfectoid rings (Lean Perfectoid Project successor efforts)?

## Mathlib gaps & new material

**Gaps (must build from scratch — confirmed missing in Mathlib 4.30.0):**
- `CompleteIntersectionLocalRing` predicate (no Mathlib entry)
- fppf flat cohomology with supports \(H^i_Z(X, G)\) (module-theoretic `LocalCohomology` exists but fppf sheaf version absent)
- Commutative finite flat group schemes / `GroupScheme` typeclass (only morphism properties exist)
- `PerfectoidRing` definition (only period rings `BDeRham`, `FontaineTheta`, `Untilt` in Mathlib)
- Arc topology / arc covers (no Mathlib entry)
- Prismatic Dieudonné theory (no Mathlib entry)

**New project material:**
- `FlatCohomologyWithSupport`: sheaf-cohomology-with-supports in fppf topology
- `PurityForFlatCohomology`: the main theorem (Track A: char-\(p\) case; Track B: full)
- `GabberConjecture_TorsionPic`, `GabberConjecture_BrauerPurity`: the two corollaries
