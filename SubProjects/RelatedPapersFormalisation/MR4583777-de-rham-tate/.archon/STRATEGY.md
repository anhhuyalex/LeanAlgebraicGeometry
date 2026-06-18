# Strategy

## Goal

Formalize the main theorem of Hilburn--Raskin (arXiv:2107.11325, MR4583777):
the canonical equivalence of DG categories
\[
  \Delta : D^!(\mathfrak{L}\mathbb{A}^1) \simeq \mathsf{IndCoh}^*(\mathcal{Y})
\]
where \(\mathfrak{L}\mathbb{A}^1\) is the algebraic loop space of \(\mathbb{A}^1\)
and \(\mathcal{Y}\) is the moduli of rank 1 de Rham local systems on the
punctured formal disc with a flat section, compatible with the Beilinson–Drinfeld
local class field theory action (Thm 1.1.0.1 = Thm 8.4.0.1).

**Infrastructure note.** The goal requires a `DGCat` type in Lean 4 (to state
"equivalence of DG categories"). No such type exists in Mathlib. Near-term
Phases 3B–5 therefore proceed axiomatically (Route B): introduce a `DGCat`
typeclass with the properties the paper uses, state and prove the equivalence
modulo those axioms, and verify the axioms as Lean/Mathlib matures.
The core concrete content — Weyl algebra modules \(W_n\text{-}\mathrm{mod}\),
truncated equivalences \(\Delta_n\), and the algebra of \(\mathcal{Y}\) — is
formalized unconditionally in parallel (Route A, Steps 1–4 and Route A', below).

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|------------|-----|-------------------|-------|
| 1. Blueprint | ACTIVE | 1 | ~0 | none | 77-page paper |
| 2. Scaffold | PLANNED | 2–3 | ~400–700 | none | axiom interface design |
| 2A. DGCat axioms + stack-quotient stubs | PLANNED | 1–2 | ~200–400 | none | interface must match paper's DGCat uses |
| 3A. Loop spaces, LocSys, Y, flatness | PLANNED | 4–8 | ~600–1500 | `PowerSeries` | stack-quotient stubs from 2A; parallelizable with 3B-i, 3C-i |
| 3B-i. Coh ⊂ QCoh on affine derived schemes | PLANNED | 2–3 | ~300–600 | none | t-structure needed; parallelizable with 3A |
| 3B-ii. Ind-completion of DG category | PLANNED | 2–4 | ~400–800 | DGCat axioms (2A) | filtered colimit in DGCat |
| 3B-iii. t-structure + Ψ-equivalence | PLANNED | 2–4 | ~400–800 | 3B-i, 3B-ii | Ψ: IndCoh*(S)^+ ≃ QCoh(S)^+ |
| 3B-iv. Semi-coherence; IndCoh*(Y) | PLANNED | 2–4 | ~400–800 | 3B-ii, 3B-iii, 3A | IndCoh*(Y) = lim_n IndCoh*(Z^≤n) |
| 3C-i. Weyl algebra W_n as k-algebra | PLANNED | 1–2 | ~150–300 | `Mathlib.RingTheory` | W_n = D(A^n); parallelizable with 3A, 3B-i |
| 3C-ii. W_n-mod as DG module category | PLANNED | 2–3 | ~300–600 | DGCat axioms (2A) | filtered colimit W_n-mod → W_{n+1}-mod |
| 3C-iii. D^!(LA^1) = colim_n W_n-mod | PLANNED | 1–2 | ~150–300 | 3C-ii | colimit in DGCat |
| 4. Truncated equivalence Δ_n (spectral realization) | PLANNED | 4–8 | ~600–1500 | 3B-iii, 3C-ii | W_n^op ≅ End(F_n); Morita theory |
| 5. Main equivalence (full faithfulness + ess. surj.) | PLANNED | 5–10 | ~800–1500 | all prior | §7+§8; colimit passage Δ = colim Δ_n |

## Routes

### Route A: Concrete algebra first (Steps 1–4; primary, unconditional)

These steps formalize the paper's accessible algebra without DGCat infrastructure.

**Step 1 — Power series algebra.** Use Mathlib's `PowerSeries` ring for
\(k[[t]]\), \(k[[t]]/t^n\), \(k((t))\). The truncated loop space
\(\mathfrak{L}^+_n\mathbb{A}^1 \cong \mathbb{A}^n\) is the key concrete object.

**Step 2 — Flatness.** Prove \(\mu_n : \mathbb{A}^{2n} \to \mathbb{A}^n\)
(truncated convolution) is flat (Lem 2.6.1.1). Pure commutative algebra.

**Step 3 — Weyl algebra.** Define \(W_n\) as the explicit \(k\)-algebra with
generators \(x_0,\ldots,x_{n-1}, \partial_0,\ldots,\partial_{n-1}\) and
canonical commutation relations; i.e.\ \(W_n = D(\mathbb{A}^n)\) as a
finitely-presented \(k\)-algebra via Mathlib's `Algebra.NonCommRing`.

**Step 4 — LocSys and Y (using stack-quotient stubs from Phase 2A).**
Define \(\mathrm{LocSys}_{\mathbb{G}_m}\), \(\mathcal{Y}'\), \(\mathcal{Y}\),
and \(\mathcal{Z}^{\leq n}\) using the axiomatized stack-quotient type from 2A.
Prove \(\mathcal{Y}\) classical (Thm 2.4.3.1) and \(\mathcal{Z}^{\leq n}\)
algebraic (Prop 2.5.3.1).

### Route A': Axiomatic categorical scaffold (Steps 5–8; required for goal)

The DGCat gap blocks stating the goal unconditionally. Route A' axiomatizes the
categorical layer and proves the equivalence modulo those axioms.

**Step 5 — DGCat typeclass.** Phase 2A introduces:
- `DGCat`: a typeclass (or axiomatized structure) for a DG category with
  morphism complexes, composition, identity, shift, cone, and a `cont` flag for
  continuous functors;
- `StackQuot`: axiom for quotient of an ind-scheme by an ind-group (used by
  LocSys and Y).

**Step 6 — W_n-mod in DGCat.** Phase 3C-ii: endow \(W_n\text{-}\mathrm{mod}\)
with the DGCat structure from Step 5. This is the correct framing for the LHS
\(D^!(\mathfrak{L}\mathbb{A}^1) = \varinjlim_n W_n\text{-}\mathrm{mod}\) —
**not** general D-module theory on ind-schemes (the paper uses only Weyl algebra
module categories; no ind-scheme D-module formalism is needed).

**Step 7 — IndCoh\* in DGCat.** Phase 3B-ii–iv: define \(\mathrm{Coh}(S)\),
\(\mathsf{IndCoh}^*(S) = \mathrm{Ind}(\mathrm{Coh}(S))\), t-structures,
\(\Psi\) equivalence, semi-coherence, and \(\mathsf{IndCoh}^*(\mathcal{Y})
= \varprojlim_n \mathsf{IndCoh}^*(\mathcal{Z}^{\leq n})\).

**Step 8 — Truncated equivalences \(\Delta_n\).** Phase 4: prove the spectral
realization \(W_n^{op} \xrightarrow{\sim}
\underline{\mathrm{End}}_{\mathsf{IndCoh}^*(\mathcal{Z}^{\leq n})}(\mathcal{F}_n)\)
(§5). Each \(\Delta_n : W_n\text{-}\mathrm{mod} \simeq
\mathsf{IndCoh}^*(\mathcal{Z}^{\leq n})\) is a Morita equivalence between
finitely-presented algebra module categories — provable via 1-categorical
Morita theory with DGCat axioms.

**Step 9 — Main equivalence.** Phase 5: full faithfulness from the truncated
equivalences (§7); essential surjectivity via classicality of \(\mathcal{Y}\)
and generation arguments (§8); then the colimit/limit passage
\(\Delta = \varinjlim_n \Delta_n\).

### Route B: Conditional result (rejected as standalone; components adopted in A')

Axiomatize the full DGCat layer and prove the equivalence modulo axioms.
The components of Route B are now embedded in Route A' (Steps 5–9) rather
than treated as a separate fallback. The distinction from a pure Route B is
that Route A (Steps 1–4) formalizes as much unconditionally as possible.

## Open strategic questions

1. **DGCat typeclass design.** What axioms are sufficient for the paper's uses?
   Minimum: morphism complexes, shift, cone, t-structure, Ind-completion, and
   continuous-functor notion. Plan: design the typeclass in Phase 2A by reading
   the paper's categorical uses bottom-up.

2. **Stack-quotient stubs.** LocSys and Y are quotients of ind-schemes by
   ind-groups. No Lean 4 / Mathlib infrastructure exists for this. Plan: Phase 2A
   introduces `StackQuot` axioms; \(\mathcal{Z}^{\leq n}\) (a finite-type
   algebraic stack) is later verified against the axiom once Mathlib's algebraic
   stack library matures.

3. **QCoh as DG 2-functor (phantom).** Mathlib has per-scheme `QCoh` categories
   but NOT QCoh as a continuous DG 2-functor Sch → DGCat_cont. The
   \(\Psi : \mathsf{IndCoh}^*(S)^+ \simeq \mathsf{QCoh}(S)^+\) bridge
   (Lem 4.2.1.2) is a DG-categorical statement; until DGCat axioms exist, Ψ
   is provable only modulo those axioms. No stopgap: the QCoh-as-bridge approach
   assumed in the prior version of this strategy was a phantom prerequisite.

4. **Phases 3A + 3C-i can start immediately.** Loop spaces (via `PowerSeries`)
   and \(W_n\) (via Mathlib's non-commutative ring theory) do not require DGCat
   axioms and can be dispatched as soon as Phase 2 scaffold is ready.

## Mathlib gaps & new material

| Gap | Needed for | Status |
|-----|-----------|--------|
| DGCat typeclass (DGCat_cont) | Phase 2A, 3B–5 | Missing; build in Phase 2A |
| Algebraic stack quotient by ind-group | Phase 2A, 3A | Missing; axiomatize in Phase 2A |
| IndCoh* (Ind-completion of DG cat) | Phase 3B-ii–iv | Missing; build in 3B-ii |
| t-structures on DG categories | Phase 3B-iii | Missing; build in 3B-iii |
| W_n as finitely-presented k-algebra | Phase 3C-i | Missing; accessible via Mathlib NonCommRing |
| W_n-mod as DG module category | Phase 3C-ii | Missing; build after DGCat in Phase 2A |
| Loop spaces as algebraic ind-schemes | Phase 3A | Partial (PowerSeries ring present) |
| Moduli stacks LocSys, Y, Z^≤n | Phase 3A | Missing; requires stack-quotient stubs |
| Semi-coherent algebras | Phase 3B-iv | Missing; build in Phase 3B-iv |
| QCoh as continuous DG 2-functor | Phase 3B-iii | Missing; NOT a usable stopgap |
