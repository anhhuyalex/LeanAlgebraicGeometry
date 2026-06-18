# Strategy

## Goal

Formalize **Theorem 1.1** (Higher Siegel–Weil formula for unitary groups, non-singular terms) from
Feng–Yun–Zhang [MR4689373, arXiv:2103.11514] as a **sorry-free Lean 4 proof**:

> Let \(n \geq 1\) and \(r \geq 0\). Let \(\mathcal{E}\) be a rank \(n\) vector bundle on \(X'\)
> and \(a : \mathcal{E} \to \sigma^*\mathcal{E}^\vee\) be an injective Hermitian map. Then
>
>   \(\frac{1}{(\log q)^r}\bigl(\frac{d}{ds}\bigr)^r\big|_{s=0}\bigl(q^{ds}\widetilde{E}_a(m(\mathcal{E}),s,\Phi)\bigr)
>   = \deg[\mathcal{Z}_{\mathcal{E}}^r(a)]\)
>
> where \(d = -\deg(\mathcal{E}) + n\deg\omega_X = -\chi(X',\mathcal{E})\).

Here \(X'/X\) is an étale double cover of a smooth projective curve over \(\mathbf{F}_q\) (\(\mathrm{char} \neq 2\)),
\(\widetilde{E}_a(m(\mathcal{E}),s,\Phi)\) is the normalized non-singular Fourier coefficient of the
Siegel–Eisenstein series, and \([\mathcal{Z}_{\mathcal{E}}^r(a)] \in \mathrm{Ch}_0(\mathcal{Z}_{\mathcal{E}}^r(a))_{\mathbf{Q}}\)
is the virtual fundamental class (degree is taken in the rationalized Chow group, axiomatized in P0).

Formalization target: `MR4689373HigherSiegelWeilFormulaForUnitaryGroupsTheNonSingularTerms/Basic.lean`.

Goal is a **full sorry-free proof** conditional on the following two **permanent P0 axioms**
(impossible to build from Mathlib; declared honestly in `archon-protected.yaml`):
- `Ch_0(𝒵_ℰ^r(a))_Q` — axiomatized in P0 as an abstract type with a degree map `deg : Ch₀ → ℚ`.
- Algebraic stack structure: `Sht_{U(n)}^r` and `𝒵_ℰ^r(a)` are axiomatized moduli stacks; Artin/DM
  stack theory is absent from Mathlib. Fallback: axiomatize stack properties as sorry-bodies; P2
  discharges what it can and escalates the rest as permanent axioms when stack infrastructure fails.

All other sorry-bodies are **temporary** and discharged across phases. Discharge plan for `Ẽ_a`:
- P0: `Ẽ_a` is a sorry-body (temporary placeholder for the Fourier coefficient).
- P1: after proving the Cho–Yamauchi formula (`Den(T, L_v, s)` = local Whittaker function), **define
  `Ẽ_a` constructively** as the formal Euler product `∏_v Den(T, L_v, s)` over all places `v`.
  This discharges the `Ẽ_a` sorry-body; the "Euler product" becomes a definition, not an axiom.
- P3b: proves the trace formula `Tr(Frob, 𝒦_d^Eis)(q^s) = Ẽ_a(m(ℰ), s, Φ)` using the
  constructive definition of `Ẽ_a`. The Euler product structure is a theorem.

All other P0 "axioms" are implemented as `noncomputable def ... := sorry` and `instance ... := sorry` —
never bare Lean `axiom` declarations. The final proof is sorry-free modulo the two permanent P0 axioms
above (Ch₀ and algebraic stack structure), which are listed in `archon-protected.yaml`.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|------------|-----|-------------------|-------|
| P0: Setup & statement | ACTIVE | ~20 | ~1500–2500 | `NumberTheory.FunctionField`, `DedekindDomain.FiniteAdeleRing`, `LinearAlgebra.UnitaryGroup` | Types absent; use axioms for stacks, Ch₀, virtual class |
| P1: Local density theory | BLOCKED | ~20 | ~1500–2500 | None (all new) | Cho–Yamauchi polynomial; new linear algebra over local fields |
| P2: Geometric side | BLOCKED | ~35 | ~3000–5000 | None (all new) | Hermitian shtukas, Ch₀ axioms, virtual cycles, good framings |
| P3a: Herm Springer theory + ℓ-adic mini-lib | BLOCKED | ~40–60 | ~4000–8000 | None (all new) | ℓ-adic perverse sheaf mini-library is critical path; ~2-year scope, build minimum needed |
| P3b: Perverse sheaves `𝒦` | BLOCKED | ~15 | ~1500–2500 | None (all new) | Objects `𝒦_d^Eis`, `𝒦_d^Int`; Frobenius trace identities |
| P3c: W_d representation theory | BLOCKED | ~10 | ~800–1200 | None (new) | Graded virtual reps of `W_d = (ℤ/2ℤ)^d ⋊ S_d`; requires P3a+P3b objects |
| P3d: Assembly | BLOCKED | ~5 | ~400–800 | None | Combine P3a–P3c to close Theorem 1.1; no new math |

**P1 ∥ P2 ∥ P3a all run in parallel** after P0's shared types are committed (none of these three
depends on the others; P3a has no dependency on P1's local density work).
**P3c requires P3a+P3b** (its plan bullets reference `Spr^{Herm}_{2d}`, `𝒦_d^Eis`, `𝒦_d^Int`).

## Routes

### Route A: Statement-first, phase-by-phase proof with axiomatized infrastructure

Formalize all type signatures and state Theorem 1.1 (with `sorry` proof) in P0, axiomatizing the
geometric objects (moduli stacks, Chow groups). Then prove in phases P1–P3d. P1 and P2 run in
parallel after P0. P3 is split into four independently-assignable sub-phases.

**Rationale**: The required infrastructure (moduli stacks of shtukas, ℓ-adic perverse sheaves,
Chow groups of stacks, automorphic forms on unitary groups) is absent from Mathlib. The entry
point is to axiomatize the geometric side (P0/P2), prove the analytic/combinatorial side (P1),
build the required sheaf-theoretic library (P3a–P3b), then close the proof (P3d).

**Lean file structure** (lean-scaffolder creates phase files; `% archon:future-covers` in chapters becomes `% archon:covers` once files exist):

| Lean file | Phase | Blueprint chapter |
|-----------|-------|-------------------|
| `…/Basic.lean` (exists) | P0+P1 | `Overview.tex` |
| `…/Geometric.lean` | P2 | `Geometric_Side.tex` |
| `…/HermitianSpringer.lean` | P3a | `Hermitian_Springer.tex` |
| `…/PerverseSheaves.lean` | P3b | `Perverse_Sheaves_K.tex` |
| `…/WdRepresentations.lean` | P3c | `Wd_Representations.tex` |
| `…/Assembly.lean` | P3d | `Assembly.tex` |

**P0 plan** (two logical lanes, both write sequentially to `Basic.lean` — see file structure table):
- *Automorphic lane*: Smooth curve `X` over `F_q` (via `NumberTheory.FunctionField`), étale double
  cover `X'`, function field `F`, adèle ring using `DedekindDomain.FiniteAdeleRing`, Hermitian forms
  `Herm_n(R, L)`, standard split skew-Hermitian space `W`, unitary group `H_n = U(W)`,
  Siegel parabolic `P_n`, degenerate principal series `I_n(s, χ)`, axiomatized `E_T`, `W_{T,v}`,
  and `Ẽ_a` (all as sorry-bodies; see `## Goal` for axiom scope).
- *Geometric lane*: Axiomatize `Sht_{U(n)}^r`, `𝒵_ℰ^r(a)`, virtual fundamental class
  `[𝒵_ℰ^r(a)] ∈ Ch₀(𝒵_ℰ^r(a))_Q`, degree map `deg : Ch₀ → ℚ`. Define `d(ℰ)`.
- State Theorem 1.1 with `sorry` proof body.

**P1 plan** (analytic; independent of P2 after P0):
- Local Hermitian lattices `L`, `M` over local field `F`; local density `Den(M, L)`.
- Cho–Yamauchi polynomial `Den(T, L)` and formula (Theorem 2.3 / §2.4 of paper).
- Verify the Cho–Yamauchi identity: `Den(T, L) = W_{T,v}` at the local level (combinatorial).
  (The global Euler product `Ẽ_a = ∏_v W_{T,v}` is an axiom from P0; P1's contribution is the
  explicit polynomial formula for each `W_{T,v}`.)

**P2 plan** (geometric; independent of P1 after P0):
- Formal definition of hermitian shtukas (chains with elementary modifications and Hermitian structures).
- Line-bundle case: `𝒵_ℒ^r(a)` has expected dimension (codim r); class `[𝒵_ℒ^r(a)]`.
- Good framing for general `ℰ`; independence of framing (§§8–10).
- Properness of `𝒵_ℰ^r(a)` for `a` injective; well-defined `deg[𝒵_ℰ^r(a)] ∈ ℚ`.
- **Algebraic stack fallback**: if Artin/DM stack foundations remain absent from Mathlib, axiomatize
  the stack properties (morphisms, torsors, fibered categories) as sorry-bodies in P2, analogously
  to P3a's perverse sheaf fallback. Trigger: progress-critic STUCK on stack infrastructure ≥2 iters.

**P3a plan** (Hermitian Springer theory + ℓ-adic mini-library; starts after P0 — runs **parallel with P1**):
- ℓ-adic perverse sheaf mini-library (critical path; sub-phases):
  - Sub-P3a-1 (~10–15 iters): Basic ℓ-adic sheaves on schemes; constructibility, pullback/pushforward.
  - Sub-P3a-2 (~10–15 iters): Direct image and derived categories; Frobenius action on cohomology.
  - Sub-P3a-3 (~10–15 iters): Application to algebraic stacks; perverse t-structure for stacks.
- Moduli stack `Herm_{2d}(X'/X)` of Hermitian torsion sheaves.
- Grothendieck–Springer resolution `π : H̃erm_{2d} → Herm_{2d}`; perverse sheaf
  `Spr^{Herm}_{2d}` with `W_d`-action (Hermitian analogue of Laumon's Springer sheaf on `Coh_d(X)`).
- Decomposition of `Spr^{Herm}_{2d}` into isotypical summands.
- Fallback: if the full mini-library exceeds scope, axiomatize Frobenius trace formulas on `Herm_{2d}`
  as sorry-bodies, analogously to the Ẽ_a axiomatization in P0.

**P3b plan** (perverse sheaves `𝒦_d^Eis` and `𝒦_d^Int`; requires P1 + P3a):
- Construct `𝒦_d^Eis` as the Eisenstein perverse sheaf on `Herm_{2d}(X'/X)` whose Frobenius
  trace at `𝒬` encodes `Ẽ_a(m(ℰ), s, Φ)` (eq. (1.2) of paper).
- Construct `𝒦_d^Int` via the Hitchin-type moduli stack `𝓜_d` and Hitchin map `f_d : 𝓜_d → 𝒜_d`;
  direct image `Rf_{d*}Q̄_ℓ` descends to `𝒦_d^Int` with endomorphism `C̄` (eq. (1.3)). Requires P2.
- Prove the Frobenius trace formulas (1.2) and (1.3) relating the two sides to the perverse sheaves.

**P3c plan** (W_d representation theory; requires P3a+P3b):
- Define `W_d = (ℤ/2ℤ)^d ⋊ S_d` and its graded virtual representation ring.
- Express `𝒦_d^Eis` and `𝒦_d^Int` (defined in P3b) as specific linear combinations of isotypical
  summands of `Spr^{Herm}_{2d}` (defined in P3a) via explicit formulas.
- Verify the identity of graded virtual representations of `W_d` that implies `𝒦_d^Eis ≅ 𝒦_d^Int`.
  (Elementary but involved algebraic computation given the P3a/P3b objects.)

**P3d plan** (assembly; requires P3b + P3c):
- Combine the isomorphism `𝒦_d^Eis ≅ 𝒦_d^Int` with the trace formulas from P3b.
- Extract the `(d/ds)^r` factor: `s` is a formal variable in `PowerSeries ℚ` (or `FormalMultilinearSeries`);
  the r-th derivative at s=0 is `PowerSeries.coeff r (q^{ds} · Ẽ_a(s))`. Mathlib's `PowerSeries.coeff`
  provides the Lean tool; P3d uses it to match the coefficient extraction on both sides.
- Close the proof of Theorem 1.1.

## Open strategic questions

1. **Algebraic stacks in Lean**: Should `Sht_{U(n)}^r` be axiomatized or modeled via
   `AlgebraicGeometry.Scheme`? For P0, axiomatization is the plan; revisit in P2.
2. **Perverse sheaf fallback**: If the ℓ-adic mini-library (Sub-P3a-1/2/3) stalls, axiomatize
   the Frobenius trace formulas on `Herm_{2d}` as sorry-bodies. Trigger: ≥3 STUCK verdicts on P3a.
3. **P3a fallback scope**: When does the perverse sheaf mini-library trigger the sorry-body fallback?
   Quantified as "≥3 STUCK verdicts on P3a" — revisit when P3a begins.

## Mathlib gaps & new material

**Absent from Mathlib (must be built or axiomatized)**:
- Hermitian shtukas and moduli stacks `Sht_{U(n)}^r` (axiomatized in P0; formalized in P2)
- Special cycles `𝒵_ℰ^r(a)` and virtual fundamental classes (axiomatized in P0; P2)
- Normalized Fourier coefficient `Ẽ_a` and Siegel–Eisenstein series `E(g, s, Φ)` — **axiomatized** in P0 (smooth/admissible representation theory of p-adic unitary groups, Haar measure on `H_n(𝔸)`, and adèle group topology beyond `FiniteAdeleRing` are all absent from Mathlib)
- Local density polynomials for Hermitian lattices (Cho–Yamauchi) (P1)
- Hermitian Springer theory; Hitchin fibration for Hermitian bundles (P3a)
- ℓ-adic perverse sheaves on algebraic stacks (mini-library, P3a) — critical-path item; sub-phases in Route A

**Partially present in Mathlib**:
- Function fields: `Mathlib.NumberTheory.FunctionField` (use in P0)
- Adèle ring: `Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing` (finite part; use in P0)
- Unitary groups: `Mathlib.LinearAlgebra.UnitaryGroup` (algebraic; not automorphic)
- Algebraic geometry: `Mathlib.AlgebraicGeometry.Modules.Sheaf` (quasi-coherent sheaves;
  locally-free sheaves of finite rank need extra definition on top)
- Function field of a scheme: `Mathlib.AlgebraicGeometry.FunctionField`

**New constructions this project introduces**:
All items in "Absent" above, plus: Hermitian lattice local density theory, W_d representation
theory (elementary), mini ℓ-adic perverse sheaf library targeting the Herm_{2d}(X'/X) case.
