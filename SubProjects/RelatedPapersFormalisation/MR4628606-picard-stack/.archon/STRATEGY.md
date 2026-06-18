# Strategy

## Goal

Formalize the four main theorems of Bae–Holmes–Pandharipande–Schmitt–Schwarz (MR4628606):
(1) Existence of the universal twisted double ramification cycle $\mathsf{DR}^{\mathsf{op}}_{g,A}$ on the Picard stack $\mathfrak{Pic}_{g,n,d}$ (Thm 1);
(2) Pixton's formula: $\mathsf{DR}^{\mathsf{op}}_{g,A} = \mathsf{P}^g_{g,A,d}$ (Main Thm);
(3) Vanishing: $\mathsf{P}^c_{g,A,d} = 0$ for $c > g$ (Thm 3);
(4) Fundamental classes of twisted meromorphic differentials equal Pixton's formula (Thm 4 / Conjecture A).

**Scope of sorry-freedom:**
- *Sorry-free deliverables*: All combinatorial content — `PrestableGraph`, `WeightingModR`, `PixtonsFormula`, `PixtonPolynomiality` (Pixton's polynomial formula and its polynomiality in $r$). These are formalizable in Lean 4 with existing Mathlib.
- *Axiom-complete deliverables*: Theorems 1–4 are proven as logical consequences of named, labeled axioms covering algebraic stacks, operational Chow groups, log geometry, and the JPPZ 2018 formula (see "Named axioms" below). Each axiom corresponds to a known result in the literature; the formalization is correct *given those axioms*. If and when Mathlib gains the required infrastructure, the axioms can be replaced by proofs.

**Named axioms** (each will be a labeled `axiom` declaration with a literature pointer):
- `Axiom.PicardStackSmooth` — $\mathfrak{Pic}_{g,n,d}$ is a smooth algebraic (Artin) stack, locally of finite type; source: Bae–Holmes–Pandharipande–Schmitt–Schwarz, Section 0.1 and 1.2.
- `Axiom.OperationalChow` — existence of operational Chow groups $\mathsf{CH}^*_{\mathsf{op}}$ for locally finite type algebraic stacks, satisfying proper pushforward, flat pullback, and Gysin maps; source: Fulton 1984, applied to stacks as in BHPSS Section 1.2.
- `Axiom.LogAbelJacobi` — logarithmic compactification of the Abel-Jacobi map yields $\mathsf{DR}^{\mathsf{op}}_{g,A}$; source: Marcus–Wise and Holmes 2019.
- `Axiom.JPPZ2018` — Janda–Pandharipande–Pixton–Zvonkine (2018) formula for DR cycles on target $\mathbb{P}^N$; source: Janda–Pandharipande–Pixton–Zvonkine, 2018. This is the keystone reduction for Thm 2; the main theorem is axiom-dependent on this until a formalization of JPPZ 2018 is available.
- `Axiom.LogSmoothDifferentials` — fundamental classes of twisted meromorphic differentials via log-smooth degeneration; source: Farkas–Pandharipande Conjecture A setup; required for Thm 4.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|-------------------|-------|
| Blueprint | ACTIVE | 1–2 | ~0 | none | none |
| Combinatorial foundations | NEXT (parallel A) | 5–8 | ~500–900 | `Finset`, `MvPolynomial` | graph isomorphism quotient |
| Algebraic geometry axiomatics | NEXT (parallel B) | 8–15 | ~800–1500 | `AlgebraicGeometry.Scheme` | design of axiom interfaces; no upstream stacks/Chow |
| Invariances of DR and Pixton | BLOCKED | 3–6 | ~300–600 | depends on AG axiomatics | requires stack/Chow axiom setup |
| Main theorem | BLOCKED | 5–10 | ~500–1000 | `Axiom.JPPZ2018` (black-box) | rubber maps, log geometry; axiom-dependent |
| Vanishing and applications | BLOCKED | 3–6 | ~300–600 | depends on main theorem | depends on Clader–Janda vanishings |

**Parallelism**: Phases "Combinatorial foundations" (parallel A) and "Algebraic geometry axiomatics" (parallel B) are mutually independent and can be dispatched as separate prover lanes once blueprint work is complete.

## Routes

### Single route: axiomatize stacks and Chow, then formalize combinatorics and main identity

The paper's proof reduces the main theorem to Janda–Pandharipande–Pixton–Zvonkine (2018) via a limit $\mathbb{P}^n \to \infty$ argument. Since algebraic stacks, operational Chow theory, and log geometry are absent from Mathlib, the strategy is:
1. Formalize the combinatorial content exactly (graphs, weightings, decorated graphs, Pixton's polynomial formula, polynomiality in $r$) — these are sorry-free.
2. State each geometric prerequisite as a named `axiom` declaration (see "Named axioms" above) with a 1-to-1 correspondence to a known result in the literature.
3. State and prove each of Theorems 1–4 as a consequence of named axioms; the formal proofs are sorry-free *given the axioms*.
4. As Mathlib gains stack/Chow infrastructure, remove axioms one by one.

**Axiom-complete checkpoint** (earliest declarable victory): once the combinatorial content is sorry-free and Thms 1–4 are proven relative to named axioms — expected after AG axiomatics + invariances phases.

## AG axiomatics sub-phase decomposition

The "Algebraic geometry axiomatics" phase (8–15 iters) must not be a monolithic block. Sub-phases:

| Sub-phase | Description | Iters | Key decision |
|-----------|-------------|-------|--------------|
| (i) Picard stack interface | Define `PicardStack` type with morphisms; state `Axiom.PicardStackSmooth` | 2–3 | algebraic stack as a typeclass or opaque type? |
| (ii) Operational Chow interface | Define `OperationalChow` ring with proper pushforward and flat pullback; state `Axiom.OperationalChow` | 3–5 | abstract ring (chosen) vs. concrete completion/limit |
| (iii) Tautological classes | Axiomatize $\psi_i$, $\xi_i$, $\eta_{a,b}$ as elements of `OperationalChow` | 1–2 | can depend on sub-phase (i)+(ii) being done |
| (iv) Boundary strata | Axiomatize boundary stratum maps $j_{\Gamma_\delta}$ and their lci property | 2–3 | key prerequisite for both tautological ring and Pixton's formula |

**Decision made**: operational Chow ring will be represented as an abstract ring (not a concrete completion/limit), keeping the axiom interface thin and compatible with eventual Mathlib integration.

## Open strategic questions

- Whether Mathlib's upcoming algebraic stacks work can be leveraged before AG axiomatics sub-phase (i) begins.
- Whether the graph automorphism quotient is best handled via `MulAction.orbitEquiv` or a bespoke `Quotient`.
- Whether to retrieve and axiomatize Clader–Janda vanishings for the Vanishing phase, or treat them as an additional named axiom.

## Mathlib gaps & new material

**Gaps to fill (axiomatized, not proven):**
- Algebraic stacks (smooth, locally finite type over a field): not in Mathlib. → `Axiom.PicardStackSmooth`.
- Operational Chow groups (bivariant classes, push-pull formalism): not in Mathlib. → `Axiom.OperationalChow`.
- Log smooth curves and log structures on moduli stacks: not in Mathlib. → `Axiom.LogAbelJacobi` (Thm 1) and `Axiom.LogSmoothDifferentials` (Thm 4).
- JPPZ 2018 formula: deep GRR-type result; not in Mathlib. → `Axiom.JPPZ2018`.

**New sorry-free project material:**
- `PrestableGraph` — combinatorial graph with genus labeling and half-edge involution.
- `WeightingModR` — half-edge weightings mod $r$ satisfying compatibility conditions.
- `PixtonsFormula` — the sum defining $\mathsf{P}^{c,r}_{g,A,d}$ as a polynomial in $r$.
- `PixtonPolynomiality` — proof that the sum is polynomial in $r$ for large $r$.

**New axiomatized project material:**
- `PicardStack` (axiomatized) — object type for the Picard stack.
- `OperationalChow` (axiomatized) — bivariant Chow class ring with functorial operations.
- `UniversalDRCycle` (axiomatized) — the DR cycle as an operational Chow class.
