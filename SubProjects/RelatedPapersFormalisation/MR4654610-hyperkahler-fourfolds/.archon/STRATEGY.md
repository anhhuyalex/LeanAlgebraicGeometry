# Strategy

## Goal

Formal Lean 4 statements and proofs (with `sorry` or named `axiom`s for deep geometry) for
the main results of Debarre–Huybrechts–Macrì–Voisin, arXiv:2201.08152 (MR4654610):

- **Theorem 1.5** (Main): A hyper-Kähler fourfold X with l, m ∈ H²(X,ℤ) satisfying
  ∫_X l⁴ = 0 and ∫_X l²m² = 2 is of K3[2] deformation type.
- **Corollary 1.6** (O'Grady's conjecture): A hyper-Kähler fourfold of K3[2] numerical type
  is of K3[2] deformation type.
- **Theorem 1.7**: P_{RR,X}(2k) = C(k+3, 2) under the conditions of Thm 1.5.
- **Theorem 1.8** (SYZ): Existence of Lagrangian fibration f: X → ℙ² with f*𝒪(1) ≅ L.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|------------|-----|-------------------|-------|
| 1: Foundations | ACTIVE | 2 | ~200 | `QuadraticForm`, `Module ℤ` | Type design complexity |
| 2a: Alg lemmas | PENDING | 2 | ~300 | `Polynomial` integrality | Notation overhead |
| 2b: Comb lemmas | PENDING | 2 | ~200 | `Nat.choose` | Guan axiom coverage |
| 3: Main theorems | PENDING | 4 | ~400 | deformation theory | sorry depth |
| 4: Polish | PENDING | 1 | ~50 | — | axiom minimality |

## Routes

### Route A: Parameterized-module approach (ACTIVE)

Every declaration is stated over an explicit variable context:
```
variable (V : Type*) [AddCommGroup V] [Module ℤ V]
  (q : QuadraticForm ℤ V) (c_X : ℚ)
  (integrate4 : V →ₗ[ℤ] V →ₗ[ℤ] V →ₗ[ℤ] V →ₗ[ℤ] ℤ)
```

This encodes H²(X,ℤ) as an abstract ℤ-module `V`, the BBF form as `q : QuadraticForm ℤ V`,
the Fujiki constant as `c_X : ℚ`, and the top-degree quartic pairing as the multilinear map
`integrate4`. The integral condition ∫_X l⁴ = 0 becomes `integrate4 l l l l = 0`. All lemmas
carry this context explicitly. Deformation type and Lagrangian fibration are represented as
opaque predicates.

**Chosen over the bundled-structure alternative** because: (a) avoids a bespoke typeclass
hierarchy that may conflict with future Mathlib HK additions; (b) reduces Phase 1 to ~200 LOC;
(c) makes each hypothesis explicit at every theorem statement — clearer formal fidelity.

#### Phase 1 lane (Foundations, ~200 LOC)

Define the variable context above and state the foundational lemmas as `axiom` declarations
(not `sorry` — see note below) for the geometric facts, plus genuine Lean proofs for the
purely algebraic/combinatorial lemmas that follow from the axioms:

- `axiom HK.fujiki_rel` — Fujiki relation ∫α^(2n) = cX·qX(α)^n
- `axiom HK.hrr_exists` — existence and properties of the HRR polynomial
- `axiom HK.period_map_surj` — period map surjectivity (used in Lemma 2.1)
- `axiom HK.guan_betti` — Guan's Betti number classification (Lemma 4.1)
- `axiom HK.deformation_type_k3sq` — the abstract notion of K3[2] deformation type

**Why named `axiom` over `sorry`**: a named axiom is explicit and enumerable via
`#check_axioms`; a `sorry` silently closes any goal including type errors. When Mathlib adds
HK geometry, filling named axioms is targeted work; patching sorries requires a search pass.

#### Phase 2a lane (Algebraic lemmas, parallel prover dispatch, ~300 LOC)

Once Phase 1 axioms compile, these five lemmas are **mutually independent** and should be
dispatched as parallel prover lanes:
- `HK.hrr_integral` — P_{RR,X}(qX(α)) ∈ ℤ (Lemma 2.1; genuine Lean proof using surjectivity axiom)
- `HK.a_is_integer` — (1/n!) ∫lⁿmⁿ ∈ ℤ (Lemma 2.2; genuine proof)
- `HK.polynomial_parity` — Lemma 3.2 (arithmetic constraint; genuine proof over ℤ[T])
- `HK.sqrt_rationality` — Lemma 4.2 (√(2aA_X) ∈ ℚ; genuine proof)
- `HK.topologicalConstant` — A_X definition (trivial, Phase 1 overflow)

**Note on Lemma 4.1 (`HK.betti_numbers`)**: this is an `axiom` citing [Gu, Main Theorem],
not a genuine Lean proof. The strategy does NOT claim a formal proof of Lemma 4.1.
Phase 2b groups it with Guan-dependent combinatorial work.

#### Phase 2b lane (Guan-dependent, ~200 LOC)

- `HK.conjecture14_fourfold` — Theorem 4.3; genuine proof once Lemmas 4.1 (axiom) and 4.2 done

#### Phase 3 lanes (Main theorems, ~400 LOC)

- `HK.hrr_formula_fourfold` — Theorem 1.7 (trivial from Thm 4.3)
- `HK.k3_deformation_type` — Theorem 1.5; uses deep geometry axioms for Sections 5–8 steps
- `HK.ogrady_conjecture` — Corollary 1.6; follows from Thm 1.5
- `HK.lagrangian_fibration` — Theorem 1.8; uses SYZ axioms

## Open strategic questions

- **Phantom prerequisite verification**: `Polynomial.eval_int_cast_map` is written in the
  blueprint as a `\mathlibok` anchor. Mathlib4 uses camelCase (`intCast` not `int_cast`) — the
  correct name is likely `Polynomial.eval_intCast_map`. Must be verified via LSP before Phase 2a
  dispatch. Mark `[expected]` until confirmed.
- **Quadratic form parity encoding**: `QuadraticForm ℤ V` in Mathlib4 is polarized differently
  from the physics convention used in the paper (the BBF form is normalized so that the
  associated bilinear form may not be integral). Need to confirm whether the project should
  use `QuadraticForm ℤ V` directly or wrap it with a divisibility condition.
- **Top-degree pairing**: the Fujiki relation encodes ∫α^{2n} in terms of q; the project
  may need only the Fujiki axiom and not a raw `integrate4` map. Revisit in Phase 1.

## Mathlib gaps & new material

| Need | Status | Source | Impact |
|------|--------|--------|--------|
| HK manifold / BBF form | GAP — not in Mathlib | axiom | Blocks all phases |
| Deformation theory | GAP — not in Mathlib | axiom | Blocks Phase 3 |
| Lagrangian fibrations | GAP — not in Mathlib | axiom | Blocks Phase 3 |
| `QuadraticForm ℤ V` | AVAILABLE | `Mathlib.LinearAlgebra.QuadraticForm.Basic` | Foundation |
| `Nat.choose` | AVAILABLE | `Mathlib.Data.Nat.Choose.Basic` | Phase 2a |
| `Polynomial.eval_intCast_map` | EXPECTED (verify name) | Mathlib | Phase 2a anchor |
| Guan Betti classification | GAP — external theorem | axiom | Blocks Phase 2b |
