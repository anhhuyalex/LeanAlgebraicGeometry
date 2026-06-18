# Strategy

## Goal

Formalize the P=W theorem for GL_n from Maulik–Shen (arXiv:2209.02568, Annals of Mathematics 200 (2024), no. 2). The theorem states: for a smooth projective curve C of genus g ≥ 2 over ℂ and coprime integers n ≥ 1, d (gcd(n,d)=1), and for all k, m ≥ 0,
$$P_k H^m(M_B(C,\mathrm{GL}_n),\mathbb{Q}) = W_{2k} H^m(M_B(C,\mathrm{GL}_n),\mathbb{Q}) = W_{2k+1} H^m(M_B(C,\mathrm{GL}_n),\mathbb{Q}),$$
where P_• is the perverse filtration (from the Hitchin fibration) and W_• is the weight filtration (from the mixed Hodge structure on M_B).

**Deliverable posture.** Mathlib lacks singular cohomology of complex varieties, perverse sheaves, and mixed Hodge theory. Therefore:
- `SmoothProjectiveCurve`, `CharacterVariety`, `DolbeaultModuli`, `HitchinFibration` will be sorry-gated opaque definitions.
- `PerverseFiltration` and `WeightFiltration` are **permanent sorry-axioms** in this project's scope (perverse sheaves / mixed Hodge theory are not Mathlib-plausible near-term); the deliverable for those is a type-correct sorry-skeleton, not a proof.
- `PEqualsW` (the main theorem) will also be sorry-gated.
- The genuine sorry-free contribution this project can make NOW is: the algebraic filtered-module framework (§1.1 of the paper) and its self-contained lemmas about indexed filtrations on ℚ-vector spaces.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|------------|-----|-------------------|-------|
| P0: Retrieve paper + establish blueprint | ACTIVE | 0 | ~0 | — | Done this iter |
| P1: Filtered ℚ-vector space framework | ACTIVE | 2–3 | ~80–150 | `Mathlib.RingTheory.FilteredAlgebra.Basic` | Design shape of Filtration type |
| P2: Strong perversity for filtrations (§1.1) | PAUSED | 3–5 | ~150–300 | Filtered module lemmas | No perverse sheaves needed for the algebraic lemmas |
| P3: Main theorem sorry-skeleton | ACTIVE | 1–2 | ~100–200 | Opaque defs for H^m, filtrations | Type choice for H^m(M_B, ℚ) |
| P4: Key sub-results (§1–4 algebraic pieces) | PAUSED | 5–10 | ~300–500 | Submodule lattice | Scope TBD after P1 |

## Routes

### Route A: Top-down (main theorem first, sorry-gated)

State the main theorem `PEqualsW` as a Lean declaration using sorry-bodied opaque definitions for all unavailable Mathlib constructions: `SmoothProjectiveCurve`, `CharacterVariety`, `HitchinFibration`, `PerverseFiltration`, `WeightFiltration`. The type of `PEqualsW` will use a sorry-gated `CohomologyGroup : ℕ → ℤ → ℚ-Module` (or similar) and `Filtration` structure.

**P3 (Main theorem statement) is ACTIVE and is the first deliverable.** It must be done before P2 (algebraic prerequisites). Concretely, P3 requires choosing:
- A Lean type for `H^m(M_B, ℚ)`: an opaque `ℚ`-module `CohomologyGroup (m : ℕ)`.
- A Lean type for a filtration: `Filtration (V : Type*) [AddCommGroup V] [Module ℚ V]` as a monotone map `ℤ → Submodule ℚ V`.
- The statement of `PEqualsW` as an equality of `Submodule ℚ (CohomologyGroup m)` terms.

This route is **primary**.

### Route B: Bottom-up (algebraic prerequisites first, sorry-free)

Formalize the algebraic/filtration content of §1.1 of the paper that does NOT require perverse sheaves. The first concrete target is:

**P1 target (filtration framework):** Introduce `structure Filtration (V : Type*) [AddCommGroup V] [Module ℚ V]` with `F : ℤ → Submodule ℚ V`, proved monotone, exhaustive (union = ⊤), and separated (intersection = ⊥). Build on `Mathlib.RingTheory.FilteredAlgebra.Basic` (`IsModuleFiltration`).

**P2 target (strong perversity algebraic lemma):** Formalize Lemma 1.2 of the paper as a pure Lean statement about indexed filtrations: "if γ : H → H[l] has the property that γ(F_i H) ⊆ F_{i+(c-l)} H for all i, then γ has strong perversity c with respect to F." This is formalizable NOW without any perverse sheaves.

This route runs **in parallel** with Route A (they write to different files).

## Open strategic questions

- Should `CohomologyGroup` be an opaque definition (no computational content) or an axiom? Opaque def preferred: it can later be replaced if Mathlib grows singular cohomology.
- The paper uses PGL_n and GL_n interchangeably in places; does the statement of P=W for GL_n require any extra coprimality hypotheses in Lean that affect the type signature?

## Mathlib gaps & new material

**Hard gaps (no Mathlib path; permanent sorry-axioms for this project):**
- **Singular cohomology H^m(X, ℚ)** — the most fundamental missing type. Mathlib has algebraic de Rham and Čech but NOT singular cohomology for complex varieties over ℂ with ℚ-coefficients. Will be introduced as an opaque sorry-gated ℚ-module in P3.
- **Perverse sheaves / BBD decomposition** — absent from Mathlib. `PerverseFiltration` remains a permanent sorry-axiom.
- **Mixed Hodge theory (Deligne)** — absent from Mathlib. `WeightFiltration` remains a permanent sorry-axiom.
- **Non-abelian Hodge correspondence** — absent; cited as a diffeomorphism fact.
- **Character varieties, Higgs bundle moduli spaces, Hitchin fibration** — no Mathlib infrastructure; all sorry-gated.

**Available / buildable in Mathlib:**
- **Filtered modules**: `Mathlib.RingTheory.FilteredAlgebra.Basic` provides `IsFiltration`, `IsRingFiltration`, `IsModuleFiltration` — the foundation for the P1 filtration framework.
- **Submodules / submodule lattice**: `Mathlib.LinearAlgebra.Submodule.*` — fully available.
- **General linear group GL_n**: `Mathlib.LinearAlgebra.GeneralLinearGroup` — VERIFIED.
- **Representation theory**: `Mathlib.RepresentationTheory.*` — partially available.
- **Algebraic curves**: partially available.
