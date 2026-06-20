# Analogy: graded-module quotient / kernel / regrading API for Stacks 00K1

## Mode
api-alignment

## Slug
quot-graded-module-api

## Iteration
014

## Question
For the graded-module side of the Stacks 00K1 inductive step (graded Hilbert–Serre
rationality, Lean target `AlgebraicGeometry.gradedModule_hilbertSeries_rational`):
(1) does Mathlib already supply the graded quotient `M/xM`, graded kernel
`K = ker(x⋆)`, regrading over `R/(x)`, and graded `Module.Finite` transfer; (2) what
is the Mathlib-aligned shape for these defs; (3) is there a route that avoids the
graded quotient/kernel entirely and works only with the degreewise `finrank`
identity?

## Project artifact(s)
- `AlgebraicJacobian/Picard/QuotScheme.lean:425-612` — the `IsRatHilb` power-series
  toolkit (`IsRatHilb`, `.ofEventuallyZero`, `.bump`, `.sub`, `.shiftRight`,
  `.antidiff`, `.ofDiffEq`). DONE and axiom-clean. `ofDiffEq` is the inductive-step
  engine: it consumes `hC' : IsRatHilb hC d`, `hK' : IsRatHilb hK d`, and a
  difference identity, and produces `IsRatHilb hM (d+1)`.
- `blueprint/src/chapters/Picard_QuotScheme.tex:346-474` — `lem:gradedHilbertSerre_rational`
  statement + proof. The proof inducts on the number `r` of degree-one κ-algebra
  generators; the inductive step applies the IH to `K` and `C = M/xM` **as f.g.
  graded modules over `R/(x)`** (an `(r−1)`-generated ring).

## Mathlib state (verified at the pinned commit)

### Present (CORRECTS iter-012 on one point)
A homogeneous-submodule scaffold now exists; iter-012's "NO graded submodule API" is
out of date. But it is a thin scaffold — SetLike/PartialOrder/ext only, **no induced
grading**.
- `Submodule.IsHomogeneous ℳ p` — `RingTheory/GradedAlgebra/Homogeneous/Submodule.lean:52`.
- `HomogeneousSubmodule 𝒜 ℳ` (bundled) — `…/Homogeneous/Submodule.lean:64`. File ends
  ~line 130: only `SetLike`, `PartialOrder`, `ext`, `mem_toSubmodule_iff`.
- `HomogeneousIdeal 𝒜 := HomogeneousSubmodule 𝒜 𝒜`, `Ideal.IsHomogeneous` —
  `…/Homogeneous/Ideal.lean:64,71`. `HomogeneousIdeal.map/comap` — `…/Homogeneous/Maps.lean:34,52`.
- `HomogeneousSubsemiring 𝒜` (bundled, scaffold-only) — `…/Homogeneous/Subsemiring.lean:38`.
- `Ideal.homogeneous_span` (so `(x)` for `x ∈ R₁` is a `HomogeneousIdeal`) —
  `…/Homogeneous/Ideal.lean:159`.
- `SetLike.IsHomogeneousElem` + `SetLike.IsHomogeneousElem.graded_smul`
  (mul-by-homogeneous sends homogeneous to homogeneous) — `Algebra/GradedMulAction.lean:136`.
- Graded-module primitives: `DirectSum.Decomposition` (`Algebra/DirectSum/Decomposition.lean`),
  `SetLike.GradedSMul`, the `GradedModule`/`Gmodule` toolkit (`Algebra/Module/GradedModule.lean`),
  `GradedRing`.
- Linear-algebra inputs for the degreewise identity: `LinearMap.finrank_range_add_finrank_ker`
  (rank–nullity), `Submodule.finrank_quotient_add_finrank` (`LinearAlgebra/Dimension/RankNullity.lean:208`).
- Finiteness glue: `Submodule.FG.restrictScalars_of_surjective` (`RingTheory/Finiteness/Ideal.lean:48`).
- Converse Hilbert extraction only: `Polynomial.existsUnique_hilbertPoly`
  (`RingTheory/Polynomial/HilbertPoly.lean`).

### Absent (CONFIRMS iter-012)
- **No `DirectSum.Decomposition` on a `HomogeneousSubmodule`** — the induced grading on
  the submodule itself. (grep over `Mathlib/` for `IsHomogeneous`/`⊓ ℳ` → Decomposition: none.)
- **No `GradedRing`/`DirectSum.Decomposition` on a quotient ring `A ⧸ I`** for homogeneous
  `I`. The entire `RingTheory/GradedAlgebra/` directory contains **zero** occurrences of `⧸`.
- **No `DirectSum.Decomposition` on a quotient module `M ⧸ p`** for homogeneous `p`.
- **No graded kernel** of a degree-shifting (mul-by-homogeneous) endomorphism.
- **No regrading** along a graded surjection (`R ↠ R/(x)`).
- **No graded `Module.Finite` transfer** through any of the above.
- **No Hilbert series / Hilbert-Serre for graded modules** (only the converse extraction).

## Decisions identified

### Decision D1: graded quotient `C = M/xM` carrying a `DirectSum.Decomposition`
- **Mathlib idiom**: none ships, but the *shape* to mirror is `HomogeneousIdeal` /
  `GradedRing`: a grading is an **unbundled `DirectSum.Decomposition` instance** on a
  family `ℕ → Submodule …`. `xM` is a homogeneous submodule (image of mul-by-`x`,
  `x` homogeneous via `SetLike.IsHomogeneousElem.graded_smul`); the quotient's
  components are `(ℳ n).map (Submodule.mkQ (xM))`.
- **Gap**: divergent-and-missing → must build. General lemma G2 below.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision D2: graded kernel `K = ker(x⋆ : M → M(1))`
- `K` **is** a `HomogeneousSubmodule 𝒜 ℳ` — reuse Mathlib's scaffold. `K = LinearMap.ker`
  of mul-by-`x`; an element lies in `K` iff each homogeneous component does (`x·mₙ ∈ ℳ_{n+1}`
  are independent), so `Submodule.IsHomogeneous` holds. The induced grading
  (`fun n => Kₙ := K ⊓ ℳ n` as a submodule of `M`) needs a `DirectSum.Decomposition`,
  which the scaffold does **not** provide. General lemma G1 below.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision D3: regrading — `C`, `K` as graded modules over `R/(x)`
- `(x)` is a `HomogeneousIdeal` (`Ideal.homogeneous_span`). Two options:
  - **D3a (quotient ring, mirrors Stacks + blueprint)**: build `GradedRing` on `R ⧸ (x)`
    (components `(𝒜 n).map (Ideal.Quotient.mk (x))`), then `SetLike.GradedSMul` for the
    `R/(x)`-action on `C`, `K`. Needs the missing graded-quotient-ring construction (G3).
  - **D3b (graded subring, avoids the quotient ring)**: restrict scalars to the graded
    κ-subalgebra `R' = κ[x₁,…,x_{r−1}] ⊆ R`. Since `x_r` annihilates `C`, `K`, they are
    `R'`-modules with the **same** grading. Avoids quotient-ring grading but needs a
    `GradedRing` instance on a homogeneous subsemiring/subalgebra (also missing) +
    `RestrictScalars` graded compatibility.
- Both need a "grading on a derived ring" construction Mathlib lacks; D3a is closer to
  the existing `HomogeneousIdeal` API and the blueprint. **Recommend D3a.**
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision D4: `Module.Finite` transfer (graded, over `R/(x)`)
- `C`, `K` are f.g. over `R` (kernel/quotient of f.g. over Noetherian `R`) and
  annihilated by `(x)`; `Submodule.FG.restrictScalars_of_surjective` (along `R ↠ R/(x)`)
  is the engine. Thin glue, no new theory — but it is glue that must be written.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (low effort).

### Decision D5: degreewise SES / `finrank` identity (the Q3 "avoidance" item)
- `dim Mₙ₊₁ − dim Mₙ = dim Cₙ₊₁ − dim Kₙ` is **pure linear algebra** on the κ-linear map
  `xₙ : Mₙ → Mₙ₊₁`: rank–nullity (`LinearMap.finrank_range_add_finrank_ker`) gives
  `dim Kₙ = dim Mₙ − rk xₙ` and `dim(Mₙ₊₁/im xₙ) = dim Mₙ₊₁ − rk xₙ`; subtract. **No graded
  object is needed for this identity.** This is exactly the `hdiff` hypothesis of
  `IsRatHilb.ofDiffEq` — and it was already the trivial input.
- **Verdict**: PROCEED (build with pure linear algebra; needs no graded API).

### Q3 — does the avoidance route collapse the sub-build? NO.
The degreewise identity (D5) genuinely avoids graded objects, but it is not the
obstruction. `IsRatHilb.ofDiffEq` *also* demands `hC' : IsRatHilb hC d` and
`hK' : IsRatHilb hK d`. The **only** source of those is the inductive hypothesis applied
to `C` and `K`, and the IH quantifies over **f.g. graded modules over an `(r−1)`-generated
ring**. To instantiate it, `C` and `K` must be presented as such objects — i.e. with
`DirectSum.Decomposition` (D1, D2), an `R/(x)`- or `R'`-module structure (D3), and
`Module.Finite` (D4). No reformulation feeds the IH "abstract vector-space families":
the recursion's payload *is* the graded structure. Free-resolution and graded-dévissage
reformulations exist but are strictly **harder** (Hilbert syzygy / graded primes — both
also absent from Mathlib). So Q3 removes D5 from the graded build (good, do it) but leaves
D1–D4 required.

## Recommendation

Build a small **graded-module-grading library** (genuine Mathlib gap-fill, all as
unbundled `DirectSum.Decomposition`/`SetLike.GradedSMul` instances mirroring
`HomogeneousIdeal`/`GradedRing`), then assemble Stacks 00K1 on top. Concrete plan:

- **G1 — grading on a homogeneous submodule.** For `p : Submodule A M` with
  `p.IsHomogeneous ℳ`, produce `DirectSum.Decomposition (fun n => (p ⊓ ℳ n) as Submodule)`
  + `SetLike.GradedSMul 𝒜 (…)`. Gives `K` (D2) and `xM` graded. Generalises cleanly →
  PR-worthy. Mirror file: `RingTheory/GradedAlgebra/Homogeneous/Submodule.lean`.
- **G2 — grading on the quotient by a homogeneous submodule.** For `p.IsHomogeneous ℳ`,
  `DirectSum.Decomposition` on `M ⧸ p` with components `(ℳ n).map (p.mkQ)`. Gives `C` (D1).
  Same file. Proof spine: `M = ⨁ ℳ n` internal, `p = ⨁ (p ⊓ ℳ n)` (from G1), so
  `M/p = ⨁ ℳ n/(p ⊓ ℳ n)`.
- **G3 — grading on `R ⧸ I` for homogeneous `I`** (`GradedRing` instance) — the missing
  graded-quotient-**ring**; specialise to `I = (x)` for D3a. (Alt: D3b graded-subalgebra
  `GradedRing` + `RestrictScalars`.)
- **G4 — regrade `C`, `K` over `R/(x)`**: `SetLike.GradedSMul (R/(x))-grading (component
  family)`, reusing G1/G2 component families with the `R/(x)`-action.
- **G5 — `Module.Finite` transfer** via `Submodule.FG.restrictScalars_of_surjective`
  (`R ↠ R/(x)`), using annihilation by `(x)`.
- **Assembly**: degreewise SES + identity via rank–nullity (D5, no graded API);
  induction on `r` (number of degree-1 generators) with base `R = κ`; inductive step feeds
  `hC', hK'` (from IH on `C`, `K` over `R/(x)`, via G1–G5) and `hdiff` (D5) into the
  existing `IsRatHilb.ofDiffEq` + `IsRatHilb.bump`.

G1 and G2 are the load-bearing, reusable, PR-quality core; G3 is the heaviest single
piece. Order the next-iter mathlib-build lane G1 → G2 → G5 → G3 → G4 → assembly, since
G1/G2/G5 unblock the most with the least risk, and the degreewise identity can be landed
independently at any time.
