# Analogy: a runaway-free induction for graded Hilbert–Serre rationality (Stacks 00K1)

## Mode
api-alignment

## Slug
quot-graded-quotient (follow-up to `quot-graded-module-api`)

## Iteration
016

## Question
Two sub-questions, both about escaping the `coeLinearMap`/`coeAddMonoidHom` whnf
runaway that blocked G2–G4 in iter-015:
1. Is there a Mathlib-idiomatic *tame encoding* of a `DirectSum.Decomposition` on a
   quotient/subtype carrier that avoids the runaway?
2. Can the Stacks-00K1 induction be restated at the level of Hilbert *functions*
   (`n ↦ dim_κ Mₙ`) so the inductive step never builds a quotient-module
   `Decomposition` at all — and if so, what is the MINIMAL structure on `C = M/xM`
   and `K = ker x` that must actually be built?

## The runaway, mechanically (verified this iter)
- `DirectSum.IsInternal A` is *by definition* `Function.Bijective (DirectSum.coeAddMonoidHom A)`
  (`Mathlib.Algebra.DirectSum.Basic`; confirmed via hover/loogle). Any goal that unfolds
  `IsInternal` on a derived carrier (subtype `↥p`, quotient `M ⧸ p`) forces `isDefEq`/`whnf`
  to reduce `coeAddMonoidHom`/`coeLinearMap` over that carrier → non-terminating
  (looped at 200k and 2,000,000 heartbeats in the prover's repros).
- `DirectSum.Decomposition.isInternal` and `isInternal_submodule_of_iSupIndep_of_iSup_eq_top`
  (the path the iter-015 prover used) both route through this `Bijective`/`coeAddMonoidHom`
  unfold — hence the timeout.
- `Submodule.map_iSup` over a family valued in `Submodule R (M ⧸ p)` triggers the same
  reduction even at *statement* time.
- G1 was rescued precisely by **never leaving the ambient `M`**: it states
  `iSupIndep (fun i => ℳ i ⊓ p)` and `⨆ i, (ℳ i ⊓ p) = p` — families valued in
  `Submodule R M`. Ambient internal gradings and `finrank` of subtype/quotient pieces
  (`↥(N ⊓ ℳ n)`, `W ⧸ range φ` in D5) are SAFE; only derived-carrier
  `IsInternal`/`Decomposition`/`map_iSup` are toxic.

## Decisions identified

### Decision Q1: tame encoding of a derived-carrier `DirectSum.Decomposition`
- **Mathlib idiom**: `DirectSum.Decomposition.ofLinearMap (ℳ) (decompose) (h_left_inv) (h_right_inv)`
  — `Mathlib.Algebra.DirectSum.Decomposition`. Signature:
  `decompose : M →ₗ[R] ⨁ i, ↥(ℳ i)`, `h_left_inv : coeLinearMap ℳ ∘ₗ decompose = id`,
  `h_right_inv : decompose ∘ₗ coeLinearMap ℳ = id`. It builds the instance WITHOUT ever
  unfolding to `Bijective`, so the `IsInternal`-whnf trigger never fires. The two
  identities can be discharged per-component with `DirectSum.coeLinearMap_of`
  (`coeLinearMap ℳ (of _ i x) = ↑x`) + `DirectSum.linearMap_ext`, i.e. a controlled
  `ext`-based proof, NOT a blind `isDefEq`. Precedent for the equiv-based handle:
  `DirectSum.decomposeLinearEquiv` and `Mathlib.Algebra.Lie.Graded` (graded Lie algebras
  manipulate the decomposition through `decomposeLinearEquiv`, never raw `IsInternal`).
- **Caveat**: `ofLinearMap` tames the *instance construction*, but you must still build the
  quotient `decompose` map and prove the two identities. If that proof reaches for
  `Submodule.map_iSup` on the quotient family, the runaway returns. So it is a viable
  escape for a SINGLE derived-carrier grading done carefully, not a free pass — and it
  does nothing for the missing graded quotient RING (G3): Mathlib has zero `⧸` in
  `RingTheory/GradedAlgebra` (`GradedRing` + `HasQuotient` loogle empty this iter).
- **Gap**: divergent-and-missing, but buildable. **Verdict**: NEEDS_MATHLIB_GAP_FILL
  (achievable; keep as documented FALLBACK).

### Decision Q2: is the Hilbert-function pivot sound, and what is the minimal C/K structure?
- **The pivot as the prover framed it (quantify the CONCLUSION over `n ↦ dim_κ Mₙ`) is NOT
  enough.** Applying the IH to `K` instantiates the IH's *carrier* to `↥K` and to `C`
  instantiates it to `M ⧸ xM`; if the IH's hypothesis demands a `DirectSum.Decomposition`
  on that carrier, you are back to the blocked subtype/quotient construction. This is the
  iter-014 Q3 obstruction ("the recursion's payload IS the graded structure") and it
  survives a conclusion-only restatement. To escape, the IH's **hypothesis** must also be
  derived-carrier-free.
- **The sound restatement: range the induction over SUBQUOTIENTS of a single FIXED ambient
  graded module.** Fix `ℳ : ℕ → Submodule κ M` with `[DirectSum.Decomposition ℳ]` (ambient
  — safe). Quantify over a pair of homogeneous submodules `N' ≤ N ⊆ M` plus `r` pairwise-
  commuting degree-+1 κ-endomorphisms `t : Fin r → (M →ₗ[κ] M)` preserving `N` and `N'`.
  Hilbert function defined AMBIENT-LY:
  `h(n) = (finrank κ ↥(N ⊓ ℳ n) : ℤ) − finrank κ ↥(N' ⊓ ℳ n)`  (cast to ℚ for `IsRatHilb`).
  Conclusion: `IsRatHilb h r`.
  - This class is **closed** under the two operations of the SES, with both results
    annihilated by the killed endo `x = t_{r-1}`, and both expressed as ambient pairs:
    - `K = ker(x)` subquotient `= (N ⊓ x⁻¹(N'), N')`  (preimage is a homogeneous submodule of `M`);
    - `C = coker(x) = N/(N' + x·N)` subquotient `= (N, N' + x·N)`  (`N' + x·N` homogeneous in `M`).
    A subquotient of a subquotient of `M` is again a subquotient of `M` — the framework
    never produces a derived carrier.
  - **Minimal structure on `C` and `K`: NONE on a quotient/subtype carrier.** `C` is just
    the ambient pair `(⊤, x·M)` of homogeneous submodules and the ambient dimension-
    difference function `n ↦ dim(ℳ n) − dim(x·M ⊓ ℳ n)`; `x·M ⊓ ℳ n = x·(ℳ (n-1))`
    is an ambient identity (x homogeneous of degree 1 + G1). `K` is the pair `(ker x, ⊥)`.
    No `DirectSum.Decomposition (M ⧸ xM)`, no `DirectSum.Decomposition ↥K`, no
    `GradedRing (R ⧸ (x))` is ever formed.
- **Why subquotients and not just submodules**: `coker(x) = N/xN` is killed by `x` (so it is
  in the (r−1)-endo IH domain), but `xN ⊆ N` is NOT killed by `x`, so the
  "`h_C = h_N − h_{xN}` via `IsRatHilb.sub`" shortcut fails — `xN` is not an IH object. The
  minimal class closed under ker+coker of a degree-1 endo starting from `M` is exactly
  subquotients. (`IsRatHilb.sub` is still used internally, on `h_C` and shifted `h_K`, by
  the already-landed `IsRatHilb.ofDiffEq`.)
- **Finiteness (the residual G5)**: carry "`M` f.g. over `κ[t_0,…,t_{r-1}]`" (equivalently
  `Module.Finite`); the base `r = 0` gives a finite-dimensional subquotient ⇒ `h` eventually
  `0` ⇒ `IsRatHilb.ofEventuallyZero`. Sub/quotient + Noetherian + annihilation-by-`x`
  transfers f.g. down a generator (`Submodule.FG`, `Module.Finite.quotient`,
  `Submodule.FG.restrictScalars_of_surjective`). This stays ambient (it is about FG of
  ambient submodules, never a derived-carrier grading).
- **Gap**: this is a project-design restatement that AVOIDS the Mathlib gap entirely.
  **Verdict**: PROCEED (build the ambient subquotient induction; it sidesteps G2–G4).

## Recommendation

Adopt **Route 2 (the ambient subquotient induction)** — it is the sound realization of the
prover's Hilbert-function pivot and the only route that makes the runaway *structurally
impossible*, because every object that ever appears is an ambient family
`fun n => Naux ⊓ ℳ n` of submodules of the FIXED `M`, exactly the shape G1 proved safe.
It eliminates G2, G3 and G4 as originally specified (no quotient-module Decomposition, no
graded quotient ring, no regrading) and reduces G5 to ambient FG bookkeeping. Keep
**Route 1 (`DirectSum.Decomposition.ofLinearMap`)** documented as the fallback for any
future lemma that genuinely needs an honest graded object on a derived carrier.

### Residual build list (Route 2), ordered

1. **`SubquotientHilb` data + ambient Hilbert function** (new). Package: fixed `ℳ` with
   `[DirectSum.Decomposition ℳ]`, finite-dim components; homogeneous `N' ≤ N`; commuting
   degree-+1 endos `t : Fin r → M →ₗ[κ] M` preserving `N`, `N'`; `Module.Finite` witness.
   Define `hilb : ℕ → ℚ := fun n => ((finrank κ ↥(N ⊓ ℳ n) : ℤ) − finrank κ ↥(N' ⊓ ℳ n))`.
   Reuses G1 (`homogeneousSubmodule_iSup_inf_eq`, `homogeneousSubmodule_inf_iSupIndep`).
2. **Ambient `ker`/`coker` closure lemmas** (new): build the two subquotient pairs above,
   prove homogeneity of `N ⊓ x⁻¹(N')` and `N' + x·N` (G1 + `SetLike.IsHomogeneousElem.graded_smul`),
   prove the remaining endos preserve them and that `x` kills both.
3. **Degreewise difference D6** (new, small): identify the component dims of the `K`/`C`
   subquotients with `ker(x : ℳn→ℳ(n+1))` and `ℳ(n+1)/im(x)`, then apply the landed
   **D5** (`degreewise_finrank_diff`) to get `hilb_M(n+1) − hilb_M(n) = hilb_C(n+1) − hilb_K(n)`.
4. **Finiteness transfer (residual G5, ambient)** (new, low effort): f.g. of the two
   subquotients over `κ[t_0..t_{r-2}]` via Noetherian + `Submodule.FG` + annihilation by `x`.
5. **The induction `P(r)`** (new): base `r=0` via `IsRatHilb.ofEventuallyZero`; step via
   (2)+(3)+(4) feeding the landed `IsRatHilb.ofDiffEq` and `IsRatHilb.bump`.
6. **Bridge to `AlgebraicGeometry.gradedModule_hilbertSeries_rational`** (new, thin):
   instantiate `P` at `(N,N') = (⊤,⊥)`, endos = multiplication by the degree-1 generators;
   derive the `r` degree-1 generators from "f.g. κ-algebra generated in degree 1"
   (blueprint NOTE, `Picard_QuotScheme.tex` L429–435).

Landed and reused as-is: **G1** (`homogeneousSubmodule_inf_iSupIndep`,
`homogeneousSubmodule_iSup_inf_eq`), **D5** (`degreewise_finrank_diff`), the entire
`IsRatHilb` toolkit (`ofEventuallyZero`, `bump`, `sub`, `shiftRight`, `antidiff`,
`ofDiffEq`). **Dropped from the iter-014 plan**: G2 (quotient Decomposition), G3 (graded
quotient ring), G4 (regrade over R/(x)) — none are built under Route 2.
