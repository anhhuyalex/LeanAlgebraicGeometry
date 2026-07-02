# Analogy: `IsRegularLocalRing → IsDomain` (Stacks 00NQ)

## Mode
api-alignment

## Slug
isregularlocalring-isdomain

## Iteration
182

## Question

Does Mathlib have `IsRegularLocalRing R → IsDomain R` (Stacks 00NQ)? This
is the load-bearing gap in
`AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean:435
exists_isRegular_of_regularLocal`, the iter-181 Lane G helper that closes
the lower bound `(maximalIdeal R).spanFinrank ≤ depth R` for
`CohenMacaulay.of_regular`.

## Project artifact(s)

- `AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean:435–441` —
  `exists_isRegular_of_regularLocal` (typed substantive `sorry`).
- `AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean:465–503` —
  `CohenMacaulay.of_regular` (assembly closed inline mod the helper).
- `AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean:228, 268, 326` —
  off-target depth lemmas still open (pivot candidates).

## Decisions identified

### Decision 1: Does Mathlib already expose `IsRegularLocalRing → IsDomain`?

- **Mathlib idiom**: Mathlib's *only* file on regular local rings is
  `Mathlib.RingTheory.RegularLocalRing.Defs` (≈78 LOC). Cite:
  `.lake/packages/mathlib/Mathlib/RingTheory/RegularLocalRing/Defs.lean:1–79`.
  It introduces the class `IsRegularLocalRing` (extending `IsLocalRing` +
  `IsNoetherianRing` + a `spanFinrank_maximalIdeal = ringKrullDim`
  hypothesis), provides `iff_finrank_cotangentSpace`, `of_ringEquiv`, and
  *only one* derived instance going IN the regular direction:
  `IsRegularLocalRing.instOfIsLocalRingOfIsDomainOfIsPrincipalIdealRing`
  (`Defs.lean:68–76`) — i.e. `IsLocalRing + IsDomain + IsPrincipalIdealRing
  → IsRegularLocalRing`. There is **no** declaration whose conclusion is
  `IsDomain R` from `IsRegularLocalRing R`.
- **Direct LSP verification**: `lean_loogle "IsRegularLocalRing, IsDomain"`
  returns exactly the one converse-direction hit above; `lean_leansearch
  "regular local ring is a domain"` surfaces no relevant statements;
  `grep -rln "IsRegularLocalRing" Mathlib` returns the single
  `Defs.lean` file.
- **Project's current path**: typed `sorry` body in
  `exists_isRegular_of_regularLocal`. The iter-181 task_result already
  identified this as a Mathlib gap.
- **Gap**: divergent — the project needs the implication but Mathlib does
  not provide it. Not a parallel-API issue; it is a genuinely missing
  upstream theorem.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**.

### Decision 2: If absent, which 00NQ route is cheapest at pinned commit `b80f227`?

The Stacks 00NQ classical proof is a *joint induction* on
`(maximalIdeal R).spanFinrank` proving simultaneously `IsRegularLocalRing
R ⟹ IsDomain R` and the existence of an `R`-regular sequence of length
`spanFinrank` inside `𝔪`. Sub-lemmas and their Mathlib status:

| Sub-lemma | Mathlib citation | LOC to assemble |
|---|---|---|
| Base case: `spanFinrank = 0 ⟹ 𝔪 = ⊥ ⟹ R is a field ⟹ IsDomain R` | `IsLocalRing.isField_iff_maximalIdeal_eq` + `Field.toIsDomain` (or `Submodule.spanFinrank_eq_zero_iff`) | 25 |
| Finitely many minimal primes | `Ideal.finite_minimalPrimes_of_isNoetherianRing` (`Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`) | 0 |
| Prime avoidance with one non-prime ideal (`𝔪²`) | `Ideal.subset_union_prime` (`Mathlib.RingTheory.Ideal.Operations`) | 30 (apply step) |
| Krull intersection in a local ring | `Ideal.iInf_pow_eq_bot_of_isLocalRing` (`Mathlib.RingTheory.Filtration`) | 0 |
| `dim R/(x) + 1 = dim R` for `x ∈ 𝔪`, `x ∈ nonZeroDivisors R` | `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors` (`Mathlib.RingTheory.KrullDimension.Regular`) | 0 |
| `dim R/(x) + 1 = dim R` for `x ∈ 𝔪`, `x ∉ ⋃ minimalPrimes` (the joint-induction step *before* we know `IsDomain`) | `Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal` (`Mathlib.RingTheory.KrullDimension.Regular`) — applied with `M = R`, with `Module.supportDim ↔ ringKrullDim` bridge | 30 |
| `R/(x)` is local + Noetherian | structural; immediate | 5 |
| `spanFinrank (𝔪/(x)) = spanFinrank 𝔪 - 1` for `x ∈ 𝔪 \ 𝔪²` (cotangent space dim drop) | **NO direct Mathlib lemma**. Closest is `IsLocalRing.finrank_cotangentSpace_eq_zero_iff` / `_le_one_iff` (qualitative); we need quantitative drop. Workable via `Submodule.finrank_quotient_add_finrank` applied to `(𝔪 + (x)/𝔪²)` ⊂ `CotangentSpace R`, but requires building a 1-dimensional κ-subspace from `x ∉ 𝔪²` | **~80 (substantial sub-helper)** |
| Joint-induction conclusion: assemble `IsRegularLocalRing (R/(x))` of dim `d-1` | `isRegularLocalRing_iff` (`Defs.lean:46`) | 15 |
| `(x)` prime ⟹ minimal prime in `(x)`: `(x)` has height ≥ 1 since `x ∉ ⋃ minimal primes`, hence chain `p₀ ⊊ (x)` with `p₀` minimal | `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes` + chain-extraction | 40 |
| Krull-intersection closing argument: `p₀ ⊆ (x) ⟹ p₀ = x · p₀ ⟹ p₀ ⊆ 𝔪ⁿ ⟹ p₀ = 0` | uses `Ideal.iInf_pow_eq_bot_of_isLocalRing` + `Nakayama` | 50 |
| Lift `(x :: rs')`-regular-sequence from `R/(x)` to `R` | `RingTheory.Sequence.IsRegular.cons` (`Mathlib.RingTheory.Regular.RegularSequence`) | 30 |

**Total estimate**: ≈ 300 LOC, predominantly assembly. The single
non-routine sub-helper is the cotangent-space dim drop (≈ 80 LOC), which
is itself a worthwhile standalone result.

- **Route (a) / (b)**: same proof tree — both go through the joint
  induction above. The directive's "(a) direct via minimal primes /
  Krull intersection" and "(b) regular-quotient induction" are not
  separate routes; they are the two halves of the same induction.
- **Route (c) via Serre's regularity (`pd_R(κ) = d`)**: requires
  `pd_R(κ) = d` for regular local `R`, which is harder than 00NQ
  itself (needs Koszul-complex-is-projective-resolution-of-κ, which is
  NOT in Mathlib at the pinned commit). **Out of scope.**

- **Verdict**: Route (a)=(b) is the only feasible path, ≈ 300 LOC,
  multi-iter, with one substantial sub-helper (cotangent dim drop).

### Decision 3: Alternative route via `IsRegularLocalRing.spanFinrank` — can we construct an `R`-regular sequence in `𝔪` without first proving `IsDomain`?

Briefly: **no, not cleanly**, for the following reason.

The first element `x₁` of the regular sequence must satisfy `IsSMulRegular
R x₁`, i.e. `x₁ ∈ nonZeroDivisors R`. By
`biUnion_associatedPrimes_eq_compl_nonZeroDivisors` (cite:
`Mathlib.RingTheory.Ideal.AssociatedPrime.Basic`), the non-zero-divisors
of a Noetherian `R` are exactly `R \ ⋃ Ass(R)`. So we need `x₁ ∈ 𝔪 \
(𝔪² ∪ ⋃ Ass(R))`.

- `𝔪 ⊄ 𝔪²` from `spanFinrank ≥ 1` ✓.
- `𝔪 ⊄ p` for each *minimal* prime `p`: height(𝔪) = d > 0 = height(p) ✓.
- `𝔪 ⊄ q` for *embedded* primes `q ∈ Ass(R) \ minimalPrimes(R)`:
  **no a priori bound** — embedded primes can have any height between
  `1` and `d`. The standard fact "regular local ⟹ no embedded primes"
  is itself a corollary of `IsRegularLocalRing → IsDomain` (since a
  domain has Ass = {⊥}).

Hence avoiding minimal primes alone is not enough to produce a
non-zero-divisor at step 1, and the induction cannot start without
the IsDomain step. The IsDomain detour is unavoidable.

- **Verdict**: **NO_USEFUL_ALTERNATIVE**. The regular sequence
  existence and the IsDomain implication share the same induction;
  one cannot be cheaply isolated from the other.

## Recommendation

The gap is **genuine Mathlib-upstream content** (Stacks 00NQ has not
been formalized at pinned commit `b80f227`). Three actionable options
for the planner; the right call depends on iter-182's appetite for a
multi-iter sub-project versus a pivot.

**Option 1 (recommended for iter-182): pivot Lane G prover.** Park
`exists_isRegular_of_regularLocal` as a known multi-iter gap. Dispatch
the iter-182 Lane G prover to one of the two off-target depth lemmas
in the same file:

- `depth_eq_smallest_ext_index` (L228) — Stacks 00LP. The Ext
  characterization of depth. Substantive but independent of the
  `IsDomain` gap. Once closed, it becomes the canonical depth
  computation tool and is what `auslander_buchsbaum_formula`
  ultimately consumes.
- `depth_of_short_exact` (L268) — Stacks 00LE. The depth inequalities
  on a SES. Useful infrastructure even before `auslander_buchsbaum`
  lands.

Both have well-defined Mathlib substrates (Ext groups in
`Mathlib.CategoryTheory.Abelian.Ext`, short exact sequences in
`Mathlib.Algebra.Homology.ShortComplex.ShortExact`) and are
self-contained relative to the `IsDomain` chain.

**Option 2 (multi-iter sub-project, project-side): build 00NQ in
two lanes.**

- *Sub-lane G1* (≈ 80 LOC): cotangent-space dim drop lemma. Statement:
  for `x ∈ 𝔪 \ 𝔪²` of a Noetherian local ring `R`, the cotangent
  space of `R/(x)` has dimension one less than that of `R`. Standalone
  and reusable.
- *Sub-lane G2* (≈ 200 LOC): assembly of the joint induction
  delivering both `IsRegularLocalRing R → IsDomain R` and
  `exists_isRegular_of_regularLocal`. Consumes G1.

This is **the right long-term move** if A.4.a is on the critical path
and the Cohen-Macaulay instance is required this quarter. Estimate
2–3 iters with `helper budget ≤ 2` per iter.

**Option 3 (Mathlib upstream PR, parallel).** Submit
`IsRegularLocalRing.toIsDomain` to Mathlib as a standalone PR (the
file `Mathlib.RingTheory.RegularLocalRing.Defs` is the natural home;
the proof needs ≈ 250 LOC and Mathlib reviewers will recognize the
00NQ pattern). Wait time is multi-week and outside the loop's
control. Worth doing in parallel with Option 1.

**Project recommendation**: dispatch Option 1 this iter (pivot to
`depth_eq_smallest_ext_index`) and queue Option 2 as a new STRATEGY
row scheduled for iter-184+ once the off-target depth lemmas have
landed. Option 3 is a side action by the mathematician outside the
loop's prover budget. This sequencing preserves Lane G's iter-by-iter
substantive-content cadence and avoids a 2–3-iter dead lane on a
single sub-project.
