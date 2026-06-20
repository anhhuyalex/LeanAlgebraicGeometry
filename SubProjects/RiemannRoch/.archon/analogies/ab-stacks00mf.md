# Analogy: closing `auslander_buchsbaum_formula_succ_pd` without a standalone Stacks 00MF substrate

## Mode
cross-domain-inspiration

## Slug
ab-stacks00mf

## Iteration
201

## Structural problem (abstracted)

Given an abelian category `C`, a SES `0 → K → P → M → 0` where `P` is a
finite product of a generator-like object `R`, a "test object" `κ`, and a
derived-functor invariant `depth(X) := inf{i : Ext^i(κ, X) ≠ 0}`, recover an
exact equality `depth(K) = depth(M) + 1` from the LES of `Ext^*(κ, -)`. The
upper bound `depth(K) ≤ depth(M) + 1` is the residual difficulty (the lower
bound is the standard "snake-into-LES" assembly). The upper bound boils
down to: at the index `i = depth(M)`, the LES connecting map
`δ : Ext^i(κ, M) → Ext^{i+1}(κ, K)` must be injective, which is equivalent
to the map immediately preceding it, `Ext^i(κ, P) → Ext^i(κ, M)`, being
the zero map at the relevant index.

## Failed approaches (from directive)

- **Full minimal free resolution as a `ChainComplex ℕ`**: 3-4× over budget,
  blocked on a Mathlib-absent termination-of-syzygy-tower lemma.
- **Stacks 090V classical induction on depth(M)**: explicitly retired.
- **Direct AB formula proof in Mathlib's library**: Mathlib does not ship
  `auslander_buchsbaum_formula` axiom-clean.

## Analogues found

### Analogue: `CategoryTheory.Abelian.Ext.covariant_sequence_exact₁` + `_₂` + `_₃` (LES of `Ext^*(X, -)`) — the project's own `depth_of_short_exact` already wires it (`AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean:676–795`)

- **Domain**: derived-functor LES in any abelian category; the project's
  consumer is `RingTheory.Module` over local Noetherian R.
- **Same structural problem there**: the LES injectivity argument the
  project uses for `depth_of_short_exact (3)` (the LOWER bound `min(depth N,
  depth N'' + 1) ≤ depth N'`) is *exactly* the same shape as the desired
  UPPER bound `depth(ker f) ≤ depth(M) + 1`. The difference is the index
  at which one inspects the LES.
- **Technique**: at index `i = depth(M)`, isolate the LES fragment
  `Ext^i(κ, P) →^{·g} Ext^i(κ, M) →^{δ} Ext^{i+1}(κ, K) →^{·f} Ext^{i+1}(κ, P)`.
  If `Ext^i(κ, P) → Ext^i(κ, M)` is the zero map, then `δ` is injective on
  the nonzero source `Ext^i(κ, M) ≠ 0`, forcing `Ext^{i+1}(κ, K) ≠ 0`, i.e.
  `depth(K) ≤ i + 1 = depth(M) + 1`.
  Mathlib's `CategoryTheory.Abelian.Ext.covariant_sequence_exact₂` already
  exposes the existential `x_2.comp(g_*) = 0 ⇒ ∃ x_1, x_1.comp(f_*) = x_2`;
  this is the "injectivity of δ via vanishing of the predecessor" packaged
  as the project's `depth_of_short_exact` helpers use it.
- **Mapping to project**: instantiate the LES at `P = R^n`, `K = ker f`,
  the SES from `exists_minimalSurjection_finite_localRing`, the test object
  `κ = R/𝔪`. The `Ext^i(κ, R^n) → Ext^i(κ, M)` map collapses *because of
  minimality* — see the next analogue.
- **Porting cost**: low (already wired). The same `covariant_sequence_exact₂`
  call pattern used in `depth_of_short_exact` part (1) gives the LES
  injectivity. Cost is in the "the predecessor map is zero" lemma.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `ext_smul_eq_zero_of_mem_annihilator` (project-side, Stacks 00LP, `AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean:229–254`)

- **Domain**: Ext/derived-functor scalar action — the κ-vector-space
  structure on `Ext^*(κ, -)`.
- **Same structural problem there**: "for any `x ∈ Ann(N)` and any
  `e ∈ Ext^i(N, M)`, `x • e = 0`". This is the abstract Stacks 00LP fact
  *the project already proved axiom-clean*. It powers the iter-198 closure of
  `depth_quotSMulTop_succ_eq_depth_of_isSMulRegular`.
- **Technique**: scalar `x ∈ R` acts on `Ext^i(κ, M)` via precomposition
  by `mk₀(x · 𝟙_κ)`. For `x ∈ 𝔪 = Ann(κ)`, `x · 𝟙_κ = 0` in
  `ModuleCat`, so `mk₀ … = mk₀ 0 = 0` and `0.comp e = 0`. The same trick
  applies to **postcomposition**: by R-bilinearity of `Ext.comp` (i.e.
  `Ext.bilinearCompOfLinear` in `Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear`),
  `e.comp (mk₀(x · 𝟙_M))` = `x • (e.comp (mk₀ 𝟙_M))` = `x • e`, and the
  identical annihilator argument yields zero.
- **Mapping to project**: this is the *engine that makes the "predecessor
  map is zero" lemma true*. The "predecessor map" `Ext^i(κ, R^n) → Ext^i(κ, M)`
  is induced by `f : R^n → M`. By minimality (the existing
  `exists_minimalSurjection_finite_localRing` lemma), the matrix `A` of
  the kernel inclusion `K ≅ R^m ↪ R^n` has entries in `𝔪`. The
  postcomposition by `A` (i.e. `Ext^i(κ, A) : Ext^i(κ, R^m) → Ext^i(κ, R^n)`)
  is then the zero map, by the matrix-decomposition route:
  `A = ∑_{i,j} A_{ij} • E_{ij}` (sum over basis matrices, scalars in 𝔪);
  the Ext bilinearity (`Ext.add_comp` + `Ext.smul_comp`) distributes;
  each summand has a factor `A_{ij} ∈ Ann(κ)` acting on
  `Ext^i(κ, R^n)`, which by `ext_smul_eq_zero_of_mem_annihilator` is zero.
  Plug this "predecessor map is zero" into the LES injectivity argument
  above to close the base case `pd M = 1 ⇒ depth M < depth R`.
- **Porting cost**: medium. The matrix-decomposition helper is ~30-60 LOC
  (basis-matrix decomposition of an R-linear map, finite-sum distributivity
  of `Ext.comp`, invoking the existing `ext_smul_eq_zero_of_mem_annihilator`).
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `CategoryTheory.Abelian.Ext.bilinearComp` / `bilinearCompOfLinear` (`Mathlib.Algebra.Homology.DerivedCategory.Ext.{Basic,Linear}`)

- **Domain**: bilinearity of derived-functor composition.
- **Same structural problem there**: `Ext.comp` is `R`-bilinear, with the
  named lemmas `Ext.add_comp`, `Ext.comp_add`, `Ext.smul_comp`,
  `Ext.comp_smul`, and the bundled forms
  `Ext.bilinearComp` (AddCommGroup-bilinear) and
  `Ext.bilinearCompOfLinear` (`R`-bilinear).
- **Technique**: rewrite `Ext.comp` as a bilinear pairing
  `Ext X Y a →ₗ[R] Ext Y Z b →ₗ[R] Ext X Z (a+b)` and apply the standard
  "sum and scalar-multiply commute with the pairing" lemmas. This is
  exactly the machinery needed to push the matrix decomposition through
  `Ext^i(κ, A)`.
- **Mapping to project**: the `Ext.add_comp` + `Ext.smul_comp` lemmas are
  the building blocks of the "predecessor map is zero" lemma above. No
  additional Mathlib infrastructure is needed beyond what is already
  imported transitively.
- **Porting cost**: low (Mathlib provides the lemmas; the use site is the
  ~30-60 LOC matrix-collapse helper described above).
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Module.free_of_flat_of_isLocalRing` (`Mathlib.RingTheory.LocalRing.Module`)

- **Domain**: structure of projectives over local rings.
- **Same structural problem there**: a finite projective module over a
  local ring is free (since projective ⟹ flat, and flat + finite over
  local ⟹ free).
- **Technique**: standard structure result; no novel technique to port.
- **Mapping to project**: in the base case `pd M = 1`, the kernel `K` of
  the minimal surjection has `pd K = 0`, hence projective, hence (being
  finite over a local ring) free. This is what makes `K ≅ R^m` available
  in the base case, which is required for the matrix-decomposition step.
  Direct Mathlib import — no project-side build needed.
- **Porting cost**: low (just invoke `Module.free_of_flat_of_isLocalRing`
  via `Module.Flat.of_projective`).
- **Verdict**: ANALOGUE_FOUND.

### Discarded analogues

- **`Mathlib.RingTheory.KrullDimension.Regular` (depth-via-dim machinery)**:
  the project-side `Module.depth` is built on `Ext`-indices, not on
  `ringKrullDim` arithmetic. The KrullDim-side lemmas do not interface
  with the project's `depth` predicate without an `IsCohenMacaulay`-style
  bridge that the project explicitly is *building*, not consuming. Dropped.
- **Sheaf-cohomology LES injectivity (`Mathlib.Topology.Sheaves.SheafCondition.LocalPredicate`)**:
  structurally identical (`δ` injective when preceding map is zero) but
  the technique boils down to the same `covariant_sequence_exact` shape
  already in hand. No additional value beyond the project's existing
  Ext-LES wiring.
- **Group-cohomology LES (`Mathlib.RepresentationTheory.GroupCohomology`)**:
  same structural shape, same technique, no portable surplus.
- **Cohen-Macaulay depth-comparison short-cut**: the project's
  `CohenMacaulay` predicate (defined this file, §6) is itself downstream
  of the AB formula being closed; using `[CohenMacaulay R]` to side-step
  the closure would be circular. Dropped.

## Top suggestion

**Adopt Path B (LES-injectivity route) rather than Path A (standalone
Stacks 00MF substrate).** The closure splits into:

1. **Inductive step** `pd M = k + 1`, `k ≥ 1` (~50-80 LOC): apply
   `hasProjectiveDimensionLT_ker_of_surjection` + the descent-non-LT
   contrapositive (via `hasProjectiveDimensionLT_succ_of_hasProjectiveDimensionLT_ker`)
   to get `pd K = k` *exactly*. IH gives `k + depth K = depth R`, hence
   `depth K < depth R` (subtraction in ℕ∞ is "honest" because `k ≥ 1` and
   `depth R ≥ k`). Lower-bound `depth M ≥ depth K - 1` from
   `depth_of_short_exact` part (2). Upper-bound `depth M ≤ depth K - 1` by
   contradiction: assume `depth M ≥ depth K`, inspect the LES at
   `i = depth K`, conclude `Ext^{depth K}(κ, R^n)` injects from
   `Ext^{depth K}(κ, K) ≠ 0`, so `depth R ≤ depth K`, contradicting IH.

2. **Base case** `pd M = 1` (~80-120 LOC): `K = ker f` is finite
   projective over local Noetherian R, hence free
   (`Module.free_of_flat_of_isLocalRing` via
   `Module.Flat.of_projective`). Pick a basis to get `K ≅ R^m` (m ≥ 1
   since M is not projective). The inclusion `K ↪ R^n` corresponds to an
   `(n × m)`-matrix `A` whose entries lie in `𝔪` (from minimality —
   `ker f ≤ 𝔪 • ⊤`). Build the helper:

   > **Lemma** (matrix-collapse): For `A : R^m → R^n` with all entries
   > in `𝔪 = Ann(κ)`, the postcomposition map
   > `(- ∘ mk₀ A) : Ext^i(κ, R^m) → Ext^i(κ, R^n)` is zero.

   Proof: `A = ∑_{i,j} A_{ij} • E_{ij}` (basis-matrix decomposition);
   by `Ext.add_comp` + `Ext.smul_comp` (Mathlib's bilinear-comp infra),
   `Ext^i(κ, A) = ∑_{i,j} A_{ij} • Ext^i(κ, E_{ij})`. Each summand has a
   scalar factor `A_{ij} ∈ Ann(κ)` acting on `Ext^i(κ, R^n)`, which by
   the *existing* helper `ext_smul_eq_zero_of_mem_annihilator` is zero.
   Hence the whole sum is zero. ~50-80 LOC.

   With matrix-collapse in hand, the LES at `i = depth R - 1` gives
   `Ext^{depth R - 1}(κ, M) → Ext^{depth R}(κ, K) → Ext^{depth R}(κ, R^n)`
   with the second map equal to `Ext(κ, A) = 0`. If `depth M ≥ depth R`
   the source vanishes, so `Ext^{depth R}(κ, K)` would have to be zero —
   but `K ≅ R^m`, `m ≥ 1`, so `depth K = depth R` and
   `Ext^{depth R}(κ, K) ≠ 0`. Contradiction. Hence `depth M < depth R`.

**Total Path B LOC estimate: ~130-200 LOC**, comparable to Path A but
without committing to a generic Buchsbaum-Eisenbud / Stacks 00MF
predicate that has no other downstream consumer in the project. The
binding new helper is the matrix-collapse lemma, which is purely a
linear-algebraic decomposition + the existing `ext_smul_…annihilator`
trick.

First Mathlib file to read for matrix-decomposition idioms:
`Mathlib.LinearAlgebra.Matrix.ToLin` (matrix ↔ linear map between
finite-free modules) and
`Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear` (R-linearity of
`Ext.comp`). First project file to touch: extend
`AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean` around line 1290
(the `RingTheory.Module` namespace with the existing `HasProjectiveDimensionLT`
helpers) with the matrix-collapse lemma, then expand
`auslander_buchsbaum_formula_succ_pd` (L1517) to take the inductive +
base-case branches and close the `sorry` at L1574.
