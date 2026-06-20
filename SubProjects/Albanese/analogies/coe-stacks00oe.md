# Analogy: Stacks 00OE — Krull-dim of smooth k-algebra at a maximal ideal

## Mode
cross-domain-inspiration

## Slug
coe-stacks00oe

## Iteration
200

## Structural problem (abstracted)

Given a smooth `R`-algebra `S` of relative dimension `n` and a maximal
ideal `m ⊂ S`, prove `ringKrullDim (S_m) = n` (equivalently
`m.height = n`). The structural shape is: "Krull dim of a localization
at a closed point equals a numerical invariant that comes from a
*finite presentation* of `S` over the base ring `R`". The numerical
invariant is `#generators − #relations` for a standard-smooth
presentation; the closed-point dimension is computed by combining
(a) the *Krull dim of the polynomial-ring localization at a maximal*
(known closed form: `=#generators`) with (b) "cut by a regular
sequence of length `#relations`" (drops dim by exactly the length).

## Failed approaches (from directive)

- **Stacks 00OE direct (fiber-dim + going-down)**: structurally sound
  but invokes an unbroken chain of Mathlib lemmas in sequence
  (going-down, fiber dim, polynomial-ring dim, Noether normalization
  in some variants) that requires careful chaining.
- **iter-198/199 Lane COE exploration**: no closure attempt committed;
  no specific failed Lean route to avoid recommending.

The failed-approach list is empty in the "what NOT to port back" sense
— the project hasn't tried and rejected anything. Every Mathlib
analogue below is fair game.

## Analogues found

Ranked by porting cost (lowest first). Mathlib does NOT package
Stacks 00OE as a single named lemma; it ships every *building block*
in usable form, so the project's task is **chaining**, not building
new infrastructure.

### Analogue 1: `Polynomial.height_eq_height_add_one`

- **Domain**: commutative algebra / Krull-dimension theory of
  polynomial rings. `Mathlib.RingTheory.KrullDimension.Polynomial`.
- **Same structural problem there**: for `R` Noetherian and any
  maximal ideal `P ⊂ R[X]` lying over a (necessarily prime) ideal
  `p ⊂ R`, we have `P.height = p.height + 1`. This is exactly the
  inductive step underlying "every maximal ideal in `k[x_1,…,x_n]`
  has height `n`" — iterate `n` times starting from a field
  (`p = 0`, `p.height = 0`).
- **Technique**: the proof goes by reducing to the case where `p`
  itself is maximal (using `Polynomial.isMaximal_comap_C_of_isJacobsonRing`
  / general height-bound machinery), then invoking Krull's principal
  ideal theorem to bound `P.height ≤ p.height + 1` and equality via
  an explicit chain of primes `(0) ⊂ pR[X] ⊂ P`.
- **Mapping to project**: for the closed-fiber part of Stacks 00OE,
  pull back `m ⊂ S` along the standard-smooth presentation surjection
  `R[ι] → S` to get a maximal ideal `m' = preimage(m) ∪ {f_j}` in
  `R[ι]`. The "polynomial-ring height" half computes
  `(preimage of m in R[ι])_localized.height = #ι` by iterating this
  lemma `#ι` times over the base ring `R` (here a field, so
  `R.ringKrullDim = 0` via `ringKrullDim_eq_zero_of_field`).
- **Porting cost**: low (≤ 30 LOC for the polynomial-ring induction
  packaged as a project-side helper). No new Mathlib gap.
- **Verdict**: ANALOGUE_FOUND.

### Analogue 2: `ringKrullDim_add_length_eq_ringKrullDim_of_isRegular`

- **Domain**: commutative algebra / regular-sequence theory.
  `Mathlib.RingTheory.KrullDimension.Regular`.
- **Same structural problem there**: for `R` Noetherian local and a
  regular sequence `rs : List R`,
  `ringKrullDim (R ⧸ Ideal.ofList rs) + rs.length = ringKrullDim R`.
  This is the *exact* statement Stacks 00OE invokes to drop dim by
  the number of relations: "modding out by a regular sequence
  decreases Krull dimension by its length".
- **Technique**: induction on the sequence length combined with
  `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` (the
  single-element case, which is Krull's principal ideal theorem in
  the form "a regular element drops dim by 1"). The single-step
  proof uses `IsSMulRegular` + non-zero-divisor membership of the
  maximal ideal.
- **Mapping to project**: for the standard-smooth presentation
  `S = R[ι] ⧸ (f_j, j ∈ σ)` with Jacobian matrix invertible, localize
  at `m' = preimage(m) ⊂ R[ι]`. Apply this lemma to
  `R' := R[ι]_{m'}` with the regular sequence `(f_j)_{j ∈ σ}`:
  `ringKrullDim (R' ⧸ (f_j)) + #σ = ringKrullDim R'`. The LHS is
  `ringKrullDim S_m` (since localization commutes with quotient
  by an ideal in the prime), the RHS is `#ι` by Analogue 1, and
  `n = #ι − #σ`.
- **Residual obligation**: show `(f_j)_{j ∈ σ}` is a regular sequence
  in `R[ι]_{m'}`. This is genuine content — it's the algebraic
  meaning of "the Jacobian is invertible" (Stacks tag 00SW / 00OW
  for the smooth case). In Mathlib at commit `b80f227` this
  regular-sequence-from-Jacobian step is not packaged; it must be
  built project-side as a 30–60 LOC helper that consumes
  `Algebra.SubmersivePresentation.jacobian_isUnit` and concludes
  `IsWeaklyRegular` via `IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal`.
- **Porting cost**: medium. The dim-drop lemma is a direct apply;
  the regular-sequence construction from the Jacobian is the
  substantive new helper (~30–60 LOC, axiom-clean against
  Mathlib's SubmersivePresentation API).
- **Verdict**: ANALOGUE_FOUND. **Top recommendation for the
  dim-arithmetic backbone.**

### Analogue 3: `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`

- **Domain**: commutative algebra / going-down for ring extensions.
  `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`.
- **Same structural problem there**: for `R`, `S` Noetherian with
  `R → S` having going-down (e.g. flat), `p ⊂ R` prime, `P ⊂ S`
  prime over `p`:
  `P.height = p.height + (height of P/pS in S/pS)`.
  This is the *fiber-dimension formula* — height of a prime in `S`
  decomposes as height in the base plus height in the closed fiber.
- **Technique**: combines `Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap`
  (going-down ⟺ generalization-preserving on Spec) with a chain-of-primes
  argument that lifts a maximal chain in `S/pS` and a maximal chain in
  `R` below `p` to a single maximal chain in `S` through `P`.
- **Mapping to project**: with `R = k` (field), `S` smooth over `k`,
  this fires with `p = 0`, `p.height = 0`, going-down free via
  `Algebra.Smooth.flat` ⟹ `Algebra.HasGoingDown.of_flat`. The formula
  reduces to `m.height = (height of m/0·S in S/0·S) = m.height in S`
  — i.e. a TAUTOLOGY when the base is a field. So this analogue
  shines NOT for the smooth-over-field case directly, but as a
  *re-usable middle step* when one wants to compose the smooth case
  with the Noether-normalization reduction (where the polynomial
  subring is itself an intermediate `R'` with non-trivial height).
- **Porting cost**: low if used as a re-export. But not the right
  driver for the field-base case.
- **Verdict**: PARTIAL_ANALOGUE — applicable but not the central
  technique for the specific closure the project needs (`R = k̄`).

### Analogue 4: `IsLocalization.AtPrime.ringKrullDim_eq_height` + `IsLocalRing.maximalIdeal_height_eq_ringKrullDim`

- **Domain**: commutative algebra / localization-and-dimension API.
  `Mathlib.RingTheory.Ideal.Height`.
- **Same structural problem there**: bridging `ringKrullDim` of a
  localization with `Ideal.height` of the localized prime:
  `ringKrullDim (Localization.atPrime p) = ↑p.height`, and the
  dual `↑(maximalIdeal R).height = ringKrullDim R` for any local R.
- **Technique**: definitional unfolding of `ringKrullDim` as the
  sup of `Ideal.primeHeight` over `IsPrime`, combined with the
  bijection `Spec(R_p) ↔ {q ∈ Spec R | q ≤ p}` that swaps the sup
  for `p.height`.
- **Mapping to project**: this is the *boundary translator* — the
  project's `isRegularLocalRing_stalk_of_smooth` goal lives on
  `ringKrullDim (X.left.presheaf.stalk z)`, which is
  `ringKrullDim (Localization.atPrime m)` via the project's
  `Scheme.ringKrullDim_stalk_eq_coheight` bridge (iter-183). To
  consume Analogues 1+2 (which speak `Ideal.height`), the proof
  starts with `IsLocalization.AtPrime.ringKrullDim_eq_height` to
  recast the goal as `m.height = n`, then runs the
  height-arithmetic chain.
- **Porting cost**: trivial (one rewrite).
- **Verdict**: ANALOGUE_FOUND. **Required adapter; not a stand-alone
  technique.**

### Analogue 5: `MvPolynomial.ringKrullDim_of_isNoetherianRing`

- **Domain**: commutative algebra / polynomial-ring dimension.
  `Mathlib.RingTheory.KrullDimension.Polynomial`.
- **Same structural problem there**: for `R` Noetherian and `ι` finite,
  `ringKrullDim (MvPolynomial ι R) = ringKrullDim R + ↑(Nat.card ι)`.
  Combined with `ringKrullDim_eq_zero_of_field`, this gives
  `ringKrullDim (k[ι]) = #ι` for the polynomial ring over a field.
- **Technique**: induction on `#ι`, reducing to `Polynomial.ringKrullDim_of_isNoetherianRing`,
  which in turn invokes a chain argument: `0 ⊂ X·R[X] ⊂ M` for any
  maximal `M`, plus a height-upper-bound from Krull's principal
  ideal theorem.
- **Mapping to project**: useful if the project wants to bound
  `m'.height ≤ ringKrullDim k[ι] = #ι` rather than computing it
  directly via Analogue 1. For the LOWER bound (the substantive
  half) the project still needs Analogue 1's per-maximal-ideal
  iteration. So this gives a one-line upper bound but not the
  equality.
- **Porting cost**: trivial as upper-bound; equality needs Analogue 1.
- **Verdict**: PARTIAL_ANALOGUE — bound-only, not equality.

### Analogue 6: `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`

- **Domain**: commutative algebra / Kähler differentials of
  standard-smooth algebras. `Mathlib.RingTheory.Smooth.StandardSmoothCotangent`.
- **Same structural problem there**: connects the `relativeDimension`
  numerical invariant with the rank of `Ω[S⁄R]` as an `S`-module:
  `Module.rank S Ω[S⁄R] = ↑n` for standard-smooth of rel dim `n`.
  This is the project's *iter-198 (i)-resolution* path — extract a
  specific `n` from the smooth structure and then use it consistently.
- **Technique**: extracts a `SubmersivePresentation` from the
  `IsStandardSmoothOfRelativeDimension` instance and uses the
  basis-of-Kähler-differentials computation for the presentation.
- **Mapping to project**: this is what the iter-198 closure of
  sub-gap (i) already rides on (the project's `rank_kaehlerDifferential_localization_eq_relativeDimension`).
  It does NOT directly give Krull-dim — Mathlib has no lemma
  `Algebra.IsStandardSmoothOfRelativeDimension.ringKrullDim_eq` or
  `_at_maximal_height_eq` to short-circuit Stacks 00OE.
- **Porting cost**: zero (already in use in the project at
  iter-198).
- **Verdict**: NO_USEFUL_ANALOGUE for sub-gap (ii.B) directly — it
  is the *cotangent-side* invariant computation, distinct from the
  Krull-dim side that (ii.B) needs.

## Top suggestion

**Compose Analogues 4 + 1 + 2** as a project-side helper chain
`smoothAlgebra_relativeDim_ringKrullDim_localization`. The recipe in
three steps:

```text
Setup (existing iter-198/199 helpers do this):
  S = standard-smooth k-algebra of relative dim n
  m ⊂ S maximal
  S_m = Localization.AtPrime S m (already wired via Stage 3)
  P : SubmersivePresentation k S ι σ with P.dimension = n   -- iter-198
  R'  := MvPolynomial ι k                                   -- the presentation source
  m'  := preimage of m in R'                                -- maximal in R'
  R'_{m'} := Localization.AtPrime R' m'
  Surjection ϕ : R'_{m'} ↠ S_m with kernel = (f_j)_{j ∈ σ}  -- localized presentation

Step 1 — recast Krull-dim as height:
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m S_m]
  -- Goal:  m.height = ↑n

Step 2 — compute the polynomial-ring height:
  have hPoly : m'.height = ↑(Nat.card ι) := by
    -- iterate Polynomial.height_eq_height_add_one #ι times,
    -- bottoming out at p = 0 with p.height = 0 (k is a field)
    sorry  -- ≤ 30 LOC packaged helper

Step 3 — drop by the regular-sequence length:
  -- Convert Stage 1 (smooth ⟹ flat) + iter-198 SubmersivePresentation
  -- + Jacobian_isUnit into:
  have hReg : RingTheory.Sequence.IsRegular R'_{m'} (relations ϕ)
  have hLen : (relations ϕ).length = Nat.card σ
  have hDimRel :
    ringKrullDim (R'_{m'} ⧸ Ideal.ofList (relations ϕ)) + Nat.card σ
      = ringKrullDim R'_{m'} :=
    ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hReg
  -- LHS ⧸ side = ringKrullDim S_m via ϕ
  -- RHS = #ι via Step 2 + IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  -- Solve for ringKrullDim S_m = #ι − #σ = n
  arithmetic
```

**The substantive residual obligation is Step 3's `hReg`** —
showing the relations of a SubmersivePresentation form a regular
sequence in `R'_{m'}`. This is Stacks 00SW (in the smooth-over-flat
case) / 00OW (Jacobian criterion); the abstract content is "the
Jacobian matrix being invertible at the closed point makes the
relations Koszul-regular". In Mathlib's current state at
`b80f227`, this is the only piece **not** ready to apply directly.

A reasonable project-side build estimate for the residual:
30–60 LOC, axiom-clean against
`Algebra.SubmersivePresentation.jacobian_isUnit` +
`RingTheory.Sequence.isRegular_cons_iff` +
`IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal`.

Steps 1 + 2 + the surjection-arithmetic in Step 3 total ≈ 50 LOC of
pure chaining of existing Mathlib lemmas.

**Total iter-201+ build estimate**: 80–120 LOC inside
`Albanese/CodimOneExtension.lean` (or split into a dedicated
`Picard/SmoothAlgebraKrullDim.lean` helper). This is **below** the
directive's "200–300 LOC on top of `transcendenceDegree` +
Noether-normalization" estimate, because the route via the
SubmersivePresentation already in hand (from iter-198) bypasses
the explicit Noether normalization step.

**First file to touch (iter-201+)**:
`AlgebraicJacobian/Albanese/CodimOneExtension.lean` around line 836
(the comment block flagged "Sub-gap (ii.B)"), or a new
`AlgebraicJacobian/Albanese/SmoothKrullDim.lean` that exports a
single helper `ringKrullDim_localization_of_isStandardSmoothOfRelativeDimension`
which the main theorem consumes via one rewrite.

## Fallback route

If Step 3's `hReg` construction proves harder than 60 LOC (the
SubmersivePresentation's relations are in `MvPolynomial ι R`, not
in `R'_{m'}`, so a base-change/extension-of-scalars argument is
needed to lift them as regular in the localization), fall back to
**Analogue 5 + iter-199's cotangent-iso (ii.A) closure**: use
`ringKrullDim_le_ringKrullDim_add_spanFinrank` to get
`ringKrullDim S_m ≤ ringKrullDim (S_m/m) + #generators of m`. With
`S_m/m = κ` (dim 0) and `#generators of m = finrank κ (m/m²) = n`
(by iter-199's (ii.A) closure), this gives **the upper bound
`ringKrullDim S_m ≤ n`**. For the lower bound, descend along the
flat map `k → S_m` and use Krull's height theorem in the form
`Ideal.height_le_spanFinrank` reversed via the Jacobian regularity.
This fallback is conceptually messier but reuses (ii.A) cotangent
finrank already in hand.

## Discarded

- **Noether normalization (`exists_finite_inj_algHom_of_fg`) +
  going-up over a polynomial subring**: feasible (Mathlib has the
  normalization plus going-up via integral extensions in
  `Mathlib.RingTheory.IntegralClosure.GoingDown`), but adds an
  intermediate Krull-dim equality that's strictly harder than
  the standard-smooth-presentation route — Noether normalization
  is generic, not closed-point aware, and the explicit
  SubmersivePresentation already encodes the Krull-dim arithmetic
  via Analogues 1+2. Keep in reserve only if the SubmersivePresentation
  ↦ regular-sequence step in Analogue 2 turns out infeasible.
- **`Module.supportDim` / `Module.supportDim_eq_ringKrullDim_quotient_annihilator`**:
  same Krull-dim content via a different packaging, doesn't add
  new technique.
- **`Algebra.trdeg` (transcendence-degree route)**: Mathlib has
  the transcendence-degree-vs-Krull-dim chain only for special
  cases (`trdeg_eq_zero` for algebraic extensions, `Polynomial.trdeg_of_isDomain`
  for the polynomial case). No general "trdeg = Krull dim for
  finite-type k-algebra integral domains" lemma exists at commit
  `b80f227`. Discarded — would itself require Stacks 00OE-shape
  reasoning to build.
- **Direct `IsRegularLocalRing.iff_finrank_cotangentSpace` consumer
  shortcut**: this is what the project's *consumer route* already
  uses (cotangent finrank = n + Krull dim = n ⟹ regular). It does
  not by itself give Krull dim; it consumes the (ii.B) output.
