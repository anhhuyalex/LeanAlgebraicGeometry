# Analogy: H1Cotangent / Γ-vanishing pivot for rigidity_over_kbar (M2.a closure)

## Mode

cross-domain-inspiration

## Slug

h1cotangent-vanishing-iter150

## Iteration

150

## Structural problem (abstracted)

We have a smooth proper geometrically irreducible scheme `X` over a field `k` and need to conclude that a chart-algebra section `b : B` annihilated by the universal Kähler derivation `D : B → Ω_{B/k}` lies in the image of `algebraMap k B`. The currently-committed path (b) decomposes this into a global cohomology statement `Γ(X, O_X) ≅ k` (sub-claims (S3.sep.1), (S3.sep.2), (S3.pi.1), (S3.pi.2)). The directive asks whether (a) the SAME content is available in Mathlib via the typeclass `Algebra.H1Cotangent k B`, (b) `rigidity_over_kbar` could consume `Subsingleton (H1Cotangent k B)` instead of `Γ ≅ k`, (c) alternative shapes (formal-scheme-style, Hopf-algebra-style, joint-derivation-kernel-style) exist elsewhere in Mathlib that could be ported.

The underlying mathematical pattern is "structure-equation cohomology in degree 0 = the base ring", encompassing both global-sections statements (Γ(X, O_X) = k for proper integral / connected) and chart-algebra statements (joint kernel of coordinate derivations = k in standard-smooth chart).

## Failed approaches (from directive)

- **Path (a) BUILD proper-Γ-flat-base-change in-tree** (~250–300 LOC): same Mathlib gap as path (b) step (e); requires Čech-equaliser + flat-tensor-exactness chase. Mathlib `b80f227` ships no `AlgebraicGeometry.IsBaseChange` namespace nor `R^iπ_*` for proper π.
- **Path (b) SMART PROOF via four (S3.*) sub-claims** (~310–550 LOC): (S3.pi.1) is the same Mathlib gap as path (a) step (e). Iter-149 status: 0/4 bodies closed.
- **KDM (p2) char-0 bridge** (iter-149 (BR.1)–(BR.4) scaffolded, (BR.5) joint-kernel-collapse remains structured sorry): the underlying obstacle is that Mathlib's `Differential.ContainConstants` typeclass packages a SINGLE-derivation property `b' = 0 ⇒ b ∈ range`, not the INTERSECTION of multiple coordinate derivations. Single-derivation kernel is strictly larger than `range (algebraMap k B)`.

## Analogues found

### Analogue: `Algebra.FormallyUnramified.range_eq_top_of_isPurelyInseparable` + `PerfectField.ofCharZero` + `Algebra.IsAlgebraic.isSeparable_of_perfectField` — CharZero-only collapse of the (S3.sep.*) lane

- **Domain**: ring theory + field theory (`Mathlib.RingTheory.Unramified.Field`,
  `Mathlib.FieldTheory.Perfect`).
- **Same structural problem there**: For a finite field extension `Γ/k` with the
  combination "purely inseparable + separable", `algebraMap k Γ` is surjective.
  Distance from project's problem: IDENTICAL on the ring side — this is literally
  the closing lemma already invoked at `ChartAlgebra.lean:460`
  (`IsPurelyInseparable.surjective_algebraMap_of_isSeparable`). The novelty
  surfaced here is the CharZero-specific instance chain that closes (b.1)
  separability for free.
- **Citations (verified live via `lean_leansearch`)**:
  - `Algebra.FormallyUnramified.range_eq_top_of_isPurelyInseparable`
    (`Mathlib.RingTheory.Unramified.Field`):
    `[Field K] [Field L] [Algebra K L] [Algebra.FormallyUnramified K L]
     [Algebra.EssFiniteType K L] [IsPurelyInseparable K L] →
     (algebraMap K L).range = ⊤`.
  - `Algebra.IsAlgebraic.isSeparable_of_perfectField` (instance in
    `Mathlib.FieldTheory.Perfect`):
    `[Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L] [PerfectField K] →
     Algebra.IsSeparable K L`.
  - `PerfectField.ofCharZero` (instance in `Mathlib.FieldTheory.Perfect`):
    `[Field K] [CharZero K] → PerfectField K`.
  - `Algebra.FormallyUnramified.iff_isSeparable`
    (`Mathlib.RingTheory.Unramified.Field`):
    `[Field K] [Field L] [Algebra K L] [Algebra.EssFiniteType K L] →
     (Algebra.FormallyUnramified K L ↔ Algebra.IsSeparable K L)`.
  - `Algebra.FormallySmooth.of_perfectField` (instance in
    `Mathlib.RingTheory.Smooth.Field`):
    `[Field K] [Field L] [Algebra K L] [PerfectField K] [Algebra.EssFiniteType K L]
     → Algebra.FormallySmooth K L`.
- **Technique**: In `CharZero`, `PerfectField k` is automatic; every algebraic
  extension of a perfect field is separable; so any finite-dimensional `Γ/k`
  satisfies `Algebra.IsSeparable k Γ` via the instance chain
  `CharZero → PerfectField → IsAlgebraic.isSeparable_of_perfectField`. The
  separability lane (b.1) becomes a one-liner. (S3.sep.1) +(S3.sep.2) collapse
  into a single `inferInstance` call once `[CharZero k]` is propagated.
- **Mapping to project**: The downstream consumers of
  `constants_integral_over_base_field` already commit to `[CharZero k]`:
  - `KaehlerDifferential.mem_range_algebraMap_of_D_eq_zero`
    (`ChartAlgebra.lean:123–194`) has `[CharZero k]`.
  - `df_zero_factors_through_constant_on_chart`
    (`ChartAlgebra.lean:222–240`) has `[CharZero k]`.

  Specialising `constants_integral_over_base_field` to `[CharZero k]` loses
  NOTHING downstream. The (b.1) lane in `ChartAlgebra.lean:424–457` then closes
  in ~5 LOC: replace the explicit
  `IsSeparable.of_isGeometricallyReduced_of_finite` call with a
  `haveI : Algebra.IsAlgebraic k Γ := Algebra.IsIntegral.isAlgebraic`
  (from the existing `_hAppTopFinite`) + the `isSeparable_of_perfectField`
  instance.

  (S3.sep.1) `isGeometricallyReduced_Gamma_of_smooth` and (S3.sep.2)
  `IsSeparable.of_isGeometricallyReduced_of_finite` become UNUSED in the
  CharZero-specialised path. They remain interesting Mathlib-PR-grade
  contributions for the general-`k` setting, but the project's M2.a critical
  path does not need them.

  **Important caveat**: the (b.2) `IsPurelyInseparable k Γ` lane is NOT
  collapsed by CharZero alone — it still requires either (S3.pi.1) flat
  base change of Γ (to derive the unique-minimal-prime hypothesis from
  `IsIntegral X_{\bar k}`), or a different angle entirely. CharZero collapses
  only the easier half of the four-sub-claim decomposition.
- **Porting cost**: **LOW** — ~10 LOC of typeclass propagation +
  ~5 LOC at the (b.1) branch + ~3 LOC at the
  `constants_integral_over_base_field` signature. No new infrastructure;
  pure consumer-side reduction.
- **Verdict**: **ANALOGUE_FOUND**.

### Analogue: Consumer reformulation over `\bar k` (sidestep (S3.pi.*) entirely)

- **Domain**: meta-strategic; the project's own iter-148 analogy
  ([[step-e-iter148]] § "Strategic recommendation to the planner") already
  flagged this as the first-choice route.
- **Same structural problem there**: when `k = \bar k` is algebraically
  closed, `constants_integral_over_base_field` collapses: `IsField Γ` +
  `(appTop).Finite` + `IsAlgClosed k` give `Γ = k` directly via
  `IsAlgClosed.algebraMap_surjective`
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`). No base-change-of-Γ needed.
- **Citations (verified)**:
  - `IsAlgClosed.algebraMap_bijective_of_isIntegral`
    (`Mathlib.FieldTheory.IsAlgClosed.Basic`):
    `[Field k] [Ring K] [IsDomain K] [IsAlgClosed k] [Algebra k K]
     [Algebra.IsIntegral k K] → Function.Bijective (algebraMap k K)`.
  - `IsAlgClosed.ringHom_bijective_of_isIntegral`
    (`Mathlib.FieldTheory.IsAlgClosed.Basic`) — the underlying RingHom form.
- **Technique**: substitute `k := \bar k` (project's `kbar` in `RigidityKbar.lean`)
  upfront. The hypothesis `Γ = \bar k` becomes immediate from
  alg-closedness-of-base + integrality-of-extension. The whole (S3.pi.*) +
  (S3.sep.*) chain becomes unused for the `rigidity_over_kbar` consumer.
- **Mapping to project**:
  - `rigidity_over_kbar`'s ambient base field IS `\bar k` (variable `kbar`,
    `[Field kbar]`). The downstream chain
    `rigidity_over_kbar → Scheme.Over.ext_of_diff_zero → df_zero_factors_through_constant_on_chart → KaehlerDifferential.mem_range_algebraMap_of_D_eq_zero → constants_integral_over_base_field`
    runs entirely over `\bar k`.
  - Hypothesize `[IsAlgClosed k]` on `constants_integral_over_base_field`
    (or write a `constants_integral_over_base_field_of_isAlgClosed`
    specialisation). The body collapses to ~15 LOC:
    1. Reduce surjectivity of `appTop.hom` to surjectivity of `algebraMap k Γ`
       (already done iter-148).
    2. Extract `IsField Γ` from `isField_of_universallyClosed` (already done).
    3. Extract `Module.Finite k Γ` from `_hAppTopFinite` (already done iter-149).
    4. `haveI : Algebra.IsIntegral k Γ := ⟨Algebra.IsIntegral.of_finite⟩`.
    5. `exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k)
       (K := Γ)).2` (extracting surjectivity from bijectivity).
  - The four (S3.*) sub-claims become DEAD CODE for the `rigidity_over_kbar`
    consumer — they are useful only for the over-`k` formulation which is
    not on the critical path.
- **Porting cost**: **LOW** — ~15 LOC for a new
  `constants_integral_over_base_field_of_isAlgClosed` specialisation +
  ~5 LOC at the consumer site of `df_zero_factors_through_constant_on_chart`
  to substitute the specialisation in.
- **Verdict**: **ANALOGUE_FOUND**. This was the iter-148 first-choice
  recommendation; iter-149 chose path (b) instead because the chart-algebra
  envelope and the iter-149 (S3.*) decomposition were already substantially
  scaffolded. The iter-150 escalation hook should revisit this decision.

### Analogue: `MvPolynomial.mkDerivation` + `MvPolynomial.derivation_C` + `MvPolynomial.derivation_eq_of_forall_mem_vars` — joint-coordinate-derivation kernel directly (KDM (BR.5) shortcut)

- **Domain**: commutative algebra / polynomial algebra
  (`Mathlib.Algebra.MvPolynomial.Derivation`).
- **Same structural problem there**: in `MvPolynomial σ k`, the joint kernel
  of all coordinate `pderiv_i` equals `MvPolynomial.C.range` (constants). This
  is the FREE case of the joint-kernel-collapse problem.
- **Citations (verified)**:
  - `MvPolynomial.derivation_C`: `D (C a) = 0` for any derivation `D : Derivation R (MvPolynomial σ R) A`.
  - `MvPolynomial.derivation_eq_of_forall_mem_vars`: a derivation is
    determined by its values on `f.vars`, i.e. on coordinate-indeterminates
    relevant to `f`.
  - `MvPolynomial.pderiv` + `MvPolynomial.pderiv_C`: coordinate derivatives
    annihilate constants.
- **Technique**: For `MvPolynomial σ k` of finite `σ` over a CharZero `k`, the
  joint kernel `⋂_i ker(pderiv_i)` equals `MvPolynomial.C.range` by direct
  monomial expansion — each monomial `c · ∏ x_i^{e_i}` with any `e_j > 0`
  gets sent to `c · e_j · x_j^{e_j - 1} · ∏_{i ≠ j} x_i^{e_i} ≠ 0` by
  `pderiv_j` (using `CharZero` to ensure `e_j ≠ 0` doesn't get killed).
  Mathlib's `MvPolynomial` API supports this directly via the monomial
  basis lemmas.
- **Mapping to project**: The KDM (BR.5) joint-kernel-collapse for a STANDARD
  SMOOTH chart `B = MvPolynomial σ k / I` reduces to two sub-pieces:
  - **Free case** for `MvPolynomial σ k`: handled by direct
    `MvPolynomial.pderiv`-monomial argument (~25 LOC).
  - **Quotient transfer**: lift the joint-kernel-equals-constants statement
    from `MvPolynomial σ k` to `MvPolynomial σ k / I` via the surjection
    `MvPolynomial σ k →ₐ[k] B`. For a STANDARD-smooth chart, the surjection
    is the kernel-of-Jacobian-invertible map; the kernel `I` contains no
    elements of `range C` other than `0`, so the joint-kernel-equals-constants
    statement transfers cleanly (~30–40 LOC).
- **Porting cost**: **MEDIUM** — ~60–80 LOC total (the directive's
  iter-149 estimate of 40–80 LOC for (BR.5) is in range with the lower
  half of this estimate). The Mathlib base is ready; no new infrastructure
  is needed beyond the quotient-transfer step.
- **Verdict**: **ANALOGUE_FOUND**.

### Analogue: `Algebra.FormallySmooth.of_perfectField` (chart-side FormallySmooth-for-free in CharZero)

- **Domain**: ring theory (`Mathlib.RingTheory.Smooth.Field`).
- **Same structural problem there**: capture "smoothness is automatic" over
  perfect fields for essentially-finite-type algebras.
- **Citations (verified)**:
  - `Algebra.FormallySmooth.of_perfectField` (instance): `[PerfectField K]
    [Algebra.EssFiniteType K L] → Algebra.FormallySmooth K L` (L is a field).
- **Technique**: derive `FormallySmooth k L` for any essentially-finite-type
  L over a perfect k.
- **Mapping to project**: For the KDM lemma, the chart algebra `B` is NOT a
  field but a chart-ring of positive Krull dimension; `Algebra.FormallySmooth.
  of_perfectField` does NOT directly apply. The lemma `Algebra.Smooth.formallySmooth`
  combined with `Algebra.instSmoothOfIsStandardSmooth` already supplies
  `FormallySmooth k B` for free under the iter-149 `[IsStandardSmoothOfRelativeDimension
  n k B]` hypothesis. So FormallySmooth for the chart-side is ALREADY a "free"
  premise; the question is what to DO with it.
  Having `FormallySmooth k B` gives:
  - `Subsingleton (H1Cotangent k B)` via `subsingleton_h1Cotangent`.
  - `Module.Projective B Ω[B⁄k]` (already known via `IsStandardSmooth.free_kaehlerDifferential`).
  Neither directly closes the KDM kernel-is-constants problem.
- **Porting cost**: zero (instance already fires under iter-149 typeclass
  setup) — but the benefit to KDM (BR.5) closure is also approximately zero.
- **Verdict**: **PARTIAL_ANALOGUE** — clarifies that `FormallySmooth` is
  not the right shape for the kernel-of-D problem; H1Cotangent vanishing
  is independent content from the joint-derivation-kernel collapse.

### Analogue (DISCARDED): `Subsingleton (Algebra.H1Cotangent k B)` as the H1Cotangent-vanishing PIVOT for rigidity_over_kbar

- **Citations**: `Algebra.FormallySmooth.subsingleton_h1Cotangent`
  (`Mathlib.RingTheory.Smooth.Basic`),
  `Algebra.IsStandardSmooth.subsingleton_h1Cotangent`
  (`Mathlib.RingTheory.Smooth.StandardSmoothCotangent`).
- **Reason for discard**: the directive's question (b) "can the chart-algebra
  closure chain consume `Subsingleton (Algebra.H1Cotangent k B)` directly,
  without routing through the `Γ ≅ k` global statement?" is based on a
  SUPERFICIAL similarity that does not survive mathematical scrutiny:
  - `Subsingleton (H1Cotangent k B)` is a statement about the SECOND cotangent
    cohomology — it says certain extensions `0 → I → R → B → 0` (with
    `I^2 = 0`) admit liftings. It is a STRUCTURAL property of the
    presentation-of-B, NOT a statement about kernels of derivations.
  - `Γ(X, O_X) ≅ k` is a statement about ZEROTH structure-sheaf cohomology
    — it says the global sections of `O_X` are exhausted by the base field.
  These are independent vanishings. There is no Mathlib theorem that
  converts H1Cotangent-vanishing of a chart-algebra into a global Γ ≅ k
  statement, nor is there a mathematical bridge: a standard-smooth chart
  algebra `B` with `Subsingleton (H1Cotangent k B)` is generic in the sense
  that it carries no information about the GLOBAL geometry of any scheme it
  glues into. The "cotangent-vanishing" naming collision between Mathlib's
  `H1Cotangent` (André-Quillen cohomology) and the project's
  "cotangent-vanishing pile" (Γ ≅ k for smooth proper geom-irr X/k)
  is exactly that — a naming collision.
- The H1Cotangent pivot is **mathematically incoherent** as proposed.
- **Verdict**: **NO_USEFUL_ANALOGUE**.

## Top suggestion

**Pivot recommended: combine the (4) consumer reformulation over `\bar k`
with the (1) CharZero collapse for the chart-algebra envelope.** Concretely:

1. **Reformulate `constants_integral_over_base_field` over an algebraically
   closed base** — introduce `constants_integral_over_base_field_of_isAlgClosed`
   in `ChartAlgebra.lean` with the additional `[IsAlgClosed k]` hypothesis;
   the body closes in ~15 LOC via `IsAlgClosed.algebraMap_surjective_of_isIntegral`
   (`Mathlib.FieldTheory.IsAlgClosed.Basic`) on the iter-148 `_hAppTopFinite`
   + `_hΓfield'` scaffold. No (S3.*) sub-claims are needed.

2. **Drop (S3.pi.1) and (S3.pi.2) from the M2.a critical path**, deferring
   them as Mathlib-PR-grade work that is NOT iter-150–155 budget. (S3.sep.1)
   and (S3.sep.2) can be kept as informational targets for the general-`k`
   formulation of `constants_integral_over_base_field` but they are also
   off the M2.a critical path.

3. **Rewire `df_zero_factors_through_constant_on_chart`
   (`ChartAlgebra.lean:222–240`) to consume
   `constants_integral_over_base_field_of_isAlgClosed`** when its consumer
   instantiates the chart-algebra envelope under `[IsAlgClosed k]`. This
   matches the actual call-site in `rigidity_over_kbar`, where `kbar` is
   algebraically closed by hypothesis.

4. **For KDM (BR.5) closure**, port the analogue (3) above: build the
   joint-coordinate-derivation kernel-equals-constants statement for
   `MvPolynomial σ k` directly via `MvPolynomial.pderiv` + monomial
   expansion (~25 LOC), then transfer to `B = MvPolynomial σ k / I` via
   the standard-smooth surjection (~30–40 LOC). Total: ~60–80 LOC,
   in range with the iter-149 directive estimate.

**Net iter-150 LOC budget for M2.a closure (revised)**:
- `constants_integral_over_base_field_of_isAlgClosed`: ~15 LOC (new lemma).
- KDM (BR.5) joint-kernel collapse: ~60–80 LOC.
- `df_zero_factors_through_constant_on_chart` rewiring: ~5 LOC.
- `Scheme.Over.ext_of_diff_zero` consumer-side adjustment: ~5–10 LOC.
- `rigidity_over_kbar` body closure: ~30–60 LOC (assuming the surrounding
  scaffolding is in place).

**Total**: ~120–170 LOC for M2.a critical path, vs ~310–550 LOC for the
iter-149 path (b) full (S3.*) decomposition. This is a **~50–60% saving**
on the M2.a body closure, at the cost of dropping (S3.pi.1) and (S3.pi.2)
from iter-150–155 (they remain valuable Mathlib-PR work for general `k`
but are off-critical-path).

**First file to touch**: `AlgebraicJacobian/Cotangent/ChartAlgebra.lean`
— add `constants_integral_over_base_field_of_isAlgClosed` between
`constants_integral_over_base_field` and `Scheme.Over.ext_of_diff_zero`,
then rewire `df_zero_factors_through_constant_on_chart` (or add an
`_of_isAlgClosed` companion) to consume it. **Second file**: the same
file, KDM (BR.5) body in `KaehlerDifferential.mem_range_algebraMap_of_D_eq_zero`
to consume the new `MvPolynomial.pderiv`-monomial joint-kernel lemma.

## Verdict-meta

The iter-149 commitment to path (b) with the four (S3.*) sub-claims was
based on the assumption that the over-`k` formulation was structurally
necessary. The iter-150 analysis surfaces that the actual M2.a consumer
(`rigidity_over_kbar`) operates over `\bar k`, so the over-`k` flat-base-
change-of-Γ machinery is NOT needed on the critical path. The escalation
hook should be exercised: **hybrid path** (consumer-reformulation +
CharZero collapse + KDM (BR.5) closure via MvPolynomial.pderiv) is the
recommended iter-150 commitment, with path (b) (S3.sep.*) salvageable
as Mathlib-PR work and path (b) (S3.pi.*) deferred indefinitely.
