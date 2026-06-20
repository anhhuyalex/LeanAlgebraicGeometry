# Analogy: Stacks 00SW — relations of a submersive presentation form a regular sequence at a closed-point localisation

## Mode
cross-domain-inspiration

## Slug
coe-stacks00sw

## Iteration
201

## Structural problem (abstracted)

Given a presentation `P : R → R[x₁,…,x_n] / (f₁,…,f_c) = S` whose Jacobian
matrix `(∂f_i/∂x_{σ(j)})_{i,j}` is invertible in `S` (i.e. a *submersive*
presentation), and a maximal ideal `m ⊂ S`, build a `RingTheory.Sequence.IsRegular`
witness for the relations `(f_j)` on the localisation
`A = (R[x_1,…,x_n])_{m'}` at the preimage maximal `m' = preimage(m)`.

Abstractly: from a *non-degeneracy of the derivative* hypothesis at a point,
extract a *regular sequence* of the cutting-down relations in a local
neighbourhood of the point. The Mathlib-aligned target signature is

```lean
lemma Algebra.SubmersivePresentation.relations_isRegular_in_localization
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι σ : Type*}
    [Finite σ] (P : Algebra.SubmersivePresentation R S ι σ)
    (m : Ideal P.Ring) [m.IsMaximal]
    (mem : ∀ j, P.relation j ∈ m)
    (A : Type*) [CommRing A] [Algebra P.Ring A] [IsLocalization.AtPrime A m] :
    RingTheory.Sequence.IsRegular A
      ((List.ofFn (fun (j : σ) => P.relation j)).map (algebraMap P.Ring A))
```

The two natural choices for the witness's index list — `List.ofFn (P.relation ∘ e)`
for a chosen `e : Fin (Fintype.card σ) ≃ σ`, or `Finset.univ.toList.map P.relation`
— are interchangeable by `IsLocalRing.isRegular_of_perm`.

## Failed approaches (from directive)

- **Build Stacks 00OE in the packaged form**
  `Algebra.IsStandardSmoothOfRelativeDimension.ringKrullDim_localization_eq_relativeDimension`
  directly: 200–300 LOC (iter-198 estimate), reduced to ~80–120 LOC by the 3-step
  composition in iter-200 (Steps 1+2 landed). Step 3 (this construction) is the
  remaining ~30–60 LOC residual.
- **Build the witness in `MvPolynomial` then transport via `RingEquiv`**: the
  Krull-dim side does this (`MvPolynomial.maximalIdeal_height_eq_card` then
  `…_eq_natCard` via `renameEquiv`); on the regular-sequence side, the direct
  `SubmersivePresentation.relation` route is cleaner because Mathlib's
  `Algebra.SubmersivePresentation` data structure already exposes the relations
  as `σ → P.Ring`.

## Analogues found

### Analogue A: `RingTheory.Sequence.IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem` (`Mathlib.RingTheory.Regular.Flat:65`)

- **Domain**: regular-sequence theory in commutative algebra (local + flat).
- **Same structural problem there**: given an `R`-module `M` with a *weakly*
  regular sequence `rs` on `M`, plus a localisation `M → N` at a prime `p`
  containing every element of `rs`, the image sequence is *honestly* regular
  on `N`. Exact statement:

  ```lean
  theorem IsWeaklyRegular.isRegular_of_isLocalizedModule_of_mem
      [Nontrivial N] [Module.Finite S N] (f : M →ₗ[R] N) [IsLocalizedModule.AtPrime p f]
      {rs : List R} (reg : IsWeaklyRegular M rs) (mem : ∀ r ∈ rs, r ∈ p) :
      IsRegular N (rs.map (algebraMap R S))
  ```

- **Technique**: combines (i) flat base change for weakly-regular (`IsWeaklyRegular.of_flat_of_isBaseChange`)
  with (ii) the local-ring bridge `IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal`
  to upgrade weakly-regular to regular when the elements all lie in the maximal
  ideal of the localisation. The "nontriviality + Module.Finite" hypothesis
  is what makes the `top_ne_smul` half of `IsRegular` follow from being inside
  the maximal ideal.
- **Mapping to project**: this is *the* bridge once an `IsWeaklyRegular P.Ring (P.relations)`
  witness exists (at any prior level — `P.Ring`, or the localisation, or any
  intermediate quotient). The mapping:
  - `R` ← `P.Ring = MvPolynomial ι k`
  - `S` ← `A` (the localisation at `m`)
  - `M` ← `P.Ring` (used as a `P.Ring`-module)
  - `N` ← `A` (used as a `P.Ring`-module via `algebraMap`)
  - `p` ← `m` (the maximal ideal of `P.Ring`)
  - `rs` ← `(List.ofFn P.relation)`
  - `mem` ← the directive's `hmem` hypothesis.

  After invoking this lemma, the IsRegular conclusion is exactly the target,
  modulo a `List.map (algebraMap …)` rewrite that the project already does
  in other places (`MvPolynomial.maximalIdeal_height_eq_natCard` transport).
- **Porting cost**: **none — direct invocation**. The hard work shifts to
  constructing the `IsWeaklyRegular P.Ring (P.relation)` premise, which is
  the next analogue.
- **Verdict**: ANALOGUE_FOUND. **This is the closing bridge.**

### Analogue B: `Algebra.SubmersivePresentation.basisCotangent` + `cotangentEquiv` (`Mathlib.RingTheory.Smooth.StandardSmoothCotangent:127,143`)

- **Domain**: cotangent complex of a smooth presentation; commutative-algebra
  side of "smooth implies free conormal".
- **Same structural problem there**: encodes the *algebraic content* of
  Jacobian invertibility in the form Mathlib actually exposes. The exact
  statements:

  ```lean
  noncomputable def cotangentEquiv : P.toExtension.Cotangent ≃ₗ[S] σ → S
  noncomputable def basisCotangent : Basis σ S P.toExtension.Cotangent
  lemma basisCotangent_apply (r : σ) :
      P.basisCotangent r = Extension.Cotangent.mk ⟨P.relation r, P.relation_mem_ker r⟩
  ```

  Reading this back: the images of `(P.relation r)_{r∈σ}` in
  `P.toExtension.Cotangent = I/I²` (where `I = ker(P.Ring →+* S)`) form an
  `S`-basis. This is the *cotangent-side* statement of Jacobian
  invertibility — equivalent in Mathlib to `jacobian_isUnit`.
- **Technique**: derived in `StandardSmoothCotangent.lean:116–144` from
  `linearIndependent_aeval_val_pderiv_relation` (relations' partial
  derivatives are linearly independent in `σ → S`) via the explicit
  isomorphism `P.toExtension.Cotangent ≃ₗ[S] σ → S` whose inverse is
  `(Cotangent.mk(relation r)) ↦ standardBasisVector r`. Crucially, this is
  the Mathlib-aligned encoding of "Jacobian invertible at every point of
  Spec S".
- **Mapping to project**: this is the substrate that *feeds* the
  `IsWeaklyRegular` construction. The route:
  1. From `basisCotangent`, the relations have linearly-independent images
     in `I/I²` over `S`.
  2. Localise: at the maximal `m` of `S`, the image is a basis of
     `I/I² ⊗_S S_m` over `S_m`, hence linearly independent in
     `(I·A)/(I·A)² ≅ I/I² ⊗_S Sₘ`.
  3. By `IsLocalRing.CotangentSpace.span_image_eq_top_iff`, the images in
     the maximal ideal `m'·A` of `A` (where `A = P.Ring_{m'}`) generate
     `I·A` exactly. Combined with linear-independence: the relations form
     a *minimal* generating set of `I·A`.
  4. Apply the **classical Stacks 00NQ theorem** ("in a regular local ring,
     a sequence in `m` whose images in `m/m²` are linearly independent
     forms a regular sequence") to conclude `IsRegular A (relations)`.
- **Porting cost**: **medium**. Step 4 is the *one* Mathlib gap: the
  Matsumura "lin-indep cotangent ⇒ regular sequence" theorem is not in
  Mathlib (verified by `lean_leansearch` — only the conormal-free side
  via `basisCotangent` lives in Mathlib, the regular-sequence direction
  is a project-side build).
- **Verdict**: ANALOGUE_FOUND. **This is the technical bridge** for Step
  3 of the closure path; the porting target is the "lin-indep cotangent ⇒
  regular sequence in regular local ring" theorem.

### Analogue C: `IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal` (`Mathlib.RingTheory.Regular.RegularSequence:510`)

- **Domain**: local-ring + finite-module regular-sequence theory.
- **Same structural problem there**: in any local Noetherian ring with a
  finite nontrivial module, the *upgrade* from weakly-regular to regular
  is automatic for sequences in the maximal ideal. Exact statement:

  ```lean
  lemma _root_.IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
      [IsLocalRing R] [Nontrivial M] [Module.Finite R M] {rs : List R}
      (h : ∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) :
      IsRegular M rs ↔ IsWeaklyRegular M rs
  ```

- **Technique**: reduces `top_ne_smul` to `top_ne_ideal_smul_of_le_jacobson_annihilator`,
  using that `maximalIdeal ≤ jacobson` (which is *automatic* in a local
  ring). The bridge is purely local-ring algebra, no Noetherian
  hypothesis on `R` (only `Module.Finite R M`).
- **Mapping to project**: once `IsWeaklyRegular A (relations.map …)` is in
  hand on the localisation `A`, this bridge gives `IsRegular A (relations.map …)`
  for free, since `A` is a local Noetherian ring (localisation of a
  Noetherian polynomial ring) and the relations lie in `m_A`. **However**,
  the cheaper route is to skip the intermediate "build IsWeaklyRegular on
  `A` then upgrade" and instead use Analogue A
  (`isRegular_of_isLocalizedModule_of_mem`) which combines the localisation
  + upgrade in one call. Use this analogue only if a
  direct `IsWeaklyRegular A`-side construction (e.g. an inductive proof
  not factoring through the polynomial ring) is preferable.
- **Porting cost**: **none — direct invocation**.
- **Verdict**: ANALOGUE_FOUND. **Use either this or Analogue A** depending
  on whether the IsWeaklyRegular witness is built on `P.Ring` (use A) or
  directly on `A` (use this).

### Analogue D: `LinearIndependent.of_isLocalizedModule_of_isRegular` (`Mathlib.RingTheory.Localization.Module`)

- **Domain**: linear-algebra-side localisation invariance.
- **Same structural problem there**: linearly independent vectors over `R`
  map to linearly independent vectors over `R_S` when the localisation
  monoid `S` consists of regular elements. Exact statement:

  ```lean
  theorem LinearIndependent.of_isLocalizedModule_of_isRegular
      (S : Submonoid R) (f : M →ₗ[R] Mₛ) [IsLocalizedModule S f]
      {v : ι → M} (hli : LinearIndependent R v)
      (hreg : ∀ s ∈ S, IsRegular s) :
      LinearIndependent R (f ∘ v)
  ```

- **Technique**: standard "tensor with `R_S` preserves linear
  independence" via flatness; uses that the localisation monoid acts by
  regular elements ⇒ the map `M → M_S` is injective on the span of `v`.
- **Mapping to project**: this is the *transport* step for the cotangent
  basis — it says that the basis property of `(P.relation r)_{r∈σ}` in
  `I/I²` survives localisation to `(I/I²)_{m}`. This is a substitute for
  step (2) in Analogue B's pipeline.
- **Porting cost**: **low**. Direct invocation with `S = m.primeCompl`,
  `M = I/I²`, `Mₛ = (I/I²)_{m}`, `v = basisCotangent`. The "every element
  regular" hypothesis is automatic in a Noetherian local domain (the
  polynomial ring `MvPolynomial ι k` is an integral domain, so every
  nonzero element is regular, and `m.primeCompl ⊂ nonZeroDivisors`).
- **Verdict**: ANALOGUE_FOUND. Auxiliary — feeds Analogue B's pipeline.

### Cross-domain analogue E: `Mathlib.Analysis.Calculus.ImplicitFunction` (implicit function theorem)

- **Domain**: differential geometry / functional analysis.
- **Same structural problem there**: given a `C^1` map `f : E → F` between
  Banach spaces with surjective derivative `df_a` at a point `a`, locally
  there is a *parametrisation* of `f⁻¹(f a)` by `ker(df_a)`, i.e. the
  zero locus is a regular submanifold cut out *transversally* by `f`'s
  components. Mathlib statement
  `HasStrictFDerivAt.implicitFunctionDataOfComplemented`:

  ```lean
  -- (rough form)
  theorem implicit_function (h : HasStrictFDerivAt f f' a)
      (hsurj : LinearMap.range f' = ⊤) :
      ∃ φ : nbd a → nbd (f a), φ is a local C¹-section
  ```

- **Technique**: contraction-mapping fixed point / Newton's method:
  iterate `x ↦ x − (df_a)⁻¹·f(x)` to construct the section. Linearisation
  + invertibility ⇒ local parametrisation.
- **Mapping to project**: structurally the *same* statement at the level
  of formal power series rings — Jacobian invertible at a point of `Spec S`
  ⇒ the relations cut out `Spec S` "linearly" in a formal neighbourhood,
  hence form a regular sequence. The contraction-mapping technique does
  *not* port directly (no contraction-mapping in the formal-power-series
  context inside Lean), but the *underlying conceptual core* is the same:
  "invertibility of the linearization is equivalent to regularity of the
  cut-out".
- **Porting cost**: **high** — the technique is not directly portable.
  Useful as a *sanity check* that the project's algebraic shape is the
  correct one. Skip for direct closure.
- **Verdict**: PARTIAL_ANALOGUE. The conceptual mirror, but no portable
  proof technique.

### Cross-domain analogue F: `Mathlib.RingTheory.Henselian.IsHenselian.exists_unique_lift` (Hensel's lemma)

- **Domain**: Henselian local rings / non-archimedean analysis.
- **Same structural problem there**: given a polynomial `f ∈ R[X]` over a
  Henselian local ring with `f(a₀) ≡ 0 (mod m)` and `f'(a₀)` a unit in
  `R/m`, there is a unique lift `a ∈ R` with `f(a) = 0` and `a ≡ a₀ (mod m)`.
  The multivariate Henselian version (`Algebra.exists_unique_lift_of_Hensel`)
  generalises: Jacobian invertible mod `m` ⇒ unique lift, hence a
  parametrisation.
- **Technique**: Newton iteration in the m-adic topology + completeness.
- **Mapping to project**: structurally identical — *Jacobian invertibility
  at a closed-point fiber ⇒ unique local lift / regular sequence*. The
  Mathlib `Henselian` library captures the *easier* direction (unique
  lift exists), not the *harder* direction (the cut-out ideal is generated
  by a regular sequence). Useful if the project ever needs the formal
  completion `Â` of `A` (which IS Henselian), but not the local
  `A = P.Ring_{m'}` directly.
- **Porting cost**: **high** — would require localizing-then-completing
  before applying Hensel; not a direct route.
- **Verdict**: PARTIAL_ANALOGUE.

### Discarded analogues

- **Mathlib's Koszul-complex API**: explicitly listed as a TODO in
  `Mathlib.RingTheory.Regular.RegularSequence:21` ("TODO: Koszul regular
  sequences"). No usable substrate.
- **`Mathlib.RingTheory.RegularLocalRing.Defs` + `spanFinrank`-based
  reasoning**: the `IsRegularLocalRing` definition uses `spanFinrank
  maximalIdeal = ringKrullDim`, which is downstream of *having* a regular
  sequence of length = dim, not a *source* of one. Going through the
  spanFinrank API would reduce to the same Matsumura "lin-indep ⇒ regular
  sequence" theorem.
- **`Module.exists_basis_of_span_of_maximalIdeal_rTensor_injective`**
  (Mathlib/RingTheory/LocalRing/Module.lean): only constructs a *basis*
  of a finite-presentation module under a Tor-vanishing hypothesis. Not
  the regular-sequence direction.
- **Sheaf-theoretic descent of regular sequences across étale covers**:
  Mathlib has no étale-descent regular-sequence API. Would require a
  separate substrate.

## Top suggestion

**Use the Analogue A + B + D composition.** Build the substantive Stacks
00NQ piece — "in a regular local ring of dim `n`, a sequence of `c`
elements in `m` whose images in `m/m²` are linearly independent forms a
regular sequence" — as a project-side lemma, then compose with Analogues
A, B, D. The full route:

1. **Build `Matsumura_lin_indep_cotangent_implies_regular`** (~30–50 LOC,
   project-side): in a regular local ring `(A, m)` of Krull dim `n`, a
   sequence `f₁, …, f_c ∈ m` whose images in `m/m²` are
   `κ = A/m`-linearly independent forms a `RingTheory.Sequence.IsRegular A
   [f₁, …, f_c]`. Proof structure (induction on `c`):
   - Base `c = 0`: `IsRegular.nil`.
   - Step: `f₁` ∉ m² (by lin-indep), so `f₁` is regular on `A` (since `A`
     is a regular ⇒ Cohen-Macaulay ⇒ depth-`n` ⇒ any non-zerodivisor in
     `m` is regular; for a regular local ring this is automatic via
     `IsRegularLocalRing.isDomain` for `A` a domain). Then `A/f₁A` is a
     regular local ring of dim `n-1`
     (via `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`
     in `Mathlib.RingTheory.KrullDimension.Regular`). Apply IH on
     `(f₂, …, f_c)` modulo `f₁`.
2. **Apply with `A = P.Ring_{m'} = (MvPolynomial ι k)_{m'}`** which is a
   regular local ring of dim `n = #ι` (by iter-200 substrate
   `ringKrullDim_localization_atMaximal_MvPolynomial` + an
   `IsRegularLocalRing` instance which polynomial-ring localisations carry
   automatically through `Module.SpanRankOperations` / Krull arithmetic).
3. **Verify lin-indep** of `(P.relation j)` images in `m_A/m_A²` via
   Analogue B (cotangent equivalence) + Analogue D (linear-independence
   under localisation). The pipeline:
   - `basisCotangent` gives lin-indep of relation classes in `I/I²` over `S`.
   - Tensor with `Sₘ`: lin-indep in `(I/I²) ⊗_S Sₘ`.
   - Identify `(I/I²) ⊗_S Sₘ` with `(I·A)/(I·A)²` (Mathlib has the
     conormal-localisation iso via `Algebra.Generators.Cotangent.tensor_lid`
     or similar; if absent project builds ~10 LOC).
   - `I·A ⊂ m_A`, so the relation classes embed into `m_A/m_A²`.
4. **Replace the directive's proposed chain** (jacobian_isUnit + isRegular_cons_iff +
   isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal) with the
   above Matsumura-based route. The directive's chain is correct *in
   principle* but heavier — it builds the regular sequence one-at-a-time
   via cons-iff inductions, where each step needs to verify
   non-zero-divisor-ness in the quotient, which forces a chain of
   regular-local-ring instances on `A / (f_1)`, `A / (f_1, f_2)`, etc.
   The Matsumura route packages that induction once.

**Cost estimate refinement.** The directive's 30–60 LOC estimate is for a
direct cons-style induction. The Matsumura-route variant lands at the
same ballpark (30–50 LOC for the named helper + ~20 LOC for the
cotangent-localisation transport bridge) but with a cleaner audit trail:
the Matsumura helper is the kind of standalone commutative-algebra lemma
Mathlib will eventually adopt (good candidate for an upstream PR).

**First Mathlib file to read for the Matsumura technique**: the existing
`Mathlib.RingTheory.KrullDimension.Regular` already wires
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim` and the
`supportDim_quotSMulTop_succ_eq_supportDim_mem_jacobson` chain — these
are the dim-drops-by-one ingredients of the induction. The Matsumura
helper is a clean ~30 LOC composition of those with `isRegular_cons_iff`
and `IsRegularLocalRing.iff_finrank_cotangentSpace`.

**First project file to touch**:
`AlgebraicJacobian/Albanese/CodimOneExtension.lean` around line 815
(just after the `ringKrullDim_quotient_add_eq_of_regular_sequence`
substrate). Add:
- `private theorem matsumura_isRegular_of_linearIndependent_cotangent` (~30–50 LOC),
- `private theorem submersivePresentation_relations_linearIndependent_cotangent_localization` (~20–30 LOC),
- `private theorem submersivePresentation_relations_isRegular_localization` (~10–15 LOC).

Then close the L1061 `sorry` in `isRegularLocalRing_stalk_of_smooth` using
those three plus the existing iter-200 dim chain.
