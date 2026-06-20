# Analogy: Closed-point cotangent iso (Stacks 02JK)

## Mode
cross-domain-inspiration

## Slug
coe-stacks02jk

## Iteration
199

## Structural problem (abstracted)

We have a commutative diagram of `R`-algebras `R → A → B` with `A → B`
surjective with kernel `J`. Mathlib gives us a *right-exact* sequence
`J.Cotangent →[kerCotangentToTensor] B ⊗_A Ω[A/R] →[mapBaseChange] Ω[B/R] → 0`.
We want this to be a short exact sequence (with the leftmost map injective)
AND, when the rightmost term vanishes, an isomorphism on the left side.
The injectivity step requires a *retraction* (a left-inverse on the
cotangent complex), which is precisely the algebraic content of "`B` is
formally smooth over `R`".

In our concrete setting: `A = S_m` (a smooth-algebra localization at a
closed point), `B = κ` (the residue field of `S_m`, equal to the ground
field `R = k̄` because the point is `k̄`-rational), `J = m`. Then
`J.Cotangent = m/m² = IsLocalRing.CotangentSpace S_m`, and we want the
iso `m/m² ≃ κ ⊗_{S_m} Ω[S_m/R]`.

## Failed approaches (from directive)

- **Direct `KaehlerDifferential.exact_mapBaseChange_map`**: gives the right
  half of the conormal sequence (surjectivity onto `κ ⊗ Ω` modulo
  `Ω[κ/k]`), but NOT injectivity of the leftmost map.
- **Conormal sequence + `Ω[κ/k] = 0` alone**: cannot establish the left
  end of the short exact sequence without an extra splitting/injectivity
  argument.

The common missing ingredient in both failed approaches is the
*retraction* — a left-inverse for the cotangent map. Mathlib supplies it
under the name "formally smooth" via several distinct API surfaces; the
project's failed approaches simply did not invoke any of them.

## Analogues found

### Analogue 1: `Algebra.Extension.formallySmooth_iff_split_injection`

- **Domain**: commutative algebra / Kähler differential theory.
  `Mathlib.RingTheory.Smooth.Basic`.
- **Same structural problem there**: given an extension
  `P : Algebra.Extension R A` (so `P.Ring → A` surjective with kernel
  `P.ker`), under the hypothesis `Algebra.FormallySmooth R P.Ring`, the
  statement
    `Algebra.FormallySmooth R A ↔ ∃ l, l ∘ₗ P.cotangentComplex = LinearMap.id`
  reformulates "A is FS over R" as the *existence of a retraction* on the
  cotangent complex `P.Cotangent →ₗ[A] P.CotangentSpace`. The cotangent
  complex is the abstract analogue of "J/J² → B ⊗_A Ω[A/R]".
- **Technique**: bundle the surjection `A → B` as an `Algebra.Extension R B`,
  obtain the retraction `l` from the formally-smooth hypothesis on `B`
  (not on `A`!), and immediately conclude that `P.cotangentComplex` is
  injective via `Function.LeftInverse.injective`.
- **Mapping to project**: instantiate
  `P := Algebra.Extension.ofSurjective (IsLocalRing.residue S_m).toAlgHom (...)`
  with `R = k̄`, `A = κ = IsLocalRing.ResidueField S_m`. Then `P.Ring = S_m`
  (formally smooth over R because *smooth* over R via Stage 4 substrate),
  `P.ker = maximalIdeal S_m`, `P.Cotangent ≃ (maximalIdeal S_m).Cotangent`
  (bridged via `Algebra.Extension.Cotangent.of` / `.val`), and
  `P.CotangentSpace = κ ⊗_{S_m} Ω[S_m/R]`. The hypothesis
  `Algebra.FormallySmooth R κ` is automatic for `κ = k̄` algebraically
  closed at a `k̄`-rational closed point (it's the identity). Conclude:
  `P.cotangentComplex` injective. Combine with
  `Algebra.Extension.exact_cotangentComplex_toKaehler` (exact at middle)
  and `Subsingleton Ω[κ/R]` (from `KaehlerDifferential.subsingleton_of_surjective`
  on `R → κ`) to upgrade injective+exact-with-zero-target to bijective.
  Finalize via `LinearEquiv.ofBijective`.
- **Porting cost**: low. ~60–90 LOC of typeclass scaffolding +
  application. No new Mathlib lemma needed.
- **Verdict**: ANALOGUE_FOUND.

### Analogue 2: `Algebra.FormallySmooth.iff_split_injection`

- **Domain**: commutative algebra / Kähler differential theory.
  `Mathlib.RingTheory.Smooth.Basic`.
- **Same structural problem there**: the un-bundled form of Analogue 1.
  For `R → P → A` with `P → A` surjective and `P` formally smooth over `R`,
    `Algebra.FormallySmooth R A ↔ ∃ l, l ∘ₗ KaehlerDifferential.kerCotangentToTensor R P A = LinearMap.id`
  where `kerCotangentToTensor R P A : (ker(P → A)).Cotangent → A ⊗_P Ω[P/R]`
  is exactly the map we want to invert.
- **Technique**: same retraction trick, but stated directly on Mathlib's
  un-bundled `kerCotangentToTensor` rather than the
  `Algebra.Extension.cotangentComplex` packaging.
- **Mapping to project**: set `R = k̄`, `P = S_m`, `A = κ`. The map
  `kerCotangentToTensor R S_m κ : m.Cotangent → κ ⊗_{S_m} Ω[S_m/R]`
  is what we want bijective. The codomain identification is essentially
  definitional (no Algebra.Extension.Cotangent bridge needed). The
  domain `m.Cotangent` already matches `IsLocalRing.CotangentSpace S_m`
  by abbreviation. After the FS hypothesis on `κ/R` provides the
  retraction, combine with `exact_kerCotangentToTensor_mapBaseChange`
  (exact at middle, conditional on `S_m → κ` surjective — automatic)
  and `Subsingleton Ω[κ/R]` to get bijectivity. `LinearEquiv.ofBijective`
  for the iso.
- **Porting cost**: low. ~40–70 LOC, simpler than Analogue 1 because it
  avoids the `Algebra.Extension.Cotangent` ↔ `Ideal.Cotangent` bridge.
  The result is `S_m`-linear; if the project wants `κ`-linear, lift via
  the `IsLocalRing.instModuleResidueFieldCotangentSpace` /
  `IsScalarTower` instances.
- **Verdict**: ANALOGUE_FOUND. **Top recommendation.**

### Analogue 3: `Algebra.FormallySmooth.iff_injective_lTensor_residueField`

- **Domain**: commutative algebra / Kähler differential theory.
  `Mathlib.RingTheory.Smooth.Local`.
- **Same structural problem there**: for `S` a local `R`-algebra and an
  extension `P : Algebra.Extension R S`, under appropriate freeness +
  finiteness + FG hypotheses,
    `Algebra.FormallySmooth R S ↔ Function.Injective (LinearMap.lTensor κ(S) P.cotangentComplex)`
  where the LHS asks injectivity AFTER tensoring with the residue field
  of `S` (which is the additional ingredient compared to Analogue 1).
- **Technique**: same retraction-implies-injection technique, but the
  conclusion is stated post-tensoring with `κ(S)`. Useful when one wants
  to assert injectivity on the residue-field-base-changed object directly.
- **Mapping to project**: more natural fit when `S` is the smooth-algebra
  localization itself (the LHS local ring), and we want a statement about
  `κ(S) ⊗_{S_m} P.cotangentComplex`. But for our problem, the target ring
  is the residue field `κ`, not `S_m`, so this analogue is structurally
  one indirection further away from what we need. Still applicable: set
  `S = κ`, `P.Ring = S_m`. Tensoring with `κ(κ) = κ` is trivial.
- **Porting cost**: medium. Heavier typeclass scaffolding
  (`Module.Free P.Ring Ω[P.Ring/R]`, `Module.Finite ...`, `P.ker.FG`),
  plus a no-op residue-field tensor at the end. ~80–120 LOC.
- **Verdict**: ANALOGUE_FOUND (but redundant given Analogues 1–2).

### Analogue 4: `Function.Exact.linearEquivOfSurjective` (structural assembly helper)

- **Domain**: pure module / linear algebra. `Mathlib.Algebra.Exact`.
- **Same structural problem there**: given `Function.Exact f g` and
  `g` surjective, produces `N ⧸ f.range ≃ P`. Standard exact-sequence
  bookkeeping with no ring-theoretic content.
- **Technique**: snake-lemma-style assembly: exactness in the middle +
  surjectivity at the right gives `(middle / range_of_left) ≃ right`;
  when `right = 0`, this collapses to surjectivity of the left map.
- **Mapping to project**: useful as the *final assembly step* in
  Analogues 1–3. Once injectivity + exactness + `Ω[κ/R] = 0` are in
  hand, this lemma (or `LinearEquiv.ofBijective`) extracts the iso.
- **Porting cost**: trivial (already a one-liner in Mathlib).
- **Verdict**: PARTIAL_ANALOGUE — supporting helper, not a structural
  technique on its own.

### Analogue 5: `Algebra.Generators.cotangentRestrict_bijective_of_basis_kaehlerDifferential`

- **Domain**: commutative algebra / generator-based Kähler theory.
  `Mathlib.RingTheory.Extension.Cotangent.Free`.
- **Same structural problem there**: for a presentation `P` with `Ω[S/R]`
  having a basis indexed by a subset of generators (which is the case for
  standard-smooth presentations), the cotangent restriction
  `P.cotangentRestrict : P.toExtension.Cotangent → (σ →₀ S)` is bijective
  under a `Subsingleton (H¹Cotangent R S)` hypothesis.
- **Technique**: directly compute `P.Cotangent ≃ (σ →₀ S)` via the
  combinatorial structure of the presentation, then identify the RHS with
  `S ⊗_P Ω[P/R]` via `KaehlerDifferential.mvPolynomialEquiv`.
- **Mapping to project**: applicable to the polynomial-ring presentation
  of `S = R[x_1, …, x_n] / I` (the standard-smooth presentation), but not
  directly to the local ring `S_m → κ`. To use it for the residue-field
  iso we'd need to chain `S → S_m → κ` and base-change the Cotangent
  identification. Significantly more work than Analogues 1–3.
- **Porting cost**: high. Goes through `Algebra.Generators` API which the
  project does not yet wire up (Stage 4 substrate uses `IsStandardSmooth`,
  not `Generators` directly). ~150–250 LOC.
- **Verdict**: PARTIAL_ANALOGUE — feasible but heavier than Analogues 1–2.

## Top suggestion

Try **Analogue 2** first: `Algebra.FormallySmooth.iff_split_injection` in
`Mathlib.RingTheory.Smooth.Basic`. The proof shape:

```lean
-- inputs: R = kbar, P = S_m, A = κ = ResidueField S_m
-- have: Algebra.FormallySmooth R S_m   (from Stage-4 smooth ⟹ FS)
-- have: Algebra.FormallySmooth R κ      (κ = R algebraically closed)
-- have: Function.Surjective (algebraMap S_m κ)   (residue is surjective)

-- Step 1: retraction → injection
obtain ⟨l, hl⟩ := (Algebra.FormallySmooth.iff_split_injection hSurj).mp ‹_›
have hInj : Function.Injective (KaehlerDifferential.kerCotangentToTensor R S_m κ) :=
  Function.LeftInverse.injective (fun x => congr_arg _ (LinearMap.congr_fun hl x))

-- Step 2: Ω[κ/R] = 0 + exactness → surjection
have hOmegaZero : Subsingleton (Ω[κ⁄R]) :=
  KaehlerDifferential.subsingleton_of_surjective R κ Function.Surjective.id   -- κ = R
have hExact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange R S_m κ hSurj
-- range(kerCotangentToTensor) = ker(mapBaseChange) = whole tensor space (target is 0)

-- Step 3: bijective → iso
exact LinearEquiv.ofBijective _ ⟨hInj, hSurj_kct⟩
```

The first file to touch is
`AlgebraicJacobian/Albanese/CodimOneExtension.lean` around line 615
(where the iso is currently expressed as the unresolved sub-gap (ii.A)),
to fold in this iso as a fresh private theorem and consume it in
`isRegularLocalRing_stalk_of_smooth` via `LinearEquiv.finrank_eq`.

Estimated total LOC: 40–70, well below the directive's 100–200
estimate, because the retraction is supplied for free by Mathlib's
formally-smooth iff-lemma rather than constructed by hand.

If Analogue 2 hits an unforeseen scalar-tower / coercion issue (the
`κ`-linearity upgrade from `S_m`-linear is the most likely friction
point), fall back to **Analogue 1** (`Algebra.Extension`-packaged form),
which carries the residue-field module structure more cleanly through
`Algebra.Extension.CotangentSpace`'s built-in `S`-module structure.

## Discarded

- **`KaehlerDifferential.exact_mapBaseChange_map` alone** — matches
  failed approach (1).
- **Conormal-only approach without retraction** — matches failed
  approach (2).
- **`Algebra.Generators.cotangentRestrict_bijective_of_basis_kaehlerDifferential`**
  — feasible but heavier (Analogue 5), worth keeping in reserve only if
  Analogues 1–3 fail.
