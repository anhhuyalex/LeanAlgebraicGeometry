# Analogy: `Differential.ContainConstants` typeclass install vs direct `KaehlerDifferential` exactness for piece (ii) `ext_of_diff_zero`

## Slug
containConstants-iter138

## Iteration
138

## Question

For the scheme-level argument "`df = 0` for `d : Γ(C, V) → Ω_{Γ(C, V) / Γ(Spec k, U)}` implies `f` factors through `Spec k`" (piece (ii) of the M2.body-pile, to be Lean-named `AlgebraicGeometry.Scheme.Over.ext_of_diff_zero`), which Mathlib idiom should the project align to?

Two paths under evaluation (per STRATEGY.md line 446):

- **(a) `Differential.ContainConstants` typeclass install**: Mathlib's `Differential.ContainConstants A B` (`Mathlib.RingTheory.Derivation.DifferentialRing:62-66`) is keyed on `[Differential B]` — a derivation `B → B` valued IN `B` (NOT in differentials) — with `mem_range_of_deriv_eq_zero` (line 67-70) consuming `x' = 0`. To use it literally the project would need a `Differential B` instance on chart algebras, obtained by selecting a derivation `B → B` from the universal `B → Ω_{B/A}` via a splitting.

- **(b) Direct `KaehlerDifferential` exactness route**: pivot piece (ii) to route through `KaehlerDifferential` exactness lemmas directly (`KaehlerDifferential.exact_mapBaseChange_map` family + a kernel-of-derivation argument on the universal Kähler module).

## Project artifact(s)

- `AlgebraicJacobian/Rigidity.lean:91` — `Scheme.Over.ext_of_eqOnOpen` (iter-125 refactor); piece (ii) `ext_of_diff_zero` will be its differential-vanishing companion. **PHANTOM**: not yet scaffolded; scheduled iter-141+.
- `blueprint/src/chapters/RigidityKbar.tex:68` — piece (ii) prose: "the ring-level half aligns with Mathlib's `Differential.ContainConstants` typeclass" framing acknowledged as loose by STRATEGY.md:446.
- `AlgebraicJacobian/Differentials.lean:86-109` — `kaehler_quotient_localization_iso` already uses `KaehlerDifferential.exact_mapBaseChange_map`. **The project's existing infrastructure is path-(b)-aligned.**
- `AlgebraicJacobian/Differentials.lean:51-66` — `relativeDifferentialsPresheaf` definitionally unfolds to `CommRingCat.KaehlerDifferential`; the chart-level Kähler module is the natural target.
- STRATEGY.md:446-447 — iter-136 framing of the alignment question.

## Mathlib snapshot

`b80f227` (project's pinned `lake-manifest.json`).

## Decisions identified

The directive asks one design question that compresses **three** orthogonal sub-decisions: (a) feasibility of `Differential B` install on chart algebras; (b) feasibility of direct `KaehlerDifferential` route; (c) scaffold shape and Lean signature for `ext_of_diff_zero`.

### Decision (1): Feasibility and cost of path (a) — `Differential B` typeclass install on chart algebras

- **Mathlib idiom (`Mathlib.RingTheory.Derivation.DifferentialRing`)**:
  ```lean
  class Differential (R : Type*) [CommRing R] where
    deriv : Derivation ℤ R R          -- a single chosen ℤ-derivation R → R

  class Differential.ContainConstants (A B : Type*)
      [CommRing A] [CommRing B] [Algebra A B] [Differential B] : Prop where
    protected mem_range_of_deriv_eq_zero {x : B} (h : x′ = 0) :
        x ∈ (algebraMap A B).range
  ```
  Two key features:
  1. `Differential B` is a **structure-bearing class** that **selects ONE specific derivation `δ : B → B`** (a `Derivation ℤ R R`, which by the lack of `ℤ`-content is just any additive Leibniz map). It is NOT the universal Kähler `B → Ω_{B/A}`.
  2. `ContainConstants A B` states the kernel of THAT SPECIFIC `δ` lies in `image(A → B)`. The statement is **weaker** than "kernel of the universal Kähler `d_{B/A} : B → Ω_{B/A}` lies in `image(A → B)`".

  **Existing Mathlib instances** of `Differential R`: ONLY the `AdjoinRoot p` / finite-extension instances in `Mathlib/FieldTheory/Differential/{Basic,Liouville}.lean` (lines 97-99, 137-145 of `Basic.lean`). These cover differential **field** extensions (a la classical Liouville theory). **No instance for non-field algebras** (no `Differential (Polynomial R)`, no `Differential (MvPolynomial σ R)`, no `Differential` for any scheme-style chart algebra). The Liouville instances require `CharZero F`, primitive element selection, Galois-style descent.

- **Project's chart algebras**: `B = Γ(C, V)` where `C` is an abstract smooth proper geometrically-irreducible curve of dim 1 over `k`. These are NOT a priori isomorphic to `k[X]`, `k(X)`, or `AdjoinRoot p`. They are abstract `CommRingCat`s emerging from `Spec` of the structure-sheaf restriction to an affine open. Concretely:
  - Locally `B` is a localization of a quotient of a polynomial ring (`B ≅ k[x_1, ..., x_n]/(f_1, ..., f_{n-1}) ⊗ S⁻¹` with `S ⊆ B`).
  - For a chart of a smooth proper geom-irr curve, `B` is a finitely-generated `k`-algebra, `IsIntegralDomain B`, dim 1, and `Ω[B/k]` is locally free of rank 1.

- **What it takes to install `Differential B` on a project chart algebra**:
  1. **Choose a derivation `δ : B → B`**. Options:
     - Pick a generator `db₀` of the rank-1 free `B`-module `Ω[B/k]` (via piece (i.c) `omega_free`-style infrastructure, restricted to a chart). Then any `b ∈ B` has `d_B b = (db/db₀) · db₀` for a unique `db/db₀ ∈ B`. Define `δ b := db/db₀`. This is the "derivative along the chosen direction".
     - LOC cost: requires `omega_free` chart-restricted (which piece (i.c.1) provides ~100-200 LOC) plus the splitting-from-generator construction (~50-100 LOC). Subtotal: ~150-300 LOC of infrastructure per chart, with `Classical.choose` chains baked into the choice of generator.
  2. **Install the typeclass instance** `Differential B`: ~30-50 LOC (mostly wrapping `δ` and verifying the `Derivation ℤ B B` shape, which requires re-coercion since the natural derivation is `k`-linear not `ℤ`-linear).
  3. **Prove `Differential.ContainConstants k B`**: the kernel of THAT SPECIFIC `δ` is `image(k → B)`. In char 0, this is equivalent to: "`δ b = 0` ⟺ `b` is in the constant subring `k`". The proof must reduce to a polynomial-ring base case (via etale-localization arguments or `Algebra.IsStandardSmoothOfRelativeDimension 1` structure). ~150-250 LOC. **In char p this FAILS** (e.g., `δ (b^p) = p b^{p-1} δ b = 0` for any `b`, so kernel of `δ` contains `B^p` ⊋ `k`); piece (iii) Frobenius iteration handles that case separately.

- **Composability with the scheme-level lift**: even with `[Differential B]` and `[Differential.ContainConstants k B]` installed, the scheme-level `Scheme.Over.ext_of_diff_zero` says "`df = 0` at the cotangent-sheaf level implies `f` factors through `Spec k`". At the algebra level, "cotangent-sheaf `df = 0`" means `d_{B/k}(f^#(a)) = 0` in `Ω[B/k]` for every `a ∈ image(f^#) ⊆ B`. This is a UNIVERSAL-Kähler statement. To consume `Differential.ContainConstants`, you must first show: "`d_{B/k}(b) = 0` in `Ω[B/k]` implies `δ b = 0`". This DOES hold (any single derivation factors through the universal one), but it means the `Differential B` install yields a STRICTLY WEAKER intermediate fact that has to be re-strengthened back to the universal version anyway. **The `Differential` install adds an indirection without removing any work.**

- **LOC envelope for path (a)** (chart-algebra-level install + ContainConstants proof + scheme-level lift): **~430-700 LOC**, of which the chart-algebra `Differential` install (~150-300 LOC) is **pure overhead** vis-à-vis path (b) — it does not contribute to the eventual scheme-level conclusion beyond what the universal-Kähler argument already gives.

- **Critical observation**: Path (a) introduces an **API mismatch**. The chart-algebra `Differential B` instance is non-canonical (depends on the choice of cotangent generator `db₀`, requiring `Classical.choose`). The scheme-level lift then has to either (i) carry the choice as a hypothesis (polluting the signature of `ext_of_diff_zero`), or (ii) marginalize the choice via "for any chosen splitting" (adding an existential layer that downstream consumers must navigate). Path (b) does not have this issue: `Ω[B/A]` is intrinsic.

- **Verdict**: **DIVERGE_INTENTIONALLY from `Differential.ContainConstants`**. The typeclass is shaped for differential **field** extensions in the classical (Rosenlicht/Liouville) tradition, not for chart algebras of an abstract smooth proper geom-irr curve. Installing it on chart algebras requires non-canonical `Classical.choose` of a cotangent generator, yields a strictly weaker intermediate fact, and adds API friction without LOC savings.

### Decision (2): Feasibility and cost of path (b) — direct `KaehlerDifferential` route

- **Mathlib idiom**: the universal Kähler module `Ω[B/A]` (`KaehlerDifferential A B`, `Mathlib.RingTheory.Kaehler.Basic`) with derivation `KaehlerDifferential.D A B : B → Ω[B/A]`. Exactness lemmas:
  - `KaehlerDifferential.exact_mapBaseChange_map A B B : Function.Exact (mapBaseChange) (map A B B)` — cotangent base-change exact sequence. Already consumed by the project's `kaehler_quotient_localization_iso` (`AlgebraicJacobian/Differentials.lean:86`).
  - `KaehlerDifferential.map_surjective` — `map A A B B` is surjective.
  - `KaehlerDifferential.polynomialEquiv R : Ω[R[X]/R] ≃ₗ[R[X]] R[X]` with `polynomialEquiv_D : polynomialEquiv R (D R R[X] P) = derivative P` (`Mathlib.RingTheory.Kaehler.Polynomial`) — polynomial-ring base case.
  - `Polynomial.eq_C_of_derivative_eq_zero {R : Type*} [Semiring R] [IsAddTorsionFree R] {f : R[X]} (h : derivative f = 0) : f = C (f.coeff 0)` (`Mathlib.Algebra.Polynomial.Derivative`) — the polynomial-derivative kernel lemma, char-0-hypothesised via `IsAddTorsionFree`.
  - `Algebra.IsStandardSmooth.free_kaehlerDifferential : [IsStandardSmooth R S] → Module.Free S Ω[S/R]` — free cotangent module on standard-smooth algebras (consumed by piece (i.c) `omega_free` already in the project's roadmap).

- **Algebra-level core lemma the project needs (NEW; not in Mathlib)**:
  ```lean
  theorem KaehlerDifferential.mem_range_algebraMap_of_D_eq_zero
      {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
      [IsAddTorsionFree R]               -- char-0 hypothesis on R
      [IsDomain B]                       -- B integral
      [Algebra.IsStandardSmoothOfRelativeDimension 1 R B]
      -- + closed-subring hypothesis: image(R) is integrally closed in B
      --   (ensures algebraic-over-R + in-B ⇒ in-image(R))
      {b : B} (h : KaehlerDifferential.D R B b = 0) :
      b ∈ (algebraMap R B).range
  ```
  Proof sketch:
  1. Reduce to the polynomial sub-case: the ring map `R[X] → B` sending `X ↦ b` has `(KaehlerDifferential.map R R R[X] B) (D R R[X] X) = D R B b = 0`. The polynomial-ring side `D R R[X] X` corresponds to `1 ∈ R[X]` under `polynomialEquiv R`. So `(map R R R[X] B)((polynomialEquiv R).symm 1) = 0`.
  2. Using `KaehlerDifferential.exact_mapBaseChange_map` for the tower `R → R[b] → B` (where `R[b] = image(R[X] → B)`), the vanishing of `D R B b` localises to a statement about `Ω[R[b]/R]`.
  3. In char 0 (`IsAddTorsionFree R`), apply `Polynomial.eq_C_of_derivative_eq_zero`-style reasoning on the polynomial pull-back: if `b` were transcendental over `R` (i.e., `R[X] → B` injective), then `D R B b ≠ 0`. Contrapositively, `D R B b = 0` ⟹ `b` algebraic over `R`.
  4. The "integrally closed" hypothesis on `image(R) ⊆ B` (which corresponds to "constants of a geom-irr smooth proper curve over k equal k" at the scheme level) closes the algebraic-element argument: `b` algebraic + `b ∈ B` + `image(R) integrally closed` ⟹ `b ∈ image(R)`.

  LOC estimate: ~200-350 LOC for the algebra-level lemma + ~50-100 LOC for the integrally-closed-constants helper (which the project may need anyway for geom-irr curve constants).

- **Scheme-level lift**:
  ```lean
  theorem AlgebraicGeometry.Scheme.Over.ext_of_diff_zero
      {X Y : Over (Spec (.of k))}
      [CharZero k]                       -- char-0 (piece (iii) handles char p)
      [GeometricallyIrreducible X.hom]
      [IsReduced X.left]
      [IsProper X.hom]
      [SmoothOfRelativeDimension 1 X.hom]
      [IsSeparated Y.hom]
      (g₁ g₂ : X ⟶ Y)
      (h_diff : -- pulled-back cotangent map of g₁ and g₂ agree, OR
                -- the relative differential of (g₁ - g₂) is zero
        ∀ {U : Y.left.Opens} (hU : IsAffineOpen U)
          {V : X.left.Opens} (hV : IsAffineOpen V)
          (e : V ≤ (Opens.map g₁.left.base).obj U)
          (e' : V ≤ (Opens.map g₂.left.base).obj U),
          KaehlerDifferential.map _ _ _ _ ∘ₗ
            (g₁.left.appLE U V e - g₂.left.appLE U V e') = 0)
      (h_pt : ∃ x : X.left.toTopCat, g₁.left.base x = g₂.left.base x) :
      g₁ = g₂
  ```
  This uses (i) the algebra-level core lemma on each affine chart to show `g₁.left.appLE` and `g₂.left.appLE` agree on each chart's image (so `g₁` and `g₂` agree topologically + on the structure sheaf on the affine cover), then (ii) `Scheme.Over.ext_of_eqOnOpen` (the iter-125-shipped rigidity from agreement on a non-empty open) to globalise. LOC ~100-150.

- **Composability with project infrastructure**: high. The project's `kaehler_quotient_localization_iso` already uses `KaehlerDifferential.exact_mapBaseChange_map` in the same idiom. `relativeDifferentialsPresheaf_obj_kaehler` provides definitional unfolding to the chart-Kähler module. The chart-level free cotangent comes from piece (i.c) `omega_free` directly (already on the roadmap). The scheme-level `ext_of_eqOnOpen` is in-tree since iter-125.

- **LOC envelope for path (b)**: **~300-600 LOC** total (algebra-level core ~200-350 + integrally-closed-constants helper ~50-100 + scheme-level lift ~100-150). Tracks the existing iter-127 estimate of 250-500 LOC with a small upward revision (~+50-100 LOC) reflecting the integrally-closed-constants helper that the loose framing did not separately budget.

- **Verdict**: **ALIGN_WITH_MATHLIB on the universal `KaehlerDifferential` idiom**. Path (b) is mathematically tighter (gives exactly the needed statement), composes cleanly with project infrastructure already in place, avoids `Classical.choose` chains, and produces an algebra-level lemma that is a clean Mathlib-PR candidate (a natural companion to `Polynomial.eq_C_of_derivative_eq_zero` extended to standard-smooth-of-rel-dim-1 algebras).

### Decision (3): Scaffold shape — Lean signature, instance binders, and body-closure pattern

- **Project-recommended scaffold shape** (when piece (ii) scaffolds iter-141+):

  ```lean
  namespace AlgebraicGeometry

  variable {k : Type u} [Field k] [CharZero k]
  -- CharZero gated explicitly: piece (iii) Frobenius iteration handles char p
  -- separately via `ext_of_diff_zero` composed with `iterateFrobenius`.

  /-- Rigidity from agreement of relative differentials and at a single point.

  For schemes over `Spec k` (char 0) with `X` a smooth proper geometrically
  irreducible curve of dim 1 and `Y` separated, two morphisms `g₁, g₂ : X ⟶ Y`
  whose pulled-back relative differentials agree on the structure sheaf and
  which agree at a single point coincide.

  This is the differential-vanishing companion of `Scheme.Over.ext_of_eqOnOpen`,
  used in the M2.body-pile piece (ii) to close `rigidity_over_k`.

  Char-p handling: composing this lemma with iterated absolute Frobenius
  (`AlgebraicGeometry.Scheme.absoluteFrobenius`, piece (iii)) handles
  positive-characteristic base fields. The bare `CharZero` hypothesis here
  is the cleanest entry-point; the char-p extension is a separate lemma. -/
  theorem Scheme.Over.ext_of_diff_zero
      {X Y : Over (Spec (.of k))}
      [GeometricallyIrreducible X.hom]
      [IsReduced X.left]
      [SmoothOfRelativeDimension 1 X.hom]
      [IsSeparated Y.hom]
      (g₁ g₂ : X ⟶ Y)
      (h_diff : -- the relative differential of g₁ equals that of g₂ at the
                -- presheaf-of-cotangents level
        ∀ {U : Y.left.Opens} (hU : IsAffineOpen U)
          {V : X.left.Opens} (hV : IsAffineOpen V)
          (e : V ≤ (Opens.map g₁.left.base).obj U)
          (he : g₁.left.base '' V.carrier = g₂.left.base '' V.carrier),
          KaehlerDifferential.D _ _ ∘
            (g₁.left.appLE U V e - g₂.left.appLE U V (he ▸ e)) = 0)
      (h_pt : ∃ x : X.left.toTopCat, g₁.left.base x = g₂.left.base x) :
      g₁ = g₂ := sorry
  ```

  **Body closure pattern**: combine the algebra-level kernel-of-d lemma (Decision 2) with `Scheme.Over.ext_of_eqOnOpen`. The `h_diff` hypothesis at each chart gives `(g₁.left.appLE) - (g₂.left.appLE)` lands in the kernel of `D R B`. Apply the algebra-level lemma to conclude the difference lands in `image(R → B)`, i.e., on the constants subring. Combined with `h_pt` (single-point agreement), the constants must be zero, so the two `appLE`s agree. This gives `g₁.left|_V = g₂.left|_V` for each affine chart. Apply `ext_of_eqOnOpen` to globalise.

- **Alternative scaffold shape (more aligned with the directive's wording)**: state piece (ii) as "`df = 0` implies factor through `Spec k`" directly, with a single morphism input rather than a pair:

  ```lean
  /-- A morphism `g : X ⟶ Y` over `Spec k` with vanishing relative differential
  factors through the structure morphism `Y.hom : Y ⟶ Spec k`. -/
  theorem Scheme.Over.factors_through_terminal_of_diff_zero
      {X Y : Over (Spec (.of k))}
      [GeometricallyIrreducible X.hom]
      [IsProper X.hom]
      [SmoothOfRelativeDimension 1 X.hom]
      (g : X ⟶ Y)
      (h_diff : ∀ {U : Y.left.Opens} (hU : IsAffineOpen U)
        {V : X.left.Opens} (hV : IsAffineOpen V)
        (e : V ≤ (Opens.map g.left.base).obj U),
        KaehlerDifferential.D _ _ ∘ g.left.appLE U V e = 0) :
      ∃ (y : ⊤_ Scheme ⟶ Y.left), g.left = (X.left.terminalFromUnique).hom ≫ y := sorry
  ```

  Either shape works; the **`ext_of_*` shape (paired morphisms)** is recommended because it composes more naturally with the consuming `rigidity_over_k` proof: that proof reduces "morphism `f : C → Albanese` is unique" to "any two such `f₁, f₂` agree", which is exactly the `ext_of_*` form's output. The "factors through" form requires an extra step to extract uniqueness.

- **Instance binders rationale**:
  - `[CharZero k]`: necessary for the kernel-of-d ⟹ kernel-of-derivative reduction. Char p handled by piece (iii).
  - `[GeometricallyIrreducible X.hom]`: gives "constants of X = k" (the integrally-closed-constants requirement for the algebra-level lemma) AND irreducibility used by `ext_of_eqOnOpen`.
  - `[IsReduced X.left]`: required by `ext_of_eqOnOpen`.
  - `[SmoothOfRelativeDimension 1 X.hom]`: gives `Algebra.IsStandardSmoothOfRelativeDimension 1` on each affine chart (locally), supplying free-rank-1 cotangent for the algebra-level lemma.
  - `[IsSeparated Y.hom]`: required by `ext_of_eqOnOpen`.
  - **`[IsProper X.hom]` is NOT strictly needed** for piece (ii) itself — properness is consumed in the *use site* (extracting the "morphism to Albanese is determined" application). Recommend omitting from `ext_of_diff_zero`'s direct signature; consumer adds it.

- **Body-closure pattern (recommended)**: build via path (b)
  ```
  Algebra-level lemma (NEW; PR-able to Mathlib)
        ↓ (chart-affine reduction)
  Scheme-level: g₁.left.appLE = g₂.left.appLE on each chart
        ↓ (project's Scheme.Over.ext_of_eqOnOpen)
  g₁ = g₂
  ```
  **NOT via** path (a) (`Differential B` typeclass install + `mem_range_of_deriv_eq_zero`).

- **Verdict**: **PROCEED** on the recommended scaffold shape. The `ext_of_*` pattern (paired morphisms) aligns with the iter-125 `ext_of_eqOnOpen` precedent and composes cleanly with the consuming `rigidity_over_k`. The `[CharZero k]` gate is explicit and the char-p extension is via a separate lemma composed with piece (iii)'s `iterateFrobenius`.

## Recommendation

**Pin path (b) for piece (ii) `ext_of_diff_zero`.** The case for path (a) (`Differential.ContainConstants` typeclass install) does not survive contact with the project's chart-algebra setup:

1. **Mathlib's `Differential` instances exist only for differential field extensions** (Liouville-tradition material in `Mathlib.FieldTheory.Differential`). No instance for non-field commutative algebras, no instance for chart-style `k`-algebras. The project cannot consume an existing instance.

2. **Installing `Differential B` on a chart algebra** of an abstract smooth proper geom-irr curve requires choosing a cotangent generator (non-canonical, `Classical.choose`-chained). The chosen derivation gives a STRICTLY WEAKER fact than the universal-Kähler kernel-of-d statement. The path (a) install is **pure overhead**.

3. **Path (b) — direct `KaehlerDifferential` route — is the existing project idiom.** `AlgebraicJacobian/Differentials.lean:86-109` already consumes `KaehlerDifferential.exact_mapBaseChange_map` in the same shape for `kaehler_quotient_localization_iso`. The piece (i.c) `omega_free` work (already on the roadmap) provides the rank-1 cotangent input. The scheme-level lift composes cleanly with `Scheme.Over.ext_of_eqOnOpen` (iter-125, in-tree).

4. **The blueprint's "ring-level half aligns with Mathlib `Differential.ContainConstants`" framing is loose and should be REPLACED in piece (ii)'s blueprint prose** with the path-(b) framing: "the ring-level half builds a new universal-Kähler kernel lemma `KaehlerDifferential.mem_range_algebraMap_of_D_eq_zero`, a clean Mathlib-PR candidate companion to `Polynomial.eq_C_of_derivative_eq_zero`".

**LOC envelope for path (b)**: **~300-600 LOC** total, decomposed as ~200-350 algebra-level core + ~50-100 integrally-closed-constants helper + ~100-150 scheme-level lift. Tracks the iter-127 estimate of 250-500 LOC with a small upward revision reflecting the integrally-closed-constants helper that the loose framing did not separately budget.

**Mathlib lemmas consumed by path (b)**:
- `KaehlerDifferential.exact_mapBaseChange_map` (already used in project)
- `KaehlerDifferential.map_surjective`
- `KaehlerDifferential.map_D`
- `KaehlerDifferential.polynomialEquiv` + `polynomialEquiv_D`
- `Polynomial.eq_C_of_derivative_eq_zero` (with `IsAddTorsionFree`)
- `Algebra.IsStandardSmooth.free_kaehlerDifferential`
- `AlgebraicGeometry.IsSmoothOfRelativeDimension.mk` / `_iff` (chart-affine reduction)
- Project: `AlgebraicGeometry.Scheme.Over.ext_of_eqOnOpen` (iter-125, in-tree)
- Project: chart-localisation identification for `relativeDifferentialsPresheaf` (piece (i.c.1), iter-137+)

**Mathlib lemmas explicitly NOT used (rejected by this verdict)**:
- `Differential.ContainConstants A B` — typeclass shape wrong for chart algebras
- `mem_range_of_deriv_eq_zero` — consumer of the above, transitively rejected
- The `Mathlib.FieldTheory.Differential.{Basic,Liouville}` install machinery — out of scope for non-field algebras

**Recommended scaffold shape (iter-141+)**: `ext_of_*` paired-morphism form with `[CharZero k]` explicit, instance binders `[GeometricallyIrreducible X.hom] [IsReduced X.left] [SmoothOfRelativeDimension 1 X.hom] [IsSeparated Y.hom]`. Body via path (b) algebra-level lemma + `Scheme.Over.ext_of_eqOnOpen`. `[IsProper X.hom]` omitted from the lemma's binders (consumer-added).

**Char-p handling**: `[CharZero k]` is the explicit gate. The char-p case is handled by a SEPARATE composition: `iterateFrobenius` (piece (iii)) precomposes to arrange `d(f^p^n) = 0` "by construction", reducing to a kernel-of-derivative argument; then the char-0 `ext_of_diff_zero` closes the iterated lemma. The two are not unified into a single typeclass-keyed lemma — separation makes the LOC envelope honest.

**Blueprint update obligation (iter-138+)**: piece (ii) prose in `blueprint/src/chapters/RigidityKbar.tex:68` should be updated to drop the loose "aligns with `Differential.ContainConstants`" framing and replace with the path-(b) framing. This is a blueprint-writer obligation, not a refactor or prover obligation.

## Verdict summary

| Decision | Verdict | Severity |
|---|---|---|
| (1) Path (a) `Differential.ContainConstants` install on chart algebras | DIVERGE_INTENTIONALLY (rejected — wrong-shape, pure overhead) | high-stakes |
| (2) Path (b) direct `KaehlerDifferential` route | ALIGN_WITH_MATHLIB (the universal `KaehlerDifferential` idiom is the right shape; consume `Polynomial.eq_C_of_derivative_eq_zero` + `exact_mapBaseChange_map`) | high-stakes |
| (3) Scaffold shape `ext_of_*` paired morphisms with `[CharZero k]` explicit | PROCEED | informational |

**Overall**: **PIN PATH (b)**. `Differential.ContainConstants` is the wrong Mathlib analogue for piece (ii); the project should align with universal `KaehlerDifferential` instead. LOC envelope ~300-600. Scaffold shape `ext_of_diff_zero` per the recommended template above.

## Severity

**high-stakes** — the verdict directly determines piece (ii)'s ~300-600 LOC build path AND the blueprint's piece (ii) prose framing. Entering iter-141+ scaffolding with the loose `Differential.ContainConstants` framing risks repeating the iter-134 placeholder-pattern mistake (under-specified Lean shape spawning low-quality prover work).
