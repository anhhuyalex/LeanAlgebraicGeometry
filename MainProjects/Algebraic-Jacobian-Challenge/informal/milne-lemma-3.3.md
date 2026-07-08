# Milne Lemma 3.3 — indeterminacy of a rational map into a group variety

Reference for `AlgebraicGeometry.Scheme.RationalMap.indeterminacy_pure_codim_one_into_grpScheme`
(`Albanese/CodimOneExtension.lean:1692`). This is the **single remaining sorry** gating the whole
Albanese rational-map-extension chain (Milne Theorem 3.2 → `extend_to_av` →
Albanese universal property). Blueprint node: `lem:milne_codim1_indeterminacy`
(`blueprint/src/chapters/Albanese_CodimOneExtension.tex`).

## Milne's statement (Abelian Varieties, §I.3 Lemma 3.3, p. 17)

> Let `φ : V ⇢ G` be a rational map from a nonsingular variety to a group variety. Then either
> `φ` is defined on all of `V`, or the points where it is not defined form a closed subset of
> pure codimension 1 in `V` (i.e., a finite union of prime divisors).

Combined with Milne 3.1 (`indeterminacy_codimGe2_of_smooth_of_complete`, codim ≥ 2 into a complete
target — **proved**), for an abelian-variety target this forces `Z(φ) = ∅`
(`av_indeterminacyLocus_eq_empty`), hence extension (Milne 3.2).

## Milne's proof (transcribed verbatim from the PDF, pages 23–24)

Define a rational map `Φ : V × V ⇢ G`, `(x, y) ↦ φ(x)·φ(y)⁻¹`. More precisely, if `(U, φ_U)`
represents `φ`, then `Φ` is represented by
```
U × U --(φ_U × φ_U)--> G × G --(id × inv)--> G × G --m--> G.
```
Clearly `Φ` is defined at a diagonal point `(x, x)` if `φ` is defined at `x`, and then
`Φ(x, x) = e`. Conversely, if `Φ` is defined at `(x, x)`, then it is defined on an open
neighbourhood of `(x, x)`; in particular there is an open `U ⊆ V` such that `Φ` is defined on
`{x} × U`. After possibly replacing `U` by a smaller open subset (not necessarily containing `x`),
`φ` will be defined on `U`. For `u ∈ U`, the formula `φ(x) = Φ(x, u)·φ(u)` defines `φ` at `x`.
Thus **`φ` is defined at `x` iff `Φ` is defined at `(x, x)`.**

The rational map `Φ` defines a map `Φ* : 𝒪_{G,e} → k(V × V)`. Since `Φ` sends `(x, x)` to `e` if
it is defined there, `Φ` is defined at `(x, x)` **iff `Im(𝒪_{G,e}) ⊆ 𝒪_{V×V,(x,x)}`.**

Now `V × V` is nonsingular, so there is a good theory of divisors. For a nonzero rational function
`f` on `V × V`, write `div(f) = div(f)₀ − div(f)_∞` with both effective (`div(f)_∞ = div(f⁻¹)₀`).
Then
```
𝒪_{V×V,(x,x)} = { f ∈ k(V×V) | div(f)_∞ does not contain (x,x) } ∪ {0}.
```
Suppose `φ` is not defined at `x`. Then for some `f ∈ Im(φ*)`, `(x, x) ∈ div(f)_∞`, and clearly
`Φ` is not defined at the points `(y, y) ∈ Δ ∩ div(f)_∞`. **This is a subset of pure codimension
one in `Δ` (AG 9.2)**, and when we identify it with a subset of `V`, it is a subset of `V` of
codimension one passing through `x` on which `φ` is not defined. ∎

## The 4-substep Lean decomposition

Let `X = V` (smooth integral over `k̄`), `G` a smooth group variety, `f : X ⇢ G` over `k̄`.
`Φ = differenceRationalMap f hover : X ×_{k̄} X ⇢ G` (built in `Albanese/DifferenceMap.lean`).

- **Sub-step 1 — the difference map `Φ`.** DONE (`differenceRationalMap`, `GrpObj.diff`,
  `grpObjDiffLeft`, `differenceRationalMap_compHom_over`). Axiom-clean.
- **Sub-step 1 domain bound / Sub-step 2 easy direction — `Dom(f) ×_{k̄} Dom(f) ⊆ Dom(Φ)`.**
  DONE (session 0042, `le_domain_differenceRationalMap` in `DifferenceMap.lean`, axiom-clean).
  This is Milne's "clearly `Φ` is defined at `(x, x)` if `φ` is defined at `x`". Supporting:
  `le_domain_compHom` (compHom domain monotonicity — a Mathlib gap), `precompDiffPairing` (the
  explicit `U×U → G×G` morphism), `precompDiffPairing_toRationalMap` (it represents `prod`).
  Blueprint: `lem:difference_map_domain_lower_bound`, `lem:compHom_domain_monotone`.
- **Sub-step 2 hard direction — `Φ` defined at `(x,x)` ⟹ `φ` defined at `x`.**
  **ALGEBRAIC CONTENT DONE** (session 0047, `DifferenceMap.lean`, all axiom-clean):
  - `GrpObj.lift_diff_lift_mul` — abstract group identity `(a·b⁻¹)·b = a` for `T`-points
    (`lift ⟨lift a b ≫ diff, b⟩ ≫ μ = a`), via `GrpObj.comp_div` + `div_mul_cancel`.
  - `grpObjMulLeft` + `pullback_lift_diff_lift_mul` — scheme transport: apply `(-).left`
    (`Over.forget`, functorial; `Over.lift_left`/`fst_left` are `rfl`) to the abstract lemma,
    lifting `A,B : Spec K ⟶ G` to over-`k̄` morphisms via `Over.homMk`.
  - `reconstruct_precomp_fst` — `f ∘ pr₁ = mᴸ ∘ ⟨Φ, f ∘ pr₂⟩` as rational maps, matched on
    function fields by `eq_of_fromFunctionField_eq` + `prod_fromFunctionField`.
  - `le_domain_precomp_fst_of_difference` — Milne's `f(x)=Φ(x,u)·f(u)` domain content:
    `Dom(Φ) ⊓ pr₂⁻¹(Dom f) ≤ Dom(f∘pr₁)`. Uses `reconstruct` + `le_domain_prod` (S2) +
    `le_domain_precomp` (S1) + `le_domain_compHom`.
  **TOPOLOGICAL REMAINDER OPEN** (the two genuine gaps for closing sub-step 2):
  (a) **existence of `u`**: find `u` with `(x,u) ∈ Dom(Φ)` and `u ∈ Dom(f)` — openness of
      `Dom(Φ) ∋ (x,x)` + irreducibility of the fibre `X_{κ(x)}` (this is WHY the theorem
      carries `GeometricallyIrreducible`: `X ×_k κ(x)` is irreducible, so two nonempty opens
      in it meet) + surjectivity of `pr₂|fibre` onto `Dom f`.
  (b) **smooth-descent reflection** `Dom(f∘pr₁) ⊆ pr₁⁻¹(Dom f)` — the REVERSE of the easy
      `le_domain_precomp` (S1), needs faithfully-flat descent of definedness along the smooth
      surjective `pr₁` (a general theorem, likely a from-scratch fppf-descent build; NOT a
      one-session item). Only then does `(x,u) ∈ Dom(f∘pr₁)` give `x ∈ Dom(f)`.
  Supporting Mathlib-gap bricks landed this session, both reusable/general:
  `RationalMap.le_domain_precomp` (`RationalMapPrecomp.lean`, S1) and `pairPartialMap` +
  `le_domain_prod` (`RationalMapProd.lean`, S2, generalizes `precompDiffPairing`).
- **Sub-step 3 — definedness ⟺ `Φ*(𝒪_{G,e}) ⊆ 𝒪_{X×X,(x,x)}`.** OPEN. Anchors the pullback at
  `e ∈ G` (Φ maps the diagonal to `e`, giving an affine chart around `e`). `functionFieldPullback`
  (`RationalMapFunctionField.lean`, K(G) → K(X×X) for dominant Φ) and `stalkPullback` exist, but
  the germ pullback at `e` (not at `Φ(η)`) needs the closure-of-image `Ḡ ∋ e` OR a direct
  local-ring pullback along `Φ`. **Dominance caveat:** `Φ` need not be dominant onto `G` (if
  `im(f)` lands in a proper subgroup); replace `G` by the closure of the image, a subgroup.
- **Sub-step 4a — pole purity on `X×X`.** DONE (`Albanese/PolePurity.lean`,
  `Scheme.exists_specializes_coheight_eq_one_of_notMem_stalk_range`): `h ∈ K(X×X)` not regular at
  `P` ⟹ ∃ coheight-1 `z ⤳ P` with `h` not regular at `z`. Axiom-clean.
- **Sub-step 4b — `Δ ∩ div(f)_∞` is pure codim 1 in `Δ ≅ X`.** OPEN. The pole divisor of
  `f = Φ*(g)` on `X×X` meets the diagonal `Δ` (which is NOT contained in it, since `Φ ≡ e` on the
  generic diagonal point, so `f = g(e)` is regular there generically) in pure codim 1 — Krull's
  Hauptidealsatz / a local equation of `div(f)_∞` restricted to `Δ`. This transports a codim-1
  pole point of `X×X` through `Δ` to a coheight-1 `z ∈ X` with `x ∈ closure{z}` and `z ∈ Z(f)`.
  **Note:** `f|_Δ` is the constant `g(e)`, so this does NOT reduce to pole-purity-on-`X` of a
  single function; it genuinely needs the `X×X` divisor + local-equation-restricted-to-`Δ`.

## Assembly (once 2-hard, 3, 4b land)

Given `x₀ ∈ Z(f)`: by (2-hard) `(x₀,x₀) ∈ Z(Φ)`; by (3) some `g ∈ 𝒪_{G,e}` has `Φ*(g) ∉
𝒪_{X×X,(x₀,x₀)}`; by (4a) a codim-1 pole point `w ⤳ (x₀,x₀)`; by (4b) transport through `Δ` to
codim-1 `z ∈ Z(f)` with `x₀ ∈ closure{z}`. The `z ∈ Z(f)` conjunct is essential (memory
`t9-albanese-endgame-unblock-map`): without it the disjunct is vacuous and cannot combine with
Milne 3.1. **Do NOT reintroduce** `extend_of_codimOneFree` (false: `ℙ² ⇢ ℙ¹`).

## Lean engineering recipes discovered (session 0042)

- **Over-ness of `f.toPartialMap`**: register local `Scheme.Over` instances `⟨X.hom⟩`, `⟨G.hom⟩`,
  then `f.IsOver S := RationalMap.isOver_iff.mpr hover`; the `f.toPartialMap.IsOver S` instance
  fires (needs `[IsReduced X.left] [G.left.IsSeparated]`), and `PartialMap.isOver_iff.mp
  inferInstance` gives `f.toPartialMap.hom ≫ G.hom = f.toPartialMap.domain.ι ≫ X.hom`. The `↘`
  reduces to `X.hom`/`G.hom` by defeq (`exact h`, not `simpa`).
- **Pullback projections are both over `S`**: register `(pullback X.hom X.hom).Over S :=
  ⟨pullback.fst _ _ ≫ X.hom⟩`; then `fst.IsOver S := ⟨rfl⟩`, `snd.IsOver S :=
  ⟨pullback.condition.symm⟩`. So both `f.toPartialMap.precomp prᵢ` inherit over-ness via
  `precomp_isOver` — avoids unfolding `precomp_hom` (which hits an instance-transparency wall).
- **KERNEL-TIMEOUT GOTCHA**: building the pairing partial map inline with `set aR/bR/Ψ := …` +
  `pullback.lift` causes `(kernel) deterministic timeout` (nested `set`-lets over pullback/scheme
  terms). FIX: extract the pairing as a **top-level `noncomputable def`** (`precompDiffPairing`,
  `where`-syntax, no `set`); it kernel-checks once in isolation and the consumer references it
  opaquely. (Consistent with the standing `set`-is-problematic lesson.)
- **Function-field match** (`precompDiffPairing_toRationalMap`): `eq_of_fromFunctionField_eq` +
  `prod_fromFunctionField` + `pullback.hom_ext`; per leg, rewrite RHS `(f.precomp prᵢ).ff =
  (f.toPartialMap.precomp prᵢ).ff` (`← fromFunctionField_toRationalMap`, `precomp_toRationalMap`,
  `toRationalMap_toPartialMap`), then `← fromFunctionField_restrict … dense_domain inf_le_left`,
  `simp only [PartialMap.fromFunctionField, fromSpecStalkOfMem, restrict_hom, Category.assoc]`,
  `congr 1` (proof-irrelevant stalk map), `exact pullback.lift_fst _ _ _`.
- `set_option`/`omit … in` must precede the docstring, not sit between it and the theorem.
