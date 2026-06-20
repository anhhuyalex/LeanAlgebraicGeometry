# Analogy: Mathlib idiom for the fibre of `pullback.snd` over a rational point

## Mode
api-alignment

## Slug
rigidity-hfib

## Iteration
159

## Question
What is the Mathlib idiom for "the fibre of `Limits.pullback.snd X.hom Y.hom` over a `k̄`-rational
point `y₀pt` of `Y` is contained in (in fact equals) the image of the canonical slice section
`s : X → X ×_{Spec k̄} Y`"? Is there an existing result, or a clean idiomatic assembly, to close
`hfib : (snd X Y).left.base ⁻¹' {y₀pt} ⊆ Set.range s.base`?

## Project artifact(s)
- `AlgebraicJacobian/AbelianVarietyRigidity.lean:154` — the `hfib` sorry.
- `AlgebraicJacobian/AbelianVarietyRigidity.lean:111-181` — enclosing `rigidity_eqOn_dense_open`;
  `s`, `y₀pt`, `ptk`, `p₂ = (snd X Y).left` defined L131-149.

## Decisions identified

### Decision: which Mathlib machinery proves the fibre-over-rational-point fact

- **Mathlib idiom**: prove a single `IsPullback` square for the slice section, then read off the
  fibre with the **`IsPullback`-level** range lemma
  `AlgebraicGeometry.Scheme.Pullback.image_preimage_eq_of_isPullback`
  (`Mathlib/AlgebraicGeometry/PullbackCarrier.lean:414`):
  `(h : IsPullback fst snd f g) (s : Set X) : snd.base '' (fst.base ⁻¹' s) = g.base ⁻¹' (f.base '' s)`.
  This is the canonical way Mathlib relates pullback projections to sets; it is stated at the
  `IsPullback` level (not the chosen-`Limits.pullback` level), so it composes with arbitrary
  pullback squares produced by the categorical pasting calculus
  (`CategoryTheory.IsPullback.{paste_horiz, of_right, of_horiz_isIso, flip}`, all in
  `Mathlib/CategoryTheory/Limits/Shapes/Pullback/IsPullback/Basic.lean`).
  Why Mathlib chose this: the `Triplet`/`tensor`/`carrierEquiv` API
  (`PullbackCarrier.lean:41-291`) is the *fine* description (it pins the exact scheme-point as a
  prime of `κ(x) ⊗_{κ(s)} κ(y)`); the `image_preimage_eq_of_isPullback` /
  `exists_preimage_of_isPullback` pair is the *coarse* topological description meant for exactly
  this kind of "where does the fibre sit" question, and it does not force the user to compute any
  residue field or tensor product.

- **Project's (about-to-be-taken) path**: the iter-158 prover lane located
  `carrierEquiv` / `Triplet` / `.tensor` / `.carrierEquiv_eq_iff` and intended to prove `hfib` by
  computing the fibre point as a prime of `κ(x) ⊗_{k̄} κ(y₀pt)`, via three sub-lemmas:
  (a) `κ(y₀pt) = k̄` because `y₀.left` is a section; (b) `Subsingleton (Spec (κ(x) ⊗_{k̄} k̄))`;
  (c) feeding that through `carrierEquiv` to land `= s x`.

- **Gap**: divergent-with-cost. The project's path *works in principle* but is the heavyweight
  parallel route. Sub-lemmas (a), (b), (c) are **all unnecessary**.

- **Cost of divergence**: (a) needs "residue field at a rational point = base field", which
  Mathlib does not package directly — it would require building a retraction-of-field-extension
  argument from the section. (b) needs `Subsingleton (Spec (pushout κ(s)→κ(x), κ(s)→κ(y)))`, i.e.
  "tensoring a field with the base field over itself is a field" — a pushout-along-an-iso fact
  that has no off-the-shelf form here. (c) is fiddly `carrierEquiv`/`Triplet.ext` plumbing. Three
  genuine sub-builds, two of them residue-field/commutative-algebra infrastructure, replacing what
  is a ~10-line categorical assembly.

- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision: how the "y₀ is a rational point / section" hypothesis enters

- **Mathlib idiom**: via `CategoryTheory.Over.w` + `Over.tensorUnit_hom`. A morphism
  `y₀ : 𝟙_ (Over S) ⟶ Y` has `Over.w y₀ : y₀.left ≫ Y.hom = (𝟙_).hom`, and
  `Over.tensorUnit_hom : (𝟙_ (Over X)).hom = 𝟙 X := rfl`
  (`Mathlib/CategoryTheory/Monoidal/Cartesian/Over.lean:68`), so `y₀.left ≫ Y.hom = 𝟙 S`. The
  section property is therefore `rfl`-clean and is exactly what makes the outer pasting square a
  pullback (`IsPullback.of_horiz_isIso`, both horizontal legs become `𝟙`). No residue field needed.
- **Project's path (Triplet route)**: would have routed this through "`κ(y₀pt)=k̄`".
- **Gap**: divergent-with-cost (subsumed by the decision above).
- **Verdict**: ALIGN_WITH_MATHLIB.

## Recommendation

Do NOT build the residue-field/tensor sub-lemmas. Close `hfib` (in fact with equality) by the
following idiomatic assembly. Let `p₁ := pullback.fst X.hom Y.hom`, `p₂ := pullback.snd X.hom Y.hom`
(so `(snd X Y).left = p₂` by `Over.snd_left`, and `s : X.left ⟶ pullback X.hom Y.hom`).

1. `hsp1 : s ≫ p₁ = 𝟙 X.left`  — from `lift_fst` at the `Over` level, pushed through
   `← Over.fst_left`, `← Over.comp_left`.
2. `hsp2 : s ≫ p₂ = X.hom ≫ y₀.left`  — from `lift_snd`, `← Over.snd_left`, `← Over.comp_left`,
   plus `(toUnit X).left = X.hom` (one line: `Over.w (toUnit X)` + `tensorUnit_hom` + `comp_id`).
3. `hsec : y₀.left ≫ Y.hom = 𝟙 (Spec (.of kbar))`  — `Over.w y₀` then `tensorUnit_hom`.
4. `houter : IsPullback (s ≫ p₁) X.hom X.hom (y₀.left ≫ Y.hom)`  — `rw [hsp1, hsec]` then
   `IsPullback.of_horiz_isIso ⟨by simp⟩` (both legs are `𝟙`, hence `IsIso`).
5. `hL : IsPullback s X.hom p₂ y₀.left`  — `IsPullback.of_right houter hsp2 (IsPullback.of_hasPullback X.hom Y.hom)`.
6. `hrange : Set.range s.base = p₂.base ⁻¹' Set.range y₀.left.base`  —
   `simpa [Set.image_univ, Set.preimage_univ] using Scheme.Pullback.image_preimage_eq_of_isPullback hL.flip Set.univ`.
7. Close: `rw [Over.snd_left, hrange]; exact Set.preimage_mono (Set.singleton_subset_iff.mpr ⟨ptk, rfl⟩)`.

Step 6 actually proves the *equality* `range s.base = p₂⁻¹(range y₀.left)`; combined with
`range y₀.left = {y₀pt}` (S subsingleton, instance `hsub` already in scope at L131) it would even
give `p₂⁻¹{y₀pt} = range s.base` exactly — but the `⊆` the lemma needs follows from step 7 without
the subsingleton, since `y₀pt ∈ range y₀.left` trivially. No `[IsAlgClosed]`, no residue fields,
no tensor products, char-free.

All cited declarations were LSP-verified at iter-159 against the project's pinned Mathlib.
