# Analogy: composite-adjunction unit cocycle for `L = Q ∘ F` (sheafify ∘ pullback), recovering the functor-wrapped inner unit via a `homEquiv`/conjugate head

## Mode
cross-domain-inspiration

## Slug
d3-mate271

## Iteration
271

## Structural problem (abstracted)
Two adjunctions whose left adjoints are composites `L = Q ∘ F` (`Q` a reflective
localization / sheafification, `F` a base-change/pullback functor). Need the unit-cocycle for the
composite-of-composites: `η^{h≫f}` factors through `η^f`, `η^h`, and a nontrivial comparison 2-cell
`(Q∘F)(h)∘(Q∘F)(f) ≅ (Q∘F)(h≫f)`. The single sticking point: a functor-wrapped comparison factor
`(pullback h).map ((sheafCompPb f).hom.app P)` (`= whiskerLeft (pullback h) (comparison_f)` at a point)
has no transposable head, so the brick `leftAdjointUniqUnitEta_app` (= `homEquiv_leftAdjointUniq_hom_app`)
cannot fire to rewrite it into the inner composite-adjunction unit `B_f.unit`.

## Failed approaches (from directive)
- Sectionwise `hom_ext; intro U; rfl`: composite-adjunction unit not sectionwise trivial (sheafification unit contaminates).
- Transposing the WHOLE tail back through `homEquiv`: circular (re-folds the R0-peel; iter-263).
- `Adjunction.comp_unit_app` + `unit_naturality` directly: inner factors never present a `homEquiv` head.
- Boundary bridge `forget_map_pushforward_map` (rfl, landed): crosses sheaf↔presheaf but supplies no head.

## Analogues found

### Analogue: `CategoryTheory.Adjunction.conjugateEquiv_whiskerLeft` (`Mathlib/CategoryTheory/Adjunction/Mates.lean:525`)  ← THE missing device
- **Domain**: pure category theory (mate calculus / conjugate transformations).
- **Same structural problem there**: how does the conjugate (= the homEquiv transpose between two
  left-adjoint factorizations) interact with *whiskering a comparison 2-cell by an outer functor*?
  Statement:
  ```
  conjugateEquiv (adj.comp adj₁) (adj.comp adj₂) (whiskerLeft L τ)
      = whiskerRight (conjugateEquiv adj₁ adj₂ τ) R
  ```
  i.e. the conjugate of `L`-whiskered `τ` (where `adj : L ⊣ R`) equals `R`-whiskered conjugate of `τ`.
- **Technique**: `ext X; ... simp [← reassoc_of% h₁, reassoc_of% h₂]` where `h₁ = (R₂⋙R).map (τ.naturality (adj.counit …))`, `h₂ = R.map (adj₂.unit_naturality (adj.counit …))`. The whole content is "slide the
  comparison's naturality + the outer adjunction's unit/counit triangle past the whiskering".
- **Mapping to project**: the project's stuck factor is `forget.map ((pullback h).map ((sheafCompPb f).hom.app P))`.
  Here `(pullback h)` is the LEFT adjoint of the h-adjunction `pullbackPushforwardAdjunction h : pullback h ⊣ pushforward h`,
  and `(pullback h).map (g.app P) = (whiskerLeft (pullback h) g).app P` for the natural transformation
  `g = (sheafCompPb f).hom`. Apply `conjugateEquiv_whiskerLeft` with `adj := (h-composite-adjunction)`,
  `adj₁/adj₂ := the two f-composite-adjunctions A_f, B_f`, `L := pullback h`, `τ := (sheafCompPb f).hom`
  (which is a `conjugateEquiv`-image of identity, since `sheafCompPb f = leftAdjointUniq A_f B_f` and
  `leftAdjointUniq = (conjugateIsoEquiv …).symm (Iso.refl _) |>.symm`, Unique.lean:36). The conclusion
  gives the factor a `whiskerRight (conjugateEquiv …) R` form whose conjugate/`homEquiv` head is exactly
  what `leftAdjointUniqUnitEta_app` consumes. The `forget`/`restrictScalars` outer wrapping is already
  crossed by the landed `forget_map_pushforward_map`.
- **Porting cost**: low–medium. One `have` mirroring `conjugateEquiv_whiskerLeft`'s 4-line proof, instantiated
  at the project's composite adjunctions. No new infrastructure; `conjugateEquiv_whiskerLeft`,
  `conjugateEquiv_comp` (Mates.lean:338), `conjugateEquiv_whiskerRight` (Mates.lean:536) are all shipped.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Adjunction.leftAdjointCompNatTrans_assoc` + `…₀₁₃_eq_conjugateEquiv_symm` (`Mathlib/CategoryTheory/Adjunction/CompositionIso.lean:155, 130`)  ← the whole cocycle, done abstractly, and ALREADY applied to sheaf pullback
- **Domain**: category theory; *directly* the alg-geom pullback setting (same Mathlib file family as the project's `sheafificationCompPullback`).
- **Same structural problem there**: the associativity/cocycle of the comparison isos `leftAdjointCompIso`
  for left adjoints of composite adjunctions — proved by transporting to the (trivial) right-adjoint side.
  CRUCIAL: Mathlib's docstring (CompositionIso.lean:19–23) states this machinery is used **precisely** for
  `PresheafOfModules.pullback` AND `SheafOfModules` pullback composition in `PullbackContinuous.lean`.
  Indeed `SheafOfModules.pullbackComp` (PullbackContinuous.lean:166) `:= leftAdjointCompIso …` and
  `SheafOfModules.pullback_assoc` (PullbackContinuous.lean:192) `:= leftAdjointCompIso_assoc …` — the exact
  analogue of the project's `sheafificationCompPullback_comp`, one functor over.
- **Technique** (the NON-circular reduction, sidestepping failed approach #2):
  1. `obtain ⟨τ, rfl⟩ := (conjugateEquiv …).surjective τ` — write each comparison factor as `conjugateEquiv`
     of an explicit RIGHT-adjoint (pushforward) transformation.
  2. `apply (conjugateEquiv …).injective` — reduce the whole identity to the right-adjoint side.
  3. `simp [leftAdjointCompNatTrans, ← conjugateEquiv_whiskerLeft, conjugateEquiv_comp,
     conjugateEquiv_associator_hom, ← conjugateEquiv_whiskerRight]` — move every whiskering/composite past
     the conjugate, collapsing to the pushforward coherence (sectionwise `rfl` for pushforward).
  This is NOT failed-approach-#2: #2 transposed and re-folded the SAME left-adjoint statement (circular);
  here the content lands on the pushforward/right-adjoint side where Mathlib's coherence is already trivial.
- **Mapping to project**: reframe `sheafificationCompPullback_comp` as a conjugate-image identity. The three
  `sheafCompPb` isos are `leftAdjointUniq` of composite adjunctions (already noted in `sheafificationCompPullback_eq_leftAdjointUniq`),
  hence `conjugateEquiv`-images; the conjugate of the whole cocycle reduces to the pushforward composition
  coherence (`SheafOfModules.pushforwardComp` is `Iso.refl`-flavoured / sectionwise trivial, per
  `pushforwardComp_hom_app_app : … = 𝟙 _`).
- **Porting cost**: medium–high. Re-does the partially-finished proof in the conjugate vocabulary rather
  than the `homEquiv`-tail vocabulary; bigger diff but structurally the canonical route and matches Mathlib's
  own proof of the sibling lemma `pullback_assoc`.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Adjunction.localization` / `localization_unit_app` (`Mathlib/CategoryTheory/Localization/Adjunction.lean:90, 121`)
- **Domain**: category theory — localization of an adjunction along reflective localizations (the abstract
  shape of sheafification).
- **Same structural problem there**: given `adj : G ⊣ F` and localization functors `L₁, L₂` with 2-commutative
  squares `CatCommSq G L₁ L₂ G'` / `CatCommSq F L₂ L₁ F'` (the comparison 2-cells), the localized adjunction
  `G' ⊣ F'` has unit
  ```
  (adj.localization …).unit.app (L₁.obj X₁) =
    L₁.map (adj.unit.app X₁) ≫ (CatCommSq.iso F L₂ L₁ F').hom.app _ ≫ F'.map ((CatCommSq.iso G L₁ L₂ G').hom.app _)
  ```
  — the localized unit *expressed through the comparison 2-cells* (`CatCommSq.iso` = the abstract
  `sheafificationCompPullback`). Exactly the cocycle shape, with `Q = L₁` and `F = G`.
- **Technique**: the localized unit is `liftNatTrans L₁ W₁ … (whiskerRight adj.unit L₁)` (universal property of
  localization extends the un-localized unit). Identities about it are proved by `natTrans_ext L₁ W₁`
  (two transformations out of a localized category agree iff they agree after whiskering with `L₁` =
  `toSheafify`) — NOT sectionwise — and the comparison 2-cells slide via `(CatCommSq.iso …).naturality`.
- **Mapping to project**: the project built `B_φ` as `Adjunction.comp` rather than `Adjunction.localization`,
  so this is a structural model, not a drop-in. The reusable lesson: avoid the sectionwise `rfl` that
  contaminates (failed approach #1) by using the localization universal property (`natTrans_ext` / the
  sheafification adjunction's `homEquiv`-injectivity on the sheafy side) instead of `intro U`.
- **Porting cost**: high (would require recasting `B_φ` as `Adjunction.localization` with `CatCommSq` data).
- **Verdict**: PARTIAL_ANALOGUE.

### Analogue (component lemmas): `unit_mateEquiv` / `unit_mateEquiv_symm` (Mates.lean:133,148); `unit_leftAdjointUniq_hom_app` (Unique.lean:51)
- **Domain**: category theory (mate calculus).
- **Same structural problem there**: relate a unit-prefixed mate/conjugate to the raw comparison.
  `unit_mateEquiv`: `G.map (adj₁.unit.app c) ≫ (mateEquiv adj₁ adj₂ α).app _ = adj₂.unit.app _ ≫ R₂.map (α.app _)`.
  `unit_leftAdjointUniq_hom_app` (`@[reassoc (attr := simp)]`):
  `adj1.unit.app x ≫ G.map ((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x`.
- **Technique / mapping**: `unit_leftAdjointUniq_hom_app` is the unit-PREFIXED reassoc form that recovers
  `G.map (leftAdjointUniq.hom.app x)` *without* manufacturing a homEquiv head — it fires mid-composite via
  its `_assoc` variant. If the project's stuck factor can be arranged so the right adjoint `G = pushforward f`
  wraps the comparison and the f-unit precedes it, this rewrites directly. The mismatch (the wrapping functor
  is `pullback h`, a *left* adjoint of the *other* adjunction, not `pushforward f`) is exactly what forces the
  `conjugateEquiv_whiskerLeft` step above first.
- **Porting cost**: low (already-shipped simp lemmas).
- **Verdict**: ANALOGUE_FOUND (supporting lemmas for the top suggestion).

## Top suggestion
Build the single missing `have` as the project-instance of **`conjugateEquiv_whiskerLeft`
(`Mathlib/CategoryTheory/Adjunction/Mates.lean:525`)**. That lemma is *literally* "the conjugate of
`(pullback h).map`-wrapped comparison = the right-whiskered conjugate", which is the homEquiv/conjugate
head that `leftAdjointUniqUnitEta_app` needs. Read first: Mates.lean:525–544 (`conjugateEquiv_whiskerLeft`
+ `_whiskerRight`), Mates.lean:338 (`conjugateEquiv_comp`), and — for the END-TO-END recipe that proves the
exact sibling coherence one functor over — `CompositionIso.lean:130–164`
(`leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm` and `leftAdjointCompNatTrans_assoc`) together with its
real consumer `PullbackContinuous.lean:192` (`SheafOfModules.pullback_assoc`). First project file to touch:
`AlgebraicJacobian/Picard/TensorObjSubstrate.lean:2638` (the `sorry` in `sheafificationCompPullback_comp_tail`),
adding a `have` that recognises `(pullback h).map ((sheafCompPb f).hom.app P) = (whiskerLeft (pullback h)
(sheafCompPb f).hom).app P`, transposes it by `conjugateEquiv_whiskerLeft`, and feeds the conjugate-headed
result to `leftAdjointUniqUnitEta_app`. If that `have` proves fiddly to instantiate, escalate to the
medium-cost route: re-prove `sheafificationCompPullback_comp` wholesale by the `surjective`/`injective` +
whisker/comp reduction of `leftAdjointCompNatTrans_assoc`, which lands the content on the trivial pushforward
side and is exactly how Mathlib proved `pullback_assoc`.
