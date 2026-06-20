# Analogy: naturality of a sheafification-unit ∘ monoidal-whiskering square across two defeq `MonoidalCategoryStruct` instances + an identity `restrictScalars (𝟙)` wrapper

## Mode
cross-domain-inspiration

## Slug
tscmp254

## Iteration
254

## Structural problem (abstracted)
We must prove a naturality square for the tensor-comparison morphism of a **monoidal
localization/reflection** (here: sheafification `a = presheafToSheaf` of presheaves of modules),
of the shape `(p ⊗ₘ q) ≫ (η ▷ ≫ ◁ η) = (η ▷ ≫ ◁ η) ≫ (ā ⊗ₘ b̄)`, where `η` is the reflection unit
and `▷/◁` are monoidal whiskerings. Two obstructions, both *elaboration*-level not math-level:
(1) the whisker terms carry two **defeq-but-head-distinct `MonoidalCategoryStruct` instances**
(one from `tensorHom_def`, one frozen into the comparison iso), so `whisker_exchange` cannot bridge
the cross-group crossing; (2) the reflection unit's codomain carries an **identity base-change
wrapper `restrictScalars (𝟙 R)`** that refuses to `whnf`-normalize and detonates `erw`.

## Failed approaches (from directive)
- `letI` instance-unification of the two monoidal structs — `whisker_exchange` still cannot cross.
- `erw`-driven `≫`-instance bridge — non-terminating `whnf` on `restrictScalars (𝟙)`-over-sheafification.
- Uniform-instance helper on the `X.ringCatSheaf.obj` / `Sheaf.val` spelling — `synthInstanceFailed` ×4.
- Element-level `TensorProduct.induction_on` — same instance/whnf split blocks the final whisker.

## Analogues found

### Analogue: `CategoryTheory.Functor.LaxMonoidal.μ_natural_left / .μ_natural_right` (and `OplaxMonoidal.δ_natural_left/right`)
Cite: `Mathlib/CategoryTheory/Monoidal/Functor.lean:70-104` (`μ_natural_left`, `μ_natural_right`,
`μ_natural`), `:246-286` (`δ_natural_left/right`, `δ_natural`). All are `@[reassoc (attr := simp)]`.

- **Domain**: category theory / monoidal functors (the abstract heart shared by every monoidal
  adjunction in Mathlib — `Mon_`, `Action`/`Rep`, localization, sheafification).
- **Same structural problem there**: this is *exactly* "naturality of a monoidal functor's tensor
  comparison `μ`/`δ` composed with a single-sided whiskering". `μ_natural_left f X' :
  F.map f ▷ F.obj X' ≫ μ ... = μ ... ≫ F.map (f ▷ X')`. The square the project is grinding by hand
  IS the paste of `δ_natural_left` (in `p`) and `δ_natural_right` (in `q`) for ONE monoidal functor.
- **Technique**: never expand `tensorHom_def` into a two-instance whisker soup. Each lemma whiskers
  on **one** side only, against the functor's **own** `μ`/`δ` — so every term lives in a single
  `MonoidalCategoryStruct` instance and the cross-group crossing never forms. The project ALREADY
  uses this exact lemma family for the sibling square S2 of `pullbackTensorMap_natural`
  (`Functor.OplaxMonoidal.δ_natural`, see TensorObjSubstrate.lean:2016). The fix is to make S3
  (`sheafifyTensorUnitIso_hom_natural`) the SAME kind of object — a `δ`/`μ` naturality of the
  sheafification monoidal functor — instead of a bespoke whisker calculation.
- **Mapping to project**: `sheafifyTensorUnitIso` relates `a(P⊗Q)` with `(aP).val ⊗ (aQ).val`; that
  is precisely the oplax comparison `δ` of the composite `sheafification ⋙ forget` (or `μ⁻¹`).
  Restate `sheafifyTensorUnitIso_hom_natural` as the paste `δ_natural_left (a.map p)` then
  `δ_natural_right (a.map q)` of that monoidal functor; both fire by `simp`/`rw` with no `erw`, no
  `tensorHom_def`, no second instance.
- **Porting cost**: low–medium. Needs the sheafification (or `sheafification ⋙ forget`) functor to
  carry a `Functor.OplaxMonoidal`/`LaxMonoidal` instance whose `δ`/`μ` IS the project's
  `sheafifyTensorUnitIso`. The project already built oplax/lax structures
  (`presheafPullbackOplaxMonoidal`, `presheafPushforwardLaxMonoidal`, memory ts242) and already
  consumes `δ_natural` at S2 — so the scaffolding pattern is in hand.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `CategoryTheory.Localization.Monoidal` — `tensorBifunctor` / `tensorBifunctorIso` / `μ_natural_left`
Cite: `Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean:86-88` (`LocalizedMonoidal` type
synonym), `:122-138` (`tensorBifunctor`, `tensorBifunctorIso`), `:172-180`
(single `monoidalCategoryStruct` on the synonym), `:184-201` (`μ`, `μ_natural_left`,
`μ_natural_right`). Consumed by `Mathlib/CategoryTheory/Sites/Monoidal.lean:161-205`
(`Sheaf.monoidalCategory` + the `presheafToSheaf.Monoidal` instance) — i.e. Mathlib's OWN
"sheafification is monoidal" lives here.

- **Domain**: category theory / localization (the construction Mathlib uses to make *sheafification*
  monoidal — the closest possible sibling of the project's setting).
- **Same structural problem there**: building a monoidal structure on a reflective localization `D`
  (sheaves) from the one on `C` (presheaves), and proving the localization functor's comparison-with-
  whiskering naturality squares — i.e. the project's exact square, in Mathlib's own hands.
- **Technique (the decisive lesson)**: Mathlib **never** proves these squares by whisker calculus.
  It (a) carries the monoidal structure on a dedicated **type synonym** `LocalizedMonoidal L W ε`
  that holds **ONE** canonical `MonoidalCategoryStruct` (no defeq-spelling collision can arise,
  because there is only one head); and (b) packages the comparison as a **bifunctor `NatTrans`**
  `tensorBifunctorIso`, reading the whisker-naturality straight off `NatTrans.naturality_app`
  (`μ_natural_left := NatTrans.naturality_app (tensorBifunctorIso …).hom Y f`, line 191). No
  `tensorHom_def`, no `whisker_exchange`, no `erw`.
- **Mapping to project**: the project's two-instance collision is the *symptom of fighting the
  whisker calculus directly* — precisely the path Mathlib structurally avoids. The portable move is
  to express the comparison as a NatTrans of bifunctors `(P,Q) ↦ a(P⊗Q)` vs
  `(P,Q) ↦ (aP).val ⊗ (aQ).val` and take naturality in `p`/`q` separately from
  `NatTrans.naturality_app`. This is the abstract justification for Analogue 1.
- **Porting cost**: high if taken literally (`Sheaf.monoidalCategory` needs `MonoidalClosed A` +
  `HasFunctorEnrichedHom` for `A = ModuleCat`, and `J.W.IsMonoidal` for `PresheafOfModules` — memory
  ts233 records this whole route as DEAD for the project). So DO NOT instantiate `LocalizedMonoidal`.
  Borrow only the **principle** (single-instance synonym + bifunctor-NatTrans naturality), realized
  cheaply through Analogue 1's `δ`/`μ` lemmas.
- **Verdict**: PARTIAL_ANALOGUE (principle portable; the construction itself is not).

### Analogue: `ModuleCat.restrictScalarsId'App_inv_naturality` + `map_id`, as used in presheaf (co)limits
Cite: def `Mathlib/Algebra/Category/ModuleCat/ChangeOfRings.lean:188-226`
(`restrictScalarsId'App`, `restrictScalarsId'`, `restrictScalarsId'App_hom/inv_naturality`,
`abbrev restrictScalarsId`); usage `Mathlib/Algebra/Category/ModuleCat/Presheaf/Colimits.lean:79`
(`rw [ModuleCat.restrictScalarsId'App_inv_naturality, map_id]`) and
`…/Presheaf/Limits.lean:84-85`; instance-diamond workaround
`…/Presheaf/Pushforward.lean:44-53` (`@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_)`).
Root of the wrapper: `…/Presheaf/Sheafify.lean:329` — `toSheafify α φ : M₀ ⟶ (restrictScalars α).obj
(sheafify α φ).val` bakes `restrictScalars α` into the unit's codomain (so `α = 𝟙` ⇒ the wrapper).

- **Domain**: change-of-rings for modules (`ModuleCat` / `PresheafOfModules`).
- **Same structural problem there**: a `restrictScalars (𝟙)` wrapper sitting on a map's codomain
  that must be stripped before it pollutes a `rw`/`whnf`.
- **Technique**: Mathlib strips it **by an explicit `rw` with the dedicated `…Id'App_*_naturality`
  simp lemma immediately, BEFORE any `whnf`-forcing step** (Colimits/Limits do exactly this), and
  side-steps the `restrictScalarsId'` instance **diamond** with explicit instance placeholders
  `(_) (_)` in a `@LinearMap.ext`. The lesson: don't let `restrictScalars (𝟙)` reach an `erw`/`whnf`
  — rewrite it away first with the named naturality lemma.
- **Mapping to project**: the catastrophic `whnf` (failed approach #2) is caused by deferring the
  wrapper to `erw`. Mirror Colimits.lean: `rw [restrictScalarsId'App_inv_naturality, map_id]`
  (ModuleCat level) / the project's own `restrictScalarsId_map` (presheaf level) as an EARLY `rw`,
  so the unit's codomain aligns syntactically and the subsequent whisker step needs no `erw`.
  Note: at the **PresheafOfModules** level Mathlib registers only `(restrictScalars (𝟙 R)).Full =
  𝟭.Full` (ChangeOfRings.lean:63) — there is **no** `PresheafOfModules.restrictScalarsId` NatIso.
  That is a genuine Mathlib gap; the project's `restrictScalarsId_map` is the correct local fill and
  should be applied eagerly, exactly as ModuleCat-level `restrictScalarsId'App_inv_naturality` is.
- **Porting cost**: low. Reorder the existing `restrictScalarsId_map` strip to fire BEFORE the
  whisker/`erw` steps.
- **Verdict**: ANALOGUE_FOUND.

## Top suggestion
Stop proving `sheafifyTensorUnitIso_hom_natural` (and S3 of `pullbackTensorMap_natural`) by hand
whisker calculus. Reformulate it as the **two single-sided naturality lemmas** of the sheafification
monoidal comparison: `Functor.OplaxMonoidal.δ_natural_left`/`δ_natural_right` (or
`LaxMonoidal.μ_natural_left/right`) of the SAME monoidal functor already used for the sibling square
S2 — read `Mathlib/CategoryTheory/Monoidal/Functor.lean:70-104,246-286`, then make
`sheafifyTensorUnitIso` literally the functor's `δ`/`μ`. Each lemma whiskers on one side only,
against one `μ`/`δ`, so both the two-instance crossing AND the `tensorHom_def` expansion vanish.
The deeper warrant is `Localization.Monoidal` (`…/Localization/Monoidal/Basic.lean:184-201`): Mathlib's
own "sheafification is monoidal" reads these squares off `NatTrans.naturality_app` of a bifunctor
iso on a single-instance type synonym — it never hand-bridges two whisker instances. Land it together
with the eager `restrictScalarsId_map` strip (Analogue 3) so no `erw`/`whnf` on `restrictScalars (𝟙)`
is ever reached. First file to touch: `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1914-1962`.
Canonical ring-functor spelling to pin everywhere (verdict on the directive's restate question):
`X.presheaf ⋙ forget₂ CommRingCat RingCat` — this is the spelling Mathlib registers the monoidal
instance against (`…/Presheaf/Monoidal.lean:32,104-105`); state `pullbackTensorMap` and its helper
isos on it (not on `Sheaf.val X.ringCatSheaf` / `X.ringCatSheaf.obj`) to also clear the D1′ Square-2
`Sheaf.val`/`.obj` merge.
