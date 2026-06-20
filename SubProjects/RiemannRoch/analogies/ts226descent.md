# Analogy: SheafOfModules morphism descent — does it exist in Mathlib, and does the descent re-route of `exists_tensorObj_inverse` / `tensorObj_assoc_iso` avoid the abandoned "d.2" stalk-⊗ gap?

## Mode
api-alignment

## Slug
ts226descent

## Iteration
226

## Question
For the by-hand `Pic X` group over the varying `𝒪_X`: (A) does Mathlib give morphism
gluing/descent for `SheafOfModules` (compatible local homs ⇒ unique global hom)? (B) a
"locally-iso ⇒ iso" criterion for sheaf-of-module morphisms? (C) dual/internal-hom commuting
with open-immersion restriction? (D) does building `exists_tensorObj_inverse` and
`tensorObj_assoc_iso` via A+B+C genuinely AVOID the abandoned stalk-⊗ commutation ("d.2"), or
does it secretly re-require a stalkwise/filtered-colimit-⊗ statement?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1822` — `tensorObj_restrict_iso` (CLOSED, d.2-free).
- `:1715` — `tensorObj_assoc_iso` (built through the OPEN `isLocallyInjective_whiskerLeft_of_W`, route (d)).
- `:1955` — `exists_tensorObj_inverse` (sorry; `Linv := dual L` now nameable since the dual landed iter-225).
- `:1912` — `tensorObj_isLocallyTrivial` (CLOSED — the template the descent route mirrors).

## Decisions identified

### Decision A: morphism gluing/descent for `SheafOfModules`

- **Mathlib idiom**: morphism gluing for `Sheaf J A` is FULLY present in
  `Mathlib.CategoryTheory.Sites.SheafHom`:
  - `CategoryTheory.presheafHom F G : Cᵒᵖ ⥤ Type` (SheafHom.lean:46) — the hom presheaf
    `U ↦ (F|_{Over U} ⟶ G|_{Over U})`.
  - `CategoryTheory.Presheaf.IsSheaf.hom : IsSheaf J G → IsSheaf J (presheafHom F G)`
    (SheafHom.lean:207) — **the hom presheaf into a sheaf is itself a sheaf** (this is the
    descent statement: morphisms are determined locally AND a compatible family glues).
  - `CategoryTheory.sheafHom F G : Sheaf J (Type _)` (SheafHom.lean:236) and
    `sheafHomSectionsEquiv : (sheafHom F G).1.sections ≃ (F ⟶ G)` (SheafHom.lean:241).
  - Separatedness companion: `CategoryTheory.eq_of_zeroHypercover_target`
    (MorphismProperty/Local.lean:189) — two morphisms equal on a cover are equal, given
    `(isomorphisms C).IsLocalAtTarget J`.
  Closest OBJECT-level descent in the module world: `SheafOfModules.QuasicoherentData.bind`
  (Sheaf/Quasicoherent.lean:358) glues quasicoherent *data* across `J.CoversTop` — proof that
  the descent machinery exists for module sheaves, but only for the QC-presentation structure,
  not arbitrary objects from a cocycle.
- **Project's path**: the blueprint wants compatible local isos through `tensorObj_restrict_iso`
  glued to a global morphism. There is **no `SheafOfModules R`-level packaging** of "hom is a
  sheaf"/amalgamation — `sheafHom` is for fixed-`A` `Sheaf J A`, not modules over a varying
  sheaf of rings.
- **Gap**: divergent-with-cost (small bridge). The genuine primitive (`Presheaf.IsSheaf.hom`)
  exists; the project must (i) forget to the underlying ab-sheaf via
  `SheafOfModules.toSheaf R` (Sheaf.lean:89, faithful + additive), glue the additive morphism
  with `sheafHom`/`sheafHomSectionsEquiv`, then (ii) promote to `𝒪_X`-linear via
  `PresheafOfModules.homMk` — R-linearity `f(r•m)=r•f(m)` is a sectionwise equation, so it
  holds globally once it holds on the cover (M separated). Est. ~30–60 LOC bridge.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (the SheafOfModules-level wrapper), but built directly on
  the existing `Sites.SheafHom` primitive — NOT a from-scratch descent build.

### Decision B: locally-iso ⇒ iso for sheaf-of-module morphisms

- **Mathlib idiom**: `CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`
  (Sites/LocallyBijective.lean:84): for `f : F ⟶ G` of `Sheaf J A`,
  `IsLocallyInjective f ∧ IsLocallySurjective f ↔ IsIso f`, given
  `[(forget A).ReflectsIsomorphisms]` + `[J.HasSheafCompose (forget A)]`.
  SheafOfModules side is already wired:
  - `SheafOfModules`/`PresheafOfModules.IsLocallyInjective`/`IsLocallySurjective` are DEFINED
    (Sheaf.lean:190,195) as the underlying ab-presheaf morphism being locally inj/surj.
  - `SheafOfModules.toSheaf R` reflects isos — used live as
    `isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf R)` (Sheaf/Localization.lean:44).
  - `(forget R).ReflectsIsomorphisms` (Sheaf.lean:80).
  For `J = Opens.grothendieckTopology X`, `[J.WEqualsLocallyBijective AddCommGrp]` +
  `HasSheafify` hold (the project already uses `W`-machinery on this site).
- **Project's path**: "iso is local" is already invoked informally; the right tool is the chain
  `IsIso f  ⇔  IsIso (toSheaf.map f)  ⇔  locally bijective`.
- **Gap**: divergent-equivalent + one connector. Missing piece: a lemma turning the project's
  "`M.restrict f` iso on an open cover" (restriction along an open *immersion*, base ring
  changes to `𝒪_U`) into the site-level `IsLocallyInjective J ∧ IsLocallySurjective J` on
  `Opens X`. Tractable (open-immersion restriction = `Over U` restriction of the ab-sheaf).
- **Verdict**: ALIGN_WITH_MATHLIB — use `isLocallyBijective_iff_isIso` ∘ `toSheaf`-reflects;
  build only the restrict→locally-bijective connector.

### Decision C: dual / internal-hom commuting with open-immersion restriction

- **Mathlib idiom**: NONE directly — Mathlib has no internal-hom/dual/`ihom` for
  `PresheafOfModules`/`SheafOfModules` (the project's presheaf `dual` is bespoke), hence no
  "`(dual M)|_U ≅ dual(M|_U)`". BUT the enabling ingredient is present and is exactly the H2
  half of the closed `tensorObj_restrict_iso`: `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`
  (ChangeOfRings.lean:285) — restrictScalars along a ring **iso** is an **equivalence**
  (`isEquivalence_functor` :303), additive (:325) and linear (:335). Open-immersion restriction
  is sectionwise such a ring iso (`f.appIso`), so its `restrictScalars` is an equivalence and
  therefore commutes with `Hom(-,-)`/dual up to iso.
- **Project's path**: backs `dual_isLocallyTrivial`; build `(dual M)|_U ≅ dual_{𝒪_U}(M|_U)` by
  the SAME H1∘H2 recipe as `tensorObj_restrict_iso` (`pushforwardPushforwardAdj` /
  `pullbackPushforwardAdjunction` + `restrictScalarsEquivalenceOfRingEquiv` carrying Hom).
- **Gap**: divergent-with-cost (bespoke, but the pieces are in hand and the ⊗ analogue is closed).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL — low/medium, mirror `tensorObj_restrict_iso`.

### Decision D: does the A+B+C route avoid the abandoned "d.2" stalk-⊗ gap?

- **Mathlib idiom**: n/a — this is a route verdict.
- **Finding**: **YES, the descent route avoids d.2 and does not secretly re-require stalk-⊗.**
  - `tensorObj_restrict_iso` is CLOSED and **d.2-free** by construction: it goes through the
    pushforward/pullback adjunction (`pushforwardPushforwardAdj` + `leftAdjointUniq`) and the
    strong-monoidality of `restrictScalars` along the open-immersion ring iso — **no stalks,
    no filtered-colimit-⊗, no whiskered-unit localizer**.
  - The local isos feeding the associator/inverse are assembled from `tensorObj_restrict_iso`
    + `tensorObj_unit_iso` + `tensorObjIsoOfIso` on trivialising opens — the EXACT pattern of
    the already-CLOSED `tensorObj_isLocallyTrivial` (`:1912`), which touches no stalk.
  - A (gluing) and B (locally-iso⇒iso) are statements about MORPHISMS of (ab-)sheaves; neither
    computes a tensor stalk. The d.2 gap (`(F ⊗ᵖ M)_x ≅ F_x ⊗_{R_x} M_x` over the varying ring)
    is never invoked.
  - Contrast: the CURRENT `tensorObj_assoc_iso` (route (d)) needs
    `isLocallyInjective_whiskerLeft_of_W` precisely because it manipulates the *iterated
    sheafification* `sheafify(η ▷ P)` directly — that whiskered-unit-stays-in-`W` step is what
    forces d.2. The descent route never forms that morphism; it builds the global iso from
    local trivialising data instead. **So the canonical-presheaf-construction route (associator
    as `sheafify(presheaf-associator)`, eval as `sheafify(internalHomEval)`) does NOT help — it
    re-hits the same `M ◁ η`/`η ▷ P` whiskering = d.2; only the gluing route escapes.**
- **Residual risk to flag (NOT d.2)**: the local isos must AGREE ON OVERLAPS (cocycle
  condition) to glue. For the associator this is the standard line-bundle cocycle bookkeeping
  on trivialising opens (`O⊗O⊗O ≅ O` associativity intertwining the transition units); for the
  inverse-eval it is `O⊗O ≅ O` (left unitor) intertwining `g_{ij}·g_{ij}⁻¹`. This is real but
  bounded work of a DIFFERENT, tractable kind than the abandoned ~300–500 LOC stalk-⊗ build.
- **Verdict**: route CONFIRMED (PROCEED) — avoids d.2; cost moves to A+B+C bridges + cocycle
  check, all built on existing Mathlib (`Sites.SheafHom`, `isLocallyBijective_iff_isIso`,
  `restrictScalarsEquivalenceOfRingEquiv`).

## Recommendation

Commit to the descent re-route; it genuinely retires d.2. Build in this order, each on an
existing Mathlib primitive:
1. **B-connector** (cheapest, unblocks everything): `f : M ⟶ N` of `X.Modules` iso when iso on
   an open cover, via `Sheaf.isLocallyBijective_iff_isIso` ∘ `SheafOfModules.toSheaf`-reflects
   (Sheaf.lean:80/89, Localization.lean:44). One connector: restrict-iso-on-cover ⇒ locally
   bijective on `Opens.grothendieckTopology X`.
2. **A-bridge**: SheafOfModules morphism amalgamation = glue the underlying ab-morphism with
   `CategoryTheory.Presheaf.IsSheaf.hom`/`sheafHomSectionsEquiv` (Sites/SheafHom.lean), then
   `PresheafOfModules.homMk` with sectionwise R-linearity.
3. **C**: `(dual M)|_U ≅ dual(M|_U)` by the `tensorObj_restrict_iso` recipe with
   `restrictScalarsEquivalenceOfRingEquiv` (ChangeOfRings.lean:285) for `dual_isLocallyTrivial`.
4. Assemble `tensorObj_assoc_iso` and `exists_tensorObj_inverse` from local trivialising isos
   (mirror `tensorObj_isLocallyTrivial:1912`) + cocycle check + A + B. Then DELETE the vestigial
   `isLocallyInjective_whiskerLeft_of_W` / whiskering-localizer apparatus and the d.2 dependency.

The descent route is the correct call. It is NOT zero-cost (A/C are gap-fills, plus a cocycle
check), but every gap-fill rests on an existing Mathlib primitive and none re-enters d.2.
