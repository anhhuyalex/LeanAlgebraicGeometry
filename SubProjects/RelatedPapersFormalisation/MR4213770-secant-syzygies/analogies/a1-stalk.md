# Analogy: stalk-of-sheafification iso for module-valued presheaves (node-4 (a1)/(a2))

## Mode
api-alignment

## Slug
a1-stalk

## Iteration
021

## Question
Node-4 (a1) `lem:tilde_pullback_stalk_sheafificationStalk`: for a presheaf of modules `P`
over a sheaf of rings on `Spec R_f`, does the sheafification unit `P → sheafify P` induce an
ISO on every stalk — i.e. is `(SheafOfModules.pullback q_f).obj (tilde M)` (= sheafification
of the presheaf pullback, via `SheafOfModules.pullbackIso`) stalkwise-iso to the *presheaf*
pullback? Sibling (a2) then identifies that presheaf-pullback stalk with `(tilde M)`'s stalk at
`q_f(x)` via `TopCat.Presheaf.stalkPullbackIso`.

## Project artifact(s)
- `Foundations.lean:53` — `Modules.isIso_iff_isIso_stalkFunctor_map`: the project already reduces
  module-sheaf isos to **Ab-level** stalk isos via `Scheme.Modules.toPresheaf X`
  (`TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso` + `isIso_iff_of_reflects_iso … toPresheaf`).
  This is the decisive context: ALL stalk work is at `AddCommGrpCat`, never per-step ModuleCat.
- `Foundations.lean:1564` — `tildePullbackComparison` (α_M), node 3.
- `Foundations.lean:1590` — `tildePullbackComparison_stalk_localizationTransitivity` (c), landed.
- `Foundations.lean:1573–1578` — node-4 decomposition header; (a1)/(a2) marked "gated on a genuine gap".
  **This memo overturns that: it is NOT a genuine gap.**

## Decisions identified

### Decision: (a1) stalk-of-sheafification — build new vs. reuse Mathlib

- **Mathlib idiom**: `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`
  (`Mathlib/Topology/Sheaves/Sheafify.lean:137`). Signature (verified via loogle, v4.30.0):
  ```
  {X : TopCat} (p₀ : ↑X) (C : Type u) [Category C] [HasColimits C] [HasTerminal C]
    (𝓕 : TopCat.Presheaf C X) [HasWeakSheafify (Opens.grothendieckTopology ↑X) C] :
    IsIso ((TopCat.Presheaf.stalkFunctor C p₀).map (toSheafify (Opens.grothendieckTopology ↑X) 𝓕))
  ```
  This is the **general-concrete-category** version (NOT just `Type`/`Ab`). Proof in Mathlib:
  `Adjunction.isIso_map_unit_of_isLeftAdjoint_comp (sheafificationAdjunction _ C) (skyscraperSheafForgetAdjunction p₀)`
  — i.e. `stalkFunctor = (sheafification ⋙ —) ` post-composed with a left adjoint, so it inverts the
  sheafification unit. Instantiate at **`C = AddCommGrpCat`** (has `HasColimits`, `HasTerminal`,
  `HasWeakSheafify (Opens.grothendieckTopology X) AddCommGrpCat`).
- **The linchpin glue (underlying-Ab of the *module* sheafification unit IS `toSheafify`)**:
  `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app`
  (`Mathlib/Algebra/Category/ModuleCat/Presheaf/Sheafification.lean:143`), proved by **`rfl`**:
  ```
  (toPresheaf _).map ((sheafificationAdjunction α).unit.app M₀) = toSheafify J M₀.presheaf
  ```
- **Packaging glue**: `SheafOfModules.pullbackIso`
  (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean`):
  `SheafOfModules.pullback φ ≅ (SheafOfModules.forget S) ⋙ (PresheafOfModules.pullback φ.hom) ⋙
   (PresheafOfModules.sheafification (𝟙 R.obj))`. So the pullback **sheaf** is literally the
  sheafification of the presheaf pullback; the comparison map is the sheafification unit (α = 𝟙).
- **Project's current path**: deferred as "genuine infrastructure gap" (Foundations.lean:1577).
- **Gap**: **divergent-and-wrong (deferral is unnecessary)** — Mathlib already has the exact
  general-C lemma. No new stalk-of-sheafification lemma is needed.
- **Verdict**: **ALIGN_WITH_MATHLIB** — reuse `stalkFunctor_map_unit_toSheafify_isIso`; do NOT build
  a bespoke module sheafify-stalk iso.

### Decision: (a2) presheaf-pullback-stalk ≅ tilde-stalk at q_f(x)

- **Mathlib idiom**: `TopCat.Presheaf.stalkPullbackIso`
  (`Mathlib/Topology/Sheaves/Stalks.lean:321`), general-C:
  `F.stalk (f x) ≅ ((TopCat.Presheaf.pullback C f).obj F).stalk x`. Instantiate `C = AddCommGrpCat`,
  `f = q_f.base`, `F = (toPresheaf … tilde M)`.
- **Remaining bridge (the real (a2) work)**: identify the underlying-Ab presheaf of
  `(PresheafOfModules.pullback φ.hom).obj (tilde M)` with `(TopCat.Presheaf.pullback AddCommGrpCat q_f.base).obj (toPresheaf (tilde M))`
  — i.e. that the module presheaf-pullback's underlying Ab presheaf is the topological inverse image.
  Mathematically true (both are the left Kan extension along `Opens.map`); the Lean identification
  is NOT a single `rfl` and is the one genuinely new bridge lemma for (a2).
- **Module-structure transport**: **NOT a blocker.** Because the project does every stalk argument
  at the Ab level (`Scheme.Modules.toPresheaf` reflects isos, Foundations.lean:53), the topological
  `stalkPullbackIso` (an Ab iso) is exactly what is consumed; linearity over the structure-sheaf
  stalk is recovered only at the END via `toPresheaf`-reflects-isos, never per node.
- **Gap**: divergent-with-cost (one bridge lemma).
- **Verdict**: **ALIGN_WITH_MATHLIB** for the anchor (`stalkPullbackIso`); **NEEDS_MATHLIB_GAP_FILL**
  only for the small `toPresheaf ∘ module-pullback ≅ TopCat-inverse-image ∘ toPresheaf` bridge.

## Recommendation

(a1) is **assemblable now**, ~3 steps, no new infrastructure:

1. State (a1) as an **Ab-level** stalk iso (match the project's existing
   `Modules.isIso_iff_isIso_stalkFunctor_map` style): the goal is
   `IsIso ((stalkFunctor AddCommGrpCat x).map ((toPresheaf _).map (sheafificationAdjunction (𝟙 _)).unit.app P))`,
   where `P` is the presheaf pullback `(PresheafOfModules.pullback φ.hom).obj (tilde M)` (and
   `SheafOfModules.pullbackIso` puts `(SheafOfModules.pullback q_f).obj (tilde M)` into this shape).
2. Rewrite the underlying-Ab unit map to `toSheafify (Opens.grothendieckTopology (Spec R_f)) P.presheaf`
   via `PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app` (`rfl`).
3. Close with `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso (C := AddCommGrpCat) …`.

(a2): anchor on `TopCat.Presheaf.stalkPullbackIso (C := AddCommGrpCat)`; build the single bridge
lemma `toPresheaf (PresheafOfModules.pullback φ.hom).obj F ≅ (TopCat.Presheaf.pullback AddCommGrpCat q_f.base).obj (toPresheaf F)`.
Do the whole node-4 stalk argument in `AddCommGrpCat`; upgrade α_M to a `SheafOfModules` iso at the
end via the project's `Modules.isIso_iff_isIso_stalkFunctor_map` (toPresheaf reflects isos) — this is
why the module-structure-on-stalk worry never materializes.
