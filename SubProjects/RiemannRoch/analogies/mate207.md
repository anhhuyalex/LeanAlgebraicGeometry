# Analogy: the base-change comparison map for `PresheafOfModules.pullback` (the mate of pushforward's monoidal structure)

## Mode
api-alignment

## Slug
mate207

## Iteration
207

## Question
Lane TS needs, project-side, the comparison map
```
(PresheafOfModules.pullback φ.hom).obj (A ⊗ B)
   ⟶ (PresheafOfModules.pullback φ.hom).obj A ⊗ (PresheafOfModules.pullback φ.hom).obj B
```
`pullback φ := (pushforward φ).leftAdjoint` is an abstract left adjoint, so the map
must be constructed as the *mate* of `pushforward φ`'s monoidal structure. The planner
proposed building, project-side, a categorical lemma
`Adjunction.leftAdjointOplaxMonoidal : (F ⊣ G) → [G.LaxMonoidal] → F.OplaxMonoidal`
by dualizing the existing `rightAdjointLaxMonoidal`. Is that the aligned move, is the
dual genuinely absent, does the wiring line up, and is there a cheaper open-immersion route?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean` — `tensorObj_restrict_iso` and the
  whole TS cascade gated on this comparison map.
- Memory `ts-restrict-iso-residual.md` — prior iter-206 framing of the gap.

## Decisions identified

### Decision A: build `Adjunction.leftAdjointOplaxMonoidal` by dualizing `rightAdjointLaxMonoidal`?

- **Mathlib idiom**: **THE LEMMA ALREADY EXISTS.**
  `CategoryTheory.Adjunction.leftAdjointOplaxMonoidal`
  (`Mathlib/CategoryTheory/Monoidal/Functor.lean:1009`):
  ```
  variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [G.LaxMonoidal]
  def leftAdjointOplaxMonoidal : F.OplaxMonoidal
  ```
  with oplax data
  - `η := (adj.homEquiv _ _).symm (ε G)`
  - `δ X Y := (adj.homEquiv _ _).symm ((adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _)`
  and ALL coherence axioms (`δ_natural_left/right`, `oplax_associativity`,
  `oplax_{left,right}_unitality`) proven (lines 1012–1051). Companions:
  `Adjunction.IsMonoidal` instance (1053), `laxMonoidalEquivOplaxMonoidal` (1070),
  and `-isSimp` projection lemmas `leftAdjointOplaxMonoidal_η/_δ`. The dual it mirrors,
  `rightAdjointLaxMonoidal` (Functor.lean:897), is the *other* direction. Both ship in
  the same file; the planner's loogle name-search returned nothing only because of
  loogle name-substring quirks / a rate-limit hit, not absence.
- **Project's current path (proposed)**: re-derive the dual lemma project-side by
  dualizing `rightAdjointLaxMonoidal`'s diagram chase.
- **Gap**: divergent-with-cost (re-inventing a shipped Mathlib lemma). Cost: a ~60-LOC
  oplax-coherence diagram chase that Mathlib already maintains, plus a parallel API that
  won't compose with `Adjunction.IsMonoidal` / `laxMonoidalEquivOplaxMonoidal`.
- **Verdict**: **ALIGN_WITH_MATHLIB** — do NOT build the dual; apply the existing
  `(pullbackPushforwardAdjunction φ).leftAdjointOplaxMonoidal`. Its `δ` IS the required
  comparison map.

### Decision B: where is the genuine project-side gap? `(pushforward φ).LaxMonoidal`.

- **Adjunction wiring — present.** `PresheafOfModules.pullbackPushforwardAdjunction φ :
  pullback φ ⊣ pushforward φ` (`Mathlib/Algebra/Category/ModuleCat/Presheaf/Pullback.lean:50`)
  exists for the SAME `φ` whose `leftAdjoint` is `pullback φ` (`pullback φ :=
  (pushforward φ).leftAdjoint`, Pullback.lean:44). No reindexing mismatch. ✓
- **The hypothesis `leftAdjointOplaxMonoidal` needs is `[(pushforward φ).LaxMonoidal]`,
  and THAT is not in Mathlib as such.** The pushforward is a *composite*:
  `pushforward φ := pushforward₀ F R ⋙ restrictScalars φ`
  (`Mathlib/Algebra/Category/ModuleCat/Presheaf/Pushforward.lean:86`).
  Mathlib's monoidal instance covers only the FIRST factor:
  `(pushforward₀OfCommRingCat F R).Monoidal`
  (`.../Presheaf/PushforwardZeroMonoidal.lean:33`), where
  `pushforward₀OfCommRingCat F R = pushforward₀ F (R ⋙ forget₂ CommRingCat RingCat)`
  (Pushforward.lean:68). There is NO monoidal/lax instance on the
  `restrictScalars φ` factor at the presheaf level, and none on `pushforward φ` itself.
- **The missing piece reduces to `(PresheafOfModules.restrictScalars φ).LaxMonoidal`.**
  Once present, Mathlib's `Functor.LaxMonoidal.comp` (Functor.lean:221) +
  `Functor.Monoidal.toLaxMonoidal` on `pushforward₀` assemble
  `(pushforward₀ F R ⋙ restrictScalars φ).LaxMonoidal`; a `CoreLaxMonoidal`/`inferInstanceAs`
  transport across the `pushforward φ` def-unfolding yields `(pushforward φ).LaxMonoidal`.
- **This presheaf-level lax instance is a sectionwise lift of an EXISTING ModuleCat lemma.**
  `ModuleCat.restrictScalars f` is already `LaxMonoidal`
  (`Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean:102`), built precisely as
  `(extendRestrictScalarsAdj f).rightAdjointLaxMonoidal` — i.e. Mathlib uses the *same*
  mate idiom one level down. The presheaf monoidal structure is sectionwise
  (`(M₁ ⊗ M₂).obj X = M₁.obj X ⊗ M₂.obj X`, Presheaf/Monoidal.lean:46–81) and presheaf
  `restrictScalars φ` is sectionwise `ModuleCat.restrictScalars (φ.app X)`, so the lax
  `μ`/`ε` glue sectionwise from the ModuleCat ones with naturality — a `CoreLaxMonoidal`
  build, NOT a new diagram chase.
- **Setup constraint (must hold in the project's statement):** the PresheafOfModules
  monoidal category requires CommRingCat-valued presheaves of rings (`R ⋙ forget₂ _ _`,
  Presheaf/Monoidal.lean:30), so both `R` and `S` must factor through CommRingCat and `φ`
  must be a morphism of presheaves of *commutative* rings. The project's `φ =
  (Scheme.Hom.toRingCatSheafHom f).hom` is structure-sheaf-valued (commutative), so this
  holds — but the instance must be stated over the CommRingCat-factored rings.
- **Gap**: NEEDS_MATHLIB_GAP_FILL (small, sectionwise) — one presheaf-level lax-monoidal
  instance for `restrictScalars`, mirroring an existing ModuleCat lemma.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** for `(PresheafOfModules.restrictScalars φ).LaxMonoidal`;
  everything downstream (`comp`, the mate, the δ map) is ALIGN_WITH_MATHLIB / free.

### Decision C: cheaper concrete open-immersion restriction route? (planner Q4)

- Searched `Mathlib/.../SheafOfModules/*` and the ModuleCat tree for a concrete
  monoidal "restrict along an open immersion" / `Scheme.Modules.restrict` functor:
  **none found** (no `SheafOfModules` pullback/monoidal file; no `IsOpenImmersion`-keyed
  monoidal restriction in `Algebra/Category/ModuleCat`). Restriction to an open in this
  project still goes through the abstract `PresheafOfModules.pullback`.
- Since `leftAdjointOplaxMonoidal` already exists, the abstract route is now cheap (one
  sectionwise lax instance away), so there is no incentive to special-case open immersions.
- **Verdict**: **PROCEED** with the abstract route; no concrete shortcut exists or is needed.

## Recommendation
Abandon the plan to build a `leftAdjointOplaxMonoidal` dual — it already ships in Mathlib
(`Functor.lean:1009`). The comparison map is literally
`Functor.OplaxMonoidal.δ (F := pullback φ)` once you write
`letI := (pullbackPushforwardAdjunction φ).leftAdjointOplaxMonoidal`. The ONE genuine
project-side obligation is `(pushforward φ).LaxMonoidal`, which is NOT shipped because
`pushforward φ = pushforward₀ F R ⋙ restrictScalars φ` and only the `pushforward₀` factor
is monoidal in Mathlib. Provide `(PresheafOfModules.restrictScalars φ).LaxMonoidal` —
a sectionwise lift of the existing `ModuleCat.restrictScalars` lax-monoidal lemma
(Monoidal/Adjunction.lean:102), assembled as a `CoreLaxMonoidal` from the sectionwise
`ModuleCat.restrictScalars (φ.app X)` data — then let `Functor.LaxMonoidal.comp` +
a defeq transport deliver `(pushforward φ).LaxMonoidal`. Estimated envelope: ~40–90 LOC
for the presheaf-level lax instance + ~10 LOC of plumbing (comp + transport + extract δ),
all over CommRingCat-factored presheaves of rings. This is a single small instance, not
a multi-file categorical build.
</content>
</invoke>
