# Analogy: scope of "build functor-level monoidality of the change-of-rings presheaf pullback"

## Mode
api-alignment

## Slug
pullback-monoidal-scope

## Iteration
056

## Question
To unblock S3/S4a (dual base-change naturality) and S4b-inner (pullback-world left-unitor
coherence), do we need to BUILD `Functor.Monoidal`/`OplaxMonoidal` on the change-of-rings presheaf
pullback? What is the minimal structure, the field shape, the pentagon cost, the cheapest path, and
does it need transport through sheafification?

## TL;DR — the premise is STALE. The instance already exists.
`PresheafOfModules.pullback φ` is **already registered `OplaxMonoidal`**, sorry-free, at
`TensorObjSubstrate.lean:1115` (`presheafPullbackOplaxMonoidal`), via Mathlib's
`Adjunction.leftAdjointOplaxMonoidal` (`Mathlib/CategoryTheory/Monoidal/Functor.lean:1009`)
fed by the project's own `presheafPushforwardLaxMonoidal` (`TensorObjSubstrate.lean:1093`).
`leftAdjointOplaxMonoidal` constructs the **full** `OplaxMonoidal` — `η`, `δ`, `δ_natural_left/right`,
`oplax_associativity` (pentagon), `oplax_left_unitality`, `oplax_right_unitality` — all for free as
the mate of the lax structure on `pushforward`. The left-unitor coherence is therefore already a
theorem: `Functor.OplaxMonoidal.left_unitality_hom (PresheafOfModules.pullback φ') (𝟙_ _)`. It is
**already consumed in the codebase**, sorry-free, at `TensorObjSubstrate.lean:1346`
(`isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta`).

So: do **not** build a monoidal instance. The S4b-inner residual is NOT "missing monoidality" — it is
the **sheafification-seam transport** of an already-available presheaf coherence to the sheaf-level
maps `pullbackTensorMap`/`pullbackUnitIso` (the B1 idiom). And the dual sorries S3/S4a are
**not addressed by monoidality at all** — the dual is internal-hom, and Mathlib has no oplax/closed
dual-preservation; they remain bespoke squares "same depth as S2".

The s4b-unitor.md (iter-055) "instance is absent" claim was scoped to a Mathlib loogle (which does
not see project-local instances) and to the *bundled sheaf* functor `restrictFunctor j`; it missed
the presheaf-level instance and is hereby corrected.

## Answers to the five directive questions

### Q1 — minimal structure for (a) left-unitor and (b) dual preservation
- **(a) left-unitor coherence**: needs only `OplaxMonoidal` (specifically the `oplax_left_unitality`
  field; hom-form `Functor.OplaxMonoidal.left_unitality_hom` [verified `Functor.lean:291`]). The
  **pentagon is NOT required** for this lemma — `left_unitality_hom`'s proof uses only
  `left_unitality`, not `associativity`. And it is **already provided** by the existing instance.
- **(b) dual preservation `F(Mᵛ) ≅ (FM)ᵛ`**: Mathlib has **no general (op)lax/strong
  "monoidal functor preserves duals"**. The only functor→dual decls are:
  - `CategoryTheory.ExactPairing.ofFaithful` / `.ofFullyFaithful`
    [verified `Monoidal/Rigid/OfEquivalence.lean:28,47`] — requires the **full** `[F.Monoidal]`
    (pentagon included; uses `Functor.Monoidal.map_whiskerLeft/Right`, `μ`) **plus `[F.Faithful]`**,
    and runs the **wrong (reflect) direction**: it builds `ExactPairing X Y` in the source from
    `ExactPairing (FX) (FY)` in the target.
  - `CategoryTheory.hasRightDualOfEquivalence` [verified `OfEquivalence.lean:74`] — requires
    `[F.Monoidal]` **and `[F.IsEquivalence]`** + an adjunction.
  Neither matches `f^*` (a pullback along an open immersion is not faithful-as-stated nor an
  equivalence). So full monoidality buys you (b) **not at all**. There is also no `Functor.Closed`
  internal-hom-preservation API that yields the project's `ℋom(-,𝒪)` dual.
  **Verdict (b): NEEDS_MATHLIB_GAP_FILL — keep the bespoke internal-hom route.**

### Q2 — field shape of the OplaxMonoidal instance (and what the project already has)
`Functor.OplaxMonoidal` fields [verified `Functor.lean:241-266`]:
| Field | Status | Project artifact |
|---|---|---|
| `η : F.obj 𝟙_ ⟶ 𝟙_` | **DONE (free)** | mate `leftAdjointOplaxMonoidal_η`; sheafified = `pullbackUnitIso`/`pullbackObjUnitToUnit` |
| `δ X Y : F.obj (X⊗Y) ⟶ F.obj X ⊗ F.obj Y` | **DONE (free)** | mate `leftAdjointOplaxMonoidal_δ`; sheafified = `pullbackTensorMap` |
| `δ_natural_left`, `δ_natural_right` | **DONE (free)** | (sheaf shadow: `pullbackTensorMap_natural` @1959) |
| `oplax_associativity` (pentagon) | **DONE (free)** | — (mate; never hand-built) |
| `oplax_left_unitality` | **DONE (free)** | — (this is the S4b coherence) |
| `oplax_right_unitality` | **DONE (free)** | — |
Canonical doctrine: extension-of-scalars `S ⊗_R -` is the LEFT adjoint, so its native structure is
**oplax** with cotensorator `δ` (matches the project's `pullbackTensorMap` direction). `OplaxMonoidal`
(not `LaxMonoidal`) is the right class, and it is already installed. **Nothing is NEW at presheaf
level.**

### Q3 — pentagon cost
**Zero.** The `oplax_associativity` field is discharged by `leftAdjointOplaxMonoidal` from the mate
calculus; it is never an independent obligation. (Had it been hand-built against
`PresheafOfModules.monoidalCategoryStruct.associator` it would be ~150-400 LOC — but it isn't needed.)

### Q4 — scope recommendation
**Do NOT build a `Functor.Monoidal` instance; build TWO targeted, bespoke cones, both skipping the
pentagon.** Rationale:
- The presheaf `OplaxMonoidal` instance + `left_unitality_hom` already exist; the S4b residual is a
  **sheaf-transport bridge**, not an instance.
- A *strong* `Functor.Monoidal` upgrade is in fact **impossible globally**: `δ` is not iso for
  general modules (the `Γ(ℙ¹,𝒪(1))=0` obstruction, noted `TensorObjSubstrate.lean:1155`); iso-ness
  holds only on line bundles via the chart-chase. So `Monoidal.ofOplaxMonoidal` cannot fire globally.
- Even a (hypothetical) strong instance would not touch S3/S4a (duals are internal-hom; see Q1b).

  | Path | LOC | Risk | Closes |
  |---|---|---|---|
  | Full `Functor.Monoidal` instance | n/a (false globally) + ∞ | — | nothing extra |
  | **Cone A: sheaf-transport of `left_unitality_hom`** | ~60-120 | low-med | S4b-inner (1200) → S4b (1206) |
  | **Cone B: bespoke dual base-change naturality** | ~150-300 | med-high | S3 (1099) + S4a (1123) |
  Closing 1099/1123/1200 then closes the terminal cocycle `trivialisation_restrict_compat` (1373) by
  the telescope already scaffolded there.

### Q5 — sheafification layer
**Yes, the work IS the sheafification transport — that is the whole remaining content of Cone A.**
The monoidal structure lives at the **presheaf** level (`PresheafOfModules.pullback φ'`). The
squares live at the **sheaf** level (`Scheme.Modules`), where the maps are `pullbackTensorMap`
(= sheafified `δ`) and `pullbackUnitIso` (= sheafified `η`). You do NOT transport the whole monoidal
structure through `sheafification`; you transport the single `left_unitality_hom` *equation* via the
already-built seam devices: `pullbackValIso` (@1165), `SheafOfModules.sheafificationCompPullback`,
`sheafifyTensorUnitIso`, and `sheafificationAdjunction.counit` naturality — exactly the B1 toolkit
that proved S2 and powers `isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta`. The bespoke squares
already own the outer sheafify+counit seam (S2/S4c precedent), so you only need the presheaf-level
coherence (have it) + the δ/η mate-identifications (Cone A sub-lemmas 1-2).

## Decisions identified

### Decision: build vs. reuse the pullback monoidal structure
- **Mathlib idiom**: `Adjunction.leftAdjointOplaxMonoidal` [verified `Functor.lean:1009`] — a lax
  right adjoint ⇒ oplax left adjoint, full structure. Why: mate calculus discharges all coherences.
- **Project's path**: already aligned — instance at `TensorObjSubstrate.lean:1115`.
- **Gap**: identical (already done). The directive proposed to re-build it.
- **Verdict**: PROCEED (reuse the existing instance; the directive's "build it" is unnecessary).

### Decision: route the dual via monoidality/rigid API vs. bespoke internal-hom
- **Mathlib idiom**: `ExactPairing.ofFaithful` / `hasRightDualOfEquivalence` — wrong direction /
  wrong hypotheses (Q1b), and require full `Monoidal` (pentagon).
- **Project's path**: bespoke `dual_restrict_iso` (`DualInverse.lean:166`) + `presheafDualUnitIso`
  (`:218`) + proven `presheafDualUnitIso_naturality`.
- **Gap**: divergent-intentionally — Mathlib's rigid API is inapplicable to `f^*`.
- **Verdict**: DIVERGE_INTENTIONALLY / NEEDS_MATHLIB_GAP_FILL — keep bespoke; do not chase the
  rigid API.

## Concrete decomposition (seeds a prover lane on `TensorObjSubstrate.lean`)

### Cone A — S4b-inner via existing presheaf left-unitality (do FIRST; cheapest, highest-confidence)
Pattern oracle: `isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta` (@1315) already does 80% of this
(it factors `a_Y.map (δ F 𝟙_ 𝟙_)` through `left_unitality_hom F`).

1. **η mate-identification** (unit-side analog of `pullbackObjUnitToUnit_comp`):
   ```lean
   lemma pullbackUnitIso_eq_sheafify_eta {X Y : Scheme.{u}} (f : Y ⟶ X) :
       (pullbackUnitIso f).hom
         = (pullbackValIso f (SheafOfModules.unit X.ringCatSheaf)).inv
             ≫ a_Y.map (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ'))
             ≫ (sheafifyTensorUnitIso …).hom   -- 𝟙_-seam closer
   ```
   (the sheafification-mate identification flagged at `:1361-1363`).
2. **δ mate-identification** (essentially the definition unfolding of `pullbackTensorMap`, @1182-1189):
   ```lean
   lemma pullbackTensorMap_eq_sheafify_delta {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) :
       pullbackTensorMap f M N
         = (pullbackValIso f (tensorObj M N)).inv
             ≫ a_Y.map (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val)
             ≫ (tensorObj-of-pullbackValIso bridge) -- δ codomain seam
   ```
3. **sheaf-level left unitality** (the actual S4b-inner content; apply `a_Y.mapIso` to
   `left_unitality_hom F` then rewrite by 1,2 + counit naturality):
   ```lean
   lemma pullbackTensorMap_left_unitality {X Y : Scheme.{u}} (f : Y ⟶ X) :
       pullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf) M
         ≫ tensorObjIsoOfIso (pullbackUnitIso f) (Iso.refl _) |>.hom
         ≫ (tensorObj_left_unitor _).hom
       = (Scheme.Modules.pullback f).map (tensorObj_left_unitor M).hom   -- F(λ_)
   ```
4. Close `tensorObj_unit_iso_restrict_compat_inner` (`TensorObjInverse.lean:1200`) by combining 3 at
   `M = 𝒪_U` with the `restrictFunctorIsoPullback`/`restrictFunctor j ≅ pullback j` reduction already
   begun there (the two `rw`s at `:1188-1190` are already in place; the residual `sorry` at `:1200`
   becomes an application of `pullbackTensorMap_left_unitality` + iso-algebra).

### Cone B — S3/S4a dual base-change naturality (bespoke; NOT monoidality)
Parallel to Bridge B1 but on the dual structural iso. Oracle: `presheafDualUnitIso_naturality`
(`DualInverse.lean:224`, proven against unit automorphisms) — generalize the target morphism from a
unit automorphism to the immersion `j`.

5. **presheaf dual comparison naturality in the immersion**:
   ```lean
   lemma presheafDual_pullback_restrict_natural {X : Scheme} {U V} (j : V ⟶ U)
       [IsOpenImmersion j] (hjι : j ≫ U.ι = V.ι) (M) :
       -- naturality of `(pullback φ).obj (dual M.val) ≅ dual ((pullback φ).obj M.val)` (Step-4 iso
       --  inside `dual_restrict_iso`) against j; the immersion analog of presheafDualUnitIso_naturality
   ```
6. **S3** `dual_restrict_iso_restrict_compat` (`TensorObjInverse.lean:1088`): chart-chase telescope
   of `dual_restrict_iso` (Step1-4) against `j`, threading `restrictCompReindex`/`dualIsoOfIso_trans`
   + sub-lemma 5 + the sheafification-seam closers (same as S2).
7. **S4a** `dual_unit_iso_restrict_compat` (`:1113`): `dual_unit_iso = sheafification.mapIso
   presheafDualUnitIso ≪≫ counit`; combine the immersion-naturality of `presheafDualUnitIso`
   (sub-lemma 5 specialized to the unit) with sub-lemma 6 (`dual_restrict_iso` naturality) + counit
   naturality.

### Then: terminal cocycle
8. `trivialisation_restrict_compat` (`:1304`, sorry @1373) closes by the telescope already written in
   its body once S2/S3/S4a/S4b/S4c are all available.

## Recommendation
Reuse the existing presheaf `OplaxMonoidal (PresheafOfModules.pullback φ)` instance and its free
`left_unitality_hom`; do **not** build a `Functor.Monoidal` instance (impossible globally — `δ` not
iso for general modules — and useless for the duals). Land **Cone A** first (S4b-inner): three
sheaf-transport bridge lemmas in the B1 idiom, with `isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta`
as the working template — low risk, ~60-120 LOC. Then **Cone B** (S3/S4a): two bespoke internal-hom
base-change naturality squares, generalizing `presheafDualUnitIso_naturality` from unit automorphisms
to the immersion `j` — the genuine remaining math, ~150-300 LOC, no monoidal shortcut. Both feed the
already-scaffolded terminal cocycle telescope at `trivialisation_restrict_compat`.
