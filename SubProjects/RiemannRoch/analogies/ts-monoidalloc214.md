# Lane TS — route (e): instantiate Mathlib's monoidal-localization API (iter-214)

**Status:** the associator/group-law realization is pivoted from the hand-assembled 3-step composite
(routes c/d) to **instantiating Mathlib's abstract monoidal-localization stack**. The decl names
below were **verified against on-disk Mathlib source** during the iter-214 plan phase (the
mathlib-analogist's own tool channel had failed and marked every name `[VERIFY]`, so the planner did
the source reads and confirmed them).

## The verified Mathlib API (on-disk, this project's pinned Mathlib)

1. `PresheafOfModules.monoidalCategory : MonoidalCategory (PresheafOfModules (R ⋙ forget₂ CommRingCat RingCat))`
   — `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean` (instance L125; `monoidalCategoryStruct` L104).
   Tensor = sectionwise relative tensor `(M⊗N)(U) = M(U) ⊗_{R(U)} N(U)`. The base
   `R ⋙ forget₂ CommRingCat RingCat` **equals** the project's `Sheaf.val X.ringCatSheaf` carrier by
   `rfl` (established iter-213). So the **varying-ring presheaf monoidal structure already exists** —
   no project work at the presheaf level.

2. `CategoryTheory.MorphismProperty.IsMonoidal` — `Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean`
   (`class IsMonoidal extends W.IsMultiplicative`, L44). Fields:
   - `whiskerLeft (X : C) {Y₁ Y₂} (g : Y₁ ⟶ Y₂) (hg : W g) : W (X ◁ g)`
   - `whiskerRight ...`
   Lemmas: `whiskerLeft_mem` (L58), `whiskerRight_mem`, constructor `IsMonoidal.mk'` (L50), and
   `(W.inverseImage F).IsMonoidal` (L72, needs `[W.RespectsIso]`).
   **The project's `isLocallyInjective_whiskerLeft_of_W` IS the `whiskerLeft` field.**
   `W_whiskerLeft_of_W` / `W_whiskerRight_of_W` (closed iter-213) are the two fields.

3. `CategoryTheory.Localization.Monoidal.LocalizedMonoidal` (same file, L82+): given
   `[MonoidalCategory C]`, `[W.IsMonoidal]`, `L : C ⥤ D` with `[L.IsLocalization W]`, and
   `ε : L.obj (𝟙_ C) ≅ unit`, `LocalizedMonoidal L W ε` carries a `MonoidalCategory` with ALL
   coherence (associator, unitors, pentagon, triangle, naturalities) derived. **No `MonoidalClosed`
   in the hypothesis chain** (the iter-213 analogist's "gated on MonoidalClosed" was a misattribution
   to the fixed-base `Sheaf.monoidalCategory` route, NOT this localization route).

4. `Mathlib/CategoryTheory/Sites/Point/IsMonoidalW.lean` — **the proof template**:
   `instance [J.HasSheafCompose (forget A)] [HasEnoughPoints J] : (J.W (A := A)).IsMonoidal`, proved
   ```
   .mk' _ (fun f g hf hg ↦ by
     simp only [hP.W_iff (A := A)] at hf hg ⊢   -- W ⟺ stalkwise iso (enough points)
     intro Φ
     rw [Functor.Monoidal.map_tensor]            -- fiber functor is monoidal
     infer_instance)                             -- id ⊗ iso = iso
   ```
   This is for presheaves valued in a **FIXED** monoidal concrete category `A` (`Cᵒᵖ ⥤ A`). It does
   NOT apply to `PresheafOfModules R` (varying ring). It IS the technique to port.
   `Mathlib/CategoryTheory/Sites/Point/Monoidal.lean` supplies the per-point fiber functor
   `Φ.presheafFiber : (Cᵒᵖ ⥤ A) ⥤ A` and proves it `OplaxMonoidal`.

5. **Genuinely Mathlib-absent (the real, only gap):** no monoidal `SheafOfModules`; no
   `PresheafOfModules` stalk/fiber/point infra (only `…/Presheaf/ColimitFunctor.lean`).

## Route (e) — the build (prover, mathlib-build mode)

The end-state monoidal structure on `Scheme.Modules = SheafOfModules X.ringCatSheaf` is
`LocalizedMonoidal` applied to `C = PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)`,
`L = PresheafOfModules.sheafification`, `W = J.W` (sheafification is the localization at the
locally-bijective maps). Coherence (incl. the associator) is then FREE.

The **sole genuinely-new obligation** is `(J.W).IsMonoidal` for the module sheafification localizer.

### Order of attack (highest leverage first)

0. **Make-or-break existence check.** Search Mathlib for any `MorphismProperty.IsMonoidal` instance
   on the `PresheafOfModules` sheafification localizer / `WEqualsLocallyBijective` for modules, or a
   monoidal `SheafOfModules`, or an `IsLocalization` glue that lets `IsMonoidalW` apply. If present
   or one-liner-transportable → instantiate and the obligation collapses to ~0. (Module-sheaf
   localization lives in `Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean`,
   `…/Presheaf/Sheafification.lean`, `…/Presheaf/Sheafify.lean`.)

1. If absent, build `(J.W).IsMonoidal` via the two fields. The closed `W_whiskerLeft/Right_of_W`
   already ARE the fields modulo `isLocallyInjective_whiskerLeft_of_W` (the lone sorry). So the work
   is: discharge that residual, package as the instance, instantiate `LocalizedMonoidal`.

2. The residual, flatness-free (mirror `IsMonoidalW.lean`):
   - **d.1** — stalkwise-iso characterisation of module-level `J.W` on `Opens X`
     (`J.W (toPresheaf f) ↔ ∀ x, IsIso (stalk-map f)`). May transport from existing `Ab`/`Type`
     local-iso ⟺ stalk-iso criteria (`TopCat.Presheaf.app_injective_iff_stalkFunctor_map_injective`,
     `locally_surjective_iff_surjective_on_stalks`) via the underlying-presheaf functor. ~80–150 LOC.
   - **d.2** — stalk ⊗ relative tensor `(A ⊗ᵖ B)_x ≅ A_x ⊗_{R_x} B_x` for `PresheafOfModules`. Build
     from "tensor commutes with the filtered colimit defining the stalk"; check whether the
     `PresheafOfModules` stalk reuses `ModuleCat` filtered-colimit + colimit-tensor lemmas (shrinks
     this). Largest piece, ~150–250 LOC; likely genuinely absent.
   - Assembly (~20 LOC): `g ∈ W` →(d.1)→ `g_x` iso → `id ⊗ g_x` iso →(d.2)→ `(F ◁ g)_x` iso →(d.1)→
     `F ◁ g ∈ W`. **No flatness, no local triviality** (the iter-213 cover/section attempt that
     needed Tor₁ was preserving injectivity ALONE; combined bijectivity routes through the stalk iso
     and never computes a kernel).

3. Then `LocalizedMonoidal` instantiation supersedes the hand-assembled `tensorObj_assoc_iso`; the
   iso-class commutative monoid + `Units` follow as in `CommRing.Pic` (`Units (Skeleton …)`).

## Why this is NOT a 5th substrate pivot

The substrate `tensorObj M N := sheafification (PresheafOfModules.Monoidal.tensorObj M.val N.val)` is
UNCHANGED. Route (e) changes only HOW the associator/coherence is obtained (Mathlib API instead of
hand-assembly) and reframes the residual as the standard `W.IsMonoidal.whiskerLeft` field. This is
the strategy-critic ts214 corrective ("reuse the monoidal-localization stack, don't re-derive").

## Provenance

- strategy-critic ts214: CHALLENGE (wrong altitude) — named the API.
- mathlib-analogist ts-monoidalloc214: synthesis (API frees coherence; residual = `W.IsMonoidal`,
  flatness-free; content is the d.1+d.2 stalk port) — tool channel FAILED, names `[VERIFY]`.
- iter-214 plan: planner did the on-disk Mathlib reads → all decl names above CONFIRMED present.
- supersedes `analogies/ts-monoidal213.md` (routes c/d) for the associator realization; the
  flat-route gap diagnosis there remains valid history.
