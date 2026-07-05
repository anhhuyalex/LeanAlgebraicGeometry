I have gathered all the information needed. Here is the structured report.

---

# Report: Mathlib API for turning an open cover into a glue datum

All paths are under the workspace-shared Mathlib:
`/home/Axel/LeanAlgebraicGeometry-Horizon/.lake-packages/mathlib/Mathlib/`
(This is the Mathlib the `Algebraic-Jacobian-Challenge` project resolves to; its own `.lake/packages/` does not contain mathlib.)

Primary file: `AlgebraicGeometry/Gluing.lean`. The whole file uses `universe v u` (line 60) and lives in `namespace AlgebraicGeometry.Scheme`.

---

## Item 1 — `gluedCover`: the real name is `AlgebraicGeometry.Scheme.Cover.gluedCover`

It is defined in `namespace Cover` (opened at `Gluing.lean:272`), with context
`variable {X : Scheme.{u}} (𝒰 : OpenCover.{u} X)` (`Gluing.lean:274`).
Because `OpenCover X` is definitionally `Cover (precoverage @IsOpenImmersion) X` and `𝒰 : OpenCover X`, dot-notation `𝒰.gluedCover` resolves to `Scheme.Cover.gluedCover`. (The module docstring at line 29 calls it `Scheme.OpenCover.gluedCover`, but there is no such literal declaration — the namespace is `Cover`.)

Exact source (`Gluing.lean:331-346`), fully with field values:

```lean
/-- The glue data associated with an open cover.
The canonical isomorphism `𝒰.gluedCover.glued ⟶ X` is provided by `𝒰.fromGlued`. -/
@[simps]
def gluedCover : Scheme.GlueData.{u} where
  J := 𝒰.I₀
  U := 𝒰.X
  V := fun ⟨x, y⟩ => pullback (𝒰.f x) (𝒰.f y)
  f _ _ := pullback.fst _ _
  f_id _ := inferInstance
  t _ _ := (pullbackSymmetry _ _).hom
  t_id x := by simp
  t' x y z := gluedCoverT' 𝒰 x y z
  t_fac x y z := by apply pullback.hom_ext <;> simp
  -- The `cocycle` field could have been `by tidy` but lean timeouts.
  cocycle x y z := glued_cover_cocycle 𝒰 x y z
  f_open _ := inferInstance
```

So concretely:
- `J = 𝒰.I₀` (the cover's index type).
- `U = 𝒰.X` (the cover's component schemes).
- `V (x,y) = pullback (𝒰.f x) (𝒰.f y)` — YES, the pullback of the two cover maps.
- `f x y = pullback.fst (𝒰.f x) (𝒰.f y)` (the `_ _` are the two cover maps).
- `t x y = (pullbackSymmetry (𝒰.f x) (𝒰.f y)).hom` — YES, `(pullbackSymmetry _ _).hom`.
- `t' x y z = gluedCoverT' 𝒰 x y z` — a helper `def` (`Gluing.lean:277-285`) built from `pullbackRightPullbackFstIso`, `pullbackSymmetry`, and `pullback.map`:

```lean
def gluedCoverT' (x y z : 𝒰.I₀) :
    pullback (pullback.fst (𝒰.f x) (𝒰.f y)) (pullback.fst (𝒰.f x) (𝒰.f z)) ⟶
      pullback (pullback.fst (𝒰.f y) (𝒰.f z)) (pullback.fst (𝒰.f y) (𝒰.f x)) := by
  refine (pullbackRightPullbackFstIso _ _ _).hom ≫ ?_
  refine ?_ ≫ (pullbackSymmetry _ _).hom
  refine ?_ ≫ (pullbackRightPullbackFstIso _ _ _).inv
  refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_
  · simp [pullback.condition]
  · simp
```

`f_id`, `f_open` are `inferInstance` (component maps are open immersions, base change stays open immersion). `@[simps]` generates `gluedCover_J`, `gluedCover_U`, `gluedCover_V`, `gluedCover_f`, `gluedCover_t`, `gluedCover_t'` (e.g. `gluedCover_U` is used at line 402).

The underlying structure `Scheme.GlueData` is (`Gluing.lean:91-94`):
```lean
structure GlueData extends CategoryTheory.GlueData Scheme where
  f_open : ∀ i j, IsOpenImmersion (f i j)
attribute [instance] GlueData.f_open
```
with `abbrev glued : Scheme := 𝖣.glued` (line 158) and `abbrev ι (i : D.J) : D.U i ⟶ D.glued := 𝖣.ι i` (line 162).

---

## Item 2 — `fromGlued` and its `IsIso` instance

`AlgebraicGeometry.Scheme.Cover.fromGlued` (`Gluing.lean:348-355`):
```lean
/-- The canonical morphism from the gluing of an open cover of `X` into `X`.
This is an isomorphism, as witnessed by an `IsIso` instance. -/
def fromGlued : 𝒰.gluedCover.glued ⟶ X := by
  fapply Multicoequalizer.desc
  · exact fun x => 𝒰.f x
  rintro ⟨x, y⟩
  change pullback.fst _ _ ≫ _ = ((pullbackSymmetry _ _).hom ≫ pullback.fst _ _) ≫ _
  simpa using! pullback.condition
```

The `IsIso` witness is an **anonymous** instance (there is NO `isIso_fromGlued` name) (`Gluing.lean:423-429`):
```lean
instance : IsIso 𝒰.fromGlued :=
  let F := Scheme.forgetToLocallyRingedSpace ⋙ LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace
  have : IsIso (F.map (fromGlued 𝒰)) := by
    change IsIso 𝒰.fromGlued.toPshHom
    apply PresheafedSpace.IsOpenImmersion.to_iso
  isIso_of_reflects_iso _ F
```
Supporting anonymous instances: `instance : IsOpenImmersion 𝒰.fromGlued` (line 420), `instance : Epi 𝒰.fromGlued.base` (line 411), and `instance (x …) : IsIso (𝒰.fromGlued.stalkMap x)` (line 382). Also `fromGlued_injective` (361), `isOpenMap_fromGlued` (391), `isOpenEmbedding_fromGlued` (408). To get an actual `≅` you would use `asIso 𝒰.fromGlued` / `inv 𝒰.fromGlued`.

---

## Item 3 — `ι_fromGlued`

`AlgebraicGeometry.Scheme.Cover.ι_fromGlued` (`Gluing.lean:357-359`):
```lean
@[simp, reassoc]
theorem ι_fromGlued (x : 𝒰.I₀) : 𝒰.gluedCover.ι x ≫ 𝒰.fromGlued = 𝒰.f x :=
  Multicoequalizer.π_desc _ _ _ _ _
```
So `𝒰.gluedCover.ι x ≫ 𝒰.fromGlued = 𝒰.f x` exactly. It carries `@[simp, reassoc]` (so `ι_fromGlued_assoc` also exists).

---

## Item 4 — Universe constraints and `Scheme.GlueData` field types

`CategoryTheory.GlueData` (`CategoryTheory/GlueData.lean`): header `universe v u₁ u₂` with `variable (C : Type u₁) [Category.{v} C]`. Fields (`GlueData.lean:51-70`):
```lean
structure GlueData where
  J : Type v
  U : J → C
  V : J × J → C
  f : ∀ i j, V (i, j) ⟶ U i
  f_mono : ∀ i j, Mono (f i j) := by infer_instance
  f_hasPullback : ∀ i j k, HasPullback (f i j) (f i k) := by infer_instance
  f_id : ∀ i, IsIso (f i i) := by infer_instance
  t : ∀ i j, V (i, j) ⟶ V (j, i)
  t_id : ∀ i, t i i = 𝟙 _
  t' : ∀ i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
  t_fac : ∀ i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
  cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _
```

Key point: **`J : Type v` where `v` is the SAME universe as the category's hom-universe `[Category.{v} C]`.** For `Scheme.{u}` (which is `Type (u+1)` and `Category.{u}`), this forces `v = u`, i.e. **the glue-data index type must live in `Type u`, the same universe as the schemes.** Hence `Scheme.GlueData.{u}` (Gluing.lean:98 `variable (D : GlueData.{u})`) has `J : Type u`, and `gluedCover : Scheme.GlueData.{u}` sets `J := 𝒰.I₀` where `𝒰 : OpenCover.{u} X`, so `𝒰.I₀ : Type u`.

- `gluedCover`, `fromGlued`, `IsIso`, and `ι_fromGlued` are all stated for `𝒰 : OpenCover.{u} X` with `X : Scheme.{u}` (index universe = scheme universe). **They DO work for `Scheme.{0}` with cover index in `Type 0`** (take `u = 0`).
- They do NOT directly accept a cover whose index type is in a strictly larger universe. To glue such a cover you must first `ulift` it: this is exactly what `glueMorphisms`/`hom_ext` do — they take `OpenCover.{v} X` for arbitrary `v` and internally use `𝒰.ulift.fromGlued` / `𝒰.ulift.gluedCover` (see lines 442, 453, 465).

Cover-side universe facts: `OpenCover (X : Scheme.{u}) : Type _ := Cover.{v} (precoverage @IsOpenImmersion) X` (`Cover/Open.lean:40`), `Cover K := Precoverage.ZeroHypercover.{v} K` (`Cover/MorphismProperty.lean:50`). `ZeroHypercover J S extends PreZeroHypercover.{w} S` with `mem₀ : … ∈ J S` (`Sites/Hypercover/Zero.lean:646-647`), and `PreZeroHypercover` (same file, 35-41) has fields `I₀ : Type w`, `X (i : I₀) : C`, `f (i : I₀) : X i ⟶ S`. So a cover's index `I₀` lives in an independent universe `v`; `gluedCover` is the specialization that pins `v = u`.

---

## Item 5 — Pullback of two open-immersion inclusions vs. intersection of opens (LOAD-BEARING)

**There is NO single packaged iso `pullback U.ι V.ι ≅ (U ⊓ V).toScheme`** in Mathlib. There is no `Scheme.Opens.pullbackIsoInf`, no `IsOpenImmersion.pullback` iso, no `Opens.inf`-to-scheme iso. What exists are the building blocks:

**`AlgebraicGeometry.pullbackRestrictIsoRestrict`** (`Restrict.lean:526-529`) — the closest thing:
```lean
/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
def pullbackRestrictIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    pullback f U.ι ≅ f ⁻¹ᵁ U := by
  refine IsOpenImmersion.isoOfRangeEq (pullback.fst f _) (Scheme.Opens.ι _) ?_
  simp [IsOpenImmersion.range_pullbackFst]
```
Specialize `f := V.ι` to get `pullback V.ι U.ι ≅ V.ι ⁻¹ᵁ U`. Its spec lemmas (`Restrict.lean:531-539`):
```lean
@[simp, reassoc] theorem pullbackRestrictIsoRestrict_inv_fst (f) (U) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst f _ = (f ⁻¹ᵁ U).ι
@[reassoc (attr := simp)] theorem pullbackRestrictIsoRestrict_hom_ι (f) (U) :
    (pullbackRestrictIsoRestrict f U).hom ≫ (f ⁻¹ᵁ U).ι = pullback.fst f _
```

To turn the restriction `V.ι ⁻¹ᵁ U` (an open of `V.toScheme`) into `U ⊓ V`, combine with:

- **`Scheme.Hom.image_preimage_eq_opensRange_inf`** (`OpenImmersion.lean:138`):
  `lemma image_preimage_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U`
- **`Scheme.Opens.opensRange_ι`** (`Restrict.lean:102`): `lemma opensRange_ι : U.ι.opensRange = U`
  (together: `V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = V ⊓ U`)
- **`Scheme.Hom.isoImage`** (`Restrict.lean:368-371`):
  `def Scheme.Hom.isoImage (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) : U.toScheme ≅ f ''ᵁ U`
  (with `isoImage_hom_ι`, `isoImage_inv_ι` at 374/380)
- **`Scheme.restrictRestrictComm`** (`Restrict.lean:357-363`):
  ```lean
  /-- `X ∣_ U ∣_ V` is isomorphic to `X ∣_ V ∣_ U` -/
  def Scheme.restrictRestrictComm (X : Scheme.{u}) (U V : X.Opens) :
      (U.ι ⁻¹ᵁ V).toScheme ≅ V.ι ⁻¹ᵁ U := …
  ```
- Range lemmas for building the iso directly via `isoOfRangeEq`: `IsOpenImmersion.range_pullbackFst` / `range_pullbackSnd` (used at 529/631) and `Scheme.Hom.opensRange_pullbackFst` (`OpenImmersion.lean:604`) / `opensRange_pullbackSnd` (587); `range_pullback_to_base_of_left` (`OpenImmersion.lean:609`): `Set.range (pullback.fst f g ≫ f) = Set.range f ∩ Set.range g`.

So a one-liner is `IsOpenImmersion.isoOfRangeEq (pullback.fst U.ι V.ι) ((U ⊓ V).ι) (by …)` using those range facts, or the composite `pullbackRestrictIsoRestrict U.ι V ≪≫ (U.ι.isoImage _) ≪≫ (eqToIso …)`. Nothing packages this for you.

**`IsOpenImmersion.lift` and its spec lemmas** (`OpenImmersion.lean`), with section context `variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)` and `variable [H : IsOpenImmersion f]` (lines 420-421):
```lean
-- 640
def lift (H' : Set.range g ⊆ Set.range f) : Y ⟶ X :=
  ⟨LocallyRingedSpace.IsOpenImmersion.lift f.toLRSHom g.toLRSHom H'⟩
-- 643
@[reassoc (attr := simp)]
theorem lift_fac (H' : Set.range g ⊆ Set.range f) : lift f g H' ≫ f = g := …
-- 647
theorem lift_uniq (H' : Set.range g ⊆ Set.range f) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' := …
-- 652
@[reassoc]
lemma comp_lift {Y' : Scheme} (g' : Y' ⟶ Y) (H : Set.range g ⊆ Set.range f) :
    g' ≫ lift f g H = lift f (g' ≫ g) (…) := …
-- 700
theorem lift_app {X Y U : Scheme.{u}} (f : U ⟶ Y) (g : X ⟶ Y) [IsOpenImmersion f] (H) (V : U.Opens) : …
```
Also `isPullback_lift_id` (657), `isoOfRangeEq` (666) with `isoOfRangeEq_hom_fac`/`_inv_fac` (672/678).

---

## Item 6 — `glueMorphisms`, `openCoverOfIsOpenCover`, `IsOpenCover`

`AlgebraicGeometry.Scheme.Cover.glueMorphisms` (`Gluing.lean:439-448`):
```lean
def glueMorphisms (𝒰 : OpenCover.{v} X) {Y : Scheme.{u}} (f : ∀ x, 𝒰.X x ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd _ _ ≫ f y) :
    X ⟶ Y := …
```
Its companions: `Scheme.Cover.hom_ext` (`Gluing.lean:451-457`):
```lean
theorem hom_ext (𝒰 : OpenCover.{v} X) {Y : Scheme} (f₁ f₂ : X ⟶ Y)
    (h : ∀ x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
```
and `Scheme.Cover.ι_glueMorphisms` (`Gluing.lean:461-464`, `@[reassoc (attr := simp)]`):
```lean
theorem ι_glueMorphisms (𝒰 : OpenCover.{v} X) {Y : Scheme} (f : ∀ x, 𝒰.X x ⟶ Y)
    (hf : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback.snd _ _ ≫ f y)
    (x : 𝒰.I₀) : 𝒰.f x ≫ 𝒰.glueMorphisms f hf = f x
```
(These three take `OpenCover.{v}` with arbitrary index universe `v`.)

`AlgebraicGeometry.Scheme.openCoverOfIsOpenCover` (`Restrict.lean:178-191`, `@[simps! I₀ X f]`):
```lean
def Scheme.openCoverOfIsOpenCover {s : Type*} (X : Scheme.{u}) (U : s → X.Opens)
    (hU : IsOpenCover U) : X.OpenCover where
  I₀ := s
  X i := U i
  f i := (U i).ι
  mem₀ := …
```

`TopologicalSpace.IsOpenCover` (`Topology/Sets/OpenCover.lean:24-26`):
```lean
/-- An indexed family of open sets whose union is `X`. -/
def IsOpenCover {ι X : Type*} [TopologicalSpace X] (u : ι → Opens X) : Prop :=
  iSup u = ⊤
```
with API `IsOpenCover.mk`, `iSup_eq_top`, `iSup_set_eq_univ`, `exists_mem`, `comap`, etc. On the scheme side, `Scheme.OpenCover.isOpenCover_opensRange` (`Cover/Open.lean:70`) turns a scheme open cover into a topological `IsOpenCover` of `(𝒰.f i).opensRange`. `GlueData.openCover` (`Gluing.lean:262`) gives the open cover of the glued scheme.

---

## Item 7 — pullback.fst / pullback.snd open-immersion instances

In `AlgebraicGeometry.Scheme.Pullback` (file `OpenImmersion.lean`), section context `variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)` with `variable [H : IsOpenImmersion f]` (lines 420-421). Two anonymous instances (`OpenImmersion.lean:540-549`):
```lean
instance : IsOpenImmersion (pullback.snd f g) := by …   -- line 540
instance : IsOpenImmersion (pullback.fst g f) := by …   -- line 547
```
Note these require only **one** of the two legs (`f`) to be an open immersion — base change of an open immersion is an open immersion. So `pullback.snd f g` and `pullback.fst g f` are automatically open immersions (and a fortiori when both `f, g` are open immersions). Also `instance [IsOpenImmersion g] : IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one)` (line 551). Supporting: `hasPullback_of_left`/`hasPullback_of_right` (534/537), and `MorphismProperty.HasPullbacks IsOpenImmersion` (`Cover/Open.lean:36`).

---

## Project-local files — no duplication risk for `gluedCover`/`fromGlued`/pullback-of-opens

Files checked:
`…/Algebraic-Jacobian-Challenge/AlgebraicJacobian/Picard/GrassmannianCells.lean` and `…/GrassmannianQuot.lean`.

- Neither file uses `Scheme.Cover.gluedCover`, `fromGlued`, `pullbackRestrictIsoRestrict`, `restrictRestrictComm`, or any pullback-of-opens-≅-intersection lemma. There is nothing to duplicate on those specific fronts.
- Instead, `GrassmannianCells.lean` builds its own `Scheme.GlueData` directly: `noncomputable def theGlueData (d r : ℕ) : Scheme.GlueData where …` (`GrassmannianCells.lean:1149`), with `V (i,j) = chartOverlap`, and `.glued` as the Grassmannian scheme (line 1166).
- The one closely-related existing item is `Grassmannian.pullbackιIso` (`GrassmannianCells.lean:1275-1279`): `pullback ((theGlueData d r).ι i) ((theGlueData d r).ι j) ≅ V(i,j)` built from `(theGlueData d r).vPullbackConeIsLimit i j` (the `Scheme.GlueData.vPullbackConeIsLimit` API), with spec lemmas `pullbackιIso_inv_fst` (1311) and `pullbackιIso_inv_snd` (1325). This identifies the pullback of the two glued inclusions `ι i, ι j` with the glue-datum's `V (i,j)` (chartOverlap) — it is NOT a pullback-of-opens/`U ⊓ V` statement, so it does not overlap with item 5.
- Heavy existing usage of the generic API you may reuse: `IsOpenImmersion.lift` / `IsOpenImmersion.lift_fac` (e.g. `GrassmannianCells.lean:1584-1586`, `GrassmannianQuot.lean:4638-4640`, `5079-5081`), `Scheme.openCoverOfIsOpenCover` + `glueMorphisms` + `Scheme.Cover.ι_glueMorphisms` + `Scheme.Cover.hom_ext` (throughout `GrassmannianQuot.lean` ~4986-5290), and `TopologicalSpace.IsOpenCover` via `Grassmannian.chartLocus_isOpenCover` (`GrassmannianQuot.lean:2681`).

---

### Quick reference (names → path:line)
- `Scheme.Cover.gluedCover` — Gluing.lean:334 · `gluedCoverT'` — 277 · cocycle helpers 315/320/325
- `Scheme.Cover.fromGlued` — Gluing.lean:350 · `ι_fromGlued` — 357 · `instance IsIso` (anonymous) — 423 · `instance IsOpenImmersion` — 420
- `Scheme.Cover.glueMorphisms` — 439 · `hom_ext` — 451 · `ι_glueMorphisms` — 461
- `Scheme.GlueData` (struct) — Gluing.lean:91 · `glued` — 158 · `ι` — 162 · `vPullbackConeIsLimit` — 201 · `openCover` — 262
- `CategoryTheory.GlueData` (struct, `J : Type v`) — CategoryTheory/GlueData.lean:51
- `PreZeroHypercover` / `ZeroHypercover` — CategoryTheory/Sites/Hypercover/Zero.lean:35 / 646
- `Cover` — Cover/MorphismProperty.lean:50 · `OpenCover` — Cover/Open.lean:40
- `pullbackRestrictIsoRestrict` — Restrict.lean:526 · `restrictRestrictComm` — 359 · `Scheme.Hom.isoImage` — 368 · `openCoverOfIsOpenCover` — 179 · `Opens.opensRange_ι` — 102
- `IsOpenImmersion.lift` — OpenImmersion.lean:640 · `lift_fac` — 644 · `lift_uniq` — 647 · `comp_lift` — 653 · `isoOfRangeEq` — 666 · `image_preimage_eq_opensRange_inf` — 138 · pullback.snd/fst open-immersion instances — 540 / 547
- `TopologicalSpace.IsOpenCover` — Topology/Sets/OpenCover.lean:25
