I have everything needed. Here is the structured report.

---

# Report: Declarations in `GlueDescent.lean` and their external dependencies

All GlueDescent items are from
`/home/Axel/LeanAlgebraicGeometry-Horizon/MainProjects/Algebraic-Jacobian-Challenge/AlgebraicJacobian/Picard/GlueDescent.lean`
(namespace `AlgebraicGeometry.Scheme.Modules`, universe-monomorphic `Scheme.GlueData.{0}` in the `GlueRestriction*` sections).

---

## 8. `pullbackBaseChangeTransport` — full definition with body (lines 57–64)

```lean
noncomputable def pullbackBaseChangeTransport {W V : Scheme.{u}} (p : W ⟶ V)
    {Yi Yj : Scheme.{u}} (a : V ⟶ Yi) (b : V ⟶ Yj)
    {Mi : Yi.Modules} {Mj : Yj.Modules}
    (g : (Scheme.Modules.pullback a).obj Mi ≅ (Scheme.Modules.pullback b).obj Mj) :
    (Scheme.Modules.pullback (p ≫ a)).obj Mi ≅ (Scheme.Modules.pullback (p ≫ b)).obj Mj :=
  (Scheme.Modules.pullbackComp p a).symm.app Mi ≪≫
    (Scheme.Modules.pullback p).mapIso g ≪≫
    (Scheme.Modules.pullbackComp p b).app Mj
```

---

## 9. Triple-overlap bridges (lines 70–98)

`glueData_bridge_src` (70–72):
```lean
theorem glueData_bridge_src (D : Scheme.GlueData.{u}) (i j k : D.J) :
    pullback.fst (D.f i j) (D.f i k) ≫ D.f i j
      = pullback.snd (D.f i j) (D.f i k) ≫ D.f i k := pullback.condition
```

`glueData_bridge_mid` (79–83):
```lean
theorem glueData_bridge_mid (D : Scheme.GlueData.{u}) (i j k : D.J) :
    pullback.fst (D.f i j) (D.f i k) ≫ (D.t i j ≫ D.f j i)
      = (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)) ≫ D.f j k := by ...
```

`glueData_bridge_tgt` (91–98):
```lean
theorem glueData_bridge_tgt (D : Scheme.GlueData.{u}) (i j k : D.J) :
    (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i)) ≫ (D.t j k ≫ D.f k j)
      = pullback.snd (D.f i j) (D.f i k) ≫ (D.t i k ≫ D.f k i) := by ...
```

---

## 11. `pullbackFreeIso` — signature (lines 255–257)

```lean
noncomputable def pullbackFreeIso {T' T : Scheme.{u}} (φ : T' ⟶ T) (I : Type u) :
    (Scheme.Modules.pullback φ).obj (SheafOfModules.free (R := T.ringCatSheaf) I)
      ≅ SheafOfModules.free (R := T'.ringCatSheaf) I := by ...
```

---

## 10. `pullback_isLocallyFreeOfRank` — full statement + proof body (lines 291–302)

```lean
lemma pullback_isLocallyFreeOfRank {T' T : Scheme.{u}} (φ : T' ⟶ T) {M : T.Modules}
    {d : ℕ} (h : SheafOfModules.IsLocallyFreeOfRank M d) :
    SheafOfModules.IsLocallyFreeOfRank ((Scheme.Modules.pullback φ).obj M) d := by
  obtain ⟨ι, U, hcover, hloc⟩ := h
  refine ⟨ι, fun i => φ ⁻¹ᵁ (U i), Scheme.Hom.iSup_preimage_eq_top φ hcover, ?_⟩
  intro i
  obtain ⟨e⟩ := hloc i
  exact ⟨(Scheme.Modules.pullbackComp (φ ⁻¹ᵁ (U i)).ι φ).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι φ (U i)).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (φ ∣_ (U i)) (U i).ι).app M).symm ≪≫
    (Scheme.Modules.pullback (φ ∣_ (U i))).mapIso e ≪≫
    pullbackFreeIso (φ ∣_ (U i)) (ULift.{u} (Fin d))⟩
```

---

## `pullback_preservesLimits_of_isOpenImmersion` — full (lines 927–930)

```lean
instance pullback_preservesLimits_of_isOpenImmersion.{w, w'} {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesLimitsOfSize.{w, w'} (Scheme.Modules.pullback f) :=
  preservesLimits_of_natIso (restrictFunctorIsoPullback f)
```

---

## 4. `glueLift_glueProj` — full statement (lines 1011–1032)

```lean
@[reassoc]
lemma glueLift_glueProj {W : D.glued.Modules}
    (k : ∀ i, W ⟶ (Scheme.Modules.pushforward (D.ι i)).obj (M i))
    (hk : ∀ p : D.J × D.J,
      k p.1 ≫
          ((Scheme.Modules.pushforward (D.ι p.1)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p.1 p.2)).unit.app (M p.1)) ≫
          (Scheme.Modules.pushforwardComp (D.f p.1 p.2) (D.ι p.1)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))
        = k p.2 ≫
          ((Scheme.Modules.pushforward (D.ι p.2)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
          (Scheme.Modules.pushforwardComp (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
            ((Scheme.Modules.pullback (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
          (Scheme.Modules.pushforward
            ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map (g p.1 p.2).inv ≫
          (Scheme.Modules.pushforwardCongr
            (show (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 = D.f p.1 p.2 ≫ D.ι p.1 by
              rw [Category.assoc]; exact D.glue_condition p.1 p.2)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))) (i : D.J) :
    glueLift D M g hC1 hC2 k hk ≫ glueProj D M g hC1 hC2 i = k i := by ...
```
(The section binds `D`, `M`, `g`, `hC1`, `hC2` as `variable`s; see lines 936, 980–993.)

---

## 1. `glueRestrictionHom` — full signature (lines 1042–1045)

```lean
noncomputable def glueRestrictionHom (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2) ⟶ M i :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _).symm
    (glueProj D M g hC1 hC2 i)
```

---

## 2. `glueRestrictEqualizerIso` (1051–1056) and `glueRestrictProdIso` (1064–1068)

```lean
noncomputable def glueRestrictEqualizerIso (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2)
      ≅ equalizer ((Scheme.Modules.pullback (D.ι i)).map (glueLegA D M))
          ((Scheme.Modules.pullback (D.ι i)).map (glueLegB D M g)) :=
  (Scheme.Modules.pullback (D.ι i)).mapIso (glueIsoEqualizer D M g hC1 hC2) ≪≫
    PreservesEqualizer.iso (Scheme.Modules.pullback (D.ι i)) _ _
```

```lean
noncomputable def glueRestrictProdIso (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).obj (glueProd D M)
      ≅ ∏ᶜ fun j => (Scheme.Modules.pullback (D.ι i)).obj
          ((Scheme.Modules.pushforward (D.ι j)).obj (M j)) :=
  PreservesProduct.iso (Scheme.Modules.pullback (D.ι i)) _
```

---

## 3. `pullback_map_glueLift_glueRestrictionHom` — FULL statement (lines 1075–1099)

```lean
lemma pullback_map_glueLift_glueRestrictionHom {W : D.glued.Modules}
    (k : ∀ i, W ⟶ (Scheme.Modules.pushforward (D.ι i)).obj (M i))
    (hk : ∀ p : D.J × D.J,
      k p.1 ≫
          ((Scheme.Modules.pushforward (D.ι p.1)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction (D.f p.1 p.2)).unit.app (M p.1)) ≫
          (Scheme.Modules.pushforwardComp (D.f p.1 p.2) (D.ι p.1)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))
        = k p.2 ≫
          ((Scheme.Modules.pushforward (D.ι p.2)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
              (D.t p.1 p.2 ≫ D.f p.2 p.1)).unit.app (M p.2)) ≫
          (Scheme.Modules.pushforwardComp (D.t p.1 p.2 ≫ D.f p.2 p.1) (D.ι p.2)).hom.app
            ((Scheme.Modules.pullback (D.t p.1 p.2 ≫ D.f p.2 p.1)).obj (M p.2)) ≫
          (Scheme.Modules.pushforward
            ((D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2)).map (g p.1 p.2).inv ≫
          (Scheme.Modules.pushforwardCongr
            (show (D.t p.1 p.2 ≫ D.f p.2 p.1) ≫ D.ι p.2 = D.f p.1 p.2 ≫ D.ι p.1 by
              rw [Category.assoc]; exact D.glue_condition p.1 p.2)).hom.app
            ((Scheme.Modules.pullback (D.f p.1 p.2)).obj (M p.1)))) (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).map (glueLift D M g hC1 hC2 k hk) ≫
        glueRestrictionHom D M g hC1 hC2 i
      = ((Scheme.Modules.pullbackPushforwardAdjunction (D.ι i)).homEquiv _ _).symm (k i) := by
  rw [glueRestrictionHom, ← Adjunction.homEquiv_naturality_left_symm,
    glueLift_glueProj]
```

Note: the `hk` hypothesis here is byte-for-byte the same descent-cocycle compatibility condition used in `glueLift`/`glueLift_glueProj`; the conclusion identifies `ιᵢ^*(glueLift …) ≫ glueRestrictionHom i` with the inverse adjoint transpose of `k i`.

---

## 5. `pullback_map_jointly_faithful` — full statement (lines 1210–1214)

```lean
lemma pullback_map_jointly_faithful (D : Scheme.GlueData.{0}) {W W' : D.glued.Modules}
    {u v : W ⟶ W'}
    (h : ∀ i, (Scheme.Modules.pullback (D.ι i)).map u
        = (Scheme.Modules.pullback (D.ι i)).map v) :
    u = v := by ...
```

---

## 7. `glueRestrict_hom_ext` — full statement (lines 3045–3049)

```lean
lemma glueRestrict_hom_ext {i : D.J} {Z : (D.U i).Modules}
    {u v : Z ⟶ (Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2)}
    (h : ∀ j, u ≫ (Scheme.Modules.pullback (D.ι i)).map (glueProj D M g hC1 hC2 j)
        = v ≫ (Scheme.Modules.pullback (D.ι i)).map (glueProj D M g hC1 hC2 j)) :
    u = v := by ...
```

---

## 6. `isIso_glueRestrictionHom` (3330–3345) and `glueRestrictionIso` (3371–3388)

`isIso_glueRestrictionHom` — full statement (all hypotheses):
```lean
theorem isIso_glueRestrictionHom (D : Scheme.GlueData.{0}) (M : ∀ i, (D.U i).Modules)
    (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
    (hC1 : ∀ i, g i i = eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj (M i))
        (show D.f i i = D.t i i ≫ D.f i i by rw [D.t_id i, Category.id_comp])))
    (hC2 : ∀ i j k,
        pullbackBaseChangeTransport (pullback.fst (D.f i j) (D.f i k))
            (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_mid D i j k)).app (M j) ≪≫
          pullbackBaseChangeTransport (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
            (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i j k)).app (M k)
        = (Scheme.Modules.pullbackCongr (glueData_bridge_src D i j k)).app (M i) ≪≫
          pullbackBaseChangeTransport (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i) (g i k)) (i : D.J) :
    IsIso (glueRestrictionHom D M g hC1 hC2 i) := by ...
```

`glueRestrictionIso` — same five hypotheses (`D`, `M`, `g`, `hC1`, `hC2` are identical to above; `(i : D.J)`), conclusion:
```lean
noncomputable def glueRestrictionIso (D : Scheme.GlueData.{0}) (M : ∀ i, (D.U i).Modules)
    (g : ∀ i j, (Scheme.Modules.pullback (D.f i j)).obj (M i) ≅
        (Scheme.Modules.pullback (D.t i j ≫ D.f j i)).obj (M j))
    (hC1 : ∀ i, g i i = eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj (M i))
        (show D.f i i = D.t i i ≫ D.f i i by rw [D.t_id i, Category.id_comp])))
    (hC2 : ∀ i j k,
        pullbackBaseChangeTransport (pullback.fst (D.f i j) (D.f i k))
            (D.f i j) (D.t i j ≫ D.f j i) (g i j) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_mid D i j k)).app (M j) ≪≫
          pullbackBaseChangeTransport (D.t' i j k ≫ pullback.fst (D.f j k) (D.f j i))
            (D.f j k) (D.t j k ≫ D.f k j) (g j k) ≪≫
          (Scheme.Modules.pullbackCongr (glueData_bridge_tgt D i j k)).app (M k)
        = (Scheme.Modules.pullbackCongr (glueData_bridge_src D i j k)).app (M i) ≪≫
          pullbackBaseChangeTransport (pullback.snd (D.f i j) (D.f i k))
            (D.f i k) (D.t i k ≫ D.f k i) (g i k)) (i : D.J) :
    (Scheme.Modules.pullback (D.ι i)).obj (glue D M g hC1 hC2) ≅ M i :=
  haveI := isIso_glueRestrictionHom D M g hC1 hC2 i
  asIso (glueRestrictionHom D M g hC1 hC2 i)
```

---

## 12. External `Scheme.Modules.*` operations — from mathlib

These are NOT project-local. They live in mathlib at
`/home/Axel/LeanAlgebraicGeometry-Horizon/.lake-packages/mathlib/Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`,
namespace `AlgebraicGeometry.Scheme.Modules` (base object `def Modules := SheafOfModules.{u} X.ringCatSheaf`, Sheaf.lean:37). Each is a thin wrapper over the `SheafOfModules.*` operation applied to `f.toRingCatSheafHom`. Variables `(f : X ⟶ Y) (g : Y ⟶ Z)`.

- `pushforward` (Sheaf.lean:164): `def pushforward : X.Modules ⥤ Y.Modules := SheafOfModules.pushforward f.toRingCatSheafHom`
- `pullback` (180): `def pullback : Y.Modules ⥤ X.Modules := SheafOfModules.pullback f.toRingCatSheafHom`
- `pullbackPushforwardAdjunction` (185): `def pullbackPushforwardAdjunction : pullback f ⊣ pushforward f := SheafOfModules.pullbackPushforwardAdjunction _`
- `pushforwardComp` (223): `def pushforwardComp : pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) := SheafOfModules.pushforwardComp _ _`
- `pullbackComp` (232): `def pullbackComp : pullback g ⋙ pullback f ≅ pullback (f ≫ g) := SheafOfModules.pullbackComp _ _`
- `pushforwardCongr` (237): `def pushforwardCongr {f g : X ⟶ Y} (hf : f = g) : pushforward f ≅ pushforward g := pushforwardNatIso _ (Opens.mapIso _ _ (hf ▸ rfl)) ≪≫ SheafOfModules.pushforwardCongr (by cat_disch)`
- `pullbackCongr` (248): `def pullbackCongr {f g : X ⟶ Y} (hf : f = g) : pullback f ≅ pullback g := eqToIso (hf ▸ rfl)`

Also present: `pushforwardId` (203), `pullbackId` (212).

### NatIso status and `_hom_app`/`_inv_app` simp lemmas

Both `pullbackComp` and `pullbackCongr` are natural isomorphisms — each is an `Iso` in a functor category (`pullback g ⋙ pullback f ≅ pullback (f ≫ g)` and `pullback f ≅ pullback g` respectively), so `.hom`/`.inv` are natural transformations and `.hom.app M`/`.inv.app M` are the components.

- Mathlib provides component simp lemmas for the *pushforward* side only: `pushforwardComp_hom_app_app`/`pushforwardComp_inv_app_app` (Sheaf.lean:227–228, both `= 𝟙 _`), `pushforwardCongr_hom_app_app`/`pushforwardCongr_inv_app_app` (241–245, `= M.presheaf.map (eqToHom (hf ▸ rfl)).op`), and `pushforwardId_hom_app_app`/`pushforwardId_inv_app_app` (206–207).
- Mathlib does NOT ship `pullbackComp_hom_app`/`pullbackComp_inv_app` or `pullbackCongr_hom_app`/`pullbackCongr_inv_app` component lemmas.
- The project supplies its own component lemmas for `pullbackCongr` (which unfold it as an `eqToHom`, since `pullbackCongr = eqToIso …`):
  - `AlgebraicGeometry.Scheme.Modules.pullbackCongr_hom_app` — QuotFunctorDef.lean:119–123: `(Scheme.Modules.pullbackCongr h).hom.app M = eqToHom (by rw [h])`
  - `AlgebraicGeometry.Scheme.Modules.pullbackCongr_inv_app` — QuotFunctorDef.lean:126–130: `(Scheme.Modules.pullbackCongr h).inv.app M = eqToHom (by rw [h])`
  - `pullbackCongr_hom_app_eqToHom` — GlueDescent.lean:1463–1468: `(Scheme.Modules.pullbackCongr h).hom.app N = eqToHom (congrArg (fun α => (Scheme.Modules.pullback α).obj N) h)` (companion `pullbackCongr_inv_app_eqToHom` at GlueDescent.lean:1893; free-sheaf variants `pullbackCongr_hom_app_free`/`pullbackCongr_inv_app_free` at 639/665).
  - For `pullbackComp` the project only adds a specialised `pullbackComp_inv_app_free_map` (GlueDescent.lean:679); there is no general `pullbackComp_hom_app`/`_inv_app` simp lemma.

(Full path for the two QuotFunctorDef lemmas: `.../AlgebraicJacobian/Picard/QuotFunctorDef.lean`, inside `namespace Modules`.)

---

## Epi search

There is **no** lemma in `GlueDescent.lean` asserting that glued morphisms are epi, nor that pullback preserves epis. `grep -i epi` yields exactly two hits, both false/incidental:

- Line 1208: the docstring of `pullback_map_jointly_faithful` names a downstream *consumer*, `` `tautologicalQuotient_epi` `` ("Engine for `tautologicalQuotient_epi`"). That lemma is not defined here — it lives in `AlgebraicJacobian/Picard/GrassmannianZariskiSheaf.lean` and `AlgebraicJacobian/Picard/GrassmannianQuot.lean`. `pullback_map_jointly_faithful` itself is a joint-faithfulness (separation) statement, not an epi statement.
- Line 2999: a false-positive substring match inside the word "book**keepi**ng" (docstring of `glueRestrict_proj_compat`); no `Epi` there.

No occurrences of `Epi`/`Mono` as actual category-theory typeclasses appear in the file. The closest "surjectivity/effectivity" content is `isIso_glueRestrictionHom` (chart restriction is an isomorphism) and `pullback_map_jointly_faithful` (chart restrictions are jointly faithful).
