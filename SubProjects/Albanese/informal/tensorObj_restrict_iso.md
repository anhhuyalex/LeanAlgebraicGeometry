# `tensorObj_restrict_iso` — corrected decomposition (iter-208 Lane TS, Route A audit)

## Target

```lean
noncomputable def tensorObj_restrict_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M N : X.Modules) :
    (tensorObj M N).restrict f ≅ tensorObj (M.restrict f) (N.restrict f)
```
where `tensorObj M N := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
(PresheafOfModules.Monoidal.tensorObj M.val N.val)`.

## State in the file (compiles GREEN, after iter-208)

The proof now performs **three real reduction steps** before the residual `sorry`:

1. `Scheme.Modules.restrictFunctorIsoPullback f` — reduce `·.restrict f` to
   `(pullback f).obj ·` (sheaf-level pullback). [Mathlib]
2. `SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom` — move the
   pullback inside the sheafification. [Mathlib]
3. **(NEW iter-208)** `(PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).mapIso ?_`
   — strip the OUTER sheafification: both sides are `sheafification.obj _`, so it
   suffices to give the presheaf-level comparison. VERIFIED: resulting goal has no
   sheafification.

After step 3 the residual is the **purely presheaf-level**
```
(PresheafOfModules.pullback φ.hom).obj (M.val ⊗ₚ N.val)
  ≅ (M.restrict f).val ⊗ₚ (N.restrict f).val
```
with `φ.hom = (Scheme.Hom.toRingCatSheafHom f).hom`, `⊗ₚ = PresheafOfModules.Monoidal.tensorObj`.

## The Route-A recipe (`analogies/tsroute208.md`) is INCORRECT on the key point

The recipe says the residual is a "~30–60 LOC sectionwise unfolding of
`PresheafOfModules.pullback φ` along the open immersion", to be discharged
"sectionwise via `isoMk` ... over each `U` both sides are `M(f''U) ⊗ N(f''U)` by
`restrict_obj` `rfl`, differing only by the scalar ring".

This conflates two DIFFERENT functors:
- `PresheafOfModules.pullback φ.hom` (what appears in the residual) is the
  **OPAQUE abstract left adjoint** `(pushforward φ.hom).leftAdjoint`
  (`Mathlib/.../Presheaf/Pullback.lean:44`, built via the `leftAdjointObjIsDefined`
  partial-adjoint machinery). It has **NO sectionwise formula**. The `restrict_obj`
  `rfl` the recipe cites is a fact about **`restrict`/`pushforward`**, not
  `pullback`: `M.restrict f = Scheme.Modules.restrictFunctor f =
  SheafOfModules.pushforward β` (a CONCRETE sectionwise pushforward along
  `f.opensFunctor`, `Modules/Sheaf.lean`), whose `.val` is
  `(PresheafOfModules.pushforward β.hom).obj M.val`.
- The kaehler precedent the recipe cites (`analogies/kaehler-...presheafpullback`,
  Decision 5) hit this EXACT opacity and **excised** its pullback-unfolding helper
  (`Cotangent/GrpObj.lean` iter-145) — it was never built.

So there is no cheap sectionwise unfolding of the opaque `pullback`. The residual
must be attacked by relating `pullback φ.hom` to the concrete `pushforward β.hom`.

## Genuine route: TWO project-side ingredients, BOTH absent from Mathlib

### H1 (the linchpin) — presheaf-level `pushforward β.hom ≅ pullback φ.hom`

`pullback φ.hom := (pushforward φ.hom).leftAdjoint`. Exhibit a presheaf-level
adjunction `PresheafOfModules.pushforward β.hom ⊣ PresheafOfModules.pushforward φ.hom`
and conclude `pushforward β.hom ≅ pullback φ.hom` by `Adjunction.leftAdjointUniq`
(against `PresheafOfModules.pullbackPushforwardAdjunction φ.hom`).

- `β.hom` is the structure map of `restrictFunctor f`: from `Modules/Sheaf.lean`,
  `restrictFunctor f = SheafOfModules.pushforward (F := f.opensFunctor)
  ⟨whiskerRight α (forget₂ CommRingCat RingCat)⟩` with `α.app U = (f.appIso U.unop).inv`.
  Hence `(M.restrict f).val = (PresheafOfModules.pushforward β.hom).obj M.val`
  DEFINITIONALLY.
- The adjunction is the **presheaf analogue of the sheaf-level**
  `SheafOfModules.pushforwardPushforwardAdj`
  (`Sheaf/PushforwardContinuous.lean:226`), built from the opens-functor
  adjunction `f.opensFunctor ⊣ Opens.map f.base`
  (`f.isOpenEmbedding.isOpenMap.adjunction`) plus the two compatibility squares
  `H₁`, `H₂`. The unit/counit have the simple sectionwise form
  `M.val.map (adj.counit/unit.app U).op`.
- **Absent Mathlib building blocks** (only the SHEAF versions exist): presheaf-level
  `PresheafOfModules.pushforwardNatTrans` and `PresheafOfModules.pushforwardCongr`.
  `pushforwardId`/`pushforwardComp` DO exist at presheaf level.
- Estimate: ~100–150 LOC (mirror `pushforwardPushforwardAdj` + the 2 helpers +
  verify `H₁`/`H₂` for the open-immersion data).

### H2 — strong-monoidal comparison for `pushforward β.hom`

`(pushforward β.hom).obj (A ⊗ₚ B) ≅ (pushforward β.hom).obj A ⊗ₚ (pushforward β.hom).obj B`.

- `PresheafOfModules.pushforward φ = pushforward₀ F R ⋙ restrictScalars φ`
  (`Presheaf/Pushforward.lean:86`). `pushforward₀OfCommRingCat` is already
  `Monoidal` (`PushforwardZeroMonoidal.lean:33`, `μIso = refl`). So H2 reduces to
  upgrading the file's lax `PresheafOfModules.restrictScalarsLaxMonoidal` (already
  present, lines 147–177) to **STRONG** when `α` is componentwise a ring iso, via
  `Functor.Monoidal.ofLaxMonoidal` (`Monoidal/Functor.lean:718`, needs
  `IsIso (ε F)` and `∀ X Y, IsIso (μ F X Y)`). Then
  `(pushforward β.hom).Monoidal := (pushforward₀OfCommRingCat).Monoidal.comp
  (restrictScalars β-part).Monoidal` and H2 is its `μIso`.
- `IsIso ε`: EASY — sectionwise `ε (ModuleCat.restrictScalars (α.app X).hom)` has
  underlying map the ring map `α.app X` (`ModuleCat.restrictScalars_η`), iso since
  `α` is a NatIso.
- `IsIso μ`: the REAL bottom gap. Sectionwise this is "`ModuleCat.restrictScalars`
  along a ring isomorphism is strong monoidal" — i.e. the tensorator
  `restrictScalars(M₁) ⊗_R restrictScalars(M₂) → restrictScalars(M₁ ⊗_S M₂)`
  (`m₁ ⊗ₜ m₂ ↦ m₁ ⊗ₜ m₂`, `ModuleCat.restrictScalars_μ_tmul`) is iso for a ring
  iso `R ≃+* S`. **Absent from Mathlib**: `ModuleCat.extendScalars` is `Monoidal`
  (`Monoidal/Adjunction.lean:42`) but `restrictScalars` is only `LaxMonoidal`
  (`:102`). Provable (~30–50 LOC) either by a direct `TensorProduct` `LinearEquiv`
  (base change along a ring iso) or by transporting `extendScalars`-monoidality
  across the adjoint equivalence `extendScalars e ⊣ restrictScalars e` (for `e`
  iso both are equivalences, so `restrictScalars e ≅ extendScalars e.symm`).
- Then lift the sectionwise `IsIso μ` to the presheaf `μ` (the file's
  `restrictScalarsLaxμ`) via a presheaf-of-modules iso-from-sectionwise criterion
  (`PresheafOfModules.toPresheaf` reflects isos + `NatTrans.isIso_iff_isIso_app`).
- Estimate: ~60–100 LOC.

### Closure once H1, H2 land

```
(pullback φ.hom).obj (M.val ⊗ₚ N.val)
  ≅[H1.symm]  (pushforward β.hom).obj (M.val ⊗ₚ N.val)
  ≅[H2]       (pushforward β.hom M.val) ⊗ₚ (pushforward β.hom N.val)
  =defeq      (M.restrict f).val ⊗ₚ (N.restrict f).val
```

## Verdict

This is a **~200–300 LOC, multi-ingredient `mathlib-build`-scale** task, NOT a
single prove-mode close. The four absent Mathlib ingredients are:
1. `PresheafOfModules.pushforwardNatTrans` (presheaf-level).
2. `PresheafOfModules.pushforwardCongr` (presheaf-level).
3. presheaf-level `pushforwardPushforwardAdj` (gives H1).
4. strong-monoidal `ModuleCat.restrictScalars` along a ring iso (gives the H2 bottom).

The informal-agent consult was unavailable this iter: the only key present
(`MOONSHOT_API_KEY`) is a "Kimi For Coding" subscription key, rejected by the
chat-completions API (403 `access_terminated_error` on `api.kimi.com/coding`,
401 on `api.moonshot.cn`) — usable only through coding-agent front-ends.

## Dead ends (do NOT retry)

- The abstract-adjoint **mate-δ route** via `(PresheafOfModules.pullback φ).Monoidal`
  / `leftAdjointOplaxMonoidal` (4 iters dead; needs general-`extendScalars`
  monoidality lift — strictly harder than H2's ring-iso case).
- "Sectionwise unfold `PresheafOfModules.pullback`" — it is an opaque left adjoint;
  no sectionwise formula; kaehler lane excised the analogue.
- Adding `IsLocallyTrivial M N` hypotheses — unnecessary (lemma is true for
  arbitrary `M N`) and there is no `SheafOfModules` iso-gluing primitive.
