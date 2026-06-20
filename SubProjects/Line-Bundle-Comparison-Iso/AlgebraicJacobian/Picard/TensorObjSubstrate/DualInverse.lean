/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.Picard.TensorObjSubstrate
import AlgebraicJacobian.Picard.TensorObjSubstrate.PresheafInternalHom
import AlgebraicJacobian.Picard.TensorObjSubstrate.DualInverse.SliceTransport

/-!
# Dual-inverse parallel lane (A.1.c.SubT §Dual, iter-251)

This file holds the **dual-inverse chain** that feeds `exists_tensorObj_inverse` in
`TensorObjSubstrate.lean`:

1. `dual_restrict_iso` — restriction along an open immersion commutes with the sheaf-level
   dual (blueprint `lem:dual_restrict_iso`; the C-bridge).  **CLOSED**: Steps 1–3
   (`restrictFunctorIsoPullback`/`sheafificationCompPullback`/strip) + H1
   (`pushforwardPushforwardAdj`∘`leftAdjointUniq`) are in place; the Step-4 presheaf residual
   `(pushforward β).obj (dual M.val) ≅ dual ((pushforward β).obj M.val)`
   is assembled sectionwise from `sliceDualTransport` (see piece 1b below) plus a thin-poset
   naturality square (closed by `subsingleton`).

   1b. `sliceDualTransport` — the per-`V` `𝒪_Y(V)`-linear iso of the Step-4 residual.  **CLOSED**:
   the obligation is a `𝒪_Y(V)`-linear equivalence between the two morphism (`Hom`)
   types `(restr fV' M.val ⟶ restr fV' 𝟙_X)` (restricted along `β.app V`) and
   `(restr V ((pushforward β).obj M.val) ⟶ restr V 𝟙_Y)`, where `fV' = f.opensFunctor.obj V`.
   ROUTE-1 (consume the shared root `Scheme.Modules.overEquivalence`/`restrictOverIso`/`unitOverIso`)
   is **STRUCTURALLY DEAD** (iter-260): those are `restrict↦over` / `unit↦unit` SHEAF isos — they say
   nothing about `dual`; producing the dual-commutation they lack needs the avoided
   `MonoidalClosed (PresheafOfModules)`.  The genuine close is the direct sectionwise build
   (ROUTE-2, sanctioned iter-261): leg-A reindexes `φ` across `f.opensFunctor` (categorical
   `restrictScalars … |>.map`), leg-B swaps the codomain unit ring via `dualUnitRingSwap`
   (= `inv (ε (restrictScalars (f.appIso W').inv.hom))`).  `map_add'` is CLOSED (iter-263) and
   `map_smul'` is CLOSED (iter-264, axiom-clean: β-naturality ring identity `s = (β.app W').hom c`
   via `Scheme.Hom.appIso_inv_naturality` + `𝒪_Y(W')`-linearity of `dualUnitRingSwap.hom` via
   `map_smul`).  `naturality`, `invFun`, `left_inv`, and `right_inv` are all closed.
2. `dual_isLocallyTrivial` — the dual of a locally-trivial module is locally trivial
   (blueprint `lem:dual_isLocallyTrivial`).  **CLOSED**: the three-step chart-chase
   `dual_restrict_iso ≪≫ (dualIsoOfIso eL).symm ≪≫ dual_unit_iso` is assembled and compiles.
   The third leg `dual_unit_iso` and its presheaf core `presheafDualUnitIso` (= the §0
   `dualUnitIsoGen`, the eval-at-`1` `dual 𝟙_ ≅ 𝟙_`) are built axiom-clean.
3. `homOfLocalCompat` — a compatible family of local `𝒪_X`-module morphisms over an open
   cover glues to a unique global morphism (blueprint `lem:sheafofmodules_hom_of_local_compat`;
   the A-bridge).  **CLOSED** (iter-256), axiom-clean; the multi-piece sheaf-of-homs gluing
   engine.  The final sub-step (c) sectionwise `𝒪_X`-linearity is closed by the native↔
   `restrictScalars 𝟙` smul bridge `hbridge` (from `Scheme.Opens.ι_appIso` +
   `ModuleCat.restrictScalars.smul_def'`), feeding the native f-leg linearity `hfl_native`.

The prover lane for this file works **in parallel** with the D1′/D3′/D4′ lane in
`TensorObjSubstrate.lean`.

Blueprint chapter: `blueprint/src/chapters/Picard_TensorObjSubstrate.tex`.
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory


namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-- **Restriction along an open immersion commutes with the sheaf-level dual (C-bridge).**

Blueprint `lem:dual_restrict_iso` (§`sec:tensorobj_dual_bridge`).  For an open immersion
`f : Y ⟶ X` and `M : X.Modules`, there is a canonical isomorphism of `𝒪_Y`-modules
```
  (dual M).restrict f  ≅  dual (M.restrict f)
```
natural in `M`, between the restriction of the sheaf-level dual and the dual of the
restriction.

/- Planner strategy:
   Blueprint label: lem:dual_restrict_iso (~L5374).

   Proof-sketch (blueprint §5.4):
   The proof runs at the PRESHEAF-OF-MODULES level (Step 3 of the tensorObj_restrict_iso
   H1∘H2 recipe already strips the outer sheafification).  Three ingredients:

   (a) Per-V slice equivalence: for each V ≤ U (= image of f), the opens functor
       `f.opensFunctor` is fully faithful with image = {W ≤ U}, so
       `Over_Y V ≃ Over_X (f.opensFunctor V)`.  This is the per-open shadow of
       `TopologicalSpace.Opens.overEquivalence` (CLOSED in Vestigial.lean via
       `overSliceSheafEquiv`).

   (b) Agreement of codomain: the structure sheaf of Y agrees with that of X under (a).

   (c) Ring-iso transport of module structure:
       `lem:restrictscalars_ringiso_dualequiv` (CLOSED in PresheafInternalHom.lean as
       `restrictScalarsRingIsoDualEquiv`):
         `RingEquiv e → Dual(restrictScalars e.toRingHom A) ≃ restrictScalars e.toRingHom (Dual A)`
       applies sectionwise at each V to transport the `𝒪_X(fV)`-module structure on
       `(dual M)|_f(V)` to the `𝒪_Y(V)`-module structure via the ring iso
       `β_V = (f.appIso V).inv : 𝒪_X(fV) ≅ 𝒪_Y(V)`.

   High-level recipe (mirrors tensorObj_restrict_iso Steps 1–4 with `dual` in place of `⊗`):
   Step 1: `(Scheme.Modules.restrictFunctorIsoPullback f).app (dual M)` — reduce `restrict`
           to abstract pullback.
   Step 2: `SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom` — move pullback
           inside sheafification.
   Step 3: strip the outer sheafification via `(sheafification …).mapIso`.
   Step 4 (the genuine new build):  close the residual presheaf goal
             `pushforward β (PresheafOfModules.dual M.val)
                 ≅ PresheafOfModules.dual ((pushforward β).obj M.val)`
           The ROUTE: sectionwise, at each V ≤ U, the value of the LHS is
           `Hom_{Over_X(fV)}(restr(fV) M.val, restr(fV) 𝟙_X)` and the value of the RHS is
           `Hom_{Over_Y V}(restr V (pushforward β M.val), restr V 𝟙_Y)`.
           The slice equivalence (a) identifies these indexing categories; the agreement (b)
           identifies the codomain `𝟙`; the ring-iso transport (c) via
           `restrictScalarsRingIsoDualEquiv` reconciles the module structures.
           Naturality in V is automatic on the thin poset `Opens X` by `Subsingleton.elim`.

   STATUS NOTE (iter-260; the shared root IS now green — `SheafOverEquivalence.lean` is sorry-free;
   supersedes the stale "route (1) gated" claim):
   The Step-4 residual reduces (via `sliceDualTransport`) to the per-`V` `𝒪_Y(V)`-linear
   equivalence (reduction now executed IN CODE in `sliceDualTransport` via
   `refine LinearEquiv.toModuleIso ?_`; the `Module 𝒪_Y(V)` instances synthesize automatically):
     `((pushforward₀ f.opensFunctor X.ringCatSheaf.obj).obj (dual M.val)).obj V`
       ≃ₗ[𝒪_Y(V)]
     `(internalHomPresheaf ((pushforward β).obj M.val) 𝟙_Y).obj V`
   i.e. `(restr fV' M.val ⟶ restr fV' 𝟙_X) ≃ₗ[𝒪_Y(V)]`
        `(restr V (pushforward β M.val) ⟶ restr V 𝟙_Y)`,
   with `fV' = f.opensFunctor.obj V.unop`.

   ROUTE-(1) IS STRUCTURALLY INSUFFICIENT (iter-260 finding — the EXACT failing step):
     The shared root `Scheme.Modules.overEquivalence` and its consumer isos
     `restrictOverIso`/`unitOverIso` (`Picard/SheafOverEquivalence.lean`) are now GREEN, but they
     are object-isos of `restrict ↦ over` and `unit ↦ unit` at the SHEAF level — they say NOTHING
     about `dual`/internal-hom.  The reduced `≃ₗ` is precisely the statement that the dual
     (`internalHomPresheaf · 𝟙_`) COMMUTES with the slice reindexing along `f.opensFunctor`.  No
     shared-root decl (grepped) provides a `dual`-commutation; obtaining one from `overEquivalence`
     would require its functor (`SheafOfModules.pushforward`) to be strong monoidal CLOSED — the
     `MonoidalClosed (PresheafOfModules R₀)` wall the project deliberately avoids
     (TensorObjSubstrate §2 `rem:scheme_modules_monoidal_off_path`).  Hence route (1) cannot close
     `sliceDualTransport`; this is structural, not tactic difficulty.  See the in-body comment of
     `sliceDualTransport` for the full diagnosis.

   GENUINE CLOSE = ROUTE (2) (the direct sectionwise build; ~150–250 LOC, instance-delicate):
     build `sliceDualTransport`'s forward map à la `homLocalSection` (`eqToHom`-conjugation
     across `f.opensFunctor` along `image_preimage_of_le`, naturality `Subsingleton.elim`, leg A)
     ∘ `restrictScalarsRingIsoDualEquiv` (the codomain-unit ring swap via `(f.appIso V).inv`,
     leg B).  Leg B does NOT type-apply standalone (fixed-carrier `N →ₗ[S] S`; here the two sides
     have different over-category INDEXING, so leg A runs first).  Per the iter-260 armed reversing
     signal this build is NOT undertaken unilaterally; it awaits planner sanction (or, instead,
     a new shared-root "overEquivalence preserves internal hom" lemma, which itself needs the
     avoided monoidal-closed structure and is therefore the harder of the two).

   Named CLOSED base lemmas this stub consumes:
   - `PresheafOfModules.dual` (PresheafInternalHom.lean) — presheaf-level dual.
   - `Scheme.Modules.dual` (TensorObjSubstrate.lean ~L207) — sheaf-level dual.
   - `InternalHom.restrictScalarsRingIsoDualEquiv` (PresheafInternalHom.lean ~L234) — the
     ring-iso / dual commutation at the `ModuleCat` level.
   - `Scheme.Modules.restrictFunctorIsoPullback` (Mathlib) — Step 1 iso.
   - `SheafOfModules.sheafificationCompPullback` (Mathlib) — Step 2 iso.
   - `PresheafOfModules.pushforwardPushforwardAdj` (PresheafInternalHom.lean) — H1.
   - `PresheafOfModules.restrictScalarsMonoidalOfBijective` (PresheafInternalHom.lean) — H2
     (not directly needed for `dual`, but the same `β`-bijectivity is used).
-/
-/
noncomputable def dual_restrict_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M : X.Modules) :
    (dual M).restrict f ≅ dual (M.restrict f) := by
  -- Step 1. Reduce `restrict` to `pullback` along the open immersion `f`.
  refine (Scheme.Modules.restrictFunctorIsoPullback f).app (dual M) ≪≫ ?_
  -- Step 2. Sheafification commutes with pullback.
  refine (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).app
      (PresheafOfModules.dual (R₀ := X.presheaf) M.val) ≪≫ ?_
  -- Step 3. Strip the outer sheafification, descending to the presheaf residual.
  refine (PresheafOfModules.sheafification (R := Y.ringCatSheaf)
      (𝟙 Y.ringCatSheaf.obj)).mapIso ?_
  -- Step 4 (RESIDUAL): the presheaf goal
  --   `(pullback φ).obj (dual M.val) ≅ dual ((M.restrict f).val)`.
  -- H1: replace `pullback φ` with `pushforward β` (β the open-immersion structure ring iso).
  let φR := (Scheme.Hom.toRingCatSheafHom f).hom
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv }
  let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  have hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φR :=
    PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φR
      (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
  let H1 := hadj.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φR)
  refine (H1.app (PresheafOfModules.dual (R₀ := X.presheaf) M.val)).symm ≪≫ ?_
  -- Residual: `(pushforward β).obj (dual M.val) ≅ dual ((pushforward β).obj M.val)`.
  -- Assemble sectionwise from `sliceDualTransport`.  The `isoMk` naturality square is the
  -- thin-poset `Opens Y` coherence of the `sliceDualTransport` family; it is closed by
  -- `subsingleton` (the connecting Hom-space in a thin poset is a subsingleton).
  refine PresheafOfModules.isoMk (fun V => sliceDualTransport f M V) ?_
  intro V W g
  -- Outer `isoMk` naturality square over the thin poset `Opens Y`: the connecting Hom-space is a
  -- subsingleton, so the square commutes definitionally (blueprint: thin-poset coherence).
  subsingleton

/-! ## §B. Local triviality of the dual -/

/-- **Two `S`-linear endomorphisms of the regular module `S` (`S` commutative) commute on `1`.**
For `a b : S →ₗ[S] S`, `a (b 1) = b (a 1)`: an `S`-linear endomorphism `g` of `S` is multiplication
by `g 1` (`g x = x * g 1`, from `g x = g (x • 1) = x • g 1`), and `S` is commutative, so the two
products `(b 1) * (a 1)` and `(a 1) * (b 1)` agree.  Used to close `presheafDualUnitIso_naturality`:
both `evalLin _ X φ` (the eval-at-`1`) and `ŝ.hom.app X` (the unit automorphism) are `𝒪_Y(X)`-linear
endomorphisms of the regular module `𝒪_Y(X)`, and `𝒪_Y(X)` is commutative. -/
private lemma linearEndo_apply_comm {S : Type u} [CommRing S] (a b : S →ₗ[S] S) :
    a (b 1) = b (a 1) := by
  have key : ∀ (g : S →ₗ[S] S) (x : S), g x = x * g 1 := fun g x => by
    rw [← smul_eq_mul, ← LinearMap.map_smul, smul_eq_mul, mul_one]
  rw [key a (b 1), key b (a 1), mul_comm]

/-- **Presheaf-level: the dual of the monoidal unit is the unit.**
`PresheafOfModules.dual 𝟙_ = ℋom(𝟙_, 𝟙_) ≅ 𝟙_`, the evaluation-at-`1` isomorphism.
Local supplement (the `PresheafOfModules`-level ingredient of `dual_unit_iso`). -/
noncomputable def presheafDualUnitIso {Y : Scheme.{u}} :
    PresheafOfModules.dual (R₀ := Y.presheaf)
        (𝟙_ (_root_.PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat)))
      ≅ 𝟙_ (_root_.PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) :=
  PresheafOfModules.dualUnitIsoGen (R₀ := Y.presheaf)

/-- **Naturality of `presheafDualUnitIso` w.r.t. unit automorphisms** (blueprint
`lem:presheafdualunitiso_naturality`, the eval-core (★')).  For any automorphism `ŝ` of
the monoidal unit `𝟙_` in
`PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat)`, the
evaluation-at-`1` isomorphism `presheafDualUnitIso : (𝟙_).dual ≅ 𝟙_` intertwines the
contravariant dual transport `PresheafOfModules.dualIsoOfIso ŝ : (𝟙_).dual ≅ (𝟙_).dual`
with `ŝ` acting on the codomain:

```
PresheafOfModules.dualIsoOfIso ŝ ≪≫ presheafDualUnitIso
  = presheafDualUnitIso ≪≫ ŝ
```

This is the presheaf eval-core (★') consumed by `dualUnitIso_dualIsoOfIso` in
`TensorObjInverse.lean` (`hN` sorry at L237): that assembly reduces `hN` to this
statement via `sheafification.mapIso` + the sheafification-counit naturality.

/- Planner strategy:
   Blueprint label: lem:presheafdualunitiso_naturality.
   `\uses`: def:presheaf_dual_unit_iso, def:dual_unit_iso_gen,
            lem:internal_hom_eval, lem:presheaf_dualisoofiso_trans.

   Setting: let `C = _root_.PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat)`.
   Both sides have type `(𝟙_ C).dual ≅ 𝟙_ C`.

   ## Key facts

   (A) `presheafDualUnitIso = dualUnitIsoGen (R₀ := Y.presheaf)` (L217 of this file).
       Its sectionwise content (from `dualUnitIsoGen` / `unitDualSectionEquiv`,
       SliceTransport.lean L42): the forward map sends a dual section
       `φ : (𝟙_).dual.obj X` to `evalLin φ 1` ∈ `(𝟙_ C).obj X = 𝒪_Y(X)`,
       where `evalLin φ 1 = (φ.app (op (Over.mk 𝟙))).hom 1`
       (PresheafInternalHom.lean L889).

   (B) `PresheafOfModules.dualIsoOfIso ŝ` (PresheafInternalHom.lean L1078):
       assembled via `dualPrecompEquiv ŝ U` (L1033) at each section `U`.
       `dualPrecompEquiv ŝ U` sends a dual section `φ` to
       `pushforward₀.map ŝ.hom ≫ φ` — i.e. precomposition of `φ` by `ŝ.hom`.
       In sectionwise terms: the new dual section `ψ = (pushforward₀.map ŝ.hom) ≫ φ`
       satisfies `ψ.app (op (Over.mk 𝟙)) = ŝ.hom.app X ≫ φ.app (op (Over.mk 𝟙))`
       (in `ModuleCat`).

   ## Sectionwise proof

   Fix a section `X : (Opens Y)ᵒᵖ` and an element `φ : (𝟙_).dual.obj X`.
   Writing `ev(φ) := evalLin φ 1 = (φ.app (op (Over.mk 𝟙))).hom 1 ∈ 𝒪_Y(X)`:

   LHS at `φ`:
     `ev(dualPrecompEquiv ŝ X φ) 1`
     = `(ŝ.hom.app X ≫ φ.app (op (Over.mk 𝟙))).hom 1`
     = `(φ.app (op (Over.mk 𝟙))).hom (ŝ.hom.app X 1)`   [by definition of composition]
     = `φ evaluated at ŝ.hom.app X 1`.

   RHS at `φ`:
     `(ŝ.hom.app X).hom (ev(φ) 1)`
     = `(ŝ.hom.app X).hom ((φ.app (op (Over.mk 𝟙))).hom 1)`
     = `ŝ evaluated at φ(1)`.

   Both `φ.app (op (Over.mk 𝟙))` and `ŝ.hom.app X` are `𝒪_Y(X)`-linear endomorphisms
   of `𝒪_Y(X)` (= the value of `𝟙_` at `X`). An `R`-linear endomorphism of `R`
   (commutative ring, viewed as a module over itself) is multiplication by a scalar
   `c = f(1) ∈ R`, so `f(r) = c * r`. Since `𝒪_Y(X)` is **commutative**, the two
   multiplications commute:
     `c₁ * (c₂ * 1) = c₁ * c₂ = c₂ * c₁ = c₂ * (c₁ * 1)`.
   Hence LHS = RHS at every section.

   ## Recommended tactic proof

   1. `apply Iso.ext` — reduces to equality of the `.hom` morphisms.
   2. `apply PresheafOfModules.hom_ext` — reduces to each section `X : (Opens Y)ᵒᵖ`.
   3. `apply ModuleCat.hom_ext; ext φ` — reduces to an element `φ`.
   4. Unfold `dualUnitIsoGen`, `dualIsoOfIso` (via `dualPrecompEquiv`), `evalLin`,
      `unitDualSectionEquiv` (SliceTransport.lean L42) — the composition/application
      chain should expose the `mul_comm` identity.
   5. The key closing step is `mul_comm` (commutativity of `𝒪_Y(X)`) or equivalently
      `smul_comm` after converting between multiplication and scalar action.
      Alternatively `LinearMap.mul_apply` + `mul_comm` once both sides are in the form
      `c₁ * c₂` resp. `c₂ * c₁`.

   Alternative via `simp`/`ring` after sufficient unfolding if the scalar-multiplication
   form is exposed. The `Iso.trans_hom` / `Iso.trans_inv` simp lemmas + `Category.assoc`
   may help simplify the composite before unfolding.

   Useful API:
   - `PresheafOfModules.dualUnitIsoGen` (PresheafInternalHom.lean) = sectionwise eval-at-1.
   - `evalLin` (PresheafInternalHom.lean L889).
   - `dualPrecompEquiv` (PresheafInternalHom.lean L1033): `toFun φ = pushforward₀.map ŝ.hom ≫ φ`.
   - `unitDualSectionEquiv` (SliceTransport.lean L42): the eval-at-1 linear equiv.
   - `mul_comm` / `smul_comm` / `CommRing.mul_comm`.
   - `PresheafOfModules.hom_ext`, `ModuleCat.hom_ext`, `LinearMap.ext`.
   - `Iso.ext`, `Iso.trans_hom`.
-/
-/
lemma presheafDualUnitIso_naturality {Y : Scheme.{u}}
    (ŝ : 𝟙_ (_root_.PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) ≅
         𝟙_ (_root_.PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat))) :
    PresheafOfModules.dualIsoOfIso ŝ ≪≫ presheafDualUnitIso (Y := Y)
      = presheafDualUnitIso (Y := Y) ≪≫ ŝ := by
  apply Iso.ext
  apply PresheafOfModules.hom_ext
  intro X
  apply ModuleCat.hom_ext
  ext φ
  simp only [Iso.trans_hom, PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
  change PresheafOfModules.evalLin _ X
      ((PresheafOfModules.pushforward₀ (Over.forget (Opposite.unop X))
        (Y.presheaf ⋙ forget₂ CommRingCat RingCat)).map ŝ.hom ≫ φ)
        (1 : ((Y.presheaf ⋙ forget₂ CommRingCat RingCat).obj X : Type u))
    = (ŝ.hom.app X).hom (PresheafOfModules.evalLin _ X φ
        (1 : ((Y.presheaf ⋙ forget₂ CommRingCat RingCat).obj X : Type u)))
  -- The composite-section evaluation is definitionally the value of `φ` on the `ŝ`-image of `1`:
  -- `evalLin _ X (pushforward₀.map ŝ.hom ≫ φ) 1 = evalLin _ X φ ((ŝ.hom.app X).hom 1)`.
  change PresheafOfModules.evalLin _ X φ
      ((ŝ.hom.app X).hom (1 : ((Y.presheaf ⋙ forget₂ CommRingCat RingCat).obj X : Type u)))
    = (ŝ.hom.app X).hom (PresheafOfModules.evalLin _ X φ
        (1 : ((Y.presheaf ⋙ forget₂ CommRingCat RingCat).obj X : Type u)))
  -- Both `evalLin _ X φ` and `ŝ.hom.app X` are `𝒪_Y(X)`-linear endomorphisms of the regular
  -- module `𝒪_Y(X)`; commutativity of `𝒪_Y(X)` closes via `linearEndo_apply_comm`.
  exact linearEndo_apply_comm
    (PresheafOfModules.evalLin _ X φ) (ModuleCat.Hom.hom (ŝ.hom.app X))

/-- **The dual of the structure sheaf is the structure sheaf.** `dual 𝒪_Y ≅ 𝒪_Y`.
The presheaf-level dual of the monoidal unit `𝟙_` is the unit (evaluation at `1`),
sheafified and identified with the (already-sheaf) unit by the sheafification counit.
Mirrors `tensorObj_unit_iso` with the presheaf left unitor replaced by
`presheafDualUnitIso`. The third leg of the `dual_isLocallyTrivial` chain. -/
noncomputable def dual_unit_iso {Y : Scheme.{u}} :
    dual (SheafOfModules.unit Y.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).mapIso
      (presheafDualUnitIso (Y := Y)) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.val)).counit).app
      (SheafOfModules.unit Y.ringCatSheaf)

/-- **The dual of a locally-trivial `𝒪_X`-module is locally trivial.**

Blueprint `lem:dual_isLocallyTrivial` (~L5472).  If `L : X.Modules` satisfies
`LineBundle.IsLocallyTrivial L`, then `dual L` is also locally trivial.

/- Planner strategy:
   Blueprint label: lem:dual_isLocallyTrivial (~L5472).
   Uses (dual_restrict_iso is PARTIAL — Step-4 `isoMk` naturality sorry at ~L546; all other deps CLOSED):
     lem:internal_hom_isSheaf  → `Scheme.Modules.dual` (TensorObjSubstrate.lean ~L207)
     lem:dual_restrict_iso     → `dual_restrict_iso` (this file, §A above — PARTIAL, Step-4 sorry)
     def:scheme_modules_dual_iso_of_iso → `Scheme.Modules.dualIsoOfIso`
                                          (TensorObjSubstrate.lean ~L218)
     lem:restrictscalars_ringiso_dualequiv → `restrictScalarsRingIsoDualEquiv`
                                             (PresheafInternalHom.lean ~L234)

   Proof-sketch (blueprint §5.4, three-step chain):
   Unpack `hL : LineBundle.IsLocallyTrivial L`:  for each `x : X` choose an affine open
   `U` with `x ∈ U`, `IsAffineOpen U`, and `eL : L.restrict U.ι ≅ SheafOfModules.unit _`.
   It suffices to exhibit `(dual L).restrict U.ι ≅ SheafOfModules.unit _`.
   The three-step chain (blueprint §5.4):

   Step 1 — `dual_restrict_iso U.ι L`:
     `(dual L).restrict U.ι  ≅  dual (L.restrict U.ι)`

   Step 2 — `dualIsoOfIso eL` (contravariant):
     `dual (L.restrict U.ι)  ≅  dual (SheafOfModules.unit (U : Scheme).ringCatSheaf)`

   Step 3 — `dual_unit_iso` (the dual of the unit is the unit):
     `dual (SheafOfModules.unit _)  ≅  SheafOfModules.unit _`
     The dual of `𝒪_U` is `ℋom(𝒪_U, 𝒪_U) ≅ 𝒪_U` via evaluation-at-1; this should be
     derivable from `InternalHom.internalHomEval` (PresheafInternalHom.lean) + the
     presheaf-level left unitor `λ_ (𝟙_)`.

   Composing Steps 1–3 gives the trivialisation of `(dual L)|_U`.
   Since x was arbitrary, `dual L` is locally trivial.

   Implementation note: the pattern is identical to `tensorObj_isLocallyTrivial`
   (TensorObjSubstrate.lean ~L526), with `dual_restrict_iso` playing the role of
   `tensorObj_restrict_iso` and `dualIsoOfIso` the role of `tensorObjIsoOfIso`.
   Use `intro x; obtain ⟨U, hxU, hU_aff, ⟨eL⟩⟩ := hL x` to unpack, then
   `exact ⟨U, hxU, hU_aff, ⟨dual_restrict_iso U.ι L ≪≫ dualIsoOfIso eL ≪≫ dual_unit_iso⟩⟩`.
   `dual_unit_iso` is CLOSED axiom-clean (§B above); the chain is assembled and compiles,
   inheriting only the `dual_restrict_iso` Step-4 residual axiomatically.

   Named CLOSED base lemmas:
   - `Scheme.Modules.dualIsoOfIso` (TensorObjSubstrate.lean ~L218).
   - `dual_restrict_iso` (this file §A — must be proved first).
   - `SheafOfModules.unit` (Mathlib).
   - `InternalHom.internalHomEval` (PresheafInternalHom.lean) — for `dual_unit_iso`.
-/
-/
lemma dual_isLocallyTrivial {X : Scheme.{u}} {L : X.Modules}
    (hL : LineBundle.IsLocallyTrivial L) :
    LineBundle.IsLocallyTrivial (dual L) := by
  -- Mirrors `tensorObj_isLocallyTrivial`: trivialise the dual on each affine open `U`
  -- where `L` is trivial, via the three-step chain
  --   `(dual L)|_U ≅ dual (L|_U) ≅ dual 𝒪_U ≅ 𝒪_U`.
  intro x
  obtain ⟨U, hxU, hU_aff, ⟨eL⟩⟩ := hL x
  refine ⟨U, hxU, hU_aff, ⟨?_⟩⟩
  exact dual_restrict_iso U.ι L ≪≫ (dualIsoOfIso eL).symm ≪≫ dual_unit_iso

/-! ## §C. The A-bridge: compatible local morphisms glue to a global morphism -/

open Opposite TopologicalSpace in
/-- **The local section of the hom-sheaf manufactured from `f i`** (the load-bearing piece
of `homOfLocalCompat`, blueprint `localSection`).  Working with the underlying `Ab`-presheaves
`F = M.val.presheaf`, `G = N.val.presheaf`, the presheaf of types
`presheafHom F G` (`Mathlib.CategoryTheory.Sites.SheafHom`) sends an open `W` to the morphisms of
the restrictions of `F`, `G` to the slice `Over W`.  Its value at `U i` is built from the
components of `f i`, conjugated by `eqToHom` along the down-set identity
`(U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ V) = V` (valid for `V ≤ U i`).  The naturality field — the genuine
coherence risk — is automatic on the thin poset `Opens X` once the `eqToHom`-conjugation is
peeled, via `Subsingleton.elim` on the hom-sets. -/
noncomputable def homLocalSection {X : Scheme.{u}} {M N : X.Modules} {ι : Type*}
    (U : ι → X.Opens) (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι) (i : ι) :
    (CategoryTheory.presheafHom M.val.presheaf N.val.presheaf).obj (op (U i)) where
  app W :=
    haveI hle : W.unop.left ≤ U i := W.unop.hom.le
    haveI himg : (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W.unop.left) = W.unop.left := by
      simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hle
    M.val.presheaf.map (eqToHom (congrArg op himg.symm)) ≫
      ((PresheafOfModules.toPresheaf _).map (f i).val).app (op ((U i).ι ⁻¹ᵁ W.unop.left)) ≫
      N.val.presheaf.map (eqToHom (congrArg op himg))
  naturality := by
    intro A B φ
    have hBA : (unop B).left ≤ (unop A).left := ((Over.forget (U i)).map φ.unop).le
    let κ : (U i).ι ⁻¹ᵁ (unop B).left ⟶ (U i).ι ⁻¹ᵁ (unop A).left :=
      (Opens.map (U i).ι.base).map (homOfLE hBA)
    have himgA : (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ (unop A).left) = (unop A).left := by
      simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (unop A).hom.le
    have himgB : (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ (unop B).left) = (unop B).left := by
      simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr (unop B).hom.le
    -- naturality of the underlying ab-presheaf morphism of `f i`
    have hm := ((PresheafOfModules.toPresheaf _).map (f i).val).naturality κ.op
    -- the two thin-poset square edges agree (`Opens X` is a thin poset)
    have hsubM : ((Over.forget (U i)).map φ.unop).op ≫ eqToHom (congrArg op himgB.symm)
        = eqToHom (congrArg op himgA.symm) ≫ ((U i).ι.opensFunctor.map κ).op :=
      Subsingleton.elim _ _
    have hsubN : ((U i).ι.opensFunctor.map κ).op ≫ eqToHom (congrArg op himgB)
        = eqToHom (congrArg op himgA) ≫ ((Over.forget (U i)).map φ.unop).op :=
      Subsingleton.elim _ _
    -- M-side: the φ-restriction followed by the `eqToHom` is the `eqToHom` followed by `κ`
    have hML : M.val.presheaf.map ((Over.forget (U i)).map φ.unop).op ≫
          M.val.presheaf.map (eqToHom (congrArg op himgB.symm))
        = M.val.presheaf.map (eqToHom (congrArg op himgA.symm)) ≫
          (M.restrict (U i).ι).val.presheaf.map κ.op := by
      rw [(M.val.presheaf.map_comp _ _).symm, hsubM]
      exact M.val.presheaf.map_comp _ _
    -- N-side analogue
    have hNR : N.val.presheaf.map ((U i).ι.opensFunctor.map κ).op ≫
          N.val.presheaf.map (eqToHom (congrArg op himgB))
        = N.val.presheaf.map (eqToHom (congrArg op himgA)) ≫
          N.val.presheaf.map ((Over.forget (U i)).map φ.unop).op := by
      rw [(N.val.presheaf.map_comp _ _).symm, hsubN]
      exact N.val.presheaf.map_comp _ _
    dsimp only [Functor.comp_map, Functor.op_map, Functor.op_obj, Functor.comp_obj]
    rw [← Category.assoc, hML]
    erw [Category.assoc, reassoc_of% hm, hNR]
    simp only [Category.assoc]
    rfl

open Opposite TopologicalSpace in
/-- **Convert a section of `presheafHom F G` over the terminal open `⊤` into a global
morphism `F ⟶ G`.**  Since `⊤` is terminal in `Opens X`, the value of `presheafHom F G`
at `op ⊤` already determines a full compatible family of sections (each open's value is the
restriction of the top section), which `presheafHomSectionsEquiv` identifies with a morphism
`F ⟶ G`.  This is sub-step (b) of `homOfLocalCompat`. -/
noncomputable def topSectionToHom {X : TopCat.{u}}
    {F G : (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab.{u}}
    (s : (CategoryTheory.presheafHom F G).obj (op ⊤)) : F ⟶ G :=
  CategoryTheory.presheafHomSectionsEquiv F G
    ⟨fun W => (CategoryTheory.presheafHom F G).map (homOfLE le_top).op s, by
      intro W W' e
      dsimp only
      rw [← Functor.map_comp_apply]
      congr 1⟩

open Opposite TopologicalSpace in
/-- **Sectionwise value of `topSectionToHom`.**  At an open `W`, the recovered morphism
evaluates to the `Over.mk (homOfLE le_top)`-component of the top section `s`. -/
lemma topSectionToHom_app {X : TopCat.{u}}
    {F G : (TopologicalSpace.Opens X)ᵒᵖ ⥤ Ab.{u}}
    (s : (CategoryTheory.presheafHom F G).obj (op ⊤)) (W : (TopologicalSpace.Opens X)ᵒᵖ) :
    (topSectionToHom s).app W = s.app (op (Over.mk (homOfLE (le_top) : W.unop ⟶ ⊤))) := by
  obtain ⟨W⟩ := W
  exact CategoryTheory.presheafHom_map_app_op_mk_id (homOfLE le_top) s

open Opposite TopologicalSpace in
/-- **Down-set image identity.**  For `V ≤ W` (opens of a scheme `X`), the image under the
open immersion `W.ι` of the preimage of `V` is `V` again: `W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V`.  This is
the equality powering the `eqToHom`-conjugations in `homLocalSection`. -/
lemma image_preimage_of_le {X : Scheme.{u}} (W : X.Opens) {V : X.Opens} (hV : V ≤ W) :
    W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V := by
  simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr hV

set_option backward.isDefEq.respectTransparency false in
open Opposite TopologicalSpace in
/-- **A-bridge: compatible local `𝒪_X`-module morphisms glue to a global morphism.**

Blueprint `lem:sheafofmodules_hom_of_local_compat` (~L5592).  Let `X` be a scheme,
`M N : X.Modules`, and `{U i}` an indexed open cover of `X`.  If for each `i` we have a
morphism `f i : M.restrict (U i).ι ⟶ N.restrict (U i).ι` in `Scheme.Modules (U i)` such
that the underlying section maps of `f i` and `f j` agree, *sectionwise*, on every open
`V ≤ U i ⊓ U j` (each conjugated into the fixed abelian-group hom-type `M(V) ⟶ N(V)` by the
canonical `eqToHom`s from the down-set identity `ι(ι⁻¹V) = V`), then there is a unique global
morphism `M ⟶ N` in `X.Modules` whose restriction to each `U i` is `f i`.

The compatibility hypothesis `hf` is the **sectionwise** overlap-agreement (iter-254 re-sign;
this `def` is NOT in `archon-protected.yaml` and has no compiling caller, so the prover owns its
signature).  The earlier `HEq` form — comparing the two `Scheme.Modules.pullback`-images of
`f i`, `f j` along the two slice-restrictions — was *unsatisfiable*: those images live in
sheafifications of pullback presheaves along *different* morphisms, hence in only-isomorphic
(not propositionally equal) objects, so no `HEq`-elimination applies and no caller can produce
the datum.  The sectionwise form compares only the section maps, which live in the fixed group
`M(V) ⟶ N(V)`, and is exactly the data a caller (two local morphisms literally agreeing on
overlaps) has at hand.  See blueprint `lem:sheafofmodules_hom_of_local_compat` sub-step (a).

/- Planner strategy:
   Blueprint label: lem:sheafofmodules_hom_of_local_compat (~L5592).
   Uses (all CLOSED):
     def:scheme_modules_homMk → `Scheme.Modules.homMk` (TensorObjSubstrate.lean ~L598)
     lem:open_immersion_slice_sheaf_equiv → `Vestigial.overSliceSheafEquiv`
                                            (TensorObjSubstrate/Vestigial.lean ~L715)

   Proof-sketch (blueprint §5.4, two-step):

   Step (i) — Glue the underlying ab-sheaf morphism:
   Forget M, N to their underlying sheaves of abelian groups.  The presheaf
   `H(W) = Hom_{Ab-preshvs}(M.val.presheaf|_W, N.val.presheaf|_W)` is a sheaf of TYPES:
   this is `Presheaf.IsSheaf.hom` (Mathlib), consuming the sheaf condition of N.
   Convert each `f i` to a local section `s i ∈ H(U i)` via the open-immersion slice
   transport `overSliceSheafEquiv` (Vestigial.lean):
     - `s i` at a pair `(V, h : V ≤ U i)` is `(f i).val.app` at the corresponding open of
       `(U i : Scheme)`, conjugated by `eqToHom` identifications from the down-set identity
       `ι_i(ι_i⁻¹(V)) = V` for `V ≤ U i`.  The naturality of `s i` in V is the
       section-direction slice of `overSliceSheafEquiv` and is automatic on the thin poset
       `Opens X` by `Subsingleton.elim`.
   Apply `TopCat.Sheaf.existsUnique_gluing` (or `Presheaf.IsSheaf.existsUnique_gluing`) to
   amalgamate the compatible family `(s i)_i` into a unique global section
   `s ∈ H(⊤) = (M.val.presheaf ⟶ N.val.presheaf)`.
   Convert the amalgamated `s` to an ab-presheaf morphism `g : M.val.presheaf ⟶ N.val.presheaf`
   via `presheafHomSectionsEquiv` / `sheafHomSectionsEquiv`.

   Step (ii) — Promote to `𝒪_X`-linear via `homMk`:
   The linearity `g(r • m) = r • g(m)` holds on each `U i` (since `g|_{U i}` comes from
   the module morphism `f i`), and the two sides agree globally because the ambient presheaf
   is separated.  Apply `Scheme.Modules.homMk g (sectionwise-linearity proof)` to produce
   `M ⟶ N` in `X.Modules`.

   Key sub-lemma to build first (most fragile piece):
   The naturality field of `s i` — that the `eqToHom`-conjugated components of `f i` commute
   across morphisms of the slice `Over (U i)` — is dominated by `overSliceSheafEquiv` and
   should be extracted as a standalone axiom-clean lemma before the full gluing assembly.

   Named CLOSED base lemmas:
   - `Scheme.Modules.homMk` (TensorObjSubstrate.lean ~L598).
   - `Vestigial.overSliceSheafEquiv` (TensorObjSubstrate/Vestigial.lean ~L715).
   - `TopCat.Presheaf.IsSheaf.hom` (Mathlib) — hom into a sheaf is a sheaf.
   - `TopCat.Sheaf.existsUnique_gluing` (Mathlib) — gluing of compatible sections.
   - `presheafHomSectionsEquiv` / `sheafHomSectionsEquiv` (Mathlib) — top-section ↔ morphism.

   Implementation note: this is a MULTI-PIECE BUILD dominated by the `s i` naturality field.
   Build `s i` (and its naturality) as a standalone verified lemma FIRST, before assembling
   the full gluing.  The step does NOT invoke any tensor stalk — it is purely about gluing
   morphisms of sheaves.
-/
-/
noncomputable def homOfLocalCompat {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
        M.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U i) hVi).symm)) ≫
          ((PresheafOfModules.toPresheaf _).map (f i).val).app (op ((U i).ι ⁻¹ᵁ V)) ≫
            N.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U i) hVi)))
          = M.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U j) hVj).symm)) ≫
              ((PresheafOfModules.toPresheaf _).map (f j).val).app (op ((U j).ι ⁻¹ᵁ V)) ≫
                N.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U j) hVj)))) :
    M ⟶ N := by
  -- Step (i): glue the underlying ab-sheaf morphism.  The morphisms-presheaf
  -- `presheafHom M.val.presheaf N.val.presheaf` (`Mathlib.CategoryTheory.Sites.SheafHom`) is a
  -- sheaf of types because `N` is a sheaf (`Presheaf.IsSheaf.hom`, consuming `N.isSheaf`).
  let H : TopCat.Sheaf (Type u) (X : TopCat) :=
    ⟨CategoryTheory.presheafHom M.val.presheaf N.val.presheaf,
      Presheaf.IsSheaf.hom M.val.presheaf N.val.presheaf N.isSheaf⟩
  -- The cover `{U i}` exhausts `X`, so `iSup U = ⊤`.
  have hsup : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := hU x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  -- The compatible family `homLocalSection U f` (its naturality is the load-bearing field,
  -- proved axiom-clean above) glues via `existsUnique_gluing` to a unique global section of `H`
  -- over `iSup U = ⊤`.  `hglue` records the unique-gluing engine fed with these local sections;
  -- it still requires the `IsCompatible` datum, which is exactly the assumed overlap agreement
  -- `hf` (transported through `Vestigial.overSliceSheafEquiv`).
  have hglue := H.existsUnique_gluing U (fun i => homLocalSection U f i)
  -- (a) The cocycle / `IsCompatible` condition: the two restrictions of `homLocalSection i`
  -- and `homLocalSection j` to the overlap `U i ⊓ U j` agree as sections of `H`.
  have hcompat : TopCat.Presheaf.IsCompatible
      (CategoryTheory.presheafHom M.val.presheaf N.val.presheaf) U
      (fun i => homLocalSection U f i) := by
    intro i j
    refine NatTrans.ext (funext fun Z => ?_)
    obtain ⟨W⟩ := Z
    erw [presheafHom_map_app W.hom (TopologicalSpace.Opens.infLELeft (U i) (U j)) _ rfl,
        presheafHom_map_app W.hom (TopologicalSpace.Opens.infLERight (U i) (U j)) _ rfl]
    -- Unfold `homLocalSection` so the goal becomes the explicit sectionwise core equation:
    -- at the overlap open `V := W.left ≤ U i ⊓ U j`,
    --   LHS = `M.map (eqToHom ..) ≫ (f i).val.app (op ((U i).ι ⁻¹ᵁ V)) ≫ N.map (eqToHom ..)`
    --   RHS = `M.map (eqToHom ..) ≫ (f j).val.app (op ((U j).ι ⁻¹ᵁ V)) ≫ N.map (eqToHom ..)`,
    -- both in the FIXED `Ab` hom-type `M.val(V) ⟶ N.val(V)`.  With the sectionwise `hf` this is
    -- exactly `hf i j W.left _ _` (the `eqToHom`-conjugations match by definitional proof
    -- irrelevance; `(Over.mk (W.hom ≫ infLE_))​.left ≡ W.left` defeq).
    simp only [homLocalSection]
    exact hf i j W.left (W.hom.le.trans inf_le_left) (W.hom.le.trans inf_le_right)
  -- (b) Glue and convert the amalgamated `op ⊤`-section to an ab-presheaf morphism `g`.
  -- `∃!` is a `Prop`, so the glued section is extracted as a term via `.choose`; `hsup`
  -- transports it from `op (iSup U)` to the terminal `op ⊤` that `topSectionToHom` consumes.
  refine homMk (topSectionToHom (hsup ▸ (hglue hcompat).choose)) ?_
  -- (c) sectionwise `𝒪_X`-linearity of `g = topSectionToHom (glued section)`.  On each `U i`
  -- the glued section restricts to `homLocalSection U f i` (the `IsGluing` datum `_hs`), whose
  -- components come from the module morphism `f i`, so `g` is `𝒪_X`-linear on opens `≤ U i`;
  -- since `{U i}` covers `X` and `N.val.presheaf` is separated (`section_ext`), linearity
  -- propagates to every section.  CLOSED (iter-256), axiom-clean: the `section_ext` separatedness
  -- reduction, the naturality + `map_smul` reduction to local linearity, the `hconn` connection
  -- lemma identifying `g|_{U i}` with `homLocalSection i`, and the inner ring-bridge (native↔
  -- `restrictScalars 𝟙` smul bridge `hbridge`, from `Scheme.Opens.ι_appIso` +
  -- `ModuleCat.restrictScalars.smul_def'`) feeding the native f-leg linearity `hfl_native` are all
  -- in place below — no `sorry` remains in this declaration.
  have _hs := (hglue hcompat).choose_spec.1
  intro V r m
  -- Abbreviate the glued ab-presheaf morphism `g`.
  set g : M.val.presheaf ⟶ N.val.presheaf :=
    topSectionToHom (hsup ▸ (hglue hcompat).choose) with hg
  -- **Connection lemma.**  On every open `W' ≤ U i`, the glued morphism `g` agrees with the
  -- local section `homLocalSection U f i` manufactured from `f i` — this is the content of the
  -- `IsGluing` datum `_hs`, transported through the `iSup U = ⊤` identification and the
  -- `presheafHom`-restriction calculus.
  have hconn : ∀ (i : ι) (W' : X.Opens) (hWi : W' ≤ U i),
      g.app (op W') = (homLocalSection U f i).app (op (Over.mk (homOfLE hWi))) := by
    intro i W' hWi
    have htr : ∀ {a : X.Opens} (h : a = ⊤) (y : H.obj.obj (op a)),
        (h ▸ y : H.obj.obj (op ⊤)) = H.obj.map (eqToHom (congrArg op h)) y := by
      intro a h y; subst h; simp
    rw [hg, topSectionToHom_app, htr hsup]
    have hop : eqToHom (congrArg op hsup) = (eqToHom hsup.symm).op := Subsingleton.elim _ _
    have hgl : TopCat.Presheaf.IsGluing H.obj U (fun i => homLocalSection U f i)
        (hglue hcompat).choose := _hs
    have hsi : (ConcreteCategory.hom (H.obj.map (Opens.leSupr U i).op)) (hglue hcompat).choose
        = homLocalSection U f i := hgl i
    rw [hop, presheafHom_map_app (homOfLE le_top) (eqToHom hsup.symm)
        (homOfLE le_top ≫ eqToHom hsup.symm) rfl, ← hsi,
      presheafHom_map_app (homOfLE hWi) (Opens.leSupr U i)
        (homOfLE hWi ≫ Opens.leSupr U i) rfl]
    rw [show (homOfLE le_top ≫ eqToHom hsup.symm : W' ⟶ iSup U)
        = (homOfLE hWi ≫ Opens.leSupr U i) from Subsingleton.elim _ _]
  -- It suffices, by separatedness of the sheaf `N`, to check the linearity equation on a
  -- neighbourhood of each point; we use the cover member `U i` through the point.
  refine N.isSheaf.section_ext ?_
  intro x hx
  obtain ⟨i, hi⟩ := hU x
  refine ⟨V.unop ⊓ U i, inf_le_left, ⟨hx, hi⟩, ?_⟩
  -- Reduce both sides via naturality of `g` (so the outer `N`-restriction is absorbed into
  -- `g.app (op W)`) and the semilinearity of the `M`, `N` restriction maps (`map_smul`) to
  -- local linearity of `g` at `W := V.unop ⊓ U i ≤ U i`.
  set W : X.Opens := V.unop ⊓ U i with hWdef
  have hWV : W ≤ V.unop := inf_le_left
  erw [← NatTrans.naturality_apply g (homOfLE hWV).op (r • m),
      PresheafOfModules.map_smul M.val (homOfLE hWV).op r m,
      PresheafOfModules.map_smul N.val (homOfLE hWV).op r ((g.app V).hom m),
      ← NatTrans.naturality_apply g (homOfLE hWV).op m]
  -- `g` agrees on `W ≤ U i` with the local section manufactured from the module morphism `f i`;
  -- it remains to prove the `homLocalSection`-component is `X.ringCatSheaf(W)`-linear.
  rw [hconn i W inf_le_right]
  -- The component is the triple composite `M.map (eqToHom e₁) ≫ (f i).val.app P ≫ N.map (eqToHom e₂)`
  -- (`P = (U i).ι ⁻¹ᵁ W`).  Decompose it into the three legs.
  simp only [homLocalSection]
  -- The `homLocalSection`-component at `W` is the triple composite
  --   `Φ = M.val.map (eqToHom e₁) ≫ (f i).val.app P ≫ N.val.map (eqToHom e₂)`  (`P = (U i).ι ⁻¹ᵁ W`),
  -- an `Ab`-morphism `M(W) ⟶ N(W)`.  We must show `Φ (r' • m') = r' • Φ m'` for the structure
  -- scalar `r' = X.ringCatSheaf.map (homOfLE hWV).op r : X.ringCatSheaf(W)`.  Expose the three legs.
  erw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
       ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
       PresheafOfModules.toPresheaf_map_app_apply,
       PresheafOfModules.toPresheaf_map_app_apply]
  -- Push the scalar through the three legs.  We use the *Γ-level* `Scheme.Modules.map_smul`
  -- (which keeps the native `Γ(M, ·)`-module structure) rather than `PresheafOfModules.map_smul`
  -- (whose semilinear codomain introduces a `restrictScalars`-along-`eqToHom` module that does not
  -- match the `f`-leg's `restrictScalars 𝟙` action — `(U i).ι.appIso = Iso.refl`).
  -- (a) `M`-leg semilinearity (CLOSED): `M.map e₁ (r' • m') = (X.ring.map e₁ r') • M.map e₁ m'`,
  -- with the native `Γ(M, image)`-action on the right (no `restrictScalars` artifact).
  erw [Scheme.Modules.map_smul M]
  -- (b) `f`-leg `(U i)`-linearity is available as the term `hfl`: `(f i).val.app P` is
  -- `(U i).ringCatSheaf(P)`-linear.  Since `(U i).ι.appIso = Iso.refl`
  -- (`AlgebraicGeometry.Scheme.Opens.ι_appIso`), `(U i).ringCatSheaf(P) = Γ(X, image)` and the
  -- `(U i)`-action on `M.restrict (U i).ι` is `ModuleCat.restrictScalars 𝟙` of the native action.
  have hfl := ((f i).val.app (op ((U i).ι ⁻¹ᵁ
    (Over.mk (homOfLE (inf_le_right : W ≤ U i))).left))).hom.map_smul
  -- **Native↔`restrictScalars 𝟙` smul bridge** for any `K : X.Modules`.  The `(U i)`-action
  -- on `K.restrict (U i).ι` is `ModuleCat.restrictScalars` of the native `Γ(X, image)`-action
  -- along the structure-ring map `(forget₂ …).map ((U i).ι.appIso _).inv`, which is the identity
  -- because `(U i).ι.appIso = Iso.refl` (`AlgebraicGeometry.Scheme.Opens.ι_appIso`).
  have hbridge : ∀ (K : X.Modules) (c : Γ(X, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W))
      (y : Γ(K, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W)),
      (c • y : Γ(K, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W))
        = (c • (show ↑((K.restrict (U i).ι).val.obj (op ((U i).ι ⁻¹ᵁ W))) from y)) := by
    intro K c y
    erw [ModuleCat.restrictScalars.smul_def']
    simp [AlgebraicGeometry.Scheme.Opens.ι_appIso]
    rfl
  -- **Native `Γ(X, image)`-linearity of the `f`-leg**, bridged from `hfl` via `hbridge`.
  have hfl_native : ∀ (c : Γ(X, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W))
      (y : Γ(M, (U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W)),
      (ConcreteCategory.hom ((f i).val.app (op ((U i).ι ⁻¹ᵁ W)))) (c • y)
        = c • (ConcreteCategory.hom ((f i).val.app (op ((U i).ι ⁻¹ᵁ W)))) y := by
    intro c y
    rw [hbridge M c y]
    erw [hfl]
    rfl
  -- (c) `N`-leg semilinearity (native), pulling the structure scalar back out.
  erw [hfl_native, Scheme.Modules.map_smul N]
  -- (d) reconcile the `eqToHom`-transported scalars: the two down-set comparison maps `e₁, e₂`
  -- compose (through the identity `(U i).ι.appIso`) to `𝟙` on `Γ(X, image)`, since
  -- `(U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ W) = W`; on the thin poset `Opens X` this is `Subsingleton.elim`.
  congr 1
  simp only [homOfLE_leOfHom, Over.forget_obj, Over.mk_left, Functor.op_obj, sheafCompose_obj_obj,
    Functor.comp_obj, CommRingCat.forgetToRingCat_obj, ObjectProperty.ι_obj, op_unop,
    Opens.ι_appIso, Iso.refl_inv, Functor.whiskerRight_app, CommRingCat.forgetToRingCat_map_hom,
    RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
    Functor.comp_map, ZeroHom.coe_mk]
  rw [← X.presheaf.map_id (op ((U i).ι ''ᵁ (U i).ι ⁻¹ᵁ W))]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp]
  refine (ConcreteCategory.congr_hom (congrArg X.presheaf.map
    (Subsingleton.elim _ (𝟙 (op W)))) _).trans ?_
  rw [X.presheaf.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
open Opposite TopologicalSpace in
/- Planner strategy:
   The glued global morphism `homOfLocalCompat U hU f hf` is built as
   `homMk (topSectionToHom (hsup ▸ (hglue hcompat).choose)) _`
   whose underlying ab-presheaf morphism is `topSectionToHom` of a glued section.
   Its restriction to `U i` recovers the local datum `homLocalSection U f i` — exactly
   the internal `IsGluing` datum exploited in `homOfLocalCompat`'s body at L514–551
   (`topSectionToHom_app`, `htr hsup`, `hgl : IsGluing … (hglue hcompat).choose`, `hsi`).

   Route:
   - `apply Scheme.Modules.hom_ext` (sectionwise equality of module morphisms).
   - Reuse `topSectionToHom_app` + the `IsGluing` restriction
     `hgl i : (H.obj.map (Opens.leSupr U i).op) (hglue hcompat).choose = homLocalSection U f i`,
     mirroring the `hconn` argument at L534–551.
   - `homMk`/`topSectionToHom` are sectionwise faithful, so agreement of the underlying
     ab-presheaf morphisms suffices.
   - ~40–80 LOC when proved (next prover lane fills the sorry this iter).
-/
lemma homOfLocalCompat_restrictFunctor_map {X : Scheme.{u}} {M N : X.Modules}
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hf : ∀ (i j : ι) (V : X.Opens) (hVi : V ≤ U i) (hVj : V ≤ U j),
        M.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U i) hVi).symm)) ≫
          ((PresheafOfModules.toPresheaf _).map (f i).val).app (op ((U i).ι ⁻¹ᵁ V)) ≫
            N.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U i) hVi)))
          = M.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U j) hVj).symm)) ≫
              ((PresheafOfModules.toPresheaf _).map (f j).val).app (op ((U j).ι ⁻¹ᵁ V)) ≫
                N.val.presheaf.map (eqToHom (congrArg op (image_preimage_of_le (U j) hVj))))
    (i : ι) :
    (Scheme.Modules.restrictFunctor (U i).ι).map (homOfLocalCompat U hU f hf) = f i := by
  -- Reconstruct the gluing internals of `homOfLocalCompat` (identical to its body), so that the
  -- underlying ab-presheaf morphism `g` of `homOfLocalCompat` is `topSectionToHom (glued section)`.
  let H : TopCat.Sheaf (Type u) (X : TopCat) :=
    ⟨CategoryTheory.presheafHom M.val.presheaf N.val.presheaf,
      Presheaf.IsSheaf.hom M.val.presheaf N.val.presheaf N.isSheaf⟩
  have hsup : iSup U = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := hU x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  have hglue := H.existsUnique_gluing U (fun i => homLocalSection U f i)
  have hcompat : TopCat.Presheaf.IsCompatible
      (CategoryTheory.presheafHom M.val.presheaf N.val.presheaf) U
      (fun i => homLocalSection U f i) := by
    intro i j
    refine NatTrans.ext (funext fun Z => ?_)
    obtain ⟨W⟩ := Z
    erw [presheafHom_map_app W.hom (TopologicalSpace.Opens.infLELeft (U i) (U j)) _ rfl,
        presheafHom_map_app W.hom (TopologicalSpace.Opens.infLERight (U i) (U j)) _ rfl]
    simp only [homLocalSection]
    exact hf i j W.left (W.hom.le.trans inf_le_left) (W.hom.le.trans inf_le_right)
  -- The glued underlying ab-presheaf morphism `g` (defeq to `(homOfLocalCompat …).val`'s presheaf).
  set g : M.val.presheaf ⟶ N.val.presheaf :=
    topSectionToHom (hsup ▸ (hglue hcompat).choose) with hg
  have _hs := (hglue hcompat).choose_spec.1
  -- **Connection lemma** (identical to `homOfLocalCompat` body L534–551): on every `W' ≤ U i`,
  -- `g` agrees with the local section manufactured from `f i`.
  have hconn : ∀ (i : ι) (W' : X.Opens) (hWi : W' ≤ U i),
      g.app (op W') = (homLocalSection U f i).app (op (Over.mk (homOfLE hWi))) := by
    intro i W' hWi
    have htr : ∀ {a : X.Opens} (h : a = ⊤) (y : H.obj.obj (op a)),
        (h ▸ y : H.obj.obj (op ⊤)) = H.obj.map (eqToHom (congrArg op h)) y := by
      intro a h y; subst h; simp
    rw [hg, topSectionToHom_app, htr hsup]
    have hop : eqToHom (congrArg op hsup) = (eqToHom hsup.symm).op := Subsingleton.elim _ _
    have hgl : TopCat.Presheaf.IsGluing H.obj U (fun i => homLocalSection U f i)
        (hglue hcompat).choose := _hs
    have hsi : (ConcreteCategory.hom (H.obj.map (Opens.leSupr U i).op)) (hglue hcompat).choose
        = homLocalSection U f i := hgl i
    rw [hop, presheafHom_map_app (homOfLE le_top) (eqToHom hsup.symm)
        (homOfLE le_top ≫ eqToHom hsup.symm) rfl, ← hsi,
      presheafHom_map_app (homOfLE hWi) (Opens.leSupr U i)
        (homOfLE hWi ≫ Opens.leSupr U i) rfl]
    rw [show (homOfLE le_top ≫ eqToHom hsup.symm : W' ⟶ iSup U)
        = (homOfLE hWi ≫ Opens.leSupr U i) from Subsingleton.elim _ _]
  -- Sectionwise reduction.
  apply SheafOfModules.Hom.ext
  refine PresheafOfModules.hom_ext (fun P => ?_)
  obtain ⟨P⟩ := P
  apply ModuleCat.hom_ext
  ext m
  -- The LHS section value is (defeq) the glued morphism `g` at the open `(U i).ι ''ᵁ P`.
  have hWi : (U i).ι ''ᵁ P ≤ U i := (U i).ι_image_le P
  -- **Local-section value at an image open** recovers `f i`: the eqToHom-conjugation collapses to
  -- the identity, since `(U i).ι ⁻¹ᵁ ((U i).ι ''ᵁ P) = P` for the open immersion `(U i).ι`.
  have key : (homLocalSection U f i).app (op (Over.mk (homOfLE hWi)))
      = ((PresheafOfModules.toPresheaf (U i).toScheme.ringCatSheaf.obj).map (f i).val).app
          (op P) := by
    simp only [homLocalSection, Over.mk_left, homOfLE_leOfHom]
    -- The two flanking `M`/`N` restriction maps are `eqToHom`s of the down-set identity; the goal
    -- is an `eqToHom`-conjugation of the natural transformation `(toPresheaf).map (f i).val`, which
    -- the naturality square (for `(U i).ι ⁻¹ᵁ ((U i).ι ''ᵁ P) = P`) collapses to the identity.
    simp only [eqToHom_map]
    have hh : (op ((U i).ι ⁻¹ᵁ ((U i).ι ''ᵁ P)) : (TopologicalSpace.Opens ↥(U i).toScheme)ᵒᵖ)
        = op P := congrArg op ((U i).ι.preimage_image_eq P)
    rw [eqToHom_comp_iff]
    have hnat := ((PresheafOfModules.toPresheaf (U i).toScheme.ringCatSheaf.obj).map
      (f i).val).naturality (eqToHom hh)
    simp only [eqToHom_map] at hnat
    exact hnat.symm
  change (ConcreteCategory.hom (g.app (op ((U i).ι ''ᵁ P)))) m
    = (ModuleCat.Hom.hom ((f i).val.app (op P))) m
  rw [hconn i ((U i).ι ''ᵁ P) hWi, key]
  rfl

end Modules

end Scheme

end AlgebraicGeometry
