/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.Picard.TensorObjSubstrate.StalkTensor
import AlgebraicJacobian.Picard.TensorObjSubstrate.Vestigial
import AlgebraicJacobian.Picard.TensorObjSubstrate.PresheafInternalHom
import AlgebraicJacobian.Picard.LineBundlePullback

/-!
# The `Scheme.Modules.tensorObj` substrate (A.1.c.SubT)

This file is the **A.1.c.SubT** file-skeleton sub-build chapter for the
positive-genus arm of `nonempty_jacobianWitness`. It records the dedicated
substrate on which the abelian-group instance of the relative Picard quotient
`Pic^♯_{C/k}(T) := Pic(C ×_k T) / π_T^* Pic(T)` rests (the residual `sorry`
of `AlgebraicJacobian/Picard/RelPicFunctor.lean`).

The mathematics is straightforward; the obstacle to formalisation is purely
infrastructural. The Lean construction of the abelian-group law
`[L] + [L'] := [L ⊗ L']` on isomorphism classes of line bundles requires three
ingredients on the Lean carrier:

1. a binary tensor-product operation
   `⊗ : Scheme.Modules X × Scheme.Modules X → Scheme.Modules X`;
2. the structure sheaf `O_X` as a designated unit object for `⊗`;
3. an inverse operation on the full subcategory of invertible objects, i.e.
   the dual `L⁻¹ = Hom(L, O_X)` of an invertible sheaf.

At Mathlib's pinned commit (`b80f227`), only a presheaf-level version of (1)
is available (`PresheafOfModules.Monoidal.tensorObj`); (2) and (3) are present
as scheme-level objects, but the binary operation in (1) that ties them
together at the `Scheme.Modules` level is missing, and there is no
`MonoidalCategory` instance on `Scheme.Modules X`. This file records the
project-side substrate that supplies (1) and consequently lifts (2) + (3)
into a monoidal-category structure on `Scheme.Modules X`.

## Status (current)

`tensorObj` and `tensorObj_functoriality` are fully defined (no `sorry`), lifting
`PresheafOfModules.Monoidal.tensorObj` through sheafification on the small Zariski
site. There are now TWO tracked typed-`sorry` residuals:
1. (deferred) `⊗`-inverse lane (`exists_tensorObj_inverse`, ~L697, cross-file gated —
   closes via the dual chain in `DualInverse.lean`).
2. (seed-1, active, iter-020) `pullbackTensorIsoOfLocallyTrivial` (~L4001, D4′ comparison
   iso — prover closes next via the `isIso_of_isIso_restrict` chart-chase).
The D3′ Sq4 per-leg brick
`pullbackValIso_comp_leg` (the `pullbackValIso` composition coherence) is **CLOSED axiom-clean
(iter-019+)** — see below — so the ENTIRE D3′ cone is sorry-free except the import-cycle-deferred
inverse.  It is proved by reducing to the sheaf-level cocycle `hH` (factoring out the leading
sheafification unit/forget via `comp_forget_cocycle`), then assembling `hH` from the inverted Sq1
(`sheafificationCompPullback_comp_inv`, via the generic `inv_telescope`), `pullbackComp` naturality,
`sheafificationCompPullback h` naturality, and the adjunction triangle `adj_unit_map_counit`, all
glued by the generic `cocycle_assemble` (every carrier-boundary `≫` crossed by `exact`, never
`rw/erw [Category.assoc]`).
**`pullbackTensorMap_restrict` (D3′) is now FULLY CLOSED (iter-019+).**
Its steps (i) [`comp_cancel_mid`+`exact`] and (ii) [`sheafifyMap_δcomp_split` δ-split] were CLOSED
(iters-015/016), STEP (iii)a [`comp_slide_nested` `S1^h` slide] iter-017, (iii)b.1/(iii)b.2
[`comp_cancel_three_lr` + `comp_slide_three`/`map_comp_slide`] iter-018, and STEP (iii)b.3 — the
**folded Sq3/Sq4 presheaf core `hcore2`** — is CLOSED iter-018: fold each side into one `a_Z.map Ψ`
via `sheafifyTensorUnitIso_hom_eq'` + the generic merge `map_comp4_eq_comp5`; `congr 1` to the presheaf
identity `Ψ_L = Ψ_R`; close it by δ-naturality of `δ_h` at `gg` (a CONCRETE `have hδnat := δ_natural`
spliced by `← reassoc_of%` — never `erw [reassoc_of% δ_natural]`, which whnf-bombs on metavar
re-synthesis), bifunctoriality (the generic `tensorHom_collapse_3_4`), reducing to the two
structurally-identical per-leg `pullbackValIso` coherences `pullbackValIso_comp_leg h f M`/`… N`.
That single brick (= blueprint `lem:pullback_val_iso_comp`; pVI-factorisation chase via the proven Sq1
`sheafificationCompPullback_comp` + counit naturality across `pullbackComp h f`) is the SOLE remaining
sorry of the whole D3′ cone; its body has the `pullbackValIso`-unfold spliced as partial progress.
The D3′ Sq1 sub-lemma
`sheafificationCompPullback_comp` is CLOSED (iter earlier).  **D1′ (`pullbackTensorMap_natural`) is CLOSED
axiom-clean (iter-255)** via the mapin255 LIGHT `show…from` `δ_natural` `F`-ascription
(Sq2) plus the `.val`/`.obj` `erw`/`refine`-isDefEq Sq3/Sq4 assembly (see its proof
below).  **STEP A — the D1′-helper
`sheafifyTensorUnitIso_hom_natural` — is CLOSED axiom-clean (iter-254)** via the tscmp254
`tensorHom`-pin: `sheafifyTensorUnitIso_hom_eq'` states the comparison as ONE `a.map (η ⊗ η)`
(single monoidal instance on the `⋙ forget₂` carrier), and the naturality reduces to
bifunctoriality (`tensorHom_comp_tensorHom`, applied as a defeq-matched TERM with explicit
`(C := …)` to bridge the non-canonical instance) + the two single-component unit squares.
**D2′ is CLOSED axiom-clean** (iter-250):
the unit-square `(∗∗)` presheaf residual inside `pullbackEtaUnitSquare` is discharged,
so `pullbackEtaUnitSquare` → `pullbackTensorMap_unit_isIso` are sorry-free
(`pullbackTensorMap_unit_isIso` verified axiom-clean: only `propext`/`Classical.choice`/
`Quot.sound`). The `(∗∗)` close is the assembly of three project lemmas — the Y-side
sheafification right-triangle `pullbackSheafifyUnitEtaTriangle`, the presheaf mate
`presheafUnit_comp_map_eta`, and the step-7 `ε`-reconciliation `epsilonPresheafToSheafUnit`
(both sides act sectionwise as `φ.hom.app X`) — after the substep-(i) `.val` reshaping and a
SYNTACTIC `restrictScalars (𝟙)`-strip via the project lemma `restrictScalarsId_map` (stripping
`restrictScalars (𝟙)` by `whnf`/`show` on the sheafification-laden composites is catastrophic;
the propositional rewrite + `erw` reassociation sidesteps it). The whole abstract mate-calculus
telescope (steps 1–6: `homEquiv` transposition, `compHomEquivFactor`/`leftAdjointUniqUnitEta` via
`hkey`, the two `homEquiv_naturality` folds, the X-side triangle `hXtri`, the X-side `homEquiv`
collapse `hrhs`) is upstream of the close. (The route-(e)
whiskering residual `isLocallyInjective_whiskerLeft_of_W` was CLOSED iter-237 in
`Vestigial.lean`, so `tensorObj_assoc_iso` is now unconditional and axiom-clean.)
The dual-block is now
complete axiom-clean: the value layer (`InternalHom.internalHom`, `dual`,
`evalLin`/`internalHomEvalApp`) plus the evaluation morphism `internalHomEval`
(its naturality CLOSED iter-224, see below). The consumer `PicSharp.addCommGroup`
was rewired downstream in `RelPicFunctor.lean` (iter-247).

iter-224 on `internalHomEval`'s naturality: CLOSED axiom-clean. The iter-222/223 `whnf`
heartbeat-bomb diagnosis (the codomain `𝟙_` forcing `kabstract` to whnf the monoidal-unit
machinery on the first rewrite) was STALE — a Mathlib update made the composition split cleanly
with `erw [ModuleCat.hom_comp, …]`, after which the six-step `evalLin`/`naturality_apply`/`hdt`
reduction goes through with no bomb, no `with_reducible`, and no `maxHeartbeats` bump.

The 2 blueprint-pinned declarations are:

1. `AlgebraicGeometry.Scheme.Modules.tensorObj` (def) — the substrate binary
   operation `⊗ : Scheme.Modules X × Scheme.Modules X → Scheme.Modules X`,
   lifting `PresheafOfModules.Monoidal.tensorObj` on underlying presheaves
   composed with sheafification on the small Zariski site.
   Per blueprint `def:scheme_modules_tensorobj`.

2. `AlgebraicGeometry.Scheme.Modules.tensorObj_functoriality` (def) — the
   functorial action of `⊗` on morphisms: a pair `f : M ⟶ M'`, `g : N ⟶ N'`
   determines `f ⊗ g : tensorObj M N ⟶ tensorObj M' N'`.
   Per blueprint `lem:scheme_modules_tensorobj_functoriality`.

(A full `MonoidalCategory (Scheme.Modules X)` instance is **deliberately not
built** — see §2 and blueprint `rem:scheme_modules_monoidal_off_path`. The group
law on iso-classes consumes only the *existence* of the three coherence
isomorphisms, never a coherent monoidal category, so no such instance is on the
critical path.)

The consumer `tensorObjOnProduct` and the `addCommGroup_via_tensorObj` stub now
live downstream in `RelPicFunctor.lean` (iter-247 import-cycle fix).

Plus (PUSH-BEYOND) the supporting helper lemmas of the lift section
(`lem:tensorobj_preserves_locally_trivial`,
`lem:tensorobj_inverse_invertible`, `lem:tensorobj_lift_onproduct`,
`lem:pullback_compatible_with_tensorobj`).

## References

Blueprint: `blueprint/src/chapters/Picard_TensorObjSubstrate.tex` (740 LOC,
4 pins). Source: [Kleiman], "The Picard scheme", §2 (FGA Explained Ch.9 §9.2),
Defs. `df:aPf` + `df:Pfs`; Stacks tags 01CR (Picard group), 03DM (relative
tensor product of `O_X`-modules). Mathlib module
`Mathlib.CategoryTheory.Monoidal.PresheafOfModules`
(`PresheafOfModules.Monoidal.tensorObj`).

## Sub-module layout (iter-232 split)

The 2375-line monolith was split into sub-files under
`AlgebraicJacobian/Picard/TensorObjSubstrate/` (all imported by this file):

- `StalkTensor.lean` — the d.2 ingredient `stalkTensorIso` (`(A⊗ᵖB).stalk ≅ A.stalk ⊗ B.stalk`).
- `Vestigial.lean` — quarantined vestigial/route-(e) sections:
  `FlatWhisker`/`WhiskerOfW` (the route-(e) whisker sorry was CLOSED iter-237;
  `isIso_sheafification_map_of_W` lives here), `StalkLinearMap`, `OverSliceSheafEquiv`.
- `PresheafInternalHom.lean` — foundational presheaf algebra + C-bridge substrate:
  `RestrictScalarsRingIsoTensor`, lax-monoidal `restrictScalars`, pushforward
  adjunction (H1), `StrongMonoidalRestrictScalars` (H2), `InternalHom`, `Dual`.
- `TensorObjSubstrate.lean` (this file) — public API:
  `Scheme.Modules.tensorObj`, unitors/braiding/assoc, `tensorObj_restrict_iso`,
  `isIso_of_isIso_restrict`, `homMk`, `exists_tensorObj_inverse` (sorry, deferred),
  `pullbackTensorIsoOfLocallyTrivial` (sorry, seed-1 active iter-020).
  Consumer `tensorObjOnProduct` and the `addCommGroup_via_tensorObj` stub now live
  downstream in `RelPicFunctor.lean` (iter-247 import-cycle fix).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry

namespace Scheme

namespace Modules

/-! ## §1. The substrate tensor-product operation -/

/-- **The substrate operation `⊗` on `Scheme.Modules X`.**

For a scheme `X` and `M, N : X.Modules`, the tensor product
`M ⊗_X N : X.Modules` is the sheafification of the presheaf-of-modules tensor
product `PresheafOfModules.Monoidal.tensorObj` of the underlying presheaves of
`M` and `N` (affine-locally `(M ⊗_X N)(Spec A) = M(Spec A) ⊗_A N(Spec A)`).

Per blueprint `def:scheme_modules_tensorobj`. The body lifts
`PresheafOfModules.Monoidal.tensorObj` through the sheafification functor on
the small Zariski site of `X` (fully defined, no `sorry`). -/
noncomputable def tensorObj {X : Scheme.{u}} (M N : X.Modules) : X.Modules :=
  ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).obj
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val N.val) :
    SheafOfModules X.ringCatSheaf)

/-- **Functoriality of `⊗_X`.**

A pair of morphisms `f : M ⟶ M'` and `g : N ⟶ N'` in `X.Modules` determines a
morphism `f ⊗ g : tensorObj M N ⟶ tensorObj M' N'`, compatible with identities
and composition; the assignment `(M, N) ↦ tensorObj M N` thereby extends to a
bifunctor `X.Modules × X.Modules ⥤ X.Modules` natural in both arguments.

Per blueprint `lem:scheme_modules_tensorobj_functoriality`. The body inherits
the morphism action from `PresheafOfModules.Monoidal.tensorObj` under
sheafification (fully defined, no `sorry`). -/
noncomputable def tensorObj_functoriality {X : Scheme.{u}} {M M' N N' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') : tensorObj M N ⟶ tensorObj M' N' :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).map
    (MonoidalCategory.tensorHom
      (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) f.val g.val)

/-- **`⊗`-invertibility of an `𝒪_X`-module.** (Blueprint
`def:scheme_modules_isinvertible`.) `M : X.Modules` is `⊗`-invertible when it
admits a tensor inverse: an object `N` with `M ⊗_X N ≅ 𝒪_X`, where
`𝒪_X = SheafOfModules.unit X.ringCatSheaf` is the designated unit. This is the
scheme-level analogue of Mathlib's `Module.Invertible`; the predicate carries its
inverse witness existentially, so the dual needed by the relative Picard group
law is definitional. -/
def IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∃ N : X.Modules, Nonempty (tensorObj M N ≅ SheafOfModules.unit X.ringCatSheaf)

/-- **The sheaf-level dual `M^∨ := ℋom_{𝒪_X}(M, 𝒪_X)`** of an `𝒪_X`-module.

For a scheme `X` and `M : X.Modules`, the dual `dual M : X.Modules` is the
sheafification of the presheaf-of-modules dual `PresheafOfModules.dual` of the
underlying presheaf of `M` (the internal hom into the structure presheaf,
`M^∨(U) = ℋom_{𝒪_X|_U}(M|_U, 𝒪_X|_U)`).

Construction = the **exact dual analogue of `tensorObj`** (this file, `tensorObj`):
apply the sheafification functor `PresheafOfModules.sheafification (𝟙 …)` on the
small Zariski site of `X` to the (axiom-clean, sub-step-3) presheaf dual
`PresheafOfModules.dual M.val`. The scheme's structure presheaf `X.presheaf` is
`CommRingCat`-valued over the single-universe topological site `Opens X`, hence is
exactly the base `R₀ : Dᵒᵖ ⥤ CommRingCat.{u}` that `PresheafOfModules.dual`
requires (the value `M^∨(U) = M|_U ⟶ R|_U` is an `R(U)`-module, needing
commutativity) — no CommRingCat/RingCat re-bridging is needed, since
`tensorObj` already takes `(R := X.presheaf)` over the same CommRingCat presheaf
and `X.ringCatSheaf.val = X.presheaf ⋙ forget₂ CommRingCat RingCat` definitionally.

The sheafification functor already lands in `SheafOfModules`, so no manual
`Presheaf.IsSheaf` / sheaf-condition descent is needed (sheafifying an already-sheaf
gives an iso object; this is the file's convention, matching `tensorObj`).

Per blueprint `lem:internal_hom_isSheaf` (§`sec:tensorobj_dual_infra`); Stacks
tags 01CM (internal hom into a sheaf is a sheaf) / 01CR item 2. This is the
`⊗`-inverse candidate of an invertible sheaf, feeding `exists_tensorObj_inverse`. -/
noncomputable def dual {X : Scheme.{u}} (M : X.Modules) : X.Modules :=
  ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).obj
      (PresheafOfModules.dual (R₀ := X.presheaf) M.val) :
    SheafOfModules X.ringCatSheaf)

/-- **The sheaf-level dual is contravariantly functorial in isomorphisms.** An isomorphism
`e : M ≅ M'` in `X.Modules` induces `dual M' ≅ dual M`, obtained by sheafifying the presheaf-level
dual iso `PresheafOfModules.dualIsoOfIso` of the underlying presheaf isomorphism. This is the
reusable "dual respects isos" ingredient (the dual analogue of `tensorObjIsoOfIso`) feeding the
assembly of `dual_isLocallyTrivial`: a trivialisation `L.restrict f ≅ 𝒪` yields, contravariantly,
`dual 𝒪 ≅ dual (L.restrict f)`. -/
noncomputable def dualIsoOfIso {X : Scheme.{u}} {M M' : X.Modules} (e : M ≅ M') :
    dual M' ≅ dual M :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).mapIso
    (PresheafOfModules.dualIsoOfIso (R₀ := X.presheaf)
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e))

/-! ## §2. (Off the critical path) the full monoidal-category structure

iter-206 PIVOT: the full `MonoidalCategory (X.Modules)` instance is
**deliberately not built**. Per blueprint `rem:scheme_modules_monoidal_off_path`,
the relative Picard group law is a structure on *isomorphism classes* of line
bundles — every group axiom is a `Nonempty (… ≅ …)` proposition, so no monoidal
coherence (pentagon/triangle/hexagon) and no `MonoidalClosed` structure is ever
consumed. The earlier `monoidalCategory := sorry` instance (and the two
localization-transport supplements `isMonoidal_W_of_whiskerLeft`,
`monoidalCategoryOfIsMonoidalW`) routed through the verified-absent
`MonoidalClosed (PresheafOfModules R₀)` wall; they are removed here. The group
law is built directly on the line-bundle subcategory from the four
existence-of-iso lemmas below, mirroring Mathlib's `CommRing.Pic`. -/

/-! ## §3. The lift through `LineBundle.OnProduct` (PUSH-BEYOND supporting lemmas)

The following helper lemmas record the lift of the substrate to the
locally-trivial subcategory used by the relative Picard consumer. They are not
`\lean{...}`-pinned in the blueprint (their statements are descriptive); the
typed signatures here scaffold the iter-203+ bodies. -/

/-- **The substrate operation respects isomorphisms in both arguments.**

A pair of isomorphisms `e : M ≅ M'` and `e' : N ≅ N'` in `X.Modules` induces an
isomorphism `tensorObj M N ≅ tensorObj M' N'`, obtained by sheafifying the
tensor product (in the presheaf-of-modules monoidal category) of the underlying
presheaf isomorphisms `e.val`, `e'.val`. Its `hom` is
`tensorObj_functoriality e.hom e'.hom`. This is the reusable functor-of-isos
ingredient feeding `tensorObj_isLocallyTrivial`. -/
noncomputable def tensorObjIsoOfIso {X : Scheme.{u}} {M M' N N' : X.Modules}
    (e : M ≅ M') (e' : N ≅ N') : tensorObj M N ≅ tensorObj M' N' :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).mapIso
    (MonoidalCategory.tensorIso
      (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e)
      ((SheafOfModules.forget X.ringCatSheaf).mapIso e'))

/-- **The substrate tensor of the structure sheaf with itself is the structure
sheaf.**

`tensorObj 𝒪_X 𝒪_X ≅ 𝒪_X`, where `𝒪_X = SheafOfModules.unit X.ringCatSheaf` is the
designated unit object. Built from the presheaf-level left unitor
`λ_ (𝟙_)` (the unit of the `PresheafOfModules` monoidal category is exactly
`SheafOfModules.unit.val`) under sheafification, composed with the
sheafification-adjunction counit isomorphism on the (already-sheaf) unit. -/
noncomputable def tensorObj_unit_iso {X : Scheme.{u}} :
    tensorObj (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf)
      ≅ SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).mapIso
      (λ_ (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).counit).app
      (SheafOfModules.unit X.ringCatSheaf)

/-- **Left unitor for `⊗_X`.** `𝒪_X ⊗_X M ≅ M`. (Blueprint
`lem:tensorobj_unit_iso`, left half, `AlgebraicGeometry.Scheme.Modules.tensorObj_left_unitor`.)
Sheafification of the presheaf-level left unitor `λ_ M.val`, composed with the
sheafification counit identifying `sheafification M.val` with the (already-sheaf)
`M`. The cheap `mapIso` pattern; uses no abstract pullback. -/
noncomputable def tensorObj_left_unitor {X : Scheme.{u}} (M : X.Modules) :
    tensorObj (SheafOfModules.unit X.ringCatSheaf) M ≅ M :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).mapIso
      ((PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)).leftUnitor M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).counit).app M

/-- **Right unitor for `⊗_X`.** `M ⊗_X 𝒪_X ≅ M`. (Blueprint
`lem:tensorobj_unit_iso`, right half, `AlgebraicGeometry.Scheme.Modules.tensorObj_right_unitor`.)
Sheafification of the presheaf-level right unitor `ρ_ M.val`, composed with the
sheafification counit. -/
noncomputable def tensorObj_right_unitor {X : Scheme.{u}} (M : X.Modules) :
    tensorObj M (SheafOfModules.unit X.ringCatSheaf) ≅ M :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).mapIso
      ((PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)).rightUnitor M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).counit).app M

/-- **Braiding for `⊗_X`.** `M ⊗_X N ≅ N ⊗_X M`. (Blueprint
`lem:tensorobj_comm_iso`, `AlgebraicGeometry.Scheme.Modules.tensorObj_braiding`.)
The presheaf-of-modules monoidal category is symmetric; its braiding `β_ M.val
N.val` sheafifies to the asserted isomorphism by the cheap `mapIso` pattern. -/
noncomputable def tensorObj_braiding {X : Scheme.{u}} (M N : X.Modules) :
    tensorObj M N ≅ tensorObj N M :=
  (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).mapIso
    (BraidedCategory.braiding
      (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) M.val N.val)

/-- **Associator for `⊗_X`.** (Blueprint
`lem:tensorobj_assoc_iso`, `AlgebraicGeometry.Scheme.Modules.tensorObj_assoc_iso`.)
For arbitrary `M, N, P : X.Modules` there is an isomorphism
`(M ⊗_X N) ⊗_X P ≅ M ⊗_X (N ⊗_X P)`. This is the objectwise existence-of-iso datum the
group law consumes (associativity as a `Nonempty (… ≅ …)`).

**UNCONDITIONAL and axiom-clean (iter-238 ROUTE (d)).** No flatness or local-triviality
hypothesis is used: the earlier flatness route (`W_whisker{Right,Left}_of_flat`, needing
sectionwise flatness — false for a general line bundle on a non-affine open) is RETIRED.
Writing `a = PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)` and `η` the
sheafification-adjunction unit, the three-step composite is:
  1. `a(η_{M.val ⊗ᵖ N.val} ▷ P.val)` is iso, giving
     `(M ⊗ N) ⊗ P ≅ a((M.val⊗N.val) ⊗ P.val)`;
  2. `a.mapIso α : a((M.val⊗N.val)⊗P.val) ≅ a(M.val⊗(N.val⊗P.val))`, `α` the
     presheaf-of-modules associator;
  3. `a(M.val ◁ η_{N.val ⊗ᵖ P.val})` is iso, giving
     `a(M.val⊗(N.val⊗P.val)) ≅ M ⊗ (N ⊗ P)`.
Steps 1/3 invert the whiskered sheafification unit via the flatness-free
`PresheafOfModules.W_whisker{Right,Left}_of_W` (η = `toSheafify ∈ J.W`, and `J.W` is
stable under whiskering) together with `isIso_sheafification_map_of_W` (the sheafification
functor IS the localization at `J.W.inverseImage (toPresheaf _)`). The defeq carrier bridge
`X.ringCatSheaf.val = X.presheaf ⋙ forget₂ CommRingCat RingCat` is handled by the leading
`letI instMS` below. -/
noncomputable def tensorObj_assoc_iso {X : Scheme.{u}} {M N P : X.Modules} :
    tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P) := by
  -- UNCONDITIONAL (iter-238, step 0): the locally-trivial hypotheses are dropped —
  -- the body never consumed them (the whiskered-unit localizer fact holds for
  -- arbitrary modules under ROUTE (d)). Matches the blueprint `lem:tensorobj_assoc_iso`
  -- framed unconditional and enables `tensorObj_assoc_iso_invertible`.
  -- Bridge the monoidal structure across the `rfl`-defeq carrier
  -- `Sheaf.val X.ringCatSheaf = X.presheaf ⋙ forget₂ CommRingCat RingCat`.
  letI instMS : MonoidalCategoryStruct (_root_.PresheafOfModules (Sheaf.val X.ringCatSheaf)) :=
    inferInstanceAs (MonoidalCategoryStruct
      (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))
  set a := PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val) with ha
  -- Underlying presheaf tensors and the sheafification unit `η = toSheafify`.
  set MN := PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M.val N.val with hMN
  set NP := PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) N.val P.val with hNP
  set η := (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).unit with hη
  -- The two whiskered-unit localizer facts (ROUTE (d), via `W_whisker{Right,Left}_of_W`).
  -- `η_A = toSheafify` lies in `J.W` (`W_toSheafify`).
  have hηMN : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app MN)) := by
    rw [hη, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.GrothendieckTopology.W_toSheafify _ _
  have hηNP : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app NP)) := by
    rw [hη, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.GrothendieckTopology.W_toSheafify _ _
  have hW1 : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app MN ▷ P.val)) :=
    PresheafOfModules.W_whiskerRight_of_W (R := X.presheaf) P.val (η.app MN) hηMN
  have hW3 : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (M.val ◁ η.app NP)) :=
    PresheafOfModules.W_whiskerLeft_of_W (R := X.presheaf) M.val (η.app NP) hηNP
  -- Steps 1 and 3: the sheafification functor inverts the whiskered units.
  have hi1 : IsIso (a.map (η.app MN ▷ P.val)) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 X.ringCatSheaf.val) _ hW1
  have hi3 : IsIso (a.map (M.val ◁ η.app NP)) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 X.ringCatSheaf.val) _ hW3
  -- Step 2: the presheaf-of-modules associator, transported under `a`.
  have e2 := a.mapIso
    ((PresheafOfModules.monoidalCategoryStruct (R := X.presheaf)).associator M.val N.val P.val)
  exact (@asIso _ _ _ _ _ hi1).symm ≪≫ e2 ≪≫ (@asIso _ _ _ _ _ hi3)

/-- **Refining a trivialisation to a smaller open.** If `M` is trivialised on an
open `U` (`M.restrict U.ι ≅ 𝒪_U`), it is trivialised on every open `W ≤ U`.

The chart-chase is identical in spirit to `LineBundle.IsLocallyTrivial.pullback`:
factor `W.ι = (X.homOfLE hWU) ≫ U.ι`, transport through `restrictFunctorCongr`
and `restrictFunctorComp` to identify `M.restrict W.ι` with
`(M.restrict U.ι).restrict (X.homOfLE hWU)`, restrict the given trivialisation
`e` along that open immersion, and identify the restricted unit with the unit
via `restrictFunctorIsoPullback` + `pullbackObjUnitToUnit` (an isomorphism
because the open immersion's `Opens.map` is `Final`). -/
noncomputable def restrictIsoUnitOfLE {X : Scheme.{u}} {M : X.Modules} {U W : X.Opens}
    (hWU : W ≤ U)
    (e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf) :
    M.restrict W.ι ≅ SheafOfModules.unit (W : Scheme).ringCatSheaf := by
  have hWU' : W ≤ (𝟙 X) ⁻¹ᵁ U := hWU
  set j : (W : Scheme) ⟶ (U : Scheme) := Scheme.Hom.resLE (𝟙 X) U W hWU' with hj
  have hjι : j ≫ U.ι = W.ι := by rw [hj, Scheme.Hom.resLE_comp_ι, Category.comp_id]
  haveI : (TopologicalSpace.Opens.map j.base).Final :=
    CategoryTheory.final_of_representablyFlat _
  -- M.restrict W.ι ≅ (pullback W.ι).obj M
  refine (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M ≪≫ ?_
  -- ≅ (pullback (j ≫ U.ι)).obj M
  refine (Scheme.Modules.pullbackCongr hjι.symm).app M ≪≫ ?_
  -- ≅ (pullback j).obj ((pullback U.ι).obj M)
  refine (Scheme.Modules.pullbackComp j U.ι).symm.app M ≪≫ ?_
  -- ≅ (pullback j).obj (M.restrict U.ι)
  refine (Scheme.Modules.pullback j).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app M) ≪≫ ?_
  -- ≅ (pullback j).obj 𝒪_U
  refine (Scheme.Modules.pullback j).mapIso e ≪≫ ?_
  -- ≅ 𝒪_W
  haveI hI : IsIso (SheafOfModules.pullbackObjUnitToUnit j.toRingCatSheafHom) := inferInstance
  exact @asIso _ _ _ _ _ hI

/-- **Substrate tensor commutes with restriction along an open immersion.**

For an open immersion `f : Y ⟶ X` and `M N : X.Modules`,
`(tensorObj M N).restrict f ≅ tensorObj (M.restrict f) (N.restrict f)`.

This is the single substrate linchpin of `A.1.c.SubT` — **CLOSED, axiom-clean**
(iter-217). It says the substrate `⊗` (sheafification of the presheaf-of-modules
tensor) commutes with the restriction functor along an open immersion. The proof
is the blueprint's four-step composite:
  Step 1 (`restrictFunctorIsoPullback`): reduce `restrict` to the abstract pullback.
  Step 2 (`SheafOfModules.sheafificationCompPullback`): move the pullback inside the
    sheafification (sheafification commutes with pullback).
  Step 3: strip the outer sheafification (`.mapIso`), descending to the presheaf goal
    `(pullback φ).obj (M.val ⊗ₚ N.val) ≅ (M.restrict f).val ⊗ₚ (N.restrict f).val`.
  Step 4: close that presheaf goal by **H1 ∘ H2**:
    • H1 (the sole Mathlib-ABSENT ingredient, BUILT this iter): the presheaf-level iso
      `pushforward β ≅ pullback φ`, obtained from the de-sheafified presheaf
      `PresheafOfModules.pushforwardPushforwardAdj` (adjunction along the open-immersion
      pair `f.opensFunctor ⊣ Opens.map f.base`) against the existing
      `pullbackPushforwardAdjunction` via `Adjunction.leftAdjointUniq`. Here `β` is the
      `restrictFunctor` structure map, so `(M.restrict f).val = (pushforward β).obj M.val`
      definitionally.
    • H2 (strong-monoidal tensorator): `pushforward β = pushforward₀ ⋙ restrictScalars β`
      with `β` sectionwise the open-immersion ring ISO `f.appIso`, so `restrictScalars β`
      is STRONG monoidal (`restrictScalarsMonoidalOfBijective`, resting on the closed
      `restrictScalarsRingIsoTensorEquiv` / `restrictScalars_isIso_{μ,ε}`); the composite
      `μIso` is the tensorator.
The superseded `Localization.Monoidal` / `J.W.IsMonoidal` route is NOT used. -/
noncomputable def tensorObj_restrict_iso {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M N : X.Modules) :
    (tensorObj M N).restrict f ≅ tensorObj (M.restrict f) (N.restrict f) := by
  -- Step 1. Reduce `restrict` to `pullback` along the open immersion `f`
  -- (`restrictFunctorIsoPullback`, Mathlib).
  refine (Scheme.Modules.restrictFunctorIsoPullback f).app (tensorObj M N) ≪≫ ?_
  -- Step 2. **Sheafification commutes with pullback.** `tensorObj M N` is, by
  -- definition, `sheafification.obj (PresheafOfModules.Monoidal.tensorObj
  -- M.val N.val)`, so the genuine Mathlib lemma
  -- `SheafOfModules.sheafificationCompPullback`
  -- (`Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous`,
  -- `sheafification ⋙ pullback φ ≅ PresheafOfModules.pullback φ.hom ⋙
  -- sheafification`) moves the pullback *inside* the sheafification. This
  -- discharges half (ii) of the original obstruction (sheafification commuting
  -- with pullback). After it the goal is the purely **presheaf-level** residual
  -- `sheafify ((PresheafOfModules.pullback φ.hom).obj (M.val ⊗ N.val))
  --    ≅ (M.restrict f).tensorObj (N.restrict f)`.
  refine (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).app
      (PresheafOfModules.Monoidal.tensorObj M.val N.val) ≪≫ ?_
  -- Step 3. **Strip the outer sheafification.** Both sides are
  -- `PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)` applied to a
  -- presheaf-of-modules: the LHS to `(pullback φ.hom).obj (M.val ⊗ₚ N.val)`, and
  -- the RHS `(M.restrict f).tensorObj (N.restrict f)` *by definition* to
  -- `(M.restrict f).val ⊗ₚ (N.restrict f).val`. So it suffices to give the
  -- comparison at the PRESHEAF level and sheafify it. This is a genuine reduction
  -- step (verified: the goal below has no sheafification).
  refine (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.obj)).mapIso ?_
  -- Step 4 (RESIDUAL CLOSURE — iter-217 H1 build). The remaining presheaf goal is
  --   `(PresheafOfModules.pullback φ).obj (M.val ⊗ₚ N.val)
  --      ≅ (M.restrict f).val ⊗ₚ (N.restrict f).val`
  -- where `φ = (Scheme.Hom.toRingCatSheafHom f).hom` and `⊗ₚ =
  -- PresheafOfModules.Monoidal.tensorObj`. We close it via:
  --  (H1, the linchpin) the presheaf-level iso `pushforward β ≅ pullback φ`, built from
  --      the presheaf `pushforwardPushforwardAdj` (above) against the existing
  --      `pullbackPushforwardAdjunction` via `leftAdjointUniq`. Here `β` is the
  --      open-immersion structure map of `restrictFunctor f`, so
  --      `(M.restrict f).val = (pushforward β).obj M.val` definitionally.
  --  (H2) the strong-monoidal comparison `(pushforward β).obj (A ⊗ₚ B) ≅
  --      (pushforward β).obj A ⊗ₚ (pushforward β).obj B`.
  -- `φR` (the scheme structure map) and `β` (the restrictFunctor structure map) are kept as
  -- `let`-bindings (zeta-transparent) so the unit/counit triangle goals below reduce; the
  -- open-immersion adjunction is INLINED for the same reason (a `have` would make `adj.unit`
  -- opaque and block the `congr` defeq, exactly as in Mathlib's sheaf-level `restrictAdjunction`).
  let φR := (Scheme.Hom.toRingCatSheafHom f).hom
  -- The restrictFunctor structure map `β` (so `(M.restrict f).val = (pushforward β).obj M.val`).
  let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
    { app := fun U => (f.appIso U.unop).inv }
  let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
    Functor.whiskerRight α (forget₂ CommRingCat RingCat)
  -- H1 via the presheaf pushforward-pushforward adjunction + `leftAdjointUniq`.
  have hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φR :=
    PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φR
      (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
      (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
  let H1 := hadj.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φR)
  refine (H1.app (PresheafOfModules.Monoidal.tensorObj M.val N.val)).symm ≪≫ ?_
  -- H2: the strong-monoidal tensorator of `pushforward β = pushforward₀ ⋙ restrictScalars β`.
  -- `β` is sectionwise bijective (it is the `forget₂`-image of the open-immersion structure ring
  -- ISO `f.appIso`), so `restrictScalars β` is STRONG monoidal (`restrictScalarsMonoidalOfBijective`),
  -- and `pushforward₀OfCommRingCat` is `Monoidal` (Mathlib); the composite's `μIso` is the tensorator.
  -- It is built over the SYNTACTIC `_ ⋙ forget₂` base form (where the `MonoidalCategory` instance is
  -- found canonically); the result is DEFEQ to the goal — whose base `X.ringCatSheaf.obj` is only
  -- defeq, not syntactically, `X.presheaf ⋙ forget₂` — and `(pushforward β).obj M.val =
  -- (M.restrict f).val` definitionally, so `exact` closes it without any instance diamond.
  have hβ : ∀ U, Function.Bijective (β.app U).hom := by
    intro U
    haveI : IsIso (β.app U) :=
      inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))
    exact ConcreteCategory.bijective_of_isIso (β.app U)
  let β' : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (f.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat := β
  haveI : (PresheafOfModules.restrictScalars β').Monoidal :=
    PresheafOfModules.restrictScalarsMonoidalOfBijective β' hβ
  exact (Functor.Monoidal.μIso
    (PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf
      ⋙ PresheafOfModules.restrictScalars β')
    (M.val : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (N.val : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))).symm

/-- **Tensor product of locally-trivial modules is locally trivial.**

If `M, N : X.Modules` are locally trivial of rank one (line bundles), so is
their tensor product `tensorObj M N`. Per blueprint
`lem:tensorobj_preserves_locally_trivial`. The proof picks, for each point `x`,
a common affine open `W ∋ x` contained in trivialising opens `U` (for `M`) and
`U'` (for `N`), refines both trivialisations to `W` via `restrictIsoUnitOfLE`,
then transports through `tensorObj_restrict_iso`, the bifunctoriality
`tensorObjIsoOfIso`, and the unit isomorphism `tensorObj_unit_iso`:
`(M ⊗ N)|_W ≅ M|_W ⊗ N|_W ≅ 𝒪_W ⊗ 𝒪_W ≅ 𝒪_W`. The only residual gap is the
substrate-restriction compatibility `tensorObj_restrict_iso`. -/
lemma tensorObj_isLocallyTrivial {X : Scheme.{u}} {M N : X.Modules}
    (hM : LineBundle.IsLocallyTrivial M) (hN : LineBundle.IsLocallyTrivial N) :
    LineBundle.IsLocallyTrivial (tensorObj M N) := by
  intro x
  obtain ⟨U, hxU, hU_aff, ⟨eM⟩⟩ := hM x
  obtain ⟨U', hxU', hU'_aff, ⟨eN⟩⟩ := hN x
  obtain ⟨W, hW_aff, hxW, hWsub⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := U ⊓ U') ⟨hxU, hxU'⟩
  have hWU : W ≤ U := le_trans hWsub inf_le_left
  have hWU' : W ≤ U' := le_trans hWsub inf_le_right
  refine ⟨W, hxW, hW_aff, ⟨?_⟩⟩
  exact tensorObj_restrict_iso W.ι M N ≪≫
    tensorObjIsoOfIso (restrictIsoUnitOfLE hWU eM) (restrictIsoUnitOfLE hWU' eN) ≪≫
    tensorObj_unit_iso

/-! ## Project-local Mathlib supplement — the d.2-free descent re-route (B-connector)

The "locally-iso ⇒ iso" half of the descent assembly of `exists_tensorObj_inverse`:
a morphism of `𝒪_X`-modules that restricts to an isomorphism on an open
neighbourhood of every point is a global isomorphism. The route is the stalkwise
iso criterion `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` (for sheaves valued
in `Ab`, whose forgetful functor reflects isos and preserves limits / filtered
colimits) together with `Scheme.Modules.restrictStalkNatIso` (restriction along an
open immersion commutes with stalks). **No stalk-⊗ ("d.2") is invoked**: this is a
statement about a single module morphism, never about the tensor stalk. -/

/-- **B-connector: a morphism of `𝒪_X`-modules that restricts to an isomorphism on
an open cover is an isomorphism.** For `φ : M ⟶ N` in `X.Modules`, if every point
`x` lies in an open `U x` on which the restriction `(restrictFunctor (U x).ι).map φ`
is an isomorphism, then `φ` is an isomorphism. This is the B-bridge of the d.2-free
descent re-route assembling `exists_tensorObj_inverse`. -/
lemma isIso_of_isIso_restrict {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (U : X → X.Opens) (hxU : ∀ x, x ∈ U x)
    (h : ∀ x, IsIso ((Scheme.Modules.restrictFunctor (U x).ι).map φ)) :
    IsIso φ := by
  -- It suffices that each stalk map of the underlying `Ab`-sheaf morphism is iso.
  have hst : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map
      ((Scheme.Modules.toPresheaf X).map φ)) := by
    intro x
    obtain ⟨x', hx'⟩ : ∃ x', (U x).ι x' = x := by
      have hmem : x ∈ (U x).ι.opensRange := by
        rw [Scheme.Opens.opensRange_ι]; exact hxU x
      exact AlgebraicGeometry.Scheme.Hom.mem_opensRange.mp hmem
    haveI : IsIso ((Scheme.Modules.restrictFunctor (U x).ι).map φ) := h x
    -- `(restrictFunctor … ⋙ toPresheaf … ⋙ stalkFunctor x').map φ` is iso (functor of an iso).
    haveI hFφ : IsIso ((Scheme.Modules.restrictFunctor (U x).ι ⋙
        Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x').map φ) := by
      dsimp only [Functor.comp_map]; exact Functor.map_isIso _ _
    -- Transport the iso across `restrictStalkNatIso` to the stalk at `(U x).ι x' = x`.
    have hGφ : IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} ((U x).ι x')).map
        ((Scheme.Modules.toPresheaf X).map φ)) :=
      (CategoryTheory.NatIso.isIso_map_iff
        (Scheme.Modules.restrictStalkNatIso (U x).ι x') φ).mp hFφ
    exact hx' ▸ hGφ
  -- Package as a morphism of `TopCat.Sheaf Ab X` and apply the stalkwise iso criterion.
  let MS : TopCat.Sheaf Ab.{u} X := ⟨M.presheaf, M.isSheaf⟩
  let NS : TopCat.Sheaf Ab.{u} X := ⟨N.presheaf, N.isSheaf⟩
  let fS : MS ⟶ NS := ⟨(Scheme.Modules.toPresheaf X).map φ⟩
  haveI : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab.{u} x).map fS.hom) := hst
  haveI hSiso : IsIso fS := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso fS
  have h1 : IsIso ((Scheme.Modules.toPresheaf X).map φ) := by
    have := (TopCat.Sheaf.forget Ab.{u} X).map_isIso fS
    exact this
  exact (CategoryTheory.isIso_iff_of_reflects_iso φ (Scheme.Modules.toPresheaf X)).mp h1

/-- **A-bridge step (ii): promote an `𝒪_X`-linear `Ab`-presheaf morphism to a module
morphism.** Given a morphism `g : M.presheaf ⟶ N.presheaf` of the underlying
`Ab`-presheaves that is sectionwise `𝒪_X`-linear, package it as a morphism `M ⟶ N`
of `𝒪_X`-modules. This wraps `PresheafOfModules.homMk` at the `Scheme.Modules` level;
it is the "promote to `𝒪_X`-linear" half of the descent A-bridge `homOfLocalCompat`
(the ab-sheaf gluing produces the linear `g`; this lemma turns it into a module map).
Sectionwise linearity is a property the consumer checks on a separated presheaf. -/
noncomputable def homMk {X : Scheme.{u}} {M N : X.Modules}
    (g : M.val.presheaf ⟶ N.val.presheaf)
    (hg : ∀ (V : (TopologicalSpace.Opens X)ᵒᵖ) (r : X.ringCatSheaf.obj.obj V) (m : M.val.obj V),
      (g.app V).hom (r • m) = r • (g.app V).hom m) :
    M ⟶ N :=
  ⟨PresheafOfModules.homMk (M₁ := M.val) (M₂ := N.val) g hg⟩

/-! ### iter-230 C-wiring diagnostic (the binding probe) — OUTCOME (ii)

The PRIMARY `dual_isLocallyTrivial` reduces, exactly as `tensorObj_isLocallyTrivial`
does, to a `dual_restrict_iso : (dual M).restrict f ≅ dual (M.restrict f)` for an open
immersion `f : Y ⟶ X`. Mirroring `tensorObj_restrict_iso` verbatim (Step 1
`restrictFunctorIsoPullback`, Step 2 `sheafificationCompPullback`, Step 3 strip the
outer sheafification, Step 4 H1 `pushforwardPushforwardAdj`∘`leftAdjointUniq`) all
TYPECHECK and leave the residual presheaf goal — verified live this iter:

  `(PresheafOfModules.pushforward β).obj (PresheafOfModules.dual M.val)
      ≅ PresheafOfModules.dual ((PresheafOfModules.pushforward β).obj M.val)`

(`(M.restrict f).val = (pushforward β).obj M.val` definitionally, `change`-confirmed).

**This residual CANNOT be discharged by the shared root `overSliceSheafEquiv`** —
outcome (ii), not (i):
  • The root is a `Sheaf`-category equivalence `Sheaf ((gt X).over U) A ≌
    Sheaf (gt ↥U) A`; the residual is a `PresheafOfModules`-level iso (Step 3 already
    stripped the outer sheafification). Different categories — no direct application
    (`overSliceSheafEquiv` is not even in scope here, and its codomain type is
    `Sheaf`, not `PresheafOfModules`).
  • The root is value-category-FIXED (arbitrary `A`); the residual is an iso of
    `ModuleCat` over the VARYING ring `𝒪_Y(V) = R_Y(V)`. The per-`V` module action
    (`internalHomObjModule` over `Over V`) is exactly what a fixed-value-cat site
    equivalence does NOT transport for free.
  • The dual's value uses the per-open slice `restr W = pushforward₀ (Over.forget W)`
    (slice over a single `W`), a finer slicing than the whole-`U` slice site
    `(gt X).over U` the root is built over.

**Precise decomposition of what (ii) actually needs** (the genuine new build; the
substrate has grown a 4th time, as strategy-critic ts230 anticipated): a
PRESHEAF-level, `R`-linear slice comparison
  `Hom_{Over_X (fV)}(restr (fV) A, restr (fV) 𝟙_X)
     ≅  Hom_{Over_Y V}(restr V ((pushforward β) A), restr V 𝟙_Y)`
natural in `V` and `𝒪_Y(V)`-linear, induced by the slice equivalence
`Over_Y V ≌ Over_X (fV)` (the per-`V` shadow of `Opens.overEquivalence`, valid because
`f.opensFunctor` is fully faithful with image `= {W ≤ U}` and `fV ≤ U`), TOGETHER WITH
the identification `restr (fV) A ≅ G^* (restr V (pushforward β A))` under that
equivalence `G` and the ring-iso transport `β = f.appIso`. This is the presheaf+module
analogue of `overSliceSheafEquiv`; the sheaf-level root does not cover it. See the
task result for the full statement of the missing ingredient.

The diagnostic def is intentionally NOT committed (it would pin a new `sorry`, which
the iter-230 HARD-TRIPWIRE directive forbids). -/

/-- **Inverse of an invertible module.**

Every line bundle `L : X.Modules` has a two-sided tensor inverse: there is a
locally-trivial `Linv : X.Modules` (the dual `L⁻¹ = Hom(L, O_X)`) together with
a tensor isomorphism `L ⊗_X Linv ≅ 𝒪_X`. Per blueprint
`lem:tensorobj_inverse_invertible`. iter-206 flat-pivot: the designated unit is
`SheafOfModules.unit X.ringCatSheaf = 𝒪_X` (the `MonoidalCategory` unit `𝟙_` is
no longer available — the full monoidal instance is off the critical path, see
§2).

**iter-226+ d.2-free descent re-route (current state).** `Linv := Scheme.Modules.dual L`
IS nameable: the sheaf-level dual `dual` (this file) landed iter-225, so the FIRST
step is no longer blocked and the iter-218 "infrastructure-missing" gate is retired.
The closure is now assembled WITHOUT the categorical "invertible object ⇒ inverse"
escape (still unavailable — no `MonoidalCategory (X.Modules)` for the varying
structure sheaf, §2) and WITHOUT the forbidden sheafify-the-presheaf-evaluation
shortcut (it re-hits the `M ◁ η` whiskering = the abandoned tensor-stalk "d.2"
gap, a DEAD END — analogist `ts226descent.md`, verdict D). Instead it glues local
trivialising data, touching no tensor stalk. Two bridges remain before this sorry
closes (see body comment): the C-bridge `dual_isLocallyTrivial` and the A-bridge
`homOfLocalCompat` (SheafOfModules morphism descent). The B-bridge
`isIso_of_isIso_restrict` (local-iso ⇒ global iso, mirroring the CLOSED
`tensorObj_isLocallyTrivial` at L1912) is DONE (iter-226, above, axiom-clean). EXACT
decomposition: `informal/exists_tensorObj_inverse.md` and `analogies/ts226descent.md`.
-/
lemma exists_tensorObj_inverse {X : Scheme.{u}} {L : X.Modules}
    (hL : LineBundle.IsLocallyTrivial L) :
    ∃ Linv : X.Modules, LineBundle.IsLocallyTrivial Linv ∧
      Nonempty (tensorObj L Linv ≅ SheafOfModules.unit X.ringCatSheaf) :=
  -- iter-226 descent re-route (d.2-FREE). `Linv := Scheme.Modules.dual L` is now
  -- nameable (dual OBJECT landed iter-225). The B-connector
  -- `isIso_of_isIso_restrict` (above, axiom-clean) closes the final "locally-iso ⇒
  -- global iso" step. Two bridges REMAIN before this sorry closes:
  --   (C) `dual_isLocallyTrivial : IsLocallyTrivial L → IsLocallyTrivial (dual L)`,
  --       via `(dual M).restrict f ≅ dual (M.restrict f)` — the dual analogue of the
  --       CLOSED `tensorObj_restrict_iso`, mirroring its H1∘H2 recipe with
  --       `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` carrying the bespoke
  --       presheaf `dual` (= `internalHom(-, R)`) across the open-immersion ring iso.
  --   (A) SheafOfModules morphism descent: glue the canonical local trivialising isos
  --       `(L ⊗ dual L)|_{Uᵢ} ≅ 𝒪_{Uᵢ}` (pattern of `tensorObj_isLocallyTrivial`,
  --       L1920) — agreeing on overlaps (bounded cocycle check, NOT d.2) — to a global
  --       `tensorObj L (dual L) ⟶ 𝒪_X` via `CategoryTheory.Presheaf.IsSheaf.hom` /
  --       `sheafHomSectionsEquiv` + `PresheafOfModules.homMk`. Then `isIso_of_isIso_restrict`
  --       upgrades the glued morphism to a global iso, closing this sorry (80→79).
  -- The FORBIDDEN sheafify-the-presheaf-eval shortcut re-hits the `M ◁ η` whiskering
  -- (d.2) and is a DEAD END; only the gluing route escapes. See the docstring and
  -- `informal/exists_tensorObj_inverse.md`.
  sorry

/-! ## §5. The invertibility-carrier Picard group `picCommGroup`

This is the by-hand commutative-group law on isomorphism classes of `⊗`-invertible
`𝒪_X`-modules (blueprint §`sec:tensorobj_pic_carrier`). Every group axiom is a single
existence-of-isomorphism `Nonempty (… ≅ …)` read as an equality of iso-classes; no
pentagon/triangle/hexagon coherence and no `MonoidalCategory` instance is invoked.
The inverse is carried by the membership witness of `IsInvertible` itself. -/

/-- **Step 1 — associator on `⊗`-invertible objects** (blueprint
`lem:tensorobj_assoc_iso_invertible`). An immediate specialisation of the now
*unconditional* `tensorObj_assoc_iso`; the invertibility hypotheses are not consumed
(they match the blueprint statement). -/
noncomputable def tensorObj_assoc_iso_invertible {X : Scheme.{u}} {M N P : X.Modules}
    (_hM : IsInvertible M) (_hN : IsInvertible N) (_hP : IsInvertible P) :
    tensorObj (tensorObj M N) P ≅ tensorObj M (tensorObj N P) :=
  tensorObj_assoc_iso

/-- **Middle-four interchange for `⊗_X`** (helper). For arbitrary `𝒪_X`-modules
`A, B, C, D`, there is an isomorphism `(A ⊗ B) ⊗ (C ⊗ D) ≅ (A ⊗ C) ⊗ (B ⊗ D)`,
assembled from the unconditional associator and the braiding (no coherence consumed).
Used to reassociate the four factors in `IsInvertible.tensorObj`. -/
private noncomputable def tensorObj_middleFour {X : Scheme.{u}} (A B C D : X.Modules) :
    tensorObj (tensorObj A B) (tensorObj C D)
      ≅ tensorObj (tensorObj A C) (tensorObj B D) :=
  tensorObj_assoc_iso ≪≫
    tensorObjIsoOfIso (Iso.refl A)
      (tensorObj_assoc_iso.symm ≪≫
        tensorObjIsoOfIso (tensorObj_braiding B C) (Iso.refl D) ≪≫
        tensorObj_assoc_iso) ≪≫
    tensorObj_assoc_iso.symm

/-- **Step 3 — `⊗`-invertibility is closed under tensor product** (blueprint
`lem:isinvertible_tensor`). If `M, M'` are `⊗`-invertible with inverses `N, N'`,
then `N ⊗ N'` is a tensor inverse of `M ⊗ M'`. -/
theorem IsInvertible.tensorObj {X : Scheme.{u}} {M M' : X.Modules}
    (hM : IsInvertible M) (hM' : IsInvertible M') :
    IsInvertible (Scheme.Modules.tensorObj M M') := by
  obtain ⟨N, ⟨e⟩⟩ := hM
  obtain ⟨N', ⟨e'⟩⟩ := hM'
  exact ⟨Scheme.Modules.tensorObj N N',
    ⟨tensorObj_middleFour M M' N N' ≪≫ tensorObjIsoOfIso e e' ≪≫ tensorObj_unit_iso⟩⟩

/-- **Step 4 — the structure sheaf is `⊗`-invertible** (blueprint
`lem:isinvertible_unit`). Witness `𝒪_X`, iso `tensorObj_unit_iso`. -/
theorem isInvertible_unit {X : Scheme.{u}} :
    IsInvertible (SheafOfModules.unit X.ringCatSheaf) :=
  ⟨SheafOfModules.unit X.ringCatSheaf, ⟨tensorObj_unit_iso⟩⟩

/-- **Step 5 — the tensor inverse is determined up to isomorphism** (blueprint
`lem:isinvertible_inverse_welldef`). If `M ⊗ N ≅ 𝒪_X` and `M ⊗ N' ≅ 𝒪_X` then
`N ≅ N'`, via the inverse-of-inverse chain. -/
theorem IsInvertible.inverse_unique {X : Scheme.{u}} {M N N' : X.Modules}
    (e : Scheme.Modules.tensorObj M N ≅ SheafOfModules.unit X.ringCatSheaf)
    (e' : Scheme.Modules.tensorObj M N' ≅ SheafOfModules.unit X.ringCatSheaf) :
    Nonempty (N ≅ N') :=
  ⟨(tensorObj_right_unitor N).symm ≪≫
    tensorObjIsoOfIso (Iso.refl N) e'.symm ≪≫
    tensorObj_assoc_iso.symm ≪≫
    tensorObjIsoOfIso (tensorObj_braiding N M ≪≫ e) (Iso.refl N') ≪≫
    tensorObj_left_unitor N'⟩

/-- The setoid of `⊗`-invertible `𝒪_X`-modules: `M ∼ M'` iff there exists an
isomorphism `M ≅ M'` (blueprint `def:pic_carrier`). -/
instance picSetoid (X : Scheme.{u}) : Setoid {M : X.Modules // IsInvertible M} where
  r M M' := Nonempty ((M : X.Modules) ≅ (M' : X.Modules))
  iseqv :=
    ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e ≪≫ f⟩⟩

/-- **Step 2 — the invertibility-carrier Picard group** (blueprint
`def:pic_carrier`): the quotient of `⊗`-invertible `𝒪_X`-modules by isomorphism. -/
def PicGroup (X : Scheme.{u}) : Type _ := Quotient (picSetoid X)

/-- Multiplication on `PicGroup X`: `[M] · [M'] := [M ⊗_X M']`, well-defined on
iso-classes by bifunctoriality (`tensorObjIsoOfIso`), landing in `PicGroup` by
`IsInvertible.tensorObj`. -/
noncomputable def picMul {X : Scheme.{u}} : PicGroup X → PicGroup X → PicGroup X :=
  Quotient.lift₂
    (fun a b => Quotient.mk _ ⟨tensorObj a.1 b.1, a.2.tensorObj b.2⟩)
    (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨a', ha'⟩ ⟨b', hb'⟩ ⟨ea⟩ ⟨eb⟩
      exact Quotient.sound ⟨tensorObjIsoOfIso ea eb⟩)

/-- The inverse class on `PicGroup X`: `[M] ↦ [N]` for the membership witness `N`
of `IsInvertible M`, well-defined by `IsInvertible.inverse_unique`. -/
noncomputable def picInv {X : Scheme.{u}} : PicGroup X → PicGroup X :=
  Quotient.lift
    (fun a => Quotient.mk _
      ⟨Classical.choose a.2,
        a.1, ⟨tensorObj_braiding _ a.1 ≪≫ (Classical.choose_spec a.2).some⟩⟩)
    (by
      rintro ⟨a, ha⟩ ⟨a', ha'⟩ ⟨ea⟩
      refine Quotient.sound ?_
      -- both `Classical.choose ha` and `Classical.choose ha'` are tensor inverses of `a`
      have h1 : tensorObj a (Classical.choose ha) ≅ SheafOfModules.unit X.ringCatSheaf :=
        (Classical.choose_spec ha).some
      have h2 : tensorObj a (Classical.choose ha') ≅ SheafOfModules.unit X.ringCatSheaf :=
        tensorObjIsoOfIso ea (Iso.refl _) ≪≫ (Classical.choose_spec ha').some
      exact IsInvertible.inverse_unique h1 h2)

/-- **Step 6 — the invertibility-carrier Picard group is abelian** (blueprint
`thm:pic_commgroup`). `[M] · [M'] := [M ⊗_X M']`, `1 := [𝒪_X]`, and `[M]⁻¹` the
class of any membership witness of `IsInvertible M`. Each group axiom is a single
existence-of-isomorphism: unit laws ← unitors, associativity ← associator,
commutativity ← braiding, left inverse ← the witness iso. No monoidal coherence. -/
noncomputable instance picCommGroup (X : Scheme.{u}) : CommGroup (PicGroup X) where
  mul := picMul
  one := Quotient.mk _ ⟨SheafOfModules.unit X.ringCatSheaf, isInvertible_unit⟩
  inv := picInv
  mul_assoc := by
    rintro a b c
    induction a using Quotient.ind with | _ a => ?_
    induction b using Quotient.ind with | _ b => ?_
    induction c using Quotient.ind with | _ c => ?_
    exact Quotient.sound ⟨tensorObj_assoc_iso⟩
  one_mul := by
    rintro a
    induction a using Quotient.ind with | _ a => ?_
    exact Quotient.sound ⟨tensorObj_left_unitor a.1⟩
  mul_one := by
    rintro a
    induction a using Quotient.ind with | _ a => ?_
    exact Quotient.sound ⟨tensorObj_right_unitor a.1⟩
  inv_mul_cancel := by
    rintro a
    induction a using Quotient.ind with | _ a => ?_
    exact Quotient.sound
      ⟨tensorObj_braiding (Classical.choose a.2) a.1 ≪≫ (Classical.choose_spec a.2).some⟩
  mul_comm := by
    rintro a b
    induction a using Quotient.ind with | _ a => ?_
    induction b using Quotient.ind with | _ b => ?_
    exact Quotient.sound ⟨tensorObj_braiding a.1 b.1⟩

/-! ## §6. Pullback-monoidality substrate (A.1.c): `IsInvertible.pullback`

Project-local Mathlib supplement. The relative Picard consumer re-bases onto the
`IsInvertible` carrier and its structure maps are *pullback* maps for GENERAL scheme
morphisms (the projection `C ×_S T → T` and base-change maps are neither open
immersions nor flat). We need that pullback preserves `⊗`-invertibility. This requires
`pullbackTensorIso` (`f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`) and `pullbackUnitIso`
(`f^*𝒪_X ≅ 𝒪_Y`). Blueprint §`sec:tensorobj_pullback_monoidality`. -/

/-- **Composition coherence of the unit→pushforward-unit comparison.**

For composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X`, the canonical comparison
`unitToPushforwardObjUnit` of the composite `h ≫ f` factors through the comparisons
of `f` and `h` and the pushforward pseudofunctor coherence `pushforwardComp`. This is
the *pushforward-side* (right-adjoint) half of the composition coherence; it is
concrete (sectionwise it is just functoriality of the structure-sheaf ring maps,
hence `rfl` after the `ext`-chain) and is the pushforward-side input from which the
genuinely-needed *pullback-side* coherence of `pullbackObjUnitToUnit` is obtained by
adjunction-mate transport. Mathlib-absent at the pinned commit. -/
lemma unitToPushforwardObjUnit_comp {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) :
    SheafOfModules.unitToPushforwardObjUnit (h ≫ f).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp h f).hom.app (SheafOfModules.unit Z.ringCatSheaf) := by
  apply SheafOfModules.Hom.ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-- **Composition coherence of the unit comparison `pullbackObjUnitToUnit`
(the genuinely-new ingredient for `pullbackUnitIso`).**

For composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X`, the canonical comparison
`f^*𝒪 ⟶ 𝒪` of the composite `h ≫ f` factors through the comparisons of `f` and `h`
and the pullback pseudofunctor coherence `pullbackComp`:
`pullbackObjUnitToUnit (h≫f) = (pullbackComp h f).inv ≫ (pullback h).map (pbu f) ≫ pbu h`.

This is the pullback-side (left-adjoint) composition coherence — Mathlib-absent at the
pinned commit and NOT a sectionwise statement (the abstract left-adjoint pullback has no
sectionwise value). It is obtained by adjunction-mate transport from the pushforward-side
coherence `unitToPushforwardObjUnit_comp`: transposing both sides under
`pullbackPushforwardAdjunction (h≫f)`, the left side becomes `unitToPushforwardObjUnit (h≫f)`
and the right side is reassembled via the conjugate/mate identity
`conjugateEquiv_pullbackComp_inv` (relating `pullbackComp.inv` to `pushforwardComp.hom`),
`unit_conjugateEquiv`, and the composite-adjunction unit `Adjunction.comp_unit_app`.

Consumed by `pullbackUnitIso`: on an affine chart `V` the inclusion `V.ι ≫ f` factors as
`g ≫ U.ι` with `Opens.map g.base` `Final`, so two applications of this coherence (one for
each factorisation) express the restricted global comparison as a composite of isomorphisms
(`pbu` for an open immersion / a `Final`-chart morphism is an iso), whence
`pullbackObjUnitToUnit f` is an iso by `isIso_of_isIso_restrict`.

The proof uses `erw` for the associativity / functoriality steps because the `SheafOfModules`
category compositions appear in defeq-but-not-syntactic forms (`Scheme.Modules.pullback f`
vs `SheafOfModules.pullback f.toRingCatSheafHom`) on which plain `rw [Category.assoc]` /
`rw [Functor.map_comp]` fail to unify. -/
lemma pullbackObjUnitToUnit_comp {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) :
    SheafOfModules.pullbackObjUnitToUnit (h ≫ f).toRingCatSheafHom =
      (Scheme.Modules.pullbackComp h f).inv.app (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pullback h).map (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
      SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom := by
  have key := unitToPushforwardObjUnit_comp h f
  have conj := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction h))
    (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f))
    (Scheme.Modules.pullbackComp h f).inv (SheafOfModules.unit X.ringCatSheaf)
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at conj
  apply (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f)).homEquiv _ _ |>.injective
  have hL : (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f)).homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit (h ≫ f).toRingCatSheafHom)
    = SheafOfModules.unitToPushforwardObjUnit (h ≫ f).toRingCatSheafHom := by
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      (h ≫ f).toRingCatSheafHom
  have hi : (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f)).homEquiv _ _
      ((Scheme.Modules.pullbackComp h f).inv.app (SheafOfModules.unit X.ringCatSheaf))
    = ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction h)).unit.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        (Scheme.Modules.pushforwardComp h f).hom.app
          ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback h).obj
            (SheafOfModules.unit X.ringCatSheaf)) := by
    rw [Adjunction.homEquiv_unit]; exact conj.symm
  have hLf : (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom
  have hLh : (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
    = SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom := by
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      h.toRingCatSheafHom
  have hinner : (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
        ((Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf)) ≫
      (Scheme.Modules.pushforward h).map
        ((Scheme.Modules.pullback h).map
            (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
          SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
    = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
        SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom := by
    have e := Adjunction.homEquiv_unit (adj := Scheme.Modules.pullbackPushforwardAdjunction h)
      (X := (Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf))
      (Y := SheafOfModules.unit Z.ringCatSheaf)
      (f := (Scheme.Modules.pullback h).map
          (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
    have key2 : (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          ((Scheme.Modules.pullback h).map
              (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
            SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
        = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom ≫
            SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom := by
      rw [Adjunction.homEquiv_naturality_left]; exact congrArg _ hLh
    exact e.symm.trans key2
  have hcomp' : ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction h)).unit.app
        (SheafOfModules.unit X.ringCatSheaf) ≫
      (Scheme.Modules.pushforward h ⋙ Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullback h).map
            (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
          SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)
    = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map
          (SheafOfModules.unitToPushforwardObjUnit h.toRingCatSheafHom) := by
    have ef := Adjunction.homEquiv_unit (adj := Scheme.Modules.pullbackPushforwardAdjunction f)
      (X := SheafOfModules.unit X.ringCatSheaf) (Y := SheafOfModules.unit Y.ringCatSheaf)
      (f := SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    rw [Adjunction.comp_unit_app, Functor.comp_map]
    erw [Category.assoc, ← Functor.map_comp, hinner, Functor.map_comp]
    erw [← Category.assoc]
    rw [show (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            (SheafOfModules.unit X.ringCatSheaf) ≫
          (Scheme.Modules.pushforward f).map
            (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
        = SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom from ef.symm.trans hLf]
    rfl
  rw [hL, key, Adjunction.homEquiv_naturality_right, hi]
  erw [Category.assoc, ← (Scheme.Modules.pushforwardComp h f).hom.naturality
      ((Scheme.Modules.pullback h).map (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ≫
        SheafOfModules.pullbackObjUnitToUnit h.toRingCatSheafHom)]
  erw [← Category.assoc, hcomp']
  erw [Category.assoc]

/-! ### Phase 1 — `pullbackUnitIso` (`f^*𝒪_X ≅ 𝒪_Y`), blueprint `lem:pullback_unit_iso`

**iter-241 RESOLUTION (the chart-chase is NOT needed).** The unit comparison
`SheafOfModules.pullbackObjUnitToUnit f` is an isomorphism for *every* morphism of
schemes `f`, not just for `Final`-chart morphisms. The Mathlib instance
`SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal` fires whenever the comparison
functor `Opens.map f.base` is `Final`, and that functor is **always** `Final`: the
preimage functor on opens preserves finite limits (it is a frame homomorphism), so it is
representably flat, whence `final_of_representablyFlat` supplies `(Opens.map f.base).Final`
unconditionally. (Verified axiom-clean for a general `f`.) The elaborate affine
chart-chase contemplated by the blueprint proof — and the iter-240 coherence linchpin
`pullbackObjUnitToUnit_comp` — are therefore unnecessary for this lemma (the linchpin is
retained above as it is the genuine Mathlib-absent pseudofunctor coherence, of independent
use for the harder Phase-2 tensor comparison).

The remaining friction was purely a Lean typeclass-resolution accident: in a context with
several `(Opens.map _).Final` hypotheses (or after a `pullbackObjUnitToUnit_comp` rewrite)
the buried implicit instance args of `pullbackObjUnitToUnit` (`[F.IsContinuous]`,
`[(pushforward φ).IsRightAdjoint]`) are defeq-but-not-syntactic, so `asIso`/`infer_instance`
fails to synthesise `IsIso (pbu f)`. The fix (mathlib-analogist `pbu-canon`, the
`Functor.Monoidal.μIso` idiom): isolate the single `Final` hypothesis in the helper
`isIso_pbu_of_final` whose body `inferInstance` runs at a clean site, then transport the
resulting witness through `asIso` by passing it *explicitly* (`@asIso … (isIso_pbu_of_final g)`)
— the application's defeq check runs at default transparency and succeeds, whereas instance
synthesis (reducible transparency) does not. -/

/-- **`IsIso (pullbackObjUnitToUnit g)` from a single `Final` hypothesis, at a clean site.**
Project-local: isolates the lone `(Opens.map g.base).Final` instance so that the Mathlib
`OfFinal` instance synthesises without colliding with other in-scope `Final`/`IsIso`
hypotheses (see the section note). -/
private lemma isIso_pbu_of_final {X Y : Scheme.{u}} (g : Y ⟶ X)
    [(TopologicalSpace.Opens.map g.base).Final] :
    IsIso (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) := inferInstance

/-- **Bundled `Iso` form of the unit comparison `pullbackObjUnitToUnit g`** for a `Final`
comparison functor — the analogue of `CategoryTheory.Functor.Monoidal.μIso`. Project-local:
hands out the isomorphism (rather than a bare `IsIso` instance) so downstream coherence
reasoning stays at the `Iso` level and never re-triggers the `pbu` instance synthesis. -/
noncomputable def pullbackObjUnitToUnitIso {X Y : Scheme.{u}} (g : Y ⟶ X)
    [(TopologicalSpace.Opens.map g.base).Final] :
    (Scheme.Modules.pullback g).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)
    (isIso_pbu_of_final g)

/-- **Pullback preserves the structure sheaf** (blueprint `lem:pullback_unit_iso`):
`f^*𝒪_X ≅ 𝒪_Y` for an arbitrary morphism of schemes `f : Y ⟶ X`, where
`𝒪_X = SheafOfModules.unit X.ringCatSheaf`. The comparison functor `Opens.map f.base` is
always `Final` (preimage on opens is representably flat), so the Mathlib unit comparison
`pullbackObjUnitToUnit f` is an isomorphism unconditionally. -/
noncomputable def pullbackUnitIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      SheafOfModules.unit Y.ringCatSheaf :=
  haveI : (TopologicalSpace.Opens.map f.base).Final := final_of_representablyFlat _
  pullbackObjUnitToUnitIso f

/-- **Sheafification reconciles the presheaf tensor with the tensor of the
sheafified factors.** For presheaves of modules `P, Q` on `X`, sheafifying the
presheaf tensor `P ⊗ Q` agrees with sheafifying the tensor of the underlying
presheaves of their sheafifications `(a P).val ⊗ (a Q).val`, where
`a = PresheafOfModules.sheafification (𝟙 𝒪_X)`. This is the "sheafification is
monoidal" reconciliation, built — exactly as in `tensorObj_assoc_iso` — by
whiskering the sheafification unit `η` (a `J.W`-morphism, hence locally bijective)
on each side and inverting under `a` via `isIso_sheafification_map_of_W` together
with the flatness-free `W_whisker{Right,Left}_of_W`. It is the bridge reconciling a
presheaf-level tensorator with the substrate `⊗_X` (whose `.val` carries an extra
sheafification on each factor), as needed by the pullback-monoidality comparison
`pullbackTensorIso`. -/
private noncomputable def sheafifyTensorUnitIso {X : Scheme.{u}}
    (P Q : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).obj
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) ≅
      (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).obj
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
          ((PresheafOfModules.sheafification
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).obj P).val
          ((PresheafOfModules.sheafification
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).obj Q).val) := by
  letI instMS : MonoidalCategoryStruct (_root_.PresheafOfModules (Sheaf.val X.ringCatSheaf)) :=
    inferInstanceAs (MonoidalCategoryStruct
      (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))
  set a := PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val) with ha
  set η := (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).unit with hη
  have hηP : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app P)) := by
    rw [hη, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.GrothendieckTopology.W_toSheafify _ _
  have hηQ : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app Q)) := by
    rw [hη, PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact CategoryTheory.GrothendieckTopology.W_toSheafify _ _
  have hW1 : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map (η.app P ▷ Q)) :=
    PresheafOfModules.W_whiskerRight_of_W (R := X.presheaf) Q (η.app P) hηP
  have hW2 : (Opens.grothendieckTopology X).W
      ((PresheafOfModules.toPresheaf _).map ((a.obj P).val ◁ η.app Q)) :=
    PresheafOfModules.W_whiskerLeft_of_W (R := X.presheaf) (a.obj P).val (η.app Q) hηQ
  have hi1 : IsIso (a.map (η.app P ▷ Q)) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 X.ringCatSheaf.val) _ hW1
  have hi2 : IsIso (a.map ((a.obj P).val ◁ η.app Q)) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 X.ringCatSheaf.val) _ hW2
  exact (@asIso _ _ _ _ _ hi1) ≪≫ (@asIso _ _ _ _ _ hi2)

/-- **The presheaf-of-modules pushforward is lax monoidal** (the analogist-named `μ_G`,
Mathlib-absent at the pin). For a morphism `φ : S₀ ⋙ forget₂ ⟶ F.op ⋙ (R₀ ⋙ forget₂)`
of presheaves of *commutative* rings, `PresheafOfModules.pushforward φ` unfolds to
`pushforward₀OfCommRingCat F R₀ ⋙ restrictScalars φ`, the composite of the strong-monoidal
topological pushforward `pushforward₀OfCommRingCat` (Mathlib) and the lax-monoidal
`restrictScalars φ` (project `restrictScalarsLaxMonoidal`), hence lax monoidal by
`Functor.LaxMonoidal.comp`.

The hypothesis necessarily uses the *inner* `forget₂` association (`F.op ⋙ (R₀ ⋙ forget₂)`,
the form `PresheafOfModules.pushforward` expects), but the monoidal-category instance on the
middle presheaf is keyed on the *outer* association `(F.op ⋙ R₀) ⋙ forget₂` (the form
`pushforward₀OfCommRingCat`'s target carries). The two are defeq; bridging them with a local
`MonoidalCategory` instance triggers a kernel-rejected diamond, so instead `φ` is defeq-cast
to the outer form (`φ'`) for the `restrictScalars` factor, and the resulting composite — defeq
to `pushforward φ` — is transported back by `exact`. This is the right-adjoint lax structure
that an eventual oplax comparison `δ` on the abstract left-adjoint pullback would inherit.
Project-local supplement; reusable for the general pullback-monoidality build. -/
noncomputable instance presheafPushforwardLaxMonoidal
    {C D : Type u} [Category.{u} C] [Category.{u} D] {F : C ⥤ D}
    {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.pushforward φ).LaxMonoidal := by
  let φ' : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      (F.op ⋙ R₀) ⋙ forget₂ CommRingCat RingCat := φ
  have h : (PresheafOfModules.pushforward₀OfCommRingCat F R₀ ⋙
      PresheafOfModules.restrictScalars φ').LaxMonoidal := inferInstance
  exact h

/-- **The abstract presheaf-of-modules pullback is oplax monoidal**, with canonical
comparison map `δ_{A,B} : f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B`. This is the mate of the lax
tensorator of `pushforward φ` (`presheafPushforwardLaxMonoidal`) across the
pullback–pushforward adjunction, via Mathlib's doctrinal `leftAdjointOplaxMonoidal`. It
supplies the canonical comparison map that the eventual `pullbackTensorIso` upgrades to an
isomorphism — note the map exists for the *abstract* left adjoint with no sectionwise value
(no `MonoidalCategory (SheafOfModules)` is needed, contra the earlier reading: the comparison
lives at the presheaf level where `PresheafOfModules` IS monoidal). Project-local supplement;
what remains Mathlib-absent is the concrete inverse-image model needed to prove `δ` is an
iso (see the Phase-2 note below). -/
noncomputable instance presheafPullbackOplaxMonoidal
    {C D : Type u} [Category.{u} C] [Category.{u} D] {F : C ⥤ D}
    {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat))
    [(PresheafOfModules.pushforward φ).IsRightAdjoint] :
    (PresheafOfModules.pullback φ).OplaxMonoidal :=
  (PresheafOfModules.pullbackPushforwardAdjunction φ).leftAdjointOplaxMonoidal

/-! ### Phase 2 — `pullbackTensorIso` status (iter-242 finding)

`pullbackUnitIso` (Phase 1) is DONE (above). The remaining `pullbackTensorIso`
(`f^*(M ⊗ N) ≅ f^*M ⊗ f^*N`, general `f`) is a genuine Mathlib-scale build, blocked
on a Mathlib-absent ingredient confirmed this iter:

  • `Scheme.Modules.pullback f` and the underlying `PresheafOfModules.pullback φ.hom`
    are BOTH `(pushforward _).leftAdjoint` — an ABSTRACT left adjoint with no sectionwise
    value. The blueprint route "build a concrete strong-monoidal `P` ≅ pullback, then
    transport via `leftAdjointUniq`" requires a CONCRETE model `P` of the pullback.
  • For an OPEN immersion (`tensorObj_restrict_iso`) the concrete model was
    `pushforward β` (β = the structure ring ISO), strong-monoidal via
    `restrictScalarsMonoidalOfBijective`. For a GENERAL `f` the concrete left adjoint is
    the inverse-image `(inverse-image presheaf) ⋙ extendScalars`: the underlying-presheaf
    inverse image is a LEFT KAN EXTENSION along `(Opens.map f.base).op` (a colimit, NOT
    sectionwise), and neither `PresheafOfModules.extendScalars` nor a concrete
    inverse-image-of-presheaves-of-modules functor exists in Mathlib at the pin. Building
    that concrete strong-monoidal functor + its adjunction to `pushforward` is the genuine
    multi-hundred-LOC obligation (Mathlib-scale; the `distribBaseChange` strong-monoidal
    core exists only at `ModuleCat.extendScalars`, the topological inverse image does not).

The reusable presheaf-level prerequisites toward that build are supplied just below
(`PresheafOfModules.pushforward` is LAX monoidal; hence the abstract presheaf pullback is
OPLAX monoidal with a canonical comparison map `δ`).

**SUPERSEDED (iter-243 pivot, see §D1'–D4' below).** The general-`f` concrete-model route is
ABANDONED and off-path. The relative Picard consumer only ever needs `δ` to be an iso on LINE
BUNDLES, and there iso-ness comes via the **local-trivialisation chart-chase** (D2'–D4'), NOT via a
concrete inverse-image model: the oplax `δ` is sheafified (`pullbackTensorMap`), reduced to the
single sheafified-presheaf comparison (`isIso_pullbackTensorMap_of_isIso_sheafifyDelta`), shown iso
on the unit pair (D2'), and globalised over a trivialising cover (D4', `isIso_of_isIso_restrict`).
The "no free oplax ⇒ preserves invertibles" obstruction (`Γ(ℙ¹,𝒪(1)) = 0`) is real for a GENERAL
module but is sidestepped for line bundles by the chart-chase — no concrete model is built. -/

/-- **Identifying the sheafified presheaf-pullback of `M.val` with the abstract pullback.**
For `f : Y ⟶ X` and `M : X.Modules`, sheafifying the presheaf-level pullback of the
underlying presheaf `M.val` recovers the abstract `𝒪`-module pullback `(pullback f).obj M`.
This is the per-object form of `SheafOfModules.sheafificationCompPullback` composed with the
sheafification counit on the (already-sheaf) `M`; it is the bridge used to reconcile the
right-hand side of the pullback–tensor comparison `pullbackTensorMap` with the substrate
`tensorObj` of the pullbacks. -/
noncomputable def pullbackValIso {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules) :
    (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).obj
        ((PresheafOfModules.pullback (f.toRingCatSheafHom).hom).obj M.val)
      ≅ (Scheme.Modules.pullback f).obj M :=
  ((SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).app M.val).symm ≪≫
    (Scheme.Modules.pullback f).mapIso
      ((asIso (PresheafOfModules.sheafificationAdjunction
        (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).counit).app M)

/-- **The sheaf-level pullback–tensor comparison map `δ_sheaf`** (blueprint
`lem:pullback_tensor_map`). For a morphism of schemes `f : Y ⟶ X` and arbitrary
`M N : X.Modules`, the canonical comparison morphism
`f^*(M ⊗_X N) ⟶ f^*M ⊗_Y f^*N`. It is the sheaf-level transport of the presheaf-level
oplax comparison `δ` (`presheafPullbackOplaxMonoidal`) through sheafification, assembled
from the `sheafificationCompPullback` device, `sheafifyTensorUnitIso`, and `pullbackValIso`.
This is a *map only*: in general it is not asserted to be an isomorphism (the invertible
case is upgraded to an iso by local trivialisation in `IsInvertible.pullback`). -/
noncomputable def pullbackTensorMap {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) :
    (Scheme.Modules.pullback f).obj (tensorObj M N) ⟶
      tensorObj ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) := by
  let φ := f.toRingCatSheafHom
  let φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) := φ.hom
  let a_Y := PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)
  refine ((SheafOfModules.sheafificationCompPullback φ).app
      (PresheafOfModules.Monoidal.tensorObj M.val N.val)).hom ≫ ?_
  refine a_Y.map (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val) ≫ ?_
  refine (sheafifyTensorUnitIso (X := Y)
      ((PresheafOfModules.pullback φ').obj M.val)
      ((PresheafOfModules.pullback φ').obj N.val)).hom ≫ ?_
  exact a_Y.map (MonoidalCategory.tensorHom
    (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
    ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
    ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom))

/-! ## Project-local Mathlib supplement — D1: the presheaf pullback Lan decomposition

These are general `PresheafOfModules` statements (any `F : C ⥤ D`, ring presheaves
`R, S`), not specific to schemes; they are project-local because Mathlib's pinned commit
exposes neither `extendScalars` nor `pullback₀` at the presheaf-of-modules level. Both are
realised as the left adjoint of an existing right adjoint: `pushforward₀ F R` is
definitionally `pushforward (𝟙 (F.op ⋙ R))` (because `restrictScalars (𝟙) = 𝟭` on the nose,
witnessed by Mathlib's `restrictScalars (𝟙 R)).Full := inferInstanceAs (𝟭 _).Full`), and
`restrictScalars φ` is definitionally `pushforward (F := 𝟭) φ`; since `pushforward _` is
always a right adjoint, so are these two, and their left adjoints `pullback₀`/`extendScalars`
exist. The decomposition `pullback φ ≅ extendScalars φ ⋙ pullback₀` then follows from the
definitional factorisation `pushforward φ = pushforward₀ F R ⋙ restrictScalars φ` by
uniqueness of left adjoints (`Adjunction.leftAdjointCompIso`).

Per blueprint `lem:pullback_lan_decomposition` (D1). **OFF-PATH (iter-243 pivot).** D1 is
axiom-clean and self-contained, but it was the first brick of the ABANDONED general
strong-monoidal pullback build (`sec:tensorobj_pullback_monoidality`, route (e)); the active
route is the loc-triv chart-chase D1'–D4' (§below), which does NOT consume `extendScalars`/
`pullback₀`. Retained as a correct, reusable presheaf-level decomposition; do NOT extend it
toward the general build (D2 scalar-strong / D3 topological-interchange are NOT pursued). -/

section PullbackLanDecomposition

variable {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
  {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}

end PullbackLanDecomposition

/-! ## Project-local Mathlib supplement — D1'–D4' loc-triv pullback–tensor comparison

The locally-trivial-restricted upgrade of the oplax comparison map
`pullbackTensorMap` (`f^*(M ⊗ N) ⟶ f^*M ⊗ f^*N`) to an isomorphism, blueprint
§`sec:tensorobj_pullback_monoidality`, sub-lemmas D1'–D4'. -/

section LocTrivPullbackTensor

/-- **The sheafified `⊗ₘ` of the two `pullbackValIso`s (piece 4 of `pullbackTensorMap`) is an
iso.** Factored out as a top-level lemma so the `tensorIso (C := _ ⋙ forget₂)` elaboration mirrors
the proven `tensorObjIsoOfIso` (it does not elaborate cleanly inside a tactic block carrying
`extract_lets` locals). Project-local helper for `isIso_pullbackTensorMap_of_isIso_sheafifyDelta`. -/
private lemma isIso_sheafify_tensorHom_pullbackValIso {X Y : Scheme.{u}}
    (f : Y ⟶ X) (M N : X.Modules) :
    IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
      (MonoidalCategory.tensorHom
        (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
        ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
        ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom))) :=
  ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).mapIso
    (MonoidalCategory.tensorIso
      (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
      ((SheafOfModules.forget Y.ringCatSheaf).mapIso (pullbackValIso f M))
      ((SheafOfModules.forget Y.ringCatSheaf).mapIso (pullbackValIso f N)))).isIso_hom

/-- **Reduction of `pullbackTensorMap` iso-ness to the sheafified presheaf δ.**

`pullbackTensorMap f M N` is the four-fold composite
`(sheafificationCompPullback).hom ≫ a_Y.map δ ≫ (sheafifyTensorUnitIso).hom ≫ a_Y.map (tensorHom …)`.
Three of the four factors (`sheafificationCompPullback`, `sheafifyTensorUnitIso`,
and the `tensorHom` of the two `pullbackValIso`s) are isomorphisms unconditionally;
the only conditional factor is the sheafification `a_Y.map δ` of the presheaf-level
oplax comparison `δ`. Hence `pullbackTensorMap f M N` is an iso whenever that
sheafified δ is an iso. This isolates the SOLE remaining content (the sheafified δ)
for D2' (unit pair) and D4' (chart-chase). Project-local. -/
lemma isIso_pullbackTensorMap_of_isIso_sheafifyDelta {X Y : Scheme.{u}}
    (f : Y ⟶ X) (M N : X.Modules)
    (h : letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
          (f.toRingCatSheafHom).hom
        IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf)
          (𝟙 Y.ringCatSheaf.val)).map
          (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val))) :
    IsIso (pullbackTensorMap f M N) := by
  unfold pullbackTensorMap
  extract_lets φ φ' a_Y
  -- piece 2 (the sheafified δ) is the only conditional factor — supplied by `h`.
  haveI hδ : IsIso (a_Y.map
      (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val)) := h
  -- pieces 1 and 3 are `Iso.hom`s; piece 4 is `a_Y.map` of the (iso) `⊗ₘ` of the two
  -- `pullbackValIso`s, supplied by the factored top-level helper.
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' hδ
    (IsIso.comp_isIso' inferInstance (isIso_sheafify_tensorHom_pullbackValIso f M N)))

/-- **Converse of `isIso_sheafification_map_of_W`.** A morphism of presheaves of modules whose
image under the associated-sheaf functor is an isomorphism lies (on underlying additive presheaves)
in the sheafification localizer `J.W`. This is the same morphism-property identity
`PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms` (the sheafification
functor *is* the localization at `J.W.inverseImage (toPresheaf _)`) read backwards. Project-local:
needed to feed the flatness-free whiskering lemmas `W_whisker{Left,Right}_of_W` from a sheafified
iso (the D2' η-bridge route, below). -/
private lemma W_of_isIso_sheafification {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R₀ : Cᵒᵖ ⥤ RingCat} {Rsh : CategoryTheory.Sheaf J RingCat} (α : R₀ ⟶ Rsh.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat] [CategoryTheory.HasWeakSheafify J AddCommGrpCat]
    {A B : _root_.PresheafOfModules.{u} R₀} (f : A ⟶ B)
    (hf : IsIso ((PresheafOfModules.sheafification α).map f)) :
    J.W ((PresheafOfModules.toPresheaf R₀).map f) := by
  have h := PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms (J := J) α
  have h2 : (CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules Rsh)).inverseImage
      (PresheafOfModules.sheafification α) f := hf
  rw [← h] at h2
  exact h2

/-- **D2' δ-wrapping — the sheafified cotensorator on the unit pair is an iso, given the η-bridge.**

The presheaf-level oplax unitality `Functor.OplaxMonoidal.left_unitality_hom` factors the
cotensorator `δ (pullback φ') 𝟙_ 𝟙_` of the abstract presheaf pullback through the unit comparison
`η (pullback φ')` (right-whiskered by `F.obj 𝟙_`) and the (iso) left unitor. Sheafifying, the
unitor factor and the `F.map (λ_ 𝟙_)` factor are isomorphisms unconditionally; the whiskered
`η`-factor `a_Y.map (η F ▷ F.obj 𝟙_)` is an iso whenever `a_Y.map (η F)` is — because a sheafified
iso lies in `J.W` (`W_of_isIso_sheafification`), `J.W` is stable under right-whiskering
(`W_whiskerRight_of_W`, flatness-free), and `J.W`-morphisms sheafify to isos
(`isIso_sheafification_map_of_W`). Hence the sheafified `δ` on the unit pair is an iso, which is
exactly the hypothesis the reduction brick `isIso_pullbackTensorMap_of_isIso_sheafifyDelta` consumes
on `M = N = 𝒪`. Project-local; the **δ-wrapping** half of D2' (`lem:pullback_tensor_iso_unit`),
self-contained modulo the η-bridge `IsIso (a_Y.map (η (pullback φ')))`. -/
lemma isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
          (f.toRingCatSheafHom).hom
        IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
          (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ')))) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
      (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ')
        (SheafOfModules.unit X.ringCatSheaf).val (SheafOfModules.unit X.ringCatSheaf).val)) := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set a_Y := PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val) with ha
  change IsIso (a_Y.map (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') (𝟙_ _) (𝟙_ _)))
  set F := PresheafOfModules.pullback φ' with hF
  have hWη : (Opens.grothendieckTopology (Y : TopCat)).W
      ((PresheafOfModules.toPresheaf _).map (Functor.OplaxMonoidal.η F)) :=
    W_of_isIso_sheafification (𝟙 Y.ringCatSheaf.val) _ h
  have hWw : (Opens.grothendieckTopology (Y : TopCat)).W
      ((PresheafOfModules.toPresheaf _).map (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ _))) :=
    PresheafOfModules.W_whiskerRight_of_W (R := Y.presheaf) _ _ hWη
  haveI hIsoW : IsIso (a_Y.map (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ _))) :=
    PresheafOfModules.isIso_sheafification_map_of_W (𝟙 Y.ringCatSheaf.val) _ hWw
  haveI hIsoLam : IsIso (a_Y.map (λ_ (F.obj (𝟙_ _))).hom) := inferInstance
  have hBC : IsIso (a_Y.map
      (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ _) ≫ (λ_ (F.obj (𝟙_ _))).hom)) := by
    rw [Functor.map_comp]; infer_instance
  haveI hD : IsIso (a_Y.map (F.map (λ_ (𝟙_ _)).hom)) := inferInstance
  have hlu := Functor.OplaxMonoidal.left_unitality_hom F (𝟙_ _)
  have key : a_Y.map (Functor.OplaxMonoidal.δ F (𝟙_ _) (𝟙_ _)) ≫
      a_Y.map (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ _) ≫ (λ_ (F.obj (𝟙_ _))).hom)
      = a_Y.map (F.map (λ_ (𝟙_ _)).hom) := by
    rw [← Functor.map_comp]; exact congrArg _ hlu
  have heq : a_Y.map (Functor.OplaxMonoidal.δ F (𝟙_ _) (𝟙_ _))
      = a_Y.map (F.map (λ_ (𝟙_ _)).hom) ≫
        inv (a_Y.map (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ _) ≫ (λ_ (F.obj (𝟙_ _))).hom)) := by
    rw [← key, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [heq]; infer_instance

/-- **D2' assembly — `pullbackTensorMap` on the unit pair is an iso, given the η-bridge.**
Chains the δ-wrapping `isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta` into the reduction brick
`isIso_pullbackTensorMap_of_isIso_sheafifyDelta` (on `M = N = 𝒪`). This is the full statement of
D2' (`lem:pullback_tensor_iso_unit`) modulo the single remaining η-bridge hypothesis
`IsIso (a_Y.map (η (pullback φ')))` (the sheafification-mate identification of the sheafified
presheaf unit comparison with `pullbackUnitIso`, the unit-side analog of
`pullbackObjUnitToUnit_comp`). Project-local. -/
lemma isIso_pullbackTensorMap_unitPair_of_isIso_sheafifyEta {X Y : Scheme.{u}} (f : Y ⟶ X)
    (h : letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
          (f.toRingCatSheafHom).hom
        IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
          (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ')))) :
    IsIso (pullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf)) := by
  apply isIso_pullbackTensorMap_of_isIso_sheafifyDelta
  exact isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta f h

/-! **D2' onward — handoff (iter-246).** The δ-wrapping half of D2' is now LANDED axiom-clean:
`isIso_sheafifyDelta_unitPair_of_isIso_sheafifyEta` reduces the sheafified `δ` on the unit pair to
the η-bridge `IsIso (a_Y.map (η (pullback φ')))` (via `left_unitality_hom` + the W-stable
right-whiskering `W_whiskerRight_of_W` fed by the new converse `W_of_isIso_sheafification`), and
`isIso_pullbackTensorMap_unitPair_of_isIso_sheafifyEta` chains it into the reduction brick. So the
SOLE remaining content of D2' is the **η-bridge**

  `IsIso (a_Y.map (η (PresheafOfModules.pullback φ')))`.

This is the commuting square (`sheafifyUnitIso` is its right vertical, built above)
`a_Y.map (η F) ≫ sheafifyUnitIso.hom = (pullbackValIso f 𝒪_X).hom ≫ pullbackObjUnitToUnit φ`.
Transposing across `SheafOfModules.pullbackPushforwardAdjunction φ` (apply `.homEquiv.injective`,
then `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`, `homEquiv_unit`,
`leftAdjointOplaxMonoidal_η`, `homEquiv_counit`) reduces the square to the concrete pushforward-side
identity (sheafification-mate bridge):

  `sheafAdj.unit.app 𝒪_X ≫ (pushforward φ).map ((pullbackValIso).inv ≫
      a_Y.map (pullback_pre.map ε_pre ≫ presheafAdj.counit) ≫ sheafifyUnitIso.hom)
    = unitToPushforwardObjUnit φ`,

where `ε_pre = LaxMonoidal.ε (PresheafOfModules.pushforward φ.hom)`. The glue is the leftAdjointUniq
compatibility of `SheafOfModules.sheafificationCompPullback`/`pullbackIso` (the bridges inside
`pullbackValIso`) — `Adjunction.{homEquiv_,unit_,}leftAdjointUniq_hom_app`,
`leftAdjointUniq_hom_app_counit` — relating the presheaf and sheaf adjunction units; this is the
unit-side analog of `pullbackObjUnitToUnit_comp`, NOT yet assembled (a self-contained next step).

* **D3'/D4'** (the chart-chase): use `isIso_of_isIso_restrict` (L546) over the common trivialising
  cover; on each chart D3' (δ commutes with the open-immersion base-change square — the sole
  genuinely-new mate calculus, analog of `pullbackObjUnitToUnit_comp`) localises the sheafified δ,
  the naturality D1' transports to the unit pair, and D2' closes. Each stays inside
  `IsIso (a_Y.map δ …)`, so `isIso_pullbackTensorMap_of_isIso_sheafifyDelta` is the shared entry. -/

/-- **Codomain identification for the D2' η-bridge.** The sheafification counit identifies the
sheafified presheaf monoidal unit `a_Y.obj 𝟙_` with the sheaf-level structure module
`𝒪_Y = SheafOfModules.unit Y.ringCatSheaf` (`𝟙_ = (unit Y).val` definitionally, and `unit Y` is
already a sheaf, so the counit at it is an isomorphism). This is the right-hand vertical of the
η-bridge square `a_Y.map (η (pullback φ')) ≫ sheafifyUnitIso.hom
= (pullbackValIso f 𝒪_X).hom ≫ pullbackObjUnitToUnit φ` whose commutativity is the remaining
content of D2' (see the handoff note above and `task_results`). Project-local building block. -/
noncomputable def sheafifyUnitIso {Y : Scheme.{u}} :
    (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).obj
        (𝟙_ (_root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat)))
      ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (asIso (PresheafOfModules.sheafificationAdjunction
    (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).counit).app (SheafOfModules.unit Y.ringCatSheaf)

/-- **Presheaf-side mate identity for the η-bridge** (`unit_app_unit_comp_map_η` instantiated).
For a scheme morphism `f : Y ⟶ X` with `φ' = f.toRingCatSheafHom.hom`, the presheaf-of-modules
adjunction unit at the monoidal unit, post-composed with the pushforward of the oplax unit
comparison `η (pullback φ')`, recovers the lax unit `ε (pushforward φ')`. This is the
presheaf-level driver of the D2' η-bridge: under sheafification (via `sheafificationCompPullback`)
it transports to the sheaf identity
`homEquiv (pullbackObjUnitToUnit φ) = unitToPushforwardObjUnit φ`.
Project-local: it certifies that the project's `presheafPushforwardLaxMonoidal` /
`presheafPullbackOplaxMonoidal` instances are `Adjunction.IsMonoidal`-compatible, so the Mathlib
mate identity fires for this concrete adjunction. -/
lemma presheafUnit_comp_map_eta {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    (PresheafOfModules.pullbackPushforwardAdjunction φ').unit.app
        (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))) ≫
      (PresheafOfModules.pushforward φ').map
        (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ'))
      = Functor.LaxMonoidal.ε (PresheafOfModules.pushforward φ') := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  haveI : (PresheafOfModules.pushforward φ').IsRightAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction φ').isRightAdjoint
  exact Adjunction.unit_app_unit_comp_map_η (PresheafOfModules.pullbackPushforwardAdjunction φ')

/-- **D2' η-bridge — IsIso reduction to the unit comparison square** (axiom-clean plumbing).
Given the commuting square identifying the sheafified presheaf unit comparison `a_Y.map (η F)`
with the sheaf-level `pullbackObjUnitToUnit φ` through the canonical isos `pullbackValIso` and
`sheafifyUnitIso`, the η-bridge `IsIso (a_Y.map (η (pullback φ')))` follows (the comparison
`pullbackObjUnitToUnit φ` is an iso since `Opens.map f.base` is always `Final`). This isolates the
SOLE remaining mathematical content of the η-bridge as the square hypothesis `hsq` (= the unit-side
analog of `pullbackObjUnitToUnit_comp`, see handoff in `task_results`). Project-local. -/
lemma isIso_sheafifyEta_of_unitSquare {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hsq : letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
          (f.toRingCatSheafHom).hom
        (pullbackValIso f (SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
            (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ')) ≫ sheafifyUnitIso.hom
          = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    IsIso ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
      (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ'))) := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set a_Y := PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val) with ha
  set F := PresheafOfModules.pullback φ' with hF
  haveI hfin : (TopologicalSpace.Opens.map f.base).Final := final_of_representablyFlat _
  haveI hpbu : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    isIso_pbu_of_final f
  have key : a_Y.map (Functor.OplaxMonoidal.η F) ≫ sheafifyUnitIso.hom
      = (pullbackValIso f (SheafOfModules.unit X.ringCatSheaf)).hom ≫
        SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom :=
    (Iso.inv_comp_eq _).mp hsq
  rw [(Iso.eq_comp_inv sheafifyUnitIso).mpr key]
  exact IsIso.comp_isIso' (IsIso.comp_isIso' inferInstance hpbu) inferInstance

/-- **Composite-adjunction `homEquiv` factorisation** (blueprint
`lem:comp_homequiv_factor_sheafify_pullback`, ★ step 3). For composable adjunctions
`adj₁ : L₁ ⊣ R₁` and `adj₂ : L₂ ⊣ R₂`, the hom-set bijection of the composite adjunction
`A = adj₁.comp adj₂ : L₁ ⋙ L₂ ⊣ R₂ ⋙ R₁` factors as the composite of the two factor
bijections: a morphism `(L₁ ⋙ L₂).obj c ⟶ e` is transposed first across `adj₂` and then
across `adj₁`. This is the standard naturality of `homEquiv` under composition of adjunctions,
read off the `homEquiv = unit ≫ R.map` formula together with `Adjunction.comp_unit_app`.
Project-local. -/
lemma compHomEquivFactor {C₁ : Type*} {C₂ : Type*} {C₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃]
    {L₁ : C₁ ⥤ C₂} {R₁ : C₂ ⥤ C₁} {L₂ : C₂ ⥤ C₃} {R₂ : C₃ ⥤ C₂}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) {c : C₁} {e : C₃}
    (g : (L₁ ⋙ L₂).obj c ⟶ e) :
    (adj₁.comp adj₂).homEquiv c e g
      = adj₁.homEquiv c (R₂.obj e) (adj₂.homEquiv (L₁.obj c) e g) := by
  simp only [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Functor.comp_map,
    Functor.map_comp]
  exact Category.assoc _ _ _

/-- **The `sheafificationCompPullback` comparison is the canonical `leftAdjointUniq`** of the
two composite adjunctions of the unit square. With
`A = (sheafificationAdjunction 𝟙_X).comp (SheafOfModules.pullbackPushforwardAdjunction φ)` (left
adjoint `a_X ⋙ SheafOfModules.pullback φ`) and
`B = (PresheafOfModules.pullbackPushforwardAdjunction φ').comp (sheafificationAdjunction 𝟙_Y)`
(left adjoint `PresheafOfModules.pullback φ' ⋙ a_Y`), the Mathlib device
`SheafOfModules.sheafificationCompPullback φ` is, on the nose (`rfl`),
`Adjunction.leftAdjointUniq A B`. This is the definitional identification the blueprint asserts
(`lem:leftadjointuniq_app_unit_eta`): it is what makes the mate-calculus `homEquiv_leftAdjointUniq`
identities fire for the concrete unit-square adjunctions. Project-local linchpin. -/
lemma sheafificationCompPullback_eq_leftAdjointUniq {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom
      = ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.val)).comp
          (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)).leftAdjointUniq
        ((PresheafOfModules.pullbackPushforwardAdjunction φ').comp
          (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
            (𝟙 Y.ringCatSheaf.val))) :=
  rfl

/-- **leftAdjointUniq transport of the composite unit** (blueprint
`lem:leftadjointuniq_app_unit_eta`, ★ step 4). For the two composite adjunctions `A`, `B` of the
unit square, applying `A.homEquiv` to the `𝟙_`-component of the comparison
`sheafificationCompPullback φ` recovers `B.unit.app 𝟙_`, which expands (by
`Adjunction.comp_unit_app` on `B`) into the presheaf pullback–pushforward unit followed by the
pushforward of the sheafification unit. This is the genuinely adjunction-theoretic head of step 4
of `lem:eta_bridge_unit_square`. Project-local. -/
lemma leftAdjointUniqUnitEta {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.val)).comp
        (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)).homEquiv
        (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))) _
        ((SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app
          (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))))
      = (PresheafOfModules.pullbackPushforwardAdjunction φ').unit.app
          (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))) ≫
        (PresheafOfModules.pushforward φ').map
          ((PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
              (𝟙 Y.ringCatSheaf.val)).unit.app
            ((PresheafOfModules.pullback φ').obj
              (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))))) := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set A := (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.val)).comp
      (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)
    with hA
  set B := (PresheafOfModules.pullbackPushforwardAdjunction φ').comp
      (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val))
    with hB
  have hg : (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app
        (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))
      = (A.leftAdjointUniq B).hom.app
        (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))) := rfl
  rw [hg]
  refine Eq.trans (Adjunction.homEquiv_leftAdjointUniq_hom_app A B
    (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))) ?_
  rw [hB, Adjunction.comp_unit_app]
  rfl

/-- **leftAdjointUniq transport of the composite unit, general object** (the `P`-general form of
`leftAdjointUniqUnitEta`, ma-d3264 step 1). For the two composite adjunctions `A`, `B` of the unit
square and ANY presheaf of modules `P`, applying `A.homEquiv` to the `P`-component of the comparison
`sheafificationCompPullback φ` recovers `B.unit.app P`, expanded by `Adjunction.comp_unit_app` on `B`
as `PrPbPushAdj φ' .unit P ≫ pushforward φ' .map (sheafAdj_Y.unit (pullback φ' P))`. This is the
R1/R5-recovery brick of `sheafificationCompPullback_comp_tail`: it identifies the `sheafCompPb f .hom.app P`
factor with the composite-adjunction `B_f`-unit. The proof is the object-generic version of
`leftAdjointUniqUnitEta` (which is the `P := 𝟙_` specialization); nothing about `𝟙_` is used. -/
lemma leftAdjointUniqUnitEta_app {X Y : Scheme.{u}} (f : Y ⟶ X)
    (P : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
          (𝟙 X.ringCatSheaf.val)).comp
        (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)).homEquiv P _
        ((SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app P)
      = (PresheafOfModules.pullbackPushforwardAdjunction φ').unit.app P ≫
        (PresheafOfModules.pushforward φ').map
          ((PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
              (𝟙 Y.ringCatSheaf.val)).unit.app
            ((PresheafOfModules.pullback φ').obj P)) := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set A := (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.val)).comp
      (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom)
    with hA
  set B := (PresheafOfModules.pullbackPushforwardAdjunction φ').comp
      (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val))
    with hB
  have hg : (SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom).hom.app P
      = (A.leftAdjointUniq B).hom.app P := rfl
  rw [hg]
  refine Eq.trans (Adjunction.homEquiv_leftAdjointUniq_hom_app A B P) ?_
  rw [hB, Adjunction.comp_unit_app]
  rfl

/-- **`restrictScalars (𝟙 R)` is the identity on morphisms.** `restrictScalars (𝟙 R)` is defeq to the
identity functor `𝟭`, so its action on a morphism is the morphism itself. Stated as a *propositional*
rewrite (proved once over an abstract `g`, hence cheap) so that the `restrictScalars (𝟙)` wrappers in
the D2′ `(∗∗)` goal can be stripped by a single SYNTACTIC `rw` — avoiding the catastrophic whole-term
`whnf` that a `show`/`rfl` triggers on the sheafification-laden composites. Project-local. -/
lemma restrictScalarsId_map {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    {M N : _root_.PresheafOfModules R} (g : M ⟶ N) :
    (PresheafOfModules.restrictScalars (𝟙 R)).map g = g := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Step 7 — the presheaf lax-unit `ε` of `pushforward φ'` is the underlying presheaf map of
the sheaf-level structure-unit comparison `unitToPushforwardObjUnit φ`** (blueprint
`lem:epsilon_presheaf_to_sheaf_unit`). Both act sectionwise as `φ.hom.app X`. This is the SOLE
genuinely-new ingredient of the D2′ `(∗∗)` close: after the abstract telescope and the Y-side
sheafification triangle fold the big `homEquiv` argument down to `ε (pushforward φ')`, this lemma
lands it on `(unitToPushforwardObjUnit φ).val` (defeq `R_X.map (unitToPushforwardObjUnit φ)`).
Proved sectionwise via the `Functor.LaxMonoidal.comp` ε-formula (`pushforward₀`'s `ε = 𝟙`),
`restrictScalarsLaxε`, `ModuleCat.restrictScalars_η`, and `unitToPushforwardObjUnit_val_app_apply`.
Project-local. -/
lemma epsilonPresheafToSheafUnit {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    Functor.LaxMonoidal.ε (PresheafOfModules.pushforward φ')
      = (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom).val := by
  apply PresheafOfModules.hom_ext
  intro X₀
  apply ModuleCat.hom_ext
  ext r
  -- Provide the `CommRing` instance on the scalar ring `S₀` in the `(restrictScalars f).obj 𝟙_`
  -- spelling that `ModuleCat.restrictScalars_η` synthesises against (synthInstance does not reduce
  -- `(restrictScalars f).obj 𝟙_` to the `forget₂`-carrier where the canonical instance is keyed).
  letI : CommRing ↑((ModuleCat.restrictScalars
      (RingCat.Hom.hom ((Hom.toRingCatSheafHom f).hom.app X₀))).obj (𝟙_ (ModuleCat
        ↑((((TopologicalSpace.Opens.map f.base).op ⋙ Y.presheaf) ⋙
            forget₂ CommRingCat RingCat).obj X₀)))) :=
    inferInstanceAs (CommRing ↑((((TopologicalSpace.Opens.map f.base).op ⋙ Y.presheaf) ⋙
      forget₂ CommRingCat RingCat).obj X₀))
  -- LHS: `ε (pushforward φ')` reduces (through the `pushforward₀ ⋙ restrictScalars` composite,
  -- `pushforward₀`'s `ε = 𝟙`) to `ε (restrictScalars φ'.app X₀)`, hence to `φ'.app X₀` by
  -- `restrictScalars_η`.  RHS: `unitToPushforwardObjUnit_val_app_apply` gives `φ.hom.app X₀`.
  erw [SheafOfModules.unitToPushforwardObjUnit_val_app_apply, ModuleCat.restrictScalars_η]
  rfl

-- The sheafification-adjunction right-triangle / unit-naturality composites force `whnf` on the heavy
-- sheafification machinery (`𝟙_Yp` vs `(unit Y).val` defeq), exceeding the default 200000 budget.
set_option maxHeartbeats 1600000 in
/-- **Y-side sheafification right-triangle for the oplax unit comparison** (substep (ii) of the D2′
`(∗∗)` close). For `f : Y ⟶ X` with `φ' = f.toRingCatSheafHom.hom` and `F = pullback φ'`, the
sheafification unit at `F.obj 𝟙ᵖ`, post-composed with the underlying presheaf maps of `a_Y.map (η F)`
and `sheafifyUnitIso.hom`, recovers the oplax unit comparison `η F`. This is exactly
`Equiv.apply_symm_apply` for the presheaf sheafification adjunction `homEquiv`: the second factor
`a_Y.map (η F) ≫ sheafifyUnitIso.hom` is `homEquiv.symm (η F)` (its counit factor `sheafifyUnitIso.hom`
is the adjunction counit at the sheaf `𝒪_Y`), so `homEquiv` of it is `η F`. Extracted as a standalone
lemma so its elaboration cost does not bloat the heavy `pullbackEtaUnitSquare` telescope. Project-local. -/
lemma pullbackSheafifyUnitEtaTriangle {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Y.ringCatSheaf))).unit.app
        ((PresheafOfModules.pullback φ').obj
          (𝟙_ (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))))
      ≫ (((PresheafOfModules.sheafification (𝟙 (Sheaf.val Y.ringCatSheaf))).map
            (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ'))).val ≫ sheafifyUnitIso.hom.val)
      = Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ') := by
  letI : (PresheafOfModules.pushforward (Hom.toRingCatSheafHom f).hom).IsRightAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction _).isRightAdjoint
  -- Reassociate, fold the sheafification-unit naturality at `η F`, then the right-triangle on `𝒪_Y`.
  rw [← Category.assoc]
  erw [← (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Y.ringCatSheaf))).unit.naturality,
    Category.assoc, Functor.id_map]
  -- Y-side right triangle on the SHEAF `𝒪_Y = unit Y`: `sheafifyUnitIso = (asIso counit).app 𝒪_Y`.
  have htri : (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Y.ringCatSheaf))).unit.app
        (𝟙_ (_root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat)))
      ≫ sheafifyUnitIso.hom.val = 𝟙 _ := by
    rw [sheafifyUnitIso]
    simpa only [Iso.app_hom, asIso_hom] using
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Sheaf.val Y.ringCatSheaf))).right_triangle_components (SheafOfModules.unit Y.ringCatSheaf)
  -- `rw [htri]` cannot fire on the LHS (the codomain `𝟙_Yp` vs `(unit Y).val` are defeq only at
  -- non-reducible transparency).  Expand the RHS `η F` to `η F ≫ 𝟙` via `Category.comp_id` (its
  -- `η F` is read off the goal — no `OplaxMonoidal` re-synthesis), then `congr 1` reduces to `htri`.
  refine Eq.trans ?_ (Category.comp_id _)
  congr 1

-- The mate-calculus telescope (steps 1–6) plus the substep-(i) `.val` reshaping and the syntactic
-- `restrictScalars (𝟙)`-strip (`kabstract` on the sheafification-laden composites) exceed the default
-- 200000 budget; 3200000 is comfortably sufficient for the assembled proof.
set_option maxHeartbeats 3200000 in
/-- **The unit square** (blueprint `lem:eta_bridge_unit_square`, the assembly target). The
sheafified presheaf unit comparison `a_Y.map (η F)`, conjugated by the canonical isos
`pullbackValIso` and `sheafifyUnitIso`, equals the sheaf-level structure-unit comparison
`pullbackObjUnitToUnit φ`. The proof transposes the square across the *sheaf* pullback–pushforward
adjunction `pullbackPushforwardAdjunction φ` (`homEquiv.injective`); the right-hand side image is
`unitToPushforwardObjUnit φ` by `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`,
reducing the square to the concrete pushforward-side identity (∗∗), which telescopes through the
already-closed `compHomEquivFactor` (step 3), `leftAdjointUniqUnitEta` (step 4) and
`presheafUnit_comp_map_eta` (step 6). Project-local. -/
lemma pullbackEtaUnitSquare {X Y : Scheme.{u}} (f : Y ⟶ X) :
    letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
        (f.toRingCatSheafHom).hom
    (pullbackValIso f (SheafOfModules.unit X.ringCatSheaf)).inv ≫
        (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
          (Functor.OplaxMonoidal.η (PresheafOfModules.pullback φ')) ≫ sheafifyUnitIso.hom
        = SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom := by
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  set φ := f.toRingCatSheafHom with hφ
  -- Transpose across the sheaf pullback–pushforward adjunction.
  apply ((SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv
    (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit Y.ringCatSheaf)).injective
  rw [SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  -- We keep the goal in `homEquiv` form (NOT unfolding via `homEquiv_unit`), driving the
  -- telescope through the closed mate-lemmas `compHomEquivFactor`, `leftAdjointUniqUnitEta`,
  -- `presheafUnit_comp_map_eta` and the `rfl`-linchpin `sheafificationCompPullback_eq_leftAdjointUniq`.
  -- Step 1: decompose `pullbackValIso.inv` into `(pullback φ).map c⁻¹ ≫ (sheafificationCompPullback φ).hom`
  -- where `c = (asIso (sheafification-counit_X)).app 𝒪_X`.
  simp only [pullbackValIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  rw [Category.assoc]
  -- Step 2: pull the leading `(pullback φ).map c⁻¹` out of `homEquiv` (`homEquiv_naturality_left`),
  -- then peel off the trailing `rest = a_Y.map (η F) ≫ sheafifyUnitIso.hom` (`homEquiv_naturality_right`).
  erw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  -- Steps 3+4: rewrite `sheafAdj.homEquiv (sheafificationCompPullback φ).hom.app 𝟙ᵖ` via the
  -- composite-adjunction factorisation `compHomEquivFactor` and then `leftAdjointUniqUnitEta`.
  have hkey :
      (SheafOfModules.pullbackPushforwardAdjunction φ).homEquiv _ _
          ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app
            (SheafOfModules.unit X.ringCatSheaf).val).hom
        = ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
              (𝟙 X.ringCatSheaf.val)).homEquiv _ _).symm
            (((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
                (𝟙 X.ringCatSheaf.val)).comp
                (SheafOfModules.pullbackPushforwardAdjunction φ)).homEquiv _ _
              ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app
                (SheafOfModules.unit X.ringCatSheaf).val).hom) := by
    rw [Equiv.eq_symm_apply, ← compHomEquivFactor]
  erw [hkey, leftAdjointUniqUnitEta f]
  -- Fold the trailing `(pushforward φ).map rest` into the X-side `homEquiv.symm`
  -- (`homEquiv_naturality_right_symm`): `symm(x) ≫ k = symm(x ≫ R_X.map k)`.
  erw [← Adjunction.homEquiv_naturality_right_symm]
  -- X-triangle (`right_triangle_components`): the sheafification unit/counit on the sheaf `𝒪_X`
  -- cancel, collapsing `homEquiv (c.hom ≫ unitToPushforwardObjUnit φ)` to `(unitToPushforwardObjUnit φ).val`.
  have hXtri : (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val X.ringCatSheaf))).unit.app
        (SheafOfModules.unit X.ringCatSheaf).val ≫
      (PresheafOfModules.restrictScalars (𝟙 (Sheaf.val X.ringCatSheaf))).map
        ((SheafOfModules.forget X.ringCatSheaf).map
          ((asIso (PresheafOfModules.sheafificationAdjunction
              (𝟙 (Sheaf.val X.ringCatSheaf))).counit).app (SheafOfModules.unit X.ringCatSheaf)).hom)
      = 𝟙 _ := by
    simpa only [Iso.app_hom, asIso_hom, Functor.comp_map] using
      (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Sheaf.val X.ringCatSheaf))).right_triangle_components (SheafOfModules.unit X.ringCatSheaf)
  have hrhs : ((PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val X.ringCatSheaf))).homEquiv
        (SheafOfModules.unit X.ringCatSheaf).val
        ((SheafOfModules.pushforward φ).obj (SheafOfModules.unit Y.ringCatSheaf)))
      (((asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val X.ringCatSheaf))).counit).app
          (SheafOfModules.unit X.ringCatSheaf)).hom ≫ SheafOfModules.unitToPushforwardObjUnit φ)
      = (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 (Sheaf.val X.ringCatSheaf))).map
          (SheafOfModules.unitToPushforwardObjUnit φ) := by
    rw [Adjunction.homEquiv_unit]
    simp only [Functor.comp_map, Functor.map_comp]
    exact (Category.assoc _ _ _).symm.trans (hXtri ▸ Category.id_comp _)
  -- Move `c⁻¹` to the RHS (`Iso.inv_comp_eq`), transpose the X-side `homEquiv.symm`
  -- (`Equiv.symm_apply_eq`), and collapse via `hrhs`, reducing to a PRESHEAF-level equation
  -- whose RHS is `(unitToPushforwardObjUnit φ).val`.
  rw [Iso.inv_comp_eq, Equiv.symm_apply_eq]
  refine Eq.trans ?_ hrhs.symm
  -- REMAINING (∗∗): the concrete pushforward-side presheaf identity.  Substep (i): split the `.val`
  -- of `g = a_Y.map (η F) ≫ sheafifyUnitIso.hom` and reduce `R_X.map ((pushforward φ).map g)`.
  simp only [Functor.comp_map, SheafOfModules.forget_map, SheafOfModules.pushforward_map_val,
    SheafOfModules.comp_val]
  -- Strip the two `restrictScalars (𝟙)` wrappers SYNTACTICALLY via `restrictScalarsId_map`, landing
  -- the goal in the syntactic presheaf category (no `whnf` on `rs`-over-sheafification — that is
  -- catastrophic).  This succeeds and leaves the CLEAN presheaf goal
  --   `(u ≫ pf₁.map toSheafify_Y) ≫ pf₂.map ((a_Y.map (η F)).val ≫ sheafifyUnitIso.hom.val)
  --      = (unitToPushforwardObjUnit (Hom.toRingCatSheafHom f)).val`,
  -- where `pf₁ = pushforward (Hom.toRingCatSheafHom f).hom` and `pf₂ = pushforward φ.hom` are DEFEQ
  -- but spelled differently (`Hom.toRingCatSheafHom f` from `leftAdjointUniqUnitEta` vs the `set`-local
  -- `φ`).  The remaining math is exactly: merge the two `pushforward`-images via `Functor.map_comp`,
  -- fold `toSheafify_Y ≫ (a_Y.map (η F)).val ≫ sheafifyUnitIso.hom.val = η F` by the (closed)
  -- `pullbackSheafifyUnitEtaTriangle f`, then `presheafUnit_comp_map_eta f` and (closed)
  -- `epsilonPresheafToSheafUnit f` collapse to `(unitToPushforwardObjUnit φ).val`.
  rw [restrictScalarsId_map, restrictScalarsId_map]
  -- Reassociate and merge the two `pushforward φ'`-images via `erw` (keyed-defeq matching tolerates the
  -- `pf₁`/`pf₂` zeta-spelling at the connecting object), fold the argument to `η F` (ii), and collapse
  -- to `(unitToPushforwardObjUnit φ).val` via (6) `presheafUnit_comp_map_eta` + (iii) `epsilonPresheafToSheafUnit`.
  erw [Category.assoc, ← Functor.map_comp, pullbackSheafifyUnitEtaTriangle f,
    presheafUnit_comp_map_eta f, epsilonPresheafToSheafUnit f]

/-- **D2′ — the pullback–tensor comparison on the unit pair is an isomorphism** (blueprint
`lem:pullback_tensor_iso_unit`). Feeds the unit square `pullbackEtaUnitSquare` into the IsIso
plumbing `isIso_sheafifyEta_of_unitSquare` (yielding `IsIso (a_Y.map (η (pullback φ')))`), then into
the iter-246 δ-wrapping `isIso_pullbackTensorMap_unitPair_of_isIso_sheafifyEta`. Project-local. -/
lemma pullbackTensorMap_unit_isIso {X Y : Scheme.{u}} (f : Y ⟶ X) :
    IsIso (pullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf)) :=
  isIso_pullbackTensorMap_unitPair_of_isIso_sheafifyEta f
    (isIso_sheafifyEta_of_unitSquare f (pullbackEtaUnitSquare f))

/-- **Characterisation of `sheafifyTensorUnitIso.hom` on the `⋙ forget₂` carrier.** Strips the
`letI instMS` cast so the two `a.map` whisker factors are stated on the same presheaf carrier as
the rest of `pullbackTensorMap` — the bridge that lets `Functor.map_comp` merge them. -/
private lemma sheafifyTensorUnitIso_hom_eq {X : Scheme.{u}}
    (P Q : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (sheafifyTensorUnitIso P Q).hom
      = (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).map
          (MonoidalCategory.whiskerRight
            (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            ((PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).unit.app P) Q) ≫
        (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).map
          (MonoidalCategory.whiskerLeft
            (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
              (𝟙 X.ringCatSheaf.val)).obj P).val
            ((PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).unit.app Q)) := by
  rfl

/-- **`sheafifyTensorUnitIso.hom` as `a.map` of a single `tensorHom`** (tscmp254 carrier-pin). The
two whisker factors of `sheafifyTensorUnitIso_hom_eq` merge (`← Functor.map_comp`) into a single
`a.map` of `η_P ▷ Q ≫ (aP).val ◁ η_Q`, which is the `tensorHom` `η_P ⊗ η_Q` of the two
sheafification-unit components by `tensorHom_def` (the `exact` absorbs the defeq `restrictScalars (𝟙)`
wrapper on `η`'s codomain that blocks a syntactic `← tensorHom_def`).  Stating the comparison as ONE
`tensorHom` keeps every term in the single monoidal instance on the `⋙ forget₂` carrier, so the
naturality reduces to plain bifunctoriality (`← tensor_comp`) + the two single-component unit
squares — no `whisker_exchange`, no cross-instance crossing. -/
private lemma sheafifyTensorUnitIso_hom_eq' {X : Scheme.{u}}
    (P Q : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (sheafifyTensorUnitIso P Q).hom
      = (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).map
          (MonoidalCategory.tensorHom
            (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            ((PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).unit.app P)
            ((PresheafOfModules.sheafificationAdjunction
              (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).unit.app Q)) := by
  rw [sheafifyTensorUnitIso_hom_eq, ← Functor.map_comp]
  congr 1
  exact (MonoidalCategory.tensorHom_def
    (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _).symm

-- The `erw` defeq matching across the `SheafOfModules`/`Scheme.Modules` carrier and the
-- sheafification-laden composites is heartbeat-heavy; bump past the default.
set_option maxHeartbeats 1600000 in
/-- **Naturality of `pullbackValIso` in the module argument.** For `u : M ⟶ M'` in `X.Modules`,
the identification `pullbackValIso f` (sheafified presheaf-pullback ≅ abstract pullback) is natural:
`a_Y.map (F.map u.val) ≫ (pullbackValIso f M').hom = (pullbackValIso f M).hom ≫ (pullback f).map u`,
where `F = PresheafOfModules.pullback φ'`. Both factors of `pullbackValIso`
(`sheafificationCompPullback` and the sheafification counit) are natural; this is their paste.
Helper for `pullbackTensorMap_natural` (D1′). -/
lemma pullbackValIso_hom_natural {X Y : Scheme.{u}} (f : Y ⟶ X) {M M' : X.Modules} (u : M ⟶ M') :
    (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).map u.val) ≫
      (pullbackValIso f M').hom
      = (pullbackValIso f M).hom ≫ (Scheme.Modules.pullback f).map u := by
  simp only [pullbackValIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc]
  erw [(SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).inv.naturality u.val]
  rw [Functor.comp_map,
    show (SheafOfModules.pullback (Hom.toRingCatSheafHom f)).map
          ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.val)).map u.val)
        = (Scheme.Modules.pullback f).map
          ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
            (𝟙 X.ringCatSheaf.val)).map u.val) from rfl]
  erw [Category.assoc]
  erw [← Functor.map_comp (Scheme.Modules.pullback f)
      ((PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).map u.val)
      ((asIso (PresheafOfModules.sheafificationAdjunction
        (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).counit).app M').hom,
    ← Functor.map_comp (Scheme.Modules.pullback f)
      ((asIso (PresheafOfModules.sheafificationAdjunction
        (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).counit).app M).hom u]
  congr 1
  congr 1
  exact (PresheafOfModules.sheafificationAdjunction
    (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).counit.naturality u

-- Whiskered sheafification-unit naturality across the sheafification-laden composites is
-- heartbeat-heavy; bump past the default.
set_option maxHeartbeats 1600000 in
/-- **Naturality of `sheafifyTensorUnitIso`.** For presheaf maps `p : P ⟶ P'`, `q : Q ⟶ Q'`,
the reconciliation `sheafifyTensorUnitIso` (relating `a(P⊗Q)` with `a((aP).val ⊗ (aQ).val)`) is
natural. It is the paste of the naturality of the sheafification unit `η` whiskered on each side.
Helper for `pullbackTensorMap_natural` (D1′). -/
lemma sheafifyTensorUnitIso_hom_natural {X : Scheme.{u}}
    {P P' Q Q' : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)}
    (p : P ⟶ P') (q : Q ⟶ Q') :
    (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).map
        (MonoidalCategory.tensorHom (C := _root_.PresheafOfModules
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)) p q) ≫
      (sheafifyTensorUnitIso P' Q').hom
      = (sheafifyTensorUnitIso P Q).hom ≫
        (PresheafOfModules.sheafification (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).map
          (MonoidalCategory.tensorHom (C := _root_.PresheafOfModules
            (X.presheaf ⋙ forget₂ CommRingCat RingCat))
            ((SheafOfModules.forget X.ringCatSheaf).map
              ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
                (𝟙 X.ringCatSheaf.val)).map p))
            ((SheafOfModules.forget X.ringCatSheaf).map
              ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
                (𝟙 X.ringCatSheaf.val)).map q))) := by
  -- Pin both comparison factors as a single `a.map (η ⊗ η)` (tscmp254 `sheafifyTensorUnitIso_hom_eq'`):
  -- the naturality is then a `Functor.map_comp` merge + plain bifunctoriality, with every term in the
  -- ONE monoidal instance on the `⋙ forget₂` carrier — no `whisker_exchange`, no cross-instance
  -- crossing, no `erw`-on-`restrictScalars (𝟙)`-over-sheafification `whnf`.
  rw [sheafifyTensorUnitIso_hom_eq', sheafifyTensorUnitIso_hom_eq']
  -- Merge both `a.map _ ≫ a.map _` (`erw`: the connecting tensor object is defeq-but-not-syntactic
  -- — `Monoidal.tensorObj` vs the `⋙ forget₂` instance, plus the `restrictScalars (𝟙)` wrapper on
  -- `η`'s codomain — but cheap: no `restrictScalars`-over-sheafification `whnf` at the boundary).
  erw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  -- Presheaf goal: (p ⊗ q) ≫ (η_{P'} ⊗ η_{Q'}) = (η_P ⊗ η_Q) ≫ (a.map p ⊗ a.map q).
  -- Single-component unit-naturality squares (`restrictScalars (𝟙)` map-wrapper stripped).
  have hp : p ≫ (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Sheaf.val X.ringCatSheaf))).unit.app P'
      = (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val X.ringCatSheaf))).unit.app P ≫
        (SheafOfModules.forget X.ringCatSheaf).map
          ((PresheafOfModules.sheafification (𝟙 (Sheaf.val X.ringCatSheaf))).map p) := by
    simpa only [Functor.id_map, Functor.comp_map, restrictScalarsId_map]
      using (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Sheaf.val X.ringCatSheaf))).unit.naturality p
  have hq : q ≫ (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Sheaf.val X.ringCatSheaf))).unit.app Q'
      = (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val X.ringCatSheaf))).unit.app Q ≫
        (SheafOfModules.forget X.ringCatSheaf).map
          ((PresheafOfModules.sheafification (𝟙 (Sheaf.val X.ringCatSheaf))).map q) := by
    simpa only [Functor.id_map, Functor.comp_map, restrictScalarsId_map]
      using (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Sheaf.val X.ringCatSheaf))).unit.naturality q
  -- Split the LHS `tensorHom`-composite (`tensorHom_comp_tensorHom`, applied as a defeq-matched TERM
  -- since `rw` cannot bridge the non-canonical monoidal instance baked into the goal), apply the two
  -- unit squares, then reassemble into the RHS `tensorHom`-composite.  `(C := …)` is supplied so the
  -- `MonoidalCategory` instance resolves (the underscore form leaves it a stuck metavariable).
  refine (MonoidalCategory.tensorHom_comp_tensorHom
    (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _ _ _).trans ?_
  rw [hp, hq]
  exact (MonoidalCategory.tensorHom_comp_tensorHom
    (C := _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _ _ _).symm

-- The 4-square diagram chase pastes naturality across the sheafification-laden composites and is
-- driven by `erw` keyed-defeq merges (bridging the `Sheaf.val`/`.obj` and monoidal-instance
-- spellings); bump well past the default.
set_option maxHeartbeats 3200000 in
/-- **D1′ — naturality of the sheaf-level pullback–tensor comparison `pullbackTensorMap`**
(blueprint `lem:pullback_tensor_map_natural`). For `a : M ⟶ M'`, `b : N ⟶ N'` in `X.Modules`,
the comparison `δ_sheaf = pullbackTensorMap f` commutes with `f^*(a ⊗ b)` on the source and
`f^*a ⊗ f^*b` on the target. Project-local. -/
lemma pullbackTensorMap_natural {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (tensorObj_functoriality a b) ≫ pullbackTensorMap f M' N'
      = pullbackTensorMap f M N ≫
        tensorObj_functoriality ((Scheme.Modules.pullback f).map a)
          ((Scheme.Modules.pullback f).map b) := by
  -- `pullbackTensorMap f M N` is the four-fold composite
  --   S1 ≫ S2 ≫ S3 ≫ S4 with
  --   S1 = (sheafificationCompPullback φ).app (M.val ⊗ N.val) .hom,
  --   S2 = a_Y.map (δ (pullback φ') M.val N.val),
  --   S3 = (sheafifyTensorUnitIso (F M.val) (F N.val)).hom,
  --   S4 = a_Y.map (tensorHom (pullbackValIso f M).hom.val (pullbackValIso f N).hom.val).
  -- Naturality is the paste of four squares:
  --   • S1 : naturality of `sheafificationCompPullback φ` at `tensorHom a.val b.val` (NatTrans);
  --   • S2 : `Functor.OplaxMonoidal.δ_natural` for `pullback φ'`, under `a_Y.map`;
  --   • S3 : `sheafifyTensorUnitIso_hom_natural` (helper above, CLOSED);
  --   • S4 : `pullbackValIso_hom_natural` (helper above, CLOSED) + bifunctoriality of `⊗`.
  -- The cleaner route (avoiding the sheaf-level carrier friction at S1) is to merge
  -- `a_Y.map δ ≫ S3 ≫ S4` into a single `a_Y.map Ψ` (Ψ presheaf-level), move S1 by its NatTrans
  -- naturality, and discharge the resulting PRESHEAF equation by `δ_natural` + the η-naturality of
  -- the two helpers — the same merge that `sheafifyTensorUnitIso_hom_natural` reduces to.
  simp only [pullbackTensorMap, tensorObj_functoriality]
  -- Square 1 (S1) — CLOSED: naturality of the `sheafificationCompPullback φ` natural iso at
  -- `a.val ⊗ₘ b.val`.  After this the goal is
  --   S1 ≫ a_Y.map (Fp.map (a.val ⊗ b.val)) ≫ a_Y.map δ' ≫ S3' ≫ S4'
  --     = (S1 ≫ a_Y.map δ ≫ S3 ≫ S4) ≫ Q0,   Fp = PresheafOfModules.pullback φ'.
  erw [(SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).hom.naturality_assoc]
  rw [Functor.comp_map]
  -- Square 2 (S2): `Functor.comp_map` left the first `a_Y` spelled `sheafification (𝟙 Y.ringCatSheaf.obj)`
  -- while the `δ`-factor reads `sheafification (𝟙 (Sheaf.val Y.ringCatSheaf))` (SAME functor,
  -- `Sheaf.val = .obj`).  Normalise `Sheaf.val → .obj` so the two `a_Y.map`s share a functor, merge
  -- them, and commute `δ` past `Fp.map (a.val ⊗ b.val)` by `δ_natural` (reverse), then split.
  dsimp only [CategoryTheory.Sheaf.val]
  -- Square 2 merge — SOLVED (iter-254): the `← Functor.map_comp` of the iter-253 BLOCKER fails because
  -- the two `a_Y.map`s are right-associated (`a.map A ≫ (a.map B ≫ rest)`), so `A`/`B` are not the
  -- direct operands of one `≫`.  The fix is the *reassoc* form `← Functor.map_comp_assoc` (`erw`, to
  -- bridge the non-canonical monoidal instance baked into the goal exactly as STEP A does): it merges
  -- `a.map (Fp.map (a.val ⊗ b.val)) ≫ a.map (δ_{M',N'}) ≫ rest`
  --   into `a.map (Fp.map (a.val ⊗ b.val) ≫ δ_{M',N'}) ≫ rest`, with `Fp = PresheafOfModules.pullback φ'`.
  erw [← Functor.map_comp_assoc]
  -- ── REMAINING (Square 2 — δ commutation): under the merged `a.map (…)` the argument is
  --   `Fp.map (a.val ⊗ b.val) ≫ δ_{M'.val,N'.val}`,  Fp = PresheafOfModules.pullback φ',
  -- which by oplax naturality `Functor.OplaxMonoidal.δ_natural` equals
  --   `δ_{M.val,N.val} ≫ (Fp.map a.val ⊗ Fp.map b.val)`.
  -- Square 2 (δ commutation) — CLOSED via the mapin255 LIGHT fix: re-present `F`'s ring-hom at the
  -- canonical `⋙ forget₂` spelling with a `show … from` ascription inside the `δ_natural` application,
  -- so the registered `MonoidalCategory` instance synthesizes.  `erw` (not `rw`): the ascription
  -- pretty-prints as `have this := …; this`, whose reducible-defeq match to the bare hom only `erw`
  -- bridges.  After this Square 2 is done; `dsimp only []` strips the cosmetic `have this := …; this`.
  erw [← Functor.OplaxMonoidal.δ_natural
    (F := PresheafOfModules.pullback
      (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
        from (Hom.toRingCatSheafHom f).hom))
    a.val b.val]
  dsimp only []
  -- Now: S1 ≫ a_Y.map (δ_{M,N} ≫ (Fp.map a.val ⊗ Fp.map b.val)) ≫ S3(M',N') ≫ S4(M',N')
  --    = (S1 ≫ a_Y.map δ_{M,N} ≫ S3(M,N) ≫ S4(M,N)) ≫ a_Y.map (a.val^* ⊗ b.val^*).
  -- Split `a_Y.map (δ ≫ φ)` and right-associate so S1 and `a_Y.map δ_{M,N}` are common prefixes.
  erw [Functor.map_comp]
  simp only [Category.assoc]
  -- Peel the common S1 (`.hom.app` vs `.app … .hom`, defeq) and `a_Y.map δ_{M,N}` via `rfl` legs.
  refine congr_arg₂ (· ≫ ·) rfl ?_
  refine congr_arg₂ (· ≫ ·) rfl ?_
  -- Residual (key): a_Y.map (Fp.map a.val ⊗ Fp.map b.val) ≫ S3(M',N') ≫ S4(M',N')
  --              = S3(M,N) ≫ S4(M,N) ≫ a_Y.map (a.val^* ⊗ b.val^*).
  -- Square 3: naturality of `sheafifyTensorUnitIso` (reassoc form, post-composed by S4(M',N')).
  erw [reassoc_of% (sheafifyTensorUnitIso_hom_natural
    ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).map a.val)
    ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).map b.val))]
  dsimp only [CategoryTheory.Sheaf.val]
  -- Now: S3(M,N) ≫ a_Y.map (forget(a_Y(Fp a.val)) ⊗ forget(a_Y(Fp b.val))) ≫ S4(M',N')
  --    = S3(M,N) ≫ a_Y.map (forget(pullbackValIso M).hom ⊗ forget(pullbackValIso N).hom) ≫ a_Y.map (a^* ⊗ b^*).
  -- `erw [Category.assoc]` bridges the `Sheaf.val`/`.obj` defeq gap in the connecting object
  -- (`pullbackValIso`'s type carries `Y.ringCatSheaf.val`, the helper carries `.obj`); plain `rw`
  -- cannot see the `(f ≫ g) ≫ h` pattern across this gap.
  erw [Category.assoc]
  -- Cancel the common `S3(M,N)` iso prefix, then merge each side's two `a_Y.map`s into a single
  -- `a_Y.map (_ ≫ _)` via `Functor.map_comp` (applied as defeq-matched TERMS so `refine`'s `isDefEq`
  -- bridges the same `.val`/`.obj` gap that blocks `rw`).
  erw [Iso.cancel_iso_hom_left]
  refine ((Functor.map_comp _ _ _).symm.trans ?_).trans (Functor.map_comp _ _ _)
  congr 1
  -- Square 4 (presheaf-level): bifunctoriality of `⊗` + naturality of `pullbackValIso` per leg.
  --   (forget(a_Y(Fp a.val)) ⊗ forget(a_Y(Fp b.val))) ≫ (forget(pullbackValIso M').hom ⊗ forget(pullbackValIso N').hom)
  -- = (forget(pullbackValIso M).hom ⊗ forget(pullbackValIso N).hom) ≫ (a^*.val ⊗ b^*.val).
  -- Per-leg naturality of `pullbackValIso` (= `pullbackValIso_hom_natural` under `forget`): merge the two
  -- `forget.map`s, apply the sheaf-level naturality, split back.  `((pullback f).map u).val` is `forget`
  -- of `(pullback f).map u`, so the closing `rfl` discharges the `forget`/`.val` boundary.
  have hleg : ∀ {P P' : X.Modules} (u : P ⟶ P'),
      (SheafOfModules.forget Y.ringCatSheaf).map
          ((PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).map u.val)) ≫
        (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f P').hom
        = (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f P).hom ≫
          ((Scheme.Modules.pullback f).map u).val := by
    intro P P' u
    rw [← Functor.map_comp]
    erw [pullbackValIso_hom_natural]
    rw [Functor.map_comp]
    rfl
  -- Split the LHS `tensorHom`-composite by bifunctoriality, rewrite each leg by `hleg`, reassemble into
  -- the RHS `tensorHom`-composite.  `(C := …)` pins the monoidal instance on the `⋙ forget₂` carrier;
  -- `erw` bridges the `Sheaf.val`/`.obj` connecting-object gap that blocks a plain `rw [hleg …]`.
  refine (MonoidalCategory.tensorHom_comp_tensorHom
    (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _ _ _).trans ?_
  erw [hleg a, hleg b]
  exact (MonoidalCategory.tensorHom_comp_tensorHom
    (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _ _ _).symm

/-- **Sq2 prerequisite — ring-map reconciliation.** For composable `h : Z ⟶ Y`, `f : Y ⟶ X`,
the structure ring-presheaf map of the composite factors through the whiskered ring maps of `f`
and `h`. This is the presheaf-level identity needed to feed `PresheafOfModules.pullbackComp` into
the oplax `comp_δ` decomposition (Sq2 of `pullbackTensorMap_restrict`). -/
private lemma toRingCatSheafHom_comp_hom_reconcile {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) :
    (Hom.toRingCatSheafHom (h ≫ f)).hom =
      (Hom.toRingCatSheafHom f).hom ≫
        (TopologicalSpace.Opens.map f.base).op.whiskerLeft (Hom.toRingCatSheafHom h).hom := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Sectionwise value of the presheaf `restrictScalars` lax tensorator.** The lax μ of
`PresheafOfModules.restrictScalars α`, evaluated at a section `W`, is by definition the `ModuleCat`
lax μ of `restrictScalars (α.app W).hom`. Exposed as a `rfl`-lemma so the heavy ambient term need not
be `whnf`-ed: rewriting with it turns `(μ (restrictScalars α) M₁ M₂).app W` into a `ModuleCat` μ on
which `ModuleCat.restrictScalars_μ_tmul` matches syntactically (a direct `erw` on the presheaf form
`whnf`-explodes). -/
private lemma restrictScalars_μ_app
    {C : Type u} [Category.{u} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : (R ⋙ forget₂ CommRingCat RingCat) ⟶ (S ⋙ forget₂ CommRingCat RingCat))
    (M₁ M₂ : _root_.PresheafOfModules (S ⋙ forget₂ CommRingCat RingCat)) (W : Cᵒᵖ) :
    (Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars α) M₁ M₂).app W
      = Functor.LaxMonoidal.μ (ModuleCat.restrictScalars (α.app W).hom)
          (M₁.obj W) (M₂.obj W) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Pure-tensor value of the `ModuleCat` `restrictScalars` lax tensorator, in `ModuleCat.Hom.hom`
application form, with `forget₂`-carrier rings.** Bridges `ModuleCat.restrictScalars_μ_tmul` (stated
with the bundled coercion) to the `ModuleCat.Hom.hom`-applied form goals carry after
`ModuleCat.hom_comp`/`LinearMap.comp_apply`.  The source/target rings are `forget₂`-carriers of
presheaves of *commutative* rings (`Rc.obj W'`, `Sc.obj W'`), so the `CommRing` instances the goal's
`⊗ₜ` carries (coming from `CommRingCat`) are exactly the ones the statement uses — a generic
`Type`-level form fails to synthesise `CommRing` on a bare `RingCat` carrier.  Applied in context to
the goal's heavy objects as explicit arguments and discharged by `erw` (matching only the residual
defeq instance differences, no `whnf` of the heavy `pushforward₀` sections, which would explode). -/
private lemma forget₂_restrictScalars_μ_hom_tmul
    {C : Type u} [Category.{u} C] {Rc Sc : Cᵒᵖ ⥤ CommRingCat.{u}} {W' : Cᵒᵖ}
    (f : (Rc ⋙ forget₂ CommRingCat RingCat).obj W' ⟶ (Sc ⋙ forget₂ CommRingCat RingCat).obj W')
    (M₁ M₂ : ModuleCat.{u} ((Sc ⋙ forget₂ CommRingCat RingCat).obj W'))
    (m : M₁) (n : M₂) :
    ModuleCat.Hom.hom (Functor.LaxMonoidal.μ (ModuleCat.restrictScalars f.hom) M₁ M₂)
        (m ⊗ₜ[(Rc ⋙ forget₂ CommRingCat RingCat).obj W'] n) = m ⊗ₜ n :=
  ModuleCat.restrictScalars_μ_tmul f.hom M₁ M₂ m n

set_option backward.isDefEq.respectTransparency false in
/-- **Pure-tensor value of the presheaf `restrictScalars` lax tensorator (full collapse).**
On a pure tensor, `(μ (restrictScalars α) M₁ M₂).app W` is the identity.  Combines
`restrictScalars_μ_app` (rfl, exposes the `ModuleCat` μ) with `ModuleCat.restrictScalars_μ_tmul`.
Stated with `M₁ M₂` as *atoms*, so the proof never `whnf`s heavy ambient objects; in context it is
`rw`-applied with `R`, `S` pinned (the `forget₂`-association the goal carries), so keyed matching
succeeds without `whnf`. -/
private lemma restrictScalars_μ_app_tmul
    {C : Type u} [Category.{u} C] {R S : Cᵒᵖ ⥤ CommRingCat.{u}}
    (α : (R ⋙ forget₂ CommRingCat RingCat) ⟶ (S ⋙ forget₂ CommRingCat RingCat))
    (M₁ M₂ : _root_.PresheafOfModules (S ⋙ forget₂ CommRingCat RingCat)) (W : Cᵒᵖ)
    (m : (M₁.obj W)) (n : (M₂.obj W)) :
    ModuleCat.Hom.hom ((Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars α) M₁ M₂).app W)
        (m ⊗ₜ[(R ⋙ forget₂ CommRingCat RingCat).obj W] n) = m ⊗ₜ n := by
  rw [restrictScalars_μ_app]
  exact ModuleCat.restrictScalars_μ_tmul (α.app W).hom (M₁.obj W) (M₂.obj W) m n

set_option backward.isDefEq.respectTransparency false in
/-- **Pure-tensor value of the `pushforward`-mapped `restrictScalars` lax tensorator.**  The "outer
leg" of `pushforwardComp_lax_μ`: `((pushforward φ).map (μ (restrictScalars ψ) N₁ N₂)).app W` applied
to a pure tensor is the identity.  Reindexes through `pushforward_map_app_apply` (`pushforward φ` is
`pushforward₀ ⋙ restrictScalars φ`, so the section map at `W` is the `μ` at `F.op.obj W`), then
collapses by `restrictScalars_μ_app_tmul`.  `N₁ N₂` are *atoms*; in context the lemma is applied to
the goal's heavy objects as explicit arguments and discharged by `erw` (which matches the residual
defeq instance differences without `whnf`-ing the heavy objects). -/
private lemma pushforward_map_restrictScalars_μ_app_tmul
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F : C ⥤ D} {G : D ⥤ E}
    {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {T₀ : Eᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat))
    (ψ : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      G.op ⋙ (T₀ ⋙ forget₂ CommRingCat RingCat))
    (N₁ N₂ : _root_.PresheafOfModules ((G.op ⋙ T₀) ⋙ forget₂ CommRingCat RingCat)) (W : Cᵒᵖ)
    (m : (N₁.obj (F.op.obj W))) (n : (N₂.obj (F.op.obj W))) :
    ModuleCat.Hom.hom
        (((PresheafOfModules.pushforward φ).map
          (Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars
            (show (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶
              ((G.op ⋙ T₀) ⋙ forget₂ CommRingCat RingCat) from ψ)) N₁ N₂)).app W)
        (m ⊗ₜ[(R₀ ⋙ forget₂ CommRingCat RingCat).obj (F.op.obj W)] n) = m ⊗ₜ n := by
  erw [PresheafOfModules.pushforward_map_app_apply]
  exact restrictScalars_μ_app_tmul _ N₁ N₂ (F.op.obj W) m n

/-- **Reduction of the `pushforward` lax tensorator to the `restrictScalars` μ (morphism level).**
The lax μ of a single `PresheafOfModules.pushforward φ` equals the lax μ of the change-of-rings
`restrictScalars φ'` on the (strongly-monoidal, `μIso = refl`) reindexed objects
`pushforward₀OfCommRingCat F R₀`. This unfolds the opaque `presheafPushforwardLaxMonoidal` μ (the
`Functor.LaxMonoidal.comp` of `pushforward₀`'s μ = identity and `restrictScalars`'s μ) to the
directly-computable `restrictScalars` μ — staying at the `PresheafOfModules` morphism level so the
`(presheaf-tensor).obj W` vs `ModuleCat`-tensor mismatch never surfaces. Mirrors the ε-twin
`epsilonPresheafToSheafUnit`. -/
private lemma pushforward_μ_eq
    {C D : Type u} [Category.{u} C] [Category.{u} D] {F : C ⥤ D}
    {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat))
    (A B : _root_.PresheafOfModules (R₀ ⋙ forget₂ CommRingCat RingCat)) :
    letI φ' : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
        (F.op ⋙ R₀) ⋙ forget₂ CommRingCat RingCat := φ
    Functor.LaxMonoidal.μ (PresheafOfModules.pushforward φ) A B
      = Functor.LaxMonoidal.μ (PresheafOfModules.restrictScalars φ')
          ((PresheafOfModules.pushforward₀OfCommRingCat F R₀).obj A)
          ((PresheafOfModules.pushforward₀OfCommRingCat F R₀).obj B) := by
  rfl

/-- **Sq2b residual — the lax-μ composition coherence of `PresheafOfModules.pushforward`
(monoidality of `pushforwardComp`).** Since `PresheafOfModules.pushforwardComp φ ψ = Iso.refl`,
the right-adjoint side of Sq2b reduces to the statement that the lax tensorator `μ` of the
*composite* pushforward `pushforward ψ ⋙ pushforward φ` (built by `Functor.LaxMonoidal.comp`)
agrees with the lax tensorator of the *single* pushforward `pushforward (φ ≫ F.op ◁ ψ)` (built by
`presheafPushforwardLaxMonoidal`).

**Status (iter-261): CLOSED, axiom-clean.** The equality is genuinely *not* `rfl`/`simp` at the
presheaf level (the `restrictScalars` μ on a pure tensor is real `ModuleCat` base-change content,
`ModuleCat.restrictScalars_μ_tmul`, not definitional).  The working route is sectionwise +
pure-tensor reduction: `Functor.LaxMonoidal.comp_μ` unfolds the composite μ, `pushforward_μ_eq`
lightens each `μ (pushforward _)` to a `restrictScalars` μ, and each leg is then collapsed to the
identity by the atomic-object helpers `forget₂_restrictScalars_μ_hom_tmul` (inner) and
`pushforward_map_restrictScalars_μ_app_tmul` (the `(pushforward φ).map …` leg, reindexed by
`pushforward_map_app_apply`).  Both helpers are applied to the goal's concrete objects as explicit
arguments and matched by `erw` — this is the only way to avoid the `whnf`-explosion that a direct
`rw`/`erw`/`simp` of `ModuleCat.restrictScalars_μ_tmul` triggers on the heavy `pushforward₀`
sections.  After both legs collapse, the LHS pure tensor is defeq to the RHS single-pushforward μ on
the same tensor, closing the goal. -/
private lemma pushforwardComp_lax_μ
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F : C ⥤ D} {G : D ⥤ E}
    {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {T₀ : Eᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat))
    (ψ : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      G.op ⋙ (T₀ ⋙ forget₂ CommRingCat RingCat))
    [(PresheafOfModules.pushforward φ).IsRightAdjoint]
    [(PresheafOfModules.pushforward ψ).IsRightAdjoint]
    (X Y : _root_.PresheafOfModules (T₀ ⋙ forget₂ CommRingCat RingCat)) :
    Functor.LaxMonoidal.μ
        (PresheafOfModules.pushforward ψ ⋙ PresheafOfModules.pushforward φ) X Y =
      Functor.LaxMonoidal.μ
        (PresheafOfModules.pushforward (F := F ⋙ G)
          (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ)) X Y := by
  -- PROOF (iter-261): the equality is checked sectionwise (`hom_ext`) and on pure tensors
  -- (`tensor_ext`).  `Functor.LaxMonoidal.comp_μ` unfolds the composite μ to
  --   `μ (pushforward φ) (..) (..)  ≫  (pushforward φ).map (μ (pushforward ψ) X Y)`,
  -- and `pushforward_μ_eq` (×2) reduces each `μ (pushforward _)` to the lighter
  -- `μ (restrictScalars _)` on the strong-monoidal `pushforward₀` objects.  On a pure tensor every
  -- `restrictScalars` μ is the identity (`ModuleCat.restrictScalars_μ_tmul`): the inner leg is
  -- collapsed by `forget₂_restrictScalars_μ_hom_tmul` (`hinner`) and the `(pushforward φ).map …`
  -- leg by `pushforward_map_restrictScalars_μ_app_tmul` (`houter`, which reindexes the section map to
  -- `F.op.obj W` via `pushforward_map_app_apply` and collapses there).  After both legs the LHS is
  -- `m ⊗ₜ n`, which is defeq to the RHS single-pushforward μ on the same pure tensor — so the final
  -- `erw [houter]` closes the goal by its trailing `rfl`.  The heavy `pushforward₀` sections never
  -- get `whnf`-ed: all collapse lemmas are stated with atomic objects and applied to the goal's
  -- concrete objects as explicit arguments, then matched by `erw` up to the residual defeq
  -- `forget₂`-association / instance differences only.
  refine PresheafOfModules.hom_ext (fun W => ?_)
  refine ModuleCat.MonoidalCategory.tensor_ext (fun m n => ?_)
  rw [Functor.LaxMonoidal.comp_μ]
  rw [pushforward_μ_eq, pushforward_μ_eq]
  rw [PresheafOfModules.comp_app]
  erw [ModuleCat.hom_comp, LinearMap.comp_apply]
  rw [restrictScalars_μ_app (R := S₀) (S := F.op ⋙ R₀)]
  have hinner := forget₂_restrictScalars_μ_hom_tmul (Rc := S₀) (Sc := F.op ⋙ R₀) (φ.app W)
    (((PresheafOfModules.pushforward₀OfCommRingCat F R₀).obj ((PresheafOfModules.pushforward ψ).obj X)).obj W)
    (((PresheafOfModules.pushforward₀OfCommRingCat F R₀).obj ((PresheafOfModules.pushforward ψ).obj Y)).obj W)
    m n
  erw [hinner]
  have houter := pushforward_map_restrictScalars_μ_app_tmul φ ψ
    ((PresheafOfModules.pushforward₀OfCommRingCat G T₀).obj X)
    ((PresheafOfModules.pushforward₀OfCommRingCat G T₀).obj Y) W m n
  erw [houter]

/-- **Sq2b — monoidality of `PresheafOfModules.pullbackComp` (the δ-transport across the
left-adjoint composition iso).** The presheaf-level core of D3′: the canonical oplax comparison
`δ` of the pullback for a composite ring map `φ ≫ F.op ◁ ψ` transports, through the pullback
pseudofunctor coherence `pullbackComp φ ψ`, into the `Functor.OplaxMonoidal.comp` comparison of
the composite `pullback φ ⋙ pullback ψ`.

This is the η→δ analogue of `pullbackObjUnitToUnit_comp`, proved at the `PresheafOfModules` level
(dissolving the `forget₂`-instance / associativity / reconcile frictions of working at the
`Scheme`/`forget₂` level). The proof is the adjunction-mate calculus: transpose under
`pullbackPushforwardAdjunction (φ ≫ F.op ◁ ψ)`, rewrite the oplax δ as the mate of the lax μ
(`Adjunction.unit_app_tensor_comp_map_δ`), and use the conjugate identity
`conjugateEquiv_leftAdjointCompIso_inv` (here `pushforwardComp = Iso.refl`, so the mate of
`pullbackComp.inv` is the identity). The sole residual is the lax-μ composition coherence of
`PresheafOfModules.pushforward` across `pushforwardComp` (`pushforwardComp_lax_μ`). -/
private lemma pullbackComp_δ
    {C D E : Type u} [Category.{u} C] [Category.{u} D] [Category.{u} E]
    {F : C ⥤ D} {G : D ⥤ E}
    {S₀ : Cᵒᵖ ⥤ CommRingCat.{u}} {R₀ : Dᵒᵖ ⥤ CommRingCat.{u}} {T₀ : Eᵒᵖ ⥤ CommRingCat.{u}}
    (φ : (S₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      F.op ⋙ (R₀ ⋙ forget₂ CommRingCat RingCat))
    (ψ : (R₀ ⋙ forget₂ CommRingCat RingCat) ⟶
      G.op ⋙ (T₀ ⋙ forget₂ CommRingCat RingCat))
    [(PresheafOfModules.pushforward φ).IsRightAdjoint]
    [(PresheafOfModules.pushforward ψ).IsRightAdjoint]
    (M N : _root_.PresheafOfModules (S₀ ⋙ forget₂ CommRingCat RingCat)) :
    Functor.OplaxMonoidal.δ
        (PresheafOfModules.pullback (F := F ⋙ G)
          (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ)) M N =
      (PresheafOfModules.pullbackComp φ ψ).inv.app (M ⊗ N) ≫
        Functor.OplaxMonoidal.δ
          (PresheafOfModules.pullback φ ⋙ PresheafOfModules.pullback ψ) M N ≫
        ((PresheafOfModules.pullbackComp φ ψ).hom.app M ⊗ₘ
          (PresheafOfModules.pullbackComp φ ψ).hom.app N) := by
  -- MATE CALCULUS (iter-259 derivation; reduces Sq2b to `pushforwardComp_lax_μ`).
  -- Transpose both sides under `aχ.homEquiv` (`aχ := pullbackPushforwardAdjunction (φ ≫ F.op ◁ ψ)`):
  apply (PresheafOfModules.pullbackPushforwardAdjunction
    (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat)
    (φ ≫ F.op.whiskerLeft ψ)).homEquiv _ _ |>.injective
  -- Both sides become `aχ.unit (M⊗N) ≫ (pushforward χ).map (…)`:
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  -- The remaining reduction (verified on paper; the wiring `rw`s are mechanical but fragile, and
  -- the *only* genuine gap is `pushforwardComp_lax_μ`, which is `rfl`-FALSE — see below):
  --
  --   LHS = aχ.unit(M⊗N) ≫ (pushforward χ).map (δ (pullback χ) M N)
  --       = (aχ.unit M ⊗ₘ aχ.unit N) ≫ μ(pushforward χ) (pullback χ M) (pullback χ N)
  --                                          [Adjunction.unit_app_tensor_comp_map_δ (adj := aχ)]
  --
  --   RHS = aχ.unit(M⊗N) ≫ (pushforward χ).map (c.inv(M⊗N) ≫ comp_δ ≫ (c.hom M ⊗ₘ c.hom N))
  --       where c := pullbackComp φ ψ.  Expand `map_comp`, then:
  --   (MATE)   aχ.unit(M⊗N) ≫ (pushforward χ).map (c.inv(M⊗N)) = aC.unit(M⊗N)
  --                              [Adjunction.unit_conjugateEquiv + conjugateEquiv_leftAdjointCompIso_inv;
  --                               here pushforwardComp = Iso.refl ⇒ the conjugate of c.inv is 𝟙, so the
  --                               `pc.hom` factor vanishes]   (aC := aφ.comp aψ)
  --   (U-C)    aC.unit(M⊗N) ≫ (pushforward ψ ⋙ pushforward φ).map (comp_δ) =
  --              (aC.unit M ⊗ₘ aC.unit N) ≫ μ(pushforward ψ ⋙ pushforward φ) (LM) (LN)
  --                              [Adjunction.unit_app_tensor_comp_map_δ (adj := aC); aC.IsMonoidal via
  --                               Adjunction.isMonoidal_comp; (pushforward χ).map ≡ (G'⋙G).map defeq]
  --   (μ-NAT)  μ(pushforward χ) (LM)(LN) ≫ (pushforward χ).map (c.hom M ⊗ₘ c.hom N) =
  --              ((pushforward χ).map (c.hom M) ⊗ₘ (pushforward χ).map (c.hom N)) ≫
  --                μ(pushforward χ) (pullback χ M) (pullback χ N)   [Functor.LaxMonoidal.μ_natural]
  --   (TRI)    aC.unit P ≫ (pushforward χ).map (c.hom P) = aχ.unit P   [(MATE) + c.inv ≫ c.hom = 𝟙]
  --   tensorHom_comp_tensorHom merges the three ⊗ₘ legs; with (TRI) the RHS becomes
  --              (aχ.unit M ⊗ₘ aχ.unit N) ≫ μ(pushforward ψ ⋙ pushforward φ) (pullback χ M)(pullback χ N).
  --
  -- LHS = RHS then holds IFF
  --   μ(pushforward ψ ⋙ pushforward φ) X Y = μ(pushforward χ) X Y   (= `pushforwardComp_lax_μ`).
  -- This is the SOLE residual.  It is NOT `rfl` (the `d3sq2b258` recipe's "rfl/short ext" prediction
  -- is empirically false): it is a genuine `ModuleCat` change-of-rings base-change coherence
  -- (`ModuleCat.restrictScalarsComp` / `homEquiv_extendScalarsComp`), with NO analog in the
  -- `rfl`-closed unit twin `unitToPushforwardObjUnit_comp`.  Pinned as `pushforwardComp_lax_μ` above.
  -- The mate-`rw` wiring of the steps above is left for the follow-up (each step's Mathlib lemma is
  -- named); the reduction itself is complete.  The LHS step (U) is wired here:
  erw [Adjunction.unit_app_tensor_comp_map_δ
    (adj := PresheafOfModules.pullbackPushforwardAdjunction
      (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ))]
  -- (MATE): the conjugate/mate of `pullbackComp.inv` is `pushforwardComp.hom = 𝟙`.
  -- (MATE) — the conjugate of `pullbackComp.inv` is `pushforwardComp.hom = 𝟙`:
  have hconj : conjugateEquiv
        ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
          (PresheafOfModules.pullbackPushforwardAdjunction ψ))
        (PresheafOfModules.pullbackPushforwardAdjunction
          (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ))
        (PresheafOfModules.pullbackComp φ ψ).inv = 𝟙 _ := by
    simp only [PresheafOfModules.pullbackComp, Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
      PresheafOfModules.pushforwardComp, Iso.refl_hom]
  have hmate : ∀ (P : _root_.PresheafOfModules (S₀ ⋙ forget₂ CommRingCat RingCat)),
      (PresheafOfModules.pullbackPushforwardAdjunction
          (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat)
          (φ ≫ F.op.whiskerLeft ψ)).unit.app P ≫
        (PresheafOfModules.pushforward (F := F ⋙ G)
          (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ)).map
          ((PresheafOfModules.pullbackComp φ ψ).inv.app P) =
      ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
        (PresheafOfModules.pullbackPushforwardAdjunction ψ)).unit.app P := by
    intro P
    have hu := unit_conjugateEquiv
      ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
        (PresheafOfModules.pullbackPushforwardAdjunction ψ))
      (PresheafOfModules.pullbackPushforwardAdjunction
        (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ))
      (PresheafOfModules.pullbackComp φ ψ).inv P
    rw [hconj] at hu
    simp only [NatTrans.id_app, Category.comp_id] at hu
    exact hu.symm
  -- Expand the RHS `map` of the composite and apply (MATE):
  rw [Functor.map_comp, Functor.map_comp]
  erw [reassoc_of% (hmate (M ⊗ N))]
  -- (U-C): rewrite `aC.unit(M⊗N) ≫ map(comp_δ)` via the mate of the composite adjunction `aC`:
  erw [reassoc_of% (Adjunction.unit_app_tensor_comp_map_δ
    (adj := (PresheafOfModules.pullbackPushforwardAdjunction φ).comp
      (PresheafOfModules.pullbackPushforwardAdjunction ψ)) M N)]
  -- (μ-COH): replace the composite-pushforward μ by the χ-pushforward μ (the genuine residual):
  rw [pushforwardComp_lax_μ φ ψ]
  -- (TRI): for any `P`, `aC.unit P ≫ (pushforward χ).map (c.hom P) = aχ.unit P`.
  have htri : ∀ (P : _root_.PresheafOfModules (S₀ ⋙ forget₂ CommRingCat RingCat)),
      ((PresheafOfModules.pullbackPushforwardAdjunction φ).comp
          (PresheafOfModules.pullbackPushforwardAdjunction ψ)).unit.app P ≫
        (PresheafOfModules.pushforward (F := F ⋙ G)
          (R := T₀ ⋙ forget₂ CommRingCat RingCat) (φ ≫ F.op.whiskerLeft ψ)).map
          ((PresheafOfModules.pullbackComp φ ψ).hom.app P) =
      (PresheafOfModules.pullbackPushforwardAdjunction
        (F := F ⋙ G) (R := T₀ ⋙ forget₂ CommRingCat RingCat)
        (φ ≫ F.op.whiskerLeft ψ)).unit.app P := by
    intro P
    erw [← reassoc_of% (hmate P)]
    erw [← Functor.map_comp]
    erw [(PresheafOfModules.pullbackComp φ ψ).inv_hom_id_app P, CategoryTheory.Functor.map_id,
      Category.comp_id]
  -- (μ-NAT): slide μ past `map (c.hom ⊗ c.hom)`, merge the legs, then apply (TRI):
  erw [← Functor.LaxMonoidal.μ_natural]
  conv_lhs => rw [← htri M, ← htri N]
  erw [← MonoidalCategory.tensorHom_comp_tensorHom
    (C := _root_.PresheafOfModules (S₀ ⋙ forget₂ CommRingCat RingCat))]
  exact Category.assoc _ _ _

/-- **Sheaf-level conjugate/mate of `pullbackComp.inv` (the R0-peel building block for Sq1).**
For composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X` and any `Q : X.Modules`, the unit of the
composite-pullback adjunction `pullbackPushforwardAdjunction (h ≫ f)`, post-composed with the
pushforward of `pullbackComp.inv`, equals the unit of the *composite* of the `f`- and `h`-adjunctions,
post-composed with `pushforwardComp.hom`.  This is the `Scheme.Modules` (sheaf-level) instance of
`unit_conjugateEquiv` combined with `conjugateEquiv_pullbackComp_inv` (the mate of `pullbackComp.inv`
is `pushforwardComp.hom`); it is the cheap, sheafification-free piece of the Sq1 mate calculus that
peels the leading `R0 = pullbackComp.inv` factor.  Extracted from the inline `conj` of
`pullbackObjUnitToUnit_comp` so the (expensive, sheafification-laden) Sq1 reassembly can cite it
directly.  Project-local. -/
private lemma sheaf_unit_comp_pushforward_pullbackComp_inv {X Y Z : Scheme.{u}}
    (h : Z ⟶ Y) (f : Y ⟶ X) (Q : X.Modules) :
    (SheafOfModules.pullbackPushforwardAdjunction (Scheme.Hom.toRingCatSheafHom (h ≫ f))).unit.app Q ≫
        (SheafOfModules.pushforward (Scheme.Hom.toRingCatSheafHom (h ≫ f))).map
          ((Scheme.Modules.pullbackComp h f).inv.app Q) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
          (Scheme.Modules.pullbackPushforwardAdjunction h)).unit.app Q ≫
        (Scheme.Modules.pushforwardComp h f).hom.app
          ((Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback h).obj Q) := by
  have conj := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction h))
    (Scheme.Modules.pullbackPushforwardAdjunction (h ≫ f))
    (Scheme.Modules.pullbackComp h f).inv Q
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at conj
  exact conj.symm

/-- **STEP-1 bridge (presheaf↔sheaf pushforward compatibility, the binding obligation of the D3′
Sq1 tail).** The forgetful functor `SheafOfModules.forget` intertwines the sheaf-level
`SheafOfModules.pushforward φ` with the presheaf-level `PresheafOfModules.pushforward φ.hom`:
for any morphism `g` of sheaves of modules over `R`,
`forget.map ((pushforward φ).map g) = (PresheafOfModules.pushforward φ.hom).map (forget.map g)`.

This is the compatibility named in the blueprint's `lem:pullback_tensor_map_basechange` Sq1-tail
binding-obligation paragraph: it is what lets the recovered sheaf-level `B_f`/`B_h` unit factors
(which live under `SheafOfModules.pushforward`) be slid across into the presheaf-level
`PresheafOfModules.pushforward` of the unit identity.  It is *definitional* — `SheafOfModules.pushforward`
is built sectionwise from `PresheafOfModules.pushforward` (`pushforward_map_val`) and `forget` is the
`.val` projection (`forget_map`), so the two sides are equal by `rfl`. -/
private lemma forget_map_pushforward_map
    {C : Type u} [Category.{u} C] {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} [Functor.IsContinuous F J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {A B : SheafOfModules.{u} R} (g : A ⟶ B) :
    (SheafOfModules.forget S).map ((SheafOfModules.pushforward φ).map g) =
      (PresheafOfModules.pushforward φ.hom).map ((SheafOfModules.forget R).map g) := by
  rfl

/-! ### PROTOTYPE (d3cocycle006): NatTrans-level cocycle for `sheafificationCompPullback`.
Proved at the natural-transformation level via two instances of
`Adjunction.leftAdjointCompNatTrans_assoc` (the conjugate-mate calculus of `Mates.lean`),
with `.app P` evaluated exactly once at the end.  Relocated above
`sheafificationCompPullback_comp_tail`, which consumes it (iter-006). -/

/-- The identity-sheafification functor of a scheme `W` (the `a_W` of the D3′ unit square),
pre-elaborated once so that statements mentioning it for several schemes at once do not
re-run the (context-sensitive) instance synthesis. Reducible. Project-local. -/
private noncomputable abbrev sheafifyIdOf (W : Scheme.{u}) :=
  PresheafOfModules.sheafification.{u} (R := W.ringCatSheaf) (𝟙 W.ringCatSheaf.val)

set_option maxHeartbeats 1600000 in
/-- **NatTrans-level composition coherence of `SheafOfModules.sheafificationCompPullback`.**
The whole-transformation form of `sheafificationCompPullback_comp`: no component, no
`eqToHom`/reindex.  Proved by the mate cocycle calculus (`conjugateEquiv_comp` discipline,
internalized in `Adjunction.leftAdjointCompNatTrans_assoc`). Project-local. -/
private lemma sheafificationCompPullback_comp_natTrans {X Y Z : Scheme.{u}}
    (h : Z ⟶ Y) (f : Y ⟶ X) :
    (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).hom =
      Functor.whiskerLeft (sheafifyIdOf X) (Scheme.Modules.pullbackComp h f).inv ≫
      Functor.whiskerRight
        (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).hom
        (Scheme.Modules.pullback h) ≫
      Functor.whiskerLeft (PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom)
        (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).hom ≫
      Functor.whiskerRight
        (PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
          (Hom.toRingCatSheafHom h).hom).hom
        (sheafifyIdOf Z) := by
  -- The six adjunctions of the first (sheaf-legged) `leftAdjointCompNatTrans_assoc` instance,
  -- exactly as in `sheafificationCompPullback_comp` (verified to elaborate there).
  let adj01 := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.val)
  let adj12 := SheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom f)
  let adj23 := SheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom h)
  let adj02 := (PresheafOfModules.pullbackPushforwardAdjunction
      (Hom.toRingCatSheafHom f).hom).comp
    (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
      (𝟙 Y.ringCatSheaf.val))
  let adj13 := SheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom (h ≫ f))
  let adj03 := (PresheafOfModules.pullbackPushforwardAdjunction
      (Hom.toRingCatSheafHom (h ≫ f)).hom).comp
    (PresheafOfModules.sheafificationAdjunction (R := Z.ringCatSheaf)
      (𝟙 Z.ringCatSheaf.val))
  let τ012 :
      ((SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) ⟶
        (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f) ⋙
          (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 X.ringCatSheaf.val))) := 𝟙 _
  let τ123 :
      SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)) ⟶
        SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h) ⋙
          SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f) :=
    (SheafOfModules.pushforwardComp.{u} (Hom.toRingCatSheafHom f)
      (Hom.toRingCatSheafHom h)).inv
  let τ013 :
      ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) ⟶
        (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)) ⋙
          (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 X.ringCatSheaf.val))) := 𝟙 _
  let τ023 :
      ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) ⟶
        (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h) ⋙
          ((SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.val)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom)) :=
    Functor.whiskerLeft (SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val))
      (PresheafOfModules.pushforwardComp.{u} (Hom.toRingCatSheafHom f).hom
        (Hom.toRingCatSheafHom h).hom).inv
  have hτ :
      τ023 ≫ Functor.whiskerLeft
          (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h)) τ012 =
        τ013 ≫ Functor.whiskerRight τ123
            (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 X.ringCatSheaf.val)) ≫
          (CategoryTheory.Functor.associator _ _ _).hom := by
    ext A
    rfl
  have E1 := Adjunction.leftAdjointCompNatTrans_assoc
    adj01 adj12 adj23 adj02 adj13 adj03 τ012 τ123 τ013 τ023 hτ
  -- The second instance: the same outer (02,23,03)-triangle, but resolved through the
  -- PRESHEAF pullback leg `adj01' = PrPbPushAdj φ'_f` instead of the sheaf leg.
  let adj01' := PresheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom f).hom
  let adj12' := PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
    (𝟙 Y.ringCatSheaf.val)
  let adj13' := (PresheafOfModules.pullbackPushforwardAdjunction
      (Hom.toRingCatSheafHom h).hom).comp
    (PresheafOfModules.sheafificationAdjunction (R := Z.ringCatSheaf)
      (𝟙 Z.ringCatSheaf.val))
  let τ012' :
      ((SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) ⟶
        ((SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) := 𝟙 _
  let τ123' :
      ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h).hom) ⟶
        (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h) ⋙
          (SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.val))) := 𝟙 _
  let τ013' :
      ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) ⟶
        (((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h).hom) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) :=
    Functor.whiskerLeft (SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val))
      (PresheafOfModules.pushforwardComp.{u} (Hom.toRingCatSheafHom f).hom
        (Hom.toRingCatSheafHom h).hom).inv
  have hτ' :
      τ023 ≫ Functor.whiskerLeft
          (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h)) τ012' =
        τ013' ≫ Functor.whiskerRight τ123'
            (PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) ≫
          (CategoryTheory.Functor.associator _ _ _).hom := by
    ext A
    rfl
  have E2 := Adjunction.leftAdjointCompNatTrans_assoc
    adj01' adj12' adj23 adj02 adj13' adj03 τ012' τ123' τ013' τ023 hτ'
  -- Identify the four generic comparison transformations with the named project isos.
  have I1 : Adjunction.leftAdjointCompNatTrans adj12 adj23 adj13 τ123
      = (Scheme.Modules.pullbackComp h f).hom := rfl
  have I2 : Adjunction.leftAdjointCompNatTrans adj01 adj13 adj03 τ013
      = (SheafOfModules.sheafificationCompPullback
          (Hom.toRingCatSheafHom (h ≫ f))).hom := rfl
  have I3 : Adjunction.leftAdjointCompNatTrans adj01 adj12 adj02 τ012
      = (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).hom := rfl
  have I4 : Adjunction.leftAdjointCompNatTrans adj12' adj23 adj13' τ123'
      = (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).hom := rfl
  have I5 : Adjunction.leftAdjointCompNatTrans adj01' adj12' adj02 τ012' = 𝟙 _ :=
    conjugateEquiv_symm_id _
  -- ★3 via a THIRD assoc instance — the (f,h)-presheaf pair against the composite presheaf
  -- pullback adjunction.  Both outer comparison transformations trivialize
  -- (`conjugateEquiv_symm_id`), so the instance identifies the mixed `(01',13',03)`-comparison
  -- with the sheafified presheaf-`pullbackComp` coherence with NO conjugate manipulation.
  let adjh' := PresheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom h).hom
  let adjZ' := PresheafOfModules.sheafificationAdjunction (R := Z.ringCatSheaf)
    (𝟙 Z.ringCatSheaf.val)
  let adjhf' := PresheafOfModules.pullbackPushforwardAdjunction
    (Hom.toRingCatSheafHom (h ≫ f)).hom
  let τ012'' :
      PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom ⟶
        PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h).hom ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom :=
    (PresheafOfModules.pushforwardComp.{u} (Hom.toRingCatSheafHom f).hom
      (Hom.toRingCatSheafHom h).hom).inv
  let τ123'' :
      ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h).hom) ⟶
        ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h).hom) := 𝟙 _
  let τ023'' :
      ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) ⟶
        ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) := 𝟙 _
  have hτ'' :
      τ023'' ≫ Functor.whiskerLeft
          (SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) τ012'' =
        τ013' ≫ Functor.whiskerRight τ123''
            (PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) ≫
          (CategoryTheory.Functor.associator _ _ _).hom := by
    ext A
    rfl
  have E3 := Adjunction.leftAdjointCompNatTrans_assoc
    adj01' adjh' adjZ' adjhf' adj13' adj03 τ012'' τ123'' τ013' τ023'' hτ''
  have J1 : Adjunction.leftAdjointCompNatTrans adjh' adjZ' adj13' τ123'' = 𝟙 _ :=
    conjugateEquiv_symm_id _
  have J2 : Adjunction.leftAdjointCompNatTrans adjhf' adjZ' adj03 τ023'' = 𝟙 _ :=
    conjugateEquiv_symm_id _
  have J3 : Adjunction.leftAdjointCompNatTrans adj01' adjh' adjhf' τ012''
      = (PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
          (Hom.toRingCatSheafHom h).hom).hom := rfl
  rw [I1, I2, I3] at E1
  simp only [I4, I5] at E2
  simp only [J1, J2, J3] at E3
  -- Assemble: evaluate both pasted identities at a component `P` (the FIRST and ONLY
  -- component evaluation), eliminate the mixed comparison `X023 = adj02.lacnt adj23 adj03 τ023`
  -- between them, and peel the invertible `pullbackComp`-whisker.
  apply NatTrans.ext
  funext P
  have e1 := congr_app E1 P
  have e2 := congr_app E2 P
  have e3 := congr_app E3 P
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app, NatTrans.id_app] at e1 e2 e3 ⊢
  -- Normalize the (defeq-coerced) object spellings so the `𝟙`-junk factors match `id_comp`.
  dsimp only [Functor.comp_obj] at e1 e2 e3 ⊢
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at e1 e2 e3
  -- Eliminate the mixed comparison `X023.app P` between the first two pasted identities,
  -- then resolve the mixed `(01',13',03)`-comparison component via the third.
  -- (The h-leg comparison stays in its `leftAdjointCompNatTrans` spelling; `I4` shows it is
  -- DEFINITIONALLY `(sheafificationCompPullback (toRingCatSheafHom h)).hom`, so the final
  -- `exact` closes the residual difference by defeq.)
  rw [← e2] at e1
  -- `J1` does not fire by `rw`/`simp` (hidden instance-level defeq mismatch between the E3
  -- elaboration and the standalone `J1` statement — verified iter-006: `simp only [J1] at e3`
  -- makes no progress); `erw` defeq-matches it.  The leftover heterogeneous `𝟙`-junk is then
  -- removed by `NatTrans.id_app` + an `erw`'d `id_comp` (the identity sits at a
  -- defeq-but-not-syntactic object spelling, so plain `rw [Category.id_comp]` cannot fire).
  erw [J1] at e3
  simp only [NatTrans.id_app] at e3
  erw [Category.id_comp] at e3
  rw [e3] at e1
  -- Peel the invertible `pullbackComp`-component; `exact` closes the remaining
  -- `Scheme.Modules` vs `SheafOfModules` spelling differences by defeq.
  exact (Iso.eq_inv_comp ((Scheme.Modules.pullbackComp h f).app
    ((PresheafOfModules.sheafification (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.val)).obj P))).mpr e1

set_option maxHeartbeats 1600000 in
/-- **The R1/R5/δ collapse tail of `sheafificationCompPullback_comp` (extracted, pc263).**
This is the reduced goal of `sheafificationCompPullback_comp` AFTER the R0-peel
(`sheaf_unit_comp_pushforward_pullbackComp_inv`) and the two `← Functor.map_comp` merges that fold
the `(forget ⋙ restrictScalars)`-image of the R0-peeled-and-`pushforwardComp`-glued unit factor
together with the `(forget ⋙ restrictScalars)`-image of the `R1 ≫ R5 ≫ δ_pre` factor into a single
`(forget ⋙ restrictScalars).map (· ≫ ·)`.  The LHS is `B_{h≫f}.unit.app P` (expanded by
`comp_unit_app` over `B_{h≫f} = (PrPbPushAdj φ'_{h≫f}).comp (sheafAdj_Z)`); the RHS is
`sheafAdj_X.homEquiv` (the `η^{sX} ≫ (forget⋙restr).map _` form) of the merged unit composite.

The collapse is the `sheafificationCompPullback` twin of the tail of `pullbackObjUnitToUnit_comp`
(L969–1001): recover the two `sheafCompPb` factors `R1 = (pullback h).map (sheafCompPb f .app P).hom`
and `R5 = (sheafCompPb h .app (PrPb_f P)).hom` as `B_f`/`B_h` units via
`homEquiv_leftAdjointUniq_hom_app` on their `sheafificationCompPullback_eq_leftAdjointUniq` form,
slide `(pushforwardComp h f).hom` past them by `(pushforwardComp h f).hom.naturality`, and collapse
`comp_unit_app` + `Adjunction.unit_naturality` to `B_{h≫f}.unit`.  Project-local. -/
private lemma sheafificationCompPullback_comp_tail {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (P : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom (h ≫ f)).hom).unit.app P ≫
        (PresheafOfModules.pushforward (Hom.toRingCatSheafHom (h ≫ f)).hom).map
          ((PresheafOfModules.sheafificationAdjunction (𝟙 Z.ringCatSheaf.val)).unit.app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom (h ≫ f)).hom).obj P)) =
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.val)).unit.app P ≫
        (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.val)).map
          ((SheafOfModules.forget X.ringCatSheaf).map
            ((((pullbackPushforwardAdjunction f).comp (pullbackPushforwardAdjunction h)).unit.app
                  ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P) ≫
                (pushforwardComp h f).hom.app
                  ((pullback h).obj
                    ((pullback f).obj
                      ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P)))) ≫
              (SheafOfModules.pushforward (Hom.toRingCatSheafHom (h ≫ f))).map
                ((pullback h).map
                    ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app P).hom ≫
                  ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
                        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj P)).hom ≫
                    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.val)).map
                      ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
                          (Hom.toRingCatSheafHom h).hom).hom.app P)))) := by
  -- RESOLVED (iter-006, recipe `d3cocycle006`): the cocycle is proved ONCE at the NatTrans
  -- level by `sheafificationCompPullback_comp_natTrans` (above — three instances of
  -- `Adjunction.leftAdjointCompNatTrans_assoc`, `.app P` evaluated exactly once).  Here we
  --  (1) take its `P`-component `hC` (the component coherence — the statement of the caller
  --      `sheafificationCompPullback_comp`),
  --  (2) transpose it FORWARD under the composite adjunction
  --      `A_{h≫f} = sheafAdj_X.comp (ShPbPushAdj (h≫f))` (`congrArg homEquiv` — the forward
  --      direction of the caller's `homEquiv.injective`), and
  --  (3) replay the caller's reduction script on the hypothesis (`at h1` instead of on the
  --      goal): evaluate the LHS transpose by `homEquiv_leftAdjointUniq_hom_app`
  --      (→ `B_{h≫f}.unit.app P`), expand the RHS by `homEquiv_unit`/`comp_unit_app`,
  --      distribute under `conv`, peel R0 by the `sheaf_unit_comp_pushforward_pullbackComp_inv`
  --      `key`, and re-merge — landing exactly on this lemma's statement.
  -- (The previous iters' forward steps — `restrictScalarsId_map` strip, RHS `Functor.map_comp`
  -- distribution, `forget_map_pushforward_map` bridge, `hwr` conjugate device — are subsumed:
  -- the NatTrans-level proof never meets the dependent component composite they fought.)
  have hC : ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).app P).hom =
      (Scheme.Modules.pullbackComp h f).inv.app
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P) ≫
        (Scheme.Modules.pullback h).map
          ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app P).hom ≫
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj P)).hom ≫
        (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.val)).map
          ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
            (Hom.toRingCatSheafHom h).hom).hom.app P) := by
    have hc := congr_app (sheafificationCompPullback_comp_natTrans h f) P
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] using hc
  have h1 := congrArg
    (((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.val)).comp
        (SheafOfModules.pullbackPushforwardAdjunction
          (Hom.toRingCatSheafHom (h ≫ f)))).homEquiv _ _) hC
  rw [sheafificationCompPullback_eq_leftAdjointUniq] at h1
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app] at h1
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h1
  conv at h1 =>
    rhs
    erw [Functor.map_comp]
    erw [Functor.comp_map (SheafOfModules.pushforward (Hom.toRingCatSheafHom (h ≫ f)))]
  have key := congrArg
    (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 (Sheaf.val X.ringCatSheaf))).map
    (sheaf_unit_comp_pushforward_pullbackComp_inv h f
      ((PresheafOfModules.sheafification (𝟙 (Sheaf.val X.ringCatSheaf))).obj P))
  rw [Functor.map_comp] at key
  simp only [Functor.comp_map] at key h1
  erw [Category.assoc] at h1
  erw [reassoc_of% key] at h1
  erw [← Functor.map_comp, ← Functor.map_comp] at h1
  exact h1

set_option maxHeartbeats 800000 in
/-- **Sq1 — composition coherence of `SheafOfModules.sheafificationCompPullback` (the S1 paste
square of D3′).** For composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X` and any presheaf of
modules `P` over `X`, the sheafification–pullback comparison of the composite `h ≫ f` factors
through the comparisons of `f` and `h`, conjugated by the sheaf-level pullback pseudofunctor iso
`Scheme.Modules.pullbackComp h f` on the left and the presheaf-level pullback pseudofunctor iso
`PresheafOfModules.pullbackComp φ'_f φ'_h` (sheafified) on the right. Mathlib-absent at the pin;
the S1-foundational composition coherence consumed by `pullbackTensorMap_restrict`. It is the
`sheafificationCompPullback` twin of `pullbackObjUnitToUnit_comp`: both `sheafificationCompPullback`
isos are `leftAdjointUniq` of composite adjunctions (`sheafificationCompPullback_eq_leftAdjointUniq`),
so the coherence is proved by the adjunction-mate calculus, transposing under the composite
`A_{h≫f} = (sheafAdj_X).comp (pullbackPushforwardAdjunction (h≫f))`. -/
private lemma sheafificationCompPullback_comp {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (P : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).app P).hom =
      (SheafOfModules.pullbackComp (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).inv.app
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P) ≫
        (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
          ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app P).hom ≫
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj P)).hom ≫
        (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.val)).map
          ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
            (Hom.toRingCatSheafHom h).hom).hom.app P) := by
  -- Both `sheafificationCompPullback` isos are `leftAdjointUniq` of composite adjunctions
  -- (`sheafificationCompPullback_eq_leftAdjointUniq`).  Transpose the whole identity under
  -- `A_{h≫f} = (sheafAdj_X).comp (pullbackPushforwardAdjunction (h≫f))` and evaluate the LHS by the
  -- mate identity `homEquiv_leftAdjointUniq_hom_app`: the transpose of `(leftAdjointUniq A B).hom.app P`
  -- is `B_{h≫f}.unit.app P`, the unit of `B_{h≫f} = (PrPbPushAdj φ'_{h≫f}).comp (sheafAdj_Z)`.
  -- Non-circular fallback scaffold (iter-002): instantiate Mathlib's abstract associativity
  -- of left-adjoint comparison transformations for the triangle
  --   sheafification_X, sheaf-pullback f, sheaf-pullback h
  -- with alternate left adjoints
  --   presheaf-pullback f ⋙ sheafification_Y,
  --   sheaf-pullback (h ≫ f),
  --   presheaf-pullback (h ≫ f) ⋙ sheafification_Z.
  -- The right-adjoint coherence is componentwise `rfl`; `hAssocComponent` is the checked
  -- high-level component equation whose LHS is
  -- `a_X.map (pullbackComp h f).hom ≫ sheafificationCompPullback (h ≫ f)`.
  let adj01 := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.val)
  let adj12 := SheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom f)
  let adj23 := SheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom h)
  let adj02 := (PresheafOfModules.pullbackPushforwardAdjunction
      (Hom.toRingCatSheafHom f).hom).comp
    (PresheafOfModules.sheafificationAdjunction (R := Y.ringCatSheaf)
      (𝟙 Y.ringCatSheaf.val))
  let adj13 := SheafOfModules.pullbackPushforwardAdjunction (Hom.toRingCatSheafHom (h ≫ f))
  let adj03 := (PresheafOfModules.pullbackPushforwardAdjunction
      (Hom.toRingCatSheafHom (h ≫ f)).hom).comp
    (PresheafOfModules.sheafificationAdjunction (R := Z.ringCatSheaf)
      (𝟙 Z.ringCatSheaf.val))
  let τ012 :
      ((SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom) ⟶
        (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f) ⋙
          (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 X.ringCatSheaf.val))) := 𝟙 _
  let τ123 :
      SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)) ⟶
        SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h) ⋙
          SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f) :=
    (SheafOfModules.pushforwardComp.{u} (Hom.toRingCatSheafHom f)
      (Hom.toRingCatSheafHom h)).inv
  let τ013 :
      ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) ⟶
        (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)) ⋙
          (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 X.ringCatSheaf.val))) := 𝟙 _
  let τ023 :
      ((SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val)) ⋙
          PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom (h ≫ f)).hom) ⟶
        (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h) ⋙
          ((SheafOfModules.forget.{u} Y.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars.{u} (𝟙 Y.ringCatSheaf.val)) ⋙
            PresheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom f).hom)) :=
    Functor.whiskerLeft (SheafOfModules.forget.{u} Z.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars.{u} (𝟙 Z.ringCatSheaf.val))
      (PresheafOfModules.pushforwardComp.{u} (Hom.toRingCatSheafHom f).hom
        (Hom.toRingCatSheafHom h).hom).inv
  have hτ :
      τ023 ≫ Functor.whiskerLeft
          (SheafOfModules.pushforward.{u} (Hom.toRingCatSheafHom h)) τ012 =
        τ013 ≫ Functor.whiskerRight τ123
            (SheafOfModules.forget.{u} X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars.{u} (𝟙 X.ringCatSheaf.val)) ≫
          (CategoryTheory.Functor.associator _ _ _).hom := by
    ext A
    rfl
  have hAssocComponent :=
    congr_app (Adjunction.leftAdjointCompNatTrans_assoc
      adj01 adj12 adj23 adj02 adj13 adj03 τ012 τ123 τ013 τ023 hτ) P
  apply ((PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.val)).comp
      (SheafOfModules.pullbackPushforwardAdjunction
        (Hom.toRingCatSheafHom (h ≫ f)))).homEquiv _ _ |>.injective
  rw [sheafificationCompPullback_eq_leftAdjointUniq]
  erw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  -- LHS is now `B_{h≫f}.unit.app P` (B := (PrPbPushAdj φ'_{h≫f}).comp (sheafAdj_Z)).  Expand BOTH
  -- composite-adjunction units (`homEquiv_unit` on the RHS, `comp_unit_app` on both) so the goal is
  -- the concrete UNIT-LEVEL identity
  --   (PrPbPushAdj φ'_{h≫f}).unit P ≫ (pushforward φ'_{h≫f}).map (sheafAdj_Z.unit (pullback φ'_{h≫f} P))
  --     = (sheafAdj_X.unit P ≫ (forget⋙restrictScalars).map ((ShPbPushAdj (h≫f)).unit (a_X P)))
  --        ≫ (pushforward (h≫f) ⋙ forget⋙restrictScalars).map (R0 ≫ R1 ≫ R5 ≫ a_Z.map δ_pre),
  -- where R0 = (pullbackComp h f).inv, R1 = (pullback h).map (sheafCompPb f .app P).hom,
  -- R5 = (sheafCompPb h .app (PrPb_f P)).hom, δ_pre = (PresheafOfModules.pullbackComp φ'_f φ'_h).hom.app P.
  -- REMAINING (the genuine residual): transport the two `pullbackComp` factors across the adjunctions
  -- — sheaf `pullbackComp h f` via `conjugateEquiv_pullbackComp_inv` / `unit_conjugateEquiv`
  -- (`pushforwardComp = Iso.refl`, exactly as in `pullbackObjUnitToUnit_comp` L920), and the
  -- presheaf `pullbackComp φ'_f φ'_h` sheafified — re-expressing R0/R1/R5/δ_pre under the right-adjoint
  -- `map` as the f- and h-unit factors (`homEquiv_leftAdjointUniq_hom_app` recovers each
  -- `sheafCompPb _ .app _ .hom` as a `B_·.unit`), then collapse via `comp_unit_app` +
  -- `Adjunction.unit_naturality` to the LHS `B_{h≫f}.unit`.  This is the `sheafificationCompPullback`
  -- twin of the `pullbackObjUnitToUnit_comp` mate calculus (L910); the concrete unit identity above is
  -- the reduced goal handed to the next iteration.
  rw [Adjunction.homEquiv_unit, Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  -- ITER-262 (prover) — VERIFIED forward step.  The `conv_rhs` distribution below is the
  -- contamination-free way to expose the four RHS factors: a plain `erw [Functor.map_comp]` on the
  -- whole goal instead rewrites the *LHS* `sheafAdj_Z.unit` into its `toSheafify ≫ restrictHomEquiv`
  -- expansion (and `rw [Functor.map_comp]` does not fire — the outer functor is a defeq-but-not-
  -- syntactic composite, and the unconfined `erw` `whnf`-times-out).  Confining the rewrites to the
  -- RHS with `conv_rhs` distributes the outer `(pushforward (h≫f) ⋙ forget ⋙ restr).map` over the
  -- four-factor composite and pushes the leading `pushforward (h≫f)` inside via `Functor.comp_map`.
  -- After it the RHS reads
  --   (sheafAdj_X.unit P ≫ (forget⋙restr).map (ShPbPushAdj(h≫f).unit (a_X P)))
  --     ≫ (forget⋙restr).map ((pushforward (h≫f)).map R0)
  --     ≫ (pushforward (h≫f) ⋙ forget⋙restr).map (R1 ≫ R5 ≫ a_Z.map δ_pre),
  -- so the second and third factors are now BOTH `(forget⋙restr).map _` and adjacent.
  conv_rhs =>
    erw [Functor.map_comp]
    erw [Functor.comp_map (SheafOfModules.pushforward (Hom.toRingCatSheafHom (h ≫ f)))]
  -- ITER-262 (prover) — R0 PEELED.  Merge the two adjacent `(forget⋙restr).map _` factors and peel
  -- the leading `R0 = (pullbackComp h f).inv` by the building block.  Plain `rw [Category.assoc]` does
  -- NOT re-expose the `(f ≫ g) ≫ h` head, and `slice_rhs` keeps the `comp_unit_app`-glued
  -- `(sheafAdj_X.unit ≫ A)` as a single factor — so we derive the merged-and-peeled equation under
  -- `(forget⋙restr).map` via `congrArg` + `Functor.map_comp`, then splice it in with `reassoc_of%`
  -- (which matches the `A ≫ (B' ≫ rest)` association in place).
  -- `key` IS the merged-and-peeled R0 equation, PROVEN (axiom-clean) and in the goal's exact spelling:
  --   `(forget⋙restr).map (ShPbPushAdj(h≫f).unit (a_X P)) ≫ (forget⋙restr).map ((pushforward (h≫f)).map R0)
  --     = (forget⋙restr).map ((ShPbPushAdj f .comp ShPbPushAdj h).unit (a_X P) ≫ pushforwardComp.hom _)`,
  -- obtained by mapping the building block `sheaf_unit_comp_pushforward_pullbackComp_inv` under
  -- `(forget⋙restr).map` and splitting with `Functor.map_comp`.  Its LHS is precisely the 2nd ≫ 3rd RHS
  -- factors of the goal.
  have key := congrArg
    (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 (Sheaf.val X.ringCatSheaf))).map
    (sheaf_unit_comp_pushforward_pullbackComp_inv h f
      ((PresheafOfModules.sheafification (𝟙 (Sheaf.val X.ringCatSheaf))).obj P))
  rw [Functor.map_comp] at key
  -- SPLICE `key` IN (R0-peel).  `simp only [Functor.comp_map]` puts goal + `key` in the same unfolded
  -- `restrictScalars.map (forget.map _)` normal form; `erw [Category.assoc]` (NOT `rw`/`simp` — the
  -- intermediate objects are defeq-but-not-syntactic `Functor.obj` applications, so only `erw`'s
  -- defeq-implicit matching flattens the `comp_unit_app`-glued `(sheafAdj_X.unit ≫ A)`) right-associates
  -- the RHS; `erw [reassoc_of% key]` then rewrites `A ≫ (B' ≫ C)` → `merged ≫ C`, replacing the leading
  -- `R0 = (pullbackComp h f).inv` factor by the composite `f`/`h`-adjunction unit + `pushforwardComp.hom`.
  simp only [Functor.comp_map] at key ⊢
  erw [Category.assoc]
  erw [reassoc_of% key]
  -- R0 PEELED.  Goal RHS now reads (X-side sheafification discharged):
  --   sheafAdj_X.unit P
  --     ≫ (forget⋙restr).map ((ShPbPushAdj f .comp ShPbPushAdj h).unit (a_X P) ≫ pushforwardComp.hom _)
  --     ≫ (forget⋙restr).map ((pushforward (h≫f)).map (R1 ≫ R5 ≫ a_Z.map δ_pre)),
  -- LHS = `B_{h≫f}.unit.app P` = `PrPbPushAdj(φ'_{h≫f}).unit P ≫ (pushforward φ'_{h≫f}).map (sheafAdj_Z.unit …)`.
  -- REMAINING TAIL (the analog of `pullbackObjUnitToUnit_comp`'s tail, L969-996): recover the two
  -- `sheafCompPb` factors R1 = `(pullback h).map (sheafCompPb f .app P).hom` and
  -- R5 = `(sheafCompPb h .app (PrPb_f P)).hom` as `B_f`/`B_h` units via `homEquiv_leftAdjointUniq_hom_app`
  -- on their `sheafificationCompPullback_eq_leftAdjointUniq` form, slide `pushforwardComp.hom` past them by
  -- `(pushforwardComp h f).hom.naturality`, and collapse `comp_unit_app` + `Adjunction.unit_naturality`
  -- to `B_{h≫f}.unit` — mirroring `hinner`/`hcomp'` + the final `erw` chain of `pullbackObjUnitToUnit_comp`.
  -- MERGE the two adjacent `(forget ⋙ restrictScalars).map _` RHS factors into one (verified `erw`),
  -- then discharge the merged tail by the extracted named lemma.
  erw [← Functor.map_comp, ← Functor.map_comp]
  exact sheafificationCompPullback_comp_tail h f P

/-- **Brick 1 (Sq-cancellation) — sheafification kills the presheaf `pullbackComp` hom∘inv round-trip.**
For composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X` and any presheaf `T` over `X`, the
sheafification functor `aZ = sheafification (𝟙 Z.ringCatSheaf.val)` sends the `hom ≫ inv` round-trip
of the Mathlib presheaf coherence `PresheafOfModules.pullbackComp φf φh` to the identity.  This is the
`D ≫ E = 𝟙` cancellation consumed by step (i) of the four-square interleave in
`pullbackTensorMap_restrict` (where `D = aZ.map (pbComp.hom.app T)` comes from the Sq1 brick
`sheafificationCompPullback_comp` and `E = aZ.map (pb.inv.app T)` from the Sq2b splice `hδ`). -/
private lemma sheafifyMap_pullbackComp_hom_inv_id {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (T : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.sheafification (R := Z.ringCatSheaf) (𝟙 Z.ringCatSheaf.val)).map
        ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
          (Hom.toRingCatSheafHom h).hom).hom.app T) ≫
      (PresheafOfModules.sheafification (R := Z.ringCatSheaf) (𝟙 Z.ringCatSheaf.val)).map
        ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
          (Hom.toRingCatSheafHom h).hom).inv.app T) = 𝟙 _ := by
  rw [← Functor.map_comp]
  erw [Iso.hom_inv_id_app]
  exact (PresheafOfModules.sheafification (R := Z.ringCatSheaf) (𝟙 Z.ringCatSheaf.val)).map_id _

/-- **Step-(i) middle-cancellation skeleton (instance-agnostic).** A purely categorical reassociation:
in any category, a 4-fold prefix ending in `d` composed with a tail beginning in its inverse `e`
(`d ≫ e = 𝟙`) collapses the cancelling pair, leaving the prefix glued to the tail.  Stated and proved
generically so every `≫` shares ONE `Category` instance and `Category.assoc` reassociates freely; it is
then `exact`-applied (NOT `rw`-applied) against the concrete D3′ goal, where the `sheafificationCompPullback`
/`pullbackComp` `.app`-components compose through DEFEQ-but-not-syntactic `SheafOfModules` instances —
`exact` unifies up to defeq and so crosses the instance gap that blocks every `rw/simp [Category.assoc]`.
This is the device that lands step (i) of `pullbackTensorMap_restrict` without the mate-`whnf` bomb. -/
private lemma comp_cancel_mid {C : Type*} [Category C] {A₀ B₀ C₀ D₀ E₀ F₀ : C}
    (r0 : A₀ ⟶ B₀) (r1 : B₀ ⟶ C₀) (r5 : C₀ ⟶ D₀) (d : D₀ ⟶ E₀) (e : E₀ ⟶ D₀)
    (rest : D₀ ⟶ F₀) (hde : d ≫ e = 𝟙 D₀) :
    (r0 ≫ r1 ≫ r5 ≫ d) ≫ e ≫ rest = r0 ≫ r1 ≫ r5 ≫ rest := by
  simp only [Category.assoc]
  rw [← Category.assoc d e rest, hde, Category.id_comp]

/-- **Generic nested slide (mirrors the post-step-(ii) goal nesting exactly).** Substitutes the
buried pair `r5 ≫ p` (the `S1^h`-then-`a.map (Fp_h.map δ_f)` factor) by `u ≫ v` through a different
intermediate object `d'`, leaving the post-substitution equation as the residual goal.  Applied by
`refine comp_slide_nested … hslide ?_`: the conclusion is written to mirror the goal's *literal*
parenthesisation `(r0 ≫ r1 ≫ r5 ≫ (p ≫ q) ≫ rtc) ≫ s3 ≫ s4`, so `refine` unifies it against the
goal by *metavariable assignment only* — no keyed `simp`/`rw`/`erw` matching, hence no
`whnf`-bomb across the defeq-but-not-syntactic `SheafOfModules` instance boundary (the same reason
`comp_cancel_mid` lands step (i) by `exact`).  The actual `rw` runs on this lemma's own
single-`[Category C]` variables, where assoc is trivial. -/
private lemma comp_slide_nested {C : Type*} [Category C] {a b c d e k m n g d' : C}
    (r0 : a ⟶ b) (r1 : b ⟶ c) (r5 : c ⟶ d) (p : d ⟶ e) (q : e ⟶ k) (rtc : k ⟶ m)
    (s3 : m ⟶ n) (s4 : n ⟶ g) (u : c ⟶ d') (v : d' ⟶ e) (rhs : a ⟶ g)
    (hsl : r5 ≫ p = u ≫ v)
    (hrest : (r0 ≫ r1 ≫ (u ≫ v) ≫ q ≫ rtc) ≫ s3 ≫ s4 = rhs) :
    (r0 ≫ r1 ≫ r5 ≫ (p ≫ q) ≫ rtc) ≫ s3 ≫ s4 = rhs := by
  have hassoc : r5 ≫ (p ≫ q) ≫ rtc = (r5 ≫ p) ≫ q ≫ rtc := by
    simp only [Category.assoc]
  rw [hassoc, hsl]; exact hrest

/-- **Generic three-prefix cancellation across an L/R-defeq boundary.** The post-slide D3′ residual
has the form `(r0 ≫ r1 ≫ (u ≫ v) ≫ q ≫ rtc) ≫ s3 ≫ s4 = r0' ≫ (m1 ≫ m2 ≫ m3 ≫ m4) ≫ …` where the
first three left factors `r0,r1,u` are *defeq-but-not-syntactically-equal* to the first three right
factors `r0',m1,m2` (the `SheafOfModules` vs `Scheme.Modules` pullback spellings).  Passing `rfl` for
`hr0/hr1/hu` discharges those leaf defeqs (small terms — no big-composite `whnf`), then the generic
`subst`+assoc reduces the goal to the pure `hcore` (the merged Sq3/Sq4 chase).  Applied by
`refine comp_cancel_three_lr … rfl rfl rfl ?_`. -/
private lemma comp_cancel_three_lr {C : Type*} [Category C]
    {a b cc c' e kk mm nn g c4 c5 c6 c7 c8 c9 : C}
    (r0 : a ⟶ b) (r1 : b ⟶ cc) (u : cc ⟶ c') (v : c' ⟶ e) (q : e ⟶ kk) (rtc : kk ⟶ mm)
    (s3 : mm ⟶ nn) (s4 : nn ⟶ g)
    (r0' : a ⟶ b) (m1 : b ⟶ cc) (m2 : cc ⟶ c') (m3 : c' ⟶ c4) (m4 : c4 ⟶ c5) (vv : c5 ⟶ c6)
    (dh : c6 ⟶ c7) (sh3 : c7 ⟶ c8) (sh4 : c8 ⟶ c9) (tf : c9 ⟶ g)
    (hr0 : r0 = r0') (hr1 : r1 = m1) (hu : u = m2)
    (hcore : v ≫ q ≫ rtc ≫ s3 ≫ s4 = m3 ≫ m4 ≫ vv ≫ dh ≫ sh3 ≫ sh4 ≫ tf) :
    (r0 ≫ r1 ≫ (u ≫ v) ≫ q ≫ rtc) ≫ s3 ≫ s4
      = r0' ≫ (m1 ≫ m2 ≫ m3 ≫ m4) ≫ vv ≫ dh ≫ sh3 ≫ sh4 ≫ tf := by
  subst hr0 hr1 hu
  simp only [Category.assoc]
  rw [hcore]

/-- **Generic slide-then-cancel for the merged Sq3/Sq4 core (instance-agnostic).** The
post-`comp_cancel_three_lr` residual of `pullbackTensorMap_restrict` has the form
`v ≫ q ≫ rtc ≫ s3 ≫ s4 = m3 ≫ m4 ≫ vv ≫ dh ≫ sh3 ≫ sh4 ≫ tf`, where the RHS prefix
`m3 ≫ m4 ≫ vv` (`= (pullback h).map S3_f ≫ (pullback h).map S4_f ≫ S1_h''`) equals, by the
naturality of the connecting iso `sheafificationCompPullback h` at the morphism `gg`
(`a_Y.map gg = S3_f ≫ S4_f`), the slid form `v ≫ vtail` with `v = S1_h` (presheaf args) and
`vtail = a_Z.map (Fp_h.map gg)`.  Splicing that equation (`hcomb`) plus the resulting folded
presheaf core (`hcore2`) closes the goal.  Stated generically over one `[Category C]` so the
`subst`/`assoc` algebra never crosses the defeq-but-not-syntactic `SheafOfModules` instance
boundary that whnf-bombs `simp`/`rw`/`erw` on the concrete goal; applied by
`refine comp_slide_three … hcomb ?_` (assignment-only unification). -/
private lemma comp_slide_three {C : Type*} [Category C]
    {a b b3 c1 c2 c3 d1 d2 d3 d4 d5 g : C}
    (v : a ⟶ b) (q : b ⟶ c1) (rtc : c1 ⟶ c2) (s3 : c2 ⟶ c3) (s4 : c3 ⟶ g)
    (m3 : a ⟶ d1) (m4 : d1 ⟶ d2) (vv : d2 ⟶ b3) (dh : b3 ⟶ d3) (sh3 : d3 ⟶ d4)
    (sh4 : d4 ⟶ d5) (tf : d5 ⟶ g) (vtail : b ⟶ b3)
    (hcomb : m3 ≫ m4 ≫ vv = v ≫ vtail)
    (hcore2 : q ≫ rtc ≫ s3 ≫ s4 = vtail ≫ dh ≫ sh3 ≫ sh4 ≫ tf) :
    v ≫ q ≫ rtc ≫ s3 ≫ s4 = m3 ≫ m4 ≫ vv ≫ dh ≫ sh3 ≫ sh4 ≫ tf := by
  rw [hcore2, ← Category.assoc v vtail, ← hcomb]
  simp only [Category.assoc]

/-- **Generic merge-then-slide for the `hcomb` leg (instance-agnostic).** Over an abstract functor
`G`, `G.map s3f ≫ G.map s4f ≫ vv` merges (`Functor.map_comp`) and rewrites by `hg : gmap = s3f ≫ s4f`
to `G.map gmap ≫ vv`, closed by the naturality `hnat`.  Stated generically so the `assoc`/`map_comp`
algebra runs on clean abstract variables, never crossing the defeq-but-not-syntactic `SheafOfModules`
instance boundary that whnf-bombs `rw [← Category.assoc]` / `rw [← Functor.map_comp]` on the concrete
post-step-(ii) goal; applied by `exact map_comp_slide G _ _ gmap _ _ hg hnat`. -/
private lemma map_comp_slide {C D : Type*} [Category C] [Category D] (G : C ⥤ D)
    {x y z : C} {w : D} (s3f : x ⟶ y) (s4f : y ⟶ z) (gmap : x ⟶ z)
    (vv : G.obj z ⟶ w) (rhs : G.obj x ⟶ w)
    (hg : gmap = s3f ≫ s4f) (hnat : G.map gmap ≫ vv = rhs) :
    G.map s3f ≫ G.map s4f ≫ vv = rhs := by
  have e : G.map s3f ≫ G.map s4f = G.map gmap := by rw [hg, Functor.map_comp]
  calc G.map s3f ≫ G.map s4f ≫ vv
        = (G.map s3f ≫ G.map s4f) ≫ vv := by rw [Category.assoc]
    _ = G.map gmap ≫ vv := by rw [e]
    _ = rhs := hnat

/-- **Generic fold-4-vs-5-under-a-functor reduction (instance-agnostic).** A 4-fold `F.map`-composite
equals a 5-fold `F.map`-composite as soon as the underlying presheaf composites agree (`hcore`).  The
`← Functor.map_comp` merge runs on this lemma's own clean `[Category C]` variables, where the
discrimination-tree match is trivial; it is then applied to the merged Sq3/Sq4 core of
`pullbackTensorMap_restrict` by `refine map_comp4_eq_comp5 _ _ _ _ _ _ _ _ _ _ ?_`
(assignment-only unification), crossing the defeq-but-not-syntactic `SheafOfModules` instance boundary
that whnf-bombs `simp`/`rw [← Functor.map_comp]` on the concrete folded goal. -/
private lemma map_comp4_eq_comp5 {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {x₀ x₁ x₂ x₃ x₄ : C} (a₁ : x₀ ⟶ x₁) (a₂ : x₁ ⟶ x₂) (a₃ : x₂ ⟶ x₃) (a₄ : x₃ ⟶ x₄)
    {z₁ z₂ z₃ z₄ : C} (b₁ : x₀ ⟶ z₁) (b₂ : z₁ ⟶ z₂) (b₃ : z₂ ⟶ z₃) (b₄ : z₃ ⟶ z₄) (b₅ : z₄ ⟶ x₄)
    (hcore : a₁ ≫ a₂ ≫ a₃ ≫ a₄ = b₁ ≫ b₂ ≫ b₃ ≫ b₄ ≫ b₅) :
    F.map a₁ ≫ F.map a₂ ≫ F.map a₃ ≫ F.map a₄
      = F.map b₁ ≫ F.map b₂ ≫ F.map b₃ ≫ F.map b₄ ≫ F.map b₅ := by
  simp only [← Functor.map_comp]
  rw [hcore]

/-- **Generic bifunctorial collapse of a 3-vs-4 `tensorHom` chain to its two legs (instance-agnostic).**
A 3-fold composite of `tensorHom`s equals a 4-fold one as soon as the two underlying leg composites
agree (`hM`, `hN`).  The `tensorHom_comp_tensorHom` interchange runs on this lemma's own clean
`[MonoidalCategory C]` variables, then it is applied to the merged Sq3/Sq4 core of
`pullbackTensorMap_restrict` by `refine tensorHom_collapse_3_4 … ?_ ?_` (assignment-only unification),
crossing the non-canonical `MonoidalCategoryStruct` instance baked into the concrete goal on which
`simp`/`rw [tensorHom_comp_tensorHom]` makes no progress. -/
private lemma tensorHom_collapse_3_4 {C : Type*} [Category C] [MonoidalCategory C]
    {xM₀ xM₁ xM₂ xM₃ xN₀ xN₁ xN₂ xN₃ : C}
    (p₁ : xM₀ ⟶ xM₁) (p₂ : xM₁ ⟶ xM₂) (p₃ : xM₂ ⟶ xM₃)
    (q₁ : xN₀ ⟶ xN₁) (q₂ : xN₁ ⟶ xN₂) (q₃ : xN₂ ⟶ xN₃)
    {yM₁ yM₂ yM₃ yN₁ yN₂ yN₃ : C}
    (r₁ : xM₀ ⟶ yM₁) (r₂ : yM₁ ⟶ yM₂) (r₃ : yM₂ ⟶ yM₃) (r₄ : yM₃ ⟶ xM₃)
    (s₁ : xN₀ ⟶ yN₁) (s₂ : yN₁ ⟶ yN₂) (s₃ : yN₂ ⟶ yN₃) (s₄ : yN₃ ⟶ xN₃)
    (hM : p₁ ≫ p₂ ≫ p₃ = r₁ ≫ r₂ ≫ r₃ ≫ r₄)
    (hN : q₁ ≫ q₂ ≫ q₃ = s₁ ≫ s₂ ≫ s₃ ≫ s₄) :
    MonoidalCategory.tensorHom p₁ q₁ ≫ MonoidalCategory.tensorHom p₂ q₂ ≫
        MonoidalCategory.tensorHom p₃ q₃
      = MonoidalCategory.tensorHom r₁ s₁ ≫ MonoidalCategory.tensorHom r₂ s₂ ≫
          MonoidalCategory.tensorHom r₃ s₃ ≫ MonoidalCategory.tensorHom r₄ s₄ := by
  simp only [MonoidalCategory.tensorHom_comp_tensorHom, hM, hN]

/-- **Generic adjunction unit-counit triangle (instance-agnostic).** For an adjunction `L ⊣ R` and
any `k : L.obj P ⟶ M`, sheafifying the unit-into-`R k` composite and post-composing the counit
recovers `k`.  This is the abstract triangle identity behind the `pullbackValIso` counit reassembly
(blueprint `lem:pullback_val_iso_comp_counit`, the (T) step): with `L = sheafification`,
`R = forget`, `P = pullback presheaf`, `M = sheaf pullback`, `k = (pullbackValIso _ _).hom`, it states
`a(η ≫ forget k) ≫ ε = k`.  Stated generically over one pair `[Category C]`/`[Category D]` so the
`Functor.map_comp`/`counit_naturality`/`left_triangle_components` algebra never crosses the
defeq-but-not-syntactic `SheafOfModules`/`Scheme.Modules` instance boundary; applied by `exact`. -/
private lemma adj_unit_map_counit {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (P : C) (M : D) (k : L.obj P ⟶ M) :
    L.map (adj.unit.app P ≫ R.map k) ≫ adj.counit.app M = k :=
  (adj.homEquiv P M).left_inv k

/-- **Generic forget-image cocycle reassembly (instance-agnostic).** Given the sheaf-level cocycle
`x ≫ y = x' ≫ y' ≫ z'` in `C`, its `F`-image, prefixed by any `η`, reassembles as the matching
forget-image composite.  Stated over one `[Category C]`/`[Category D]` so the `Functor.map_comp`
merges run on clean abstract variables; applied to the concrete D3′ reduction goal by `exact`, whose
defeq unification crosses the `Sheaf.val`/`ObjectProperty.obj` (deprecated-alias) boundary that
blocks `rw [← Functor.map_comp]` on the concrete forget-images.  This is the (T)/(H)→goal bridge in
`pullbackValIso_comp_leg` (blueprint `lem:pullback_val_iso_comp`). -/
private lemma comp_forget_cocycle {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c a' d' : C} {Wd : D} (η : Wd ⟶ F.obj a) (x : a ⟶ b) (y : b ⟶ c)
    (x' : a ⟶ a') (y' : a' ⟶ d') (z' : d' ⟶ c) (h : x ≫ y = x' ≫ y' ≫ z') :
    η ≫ F.map x ≫ F.map y = η ≫ F.map x' ≫ F.map y' ≫ F.map z' := by
  rw [← Functor.map_comp, h, Functor.map_comp, Functor.map_comp]

/-- **Generic interleaved 3-pair telescope (instance-agnostic).** A palindromic composite collapses to
its centre `g` once the three nested pairs cancel (`A≫A' = B≫B' = C≫C' = 𝟙`).  Stated over one
`[Category C]` so the `Category.assoc` flattening runs on clean abstract variables — never on the
`SheafOfModules` carrier where `simp/rw [Category.assoc]` whnf-bombs — then applied to the inverse of
`sheafificationCompPullback_comp` by `exact`.  This is the Sq4a telescope of
`sheafificationCompPullback_comp_inv`. -/
private lemma inv_telescope {C : Type*} [Category C] {w x y z t : C}
    (A : w ⟶ x) (A' : x ⟶ w) (B : x ⟶ y) (B' : y ⟶ x) (Cc : y ⟶ z) (C' : z ⟶ y) (g : w ⟶ t)
    (hA : A ≫ A' = 𝟙 w) (hB : B ≫ B' = 𝟙 x) (hC : Cc ≫ C' = 𝟙 y) :
    g = (A ≫ B ≫ Cc) ≫ C' ≫ B' ≫ A' ≫ g := by
  simp only [Category.assoc]
  rw [← Category.assoc Cc C', hC, Category.id_comp, ← Category.assoc B B', hB, Category.id_comp,
    ← Category.assoc A A', hA, Category.id_comp]

/-- **Generic cocycle assembly (instance-agnostic).** The algebraic skeleton of the `pullbackValIso`
composition coherence `hH` in `pullbackValIso_comp_leg`: the LHS reassembles via the Sq4a inverse
(`h1`) and `pullbackComp` naturality (`h2`); the RHS via `sheafificationCompPullback h` naturality
(`h3`); the two meet through the adjunction triangle `h4`.  Stated over one `[Category C]`/`[Category D]`
with abstract `F` so the `Functor.map_comp` merges and `Category.assoc` reshuffles run on clean
variables (no `SheafOfModules` whnf-bomb); applied by `exact`. -/
private lemma cocycle_assemble {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {dA dB dC dD dQ : D} {cP cQ cR cS : C}
    (p : dA ⟶ dB) (sf : dB ⟶ dC) (m1 : dC ⟶ dD)
    (sh : dA ⟶ F.obj cP) (x1 : cP ⟶ cQ) (pa : F.obj cQ ⟶ dC) (x2 : cQ ⟶ cR) (pw : F.obj cR ⟶ dD)
    (q : dA ⟶ dQ) (sQ : dQ ⟶ F.obj cS) (x3 : cP ⟶ cS) (x4 : cS ⟶ cR)
    (h1 : p ≫ sf = sh ≫ F.map x1 ≫ pa) (h2 : pa ≫ m1 = F.map x2 ≫ pw)
    (h3 : q ≫ sQ = sh ≫ F.map x3) (h4 : x3 ≫ x4 = x1 ≫ x2) :
    p ≫ sf ≫ m1 = q ≫ (sQ ≫ F.map x4) ≫ pw := by
  rw [reassoc_of% h1, h2, Category.assoc sQ, reassoc_of% h3, ← Category.assoc (F.map x1),
    ← Functor.map_comp, ← Category.assoc (F.map x3), ← Functor.map_comp, h4]

set_option maxHeartbeats 1600000 in
/-- **Step-(ii) — the `comp_δ` split of `δcomp` under `a_Z.map`.** The oplax tensorator of the
*composite* presheaf pullback `pullback φ'_f ⋙ pullback φ'_h`, sheafified, decomposes (by the Mathlib
oplax-monoidal coherence `Functor.OplaxMonoidal.comp_δ` of a composite of left adjoints) into the
sheafification of `(pullback φ'_h).map δ_f` followed by the sheafification of `δ_h` on the pulled-back
arguments. This is the mechanical step (ii) of the four-square interleave in
`pullbackTensorMap_restrict`; stated with the same `show … from` ring-map ascriptions as the proof's
`δcomp` binding so the `MonoidalCategory`/`forget₂` instances pin identically (iter-257 finding (3)).
Project-local. -/
private lemma sheafifyMap_δcomp_split {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (M N : X.Modules) :
    (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map
        (Functor.OplaxMonoidal.δ
          (PresheafOfModules.pullback
              (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom f).hom) ⋙
            PresheafOfModules.pullback
              (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map h.base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom h).hom))
          M.val N.val) =
      (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map
          ((PresheafOfModules.pullback
              (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map h.base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom h).hom)).map
            (Functor.OplaxMonoidal.δ
              (PresheafOfModules.pullback
                (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                    (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                  from (Hom.toRingCatSheafHom f).hom))
              M.val N.val)) ≫
        (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map
          (Functor.OplaxMonoidal.δ
            (PresheafOfModules.pullback
              (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map h.base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom h).hom))
            ((PresheafOfModules.pullback
              (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom f).hom)).obj M.val)
            ((PresheafOfModules.pullback
              (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                  (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                from (Hom.toRingCatSheafHom f).hom)).obj N.val)) := by
  -- `δ (F ⋙ G)` is *definitionally* `G.map (δ F) ≫ δ G` (the `Functor.OplaxMonoidal.comp`
  -- instance), so after folding the two `a.map`s by `← Functor.map_comp` the `congr 1` closes by `rfl`.
  rw [← Functor.map_comp]
  congr 1

/-- **Sq4a — inverse of the Sq1 coherence `sheafificationCompPullback_comp`** (blueprint
`lem:pullback_val_iso_comp_scpb`).  Taking inverses of the four-factor `sheafificationCompPullback_comp`
identity and cancelling `a_Z.map(PrPbComp.hom)` against the leading `a_Z.map(Pc)` gives the
`sheafCompPb⁻¹` reassembly consumed by `pullbackValIso_comp_leg`.  Project-local. -/
private lemma sheafificationCompPullback_comp_inv {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (P : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.val)).map
          ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
            (Hom.toRingCatSheafHom h).hom).hom.app P) ≫
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).app P).inv
      = ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj P)).inv ≫
          (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
            ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app P).inv ≫
          (SheafOfModules.pullbackComp (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).hom.app
            ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P) := by
  have hA : ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj P)).inv ≫
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj P)).hom = 𝟙 _ :=
    Iso.inv_hom_id _
  have hB : (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
          ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app P).inv ≫
        (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
          ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app P).hom = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  have hC : (SheafOfModules.pullbackComp (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).hom.app
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P) ≫
        (SheafOfModules.pullbackComp (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).inv.app
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj P) = 𝟙 _ :=
    Iso.hom_inv_id_app _ _
  rw [Iso.comp_inv_eq, sheafificationCompPullback_comp h f P]
  exact inv_telescope _ _ _ _ _ _ _ hA hB hC

/- Planner strategy (iter-019): closing the sole remaining `sorry` in `pullbackValIso_comp_leg`
   (blueprint `lem:pullback_val_iso_comp`, `lem:pullback_val_iso_comp_scpb`,
   `lem:pullback_val_iso_comp_counit`).

   **Post-split goal** (after both `simp only` lines at the bottom of the proof body — the
   pVI-unfold pass and the `Functor.map_comp`/`Category.assoc` atomic-split pass).  The goal is
   exactly the fully-atomic identity written in the in-proof comments at L3206–3208:
     pbᵖ.hom.app W.val ≫ η^Z ≫ FZ[SCPb(h≫f)⁻¹] ≫ FZ[ph_{h≫f}(cuX W)]
       = ph_h(η^Y) ≫ ph_h(FY[SCPb f⁻¹]) ≫ ph_h(FY[ph_f(cuX W)]) ≫ η^Z
           ≫ FZ[SCPb h⁻¹] ≫ FZ[ph_h(cuY (f*W))] ≫ FZ[(pullbackComp h f).app W .hom]
   (Notation: FZ = `SheafOfModules.forget Z.ringCatSheaf`, SCPb g =
   `SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom g)`, ph_g = sheaf pullback map,
   η^Z = sheafification unit, cuX W = sheafification counit at W, pbᵖ = `PresheafOfModules.pullbackComp`.)

   **Strategy: two in-proof `have`s, then assembly.**  Do NOT use blind multi-`erw`; instance
   boundaries between `SheafOfModules` and `Scheme.Modules` spellings cause `whnf`-bombs under
   `rw`/`erw [Category.assoc]`.  Use the existing instance-agnostic generic lemmas (stated once
   over a single `[Category C]` variable so Lean's defeq unification — not rewriting — crosses the
   boundary): `comp_cancel_mid` (L2988), `comp_slide_nested` (L3004), `comp_cancel_three_lr` (L3021),
   `comp_slide_three` (L3046), `map_comp_slide` (L3063), `map_comp4_eq_comp5` (L3081).  Apply
   each by `exact` or `refine … ?_` so the assignment is pure unification.  Region rewrites that
   genuinely stay inside the `Sheaf.val Z` carrier still need `erw`.

   **Sub-coherence 1 — SCPb⁻¹ reassembly (blueprint `lem:pullback_val_iso_comp_scpb`).**
   Derive from the PROVEN Sq1 coherence `sheafificationCompPullback_comp h f W.val` (private,
   L2795, same file).  That lemma states (with `P := W.val`):
     `(SCPb (h≫f)).app P .hom = pullbackComp(f,h)^{-1}.app(a_X.obj P)
       ≫ ph_h.map ((SCPb f).app P .hom) ≫ (SCPb h).app(pb_f P) .hom ≫ a_Z.map(pbᵖ.hom.app P)`
   Invert both sides to obtain `(SCPb (h≫f)).app P .inv`; then use
   `IsIso.inv_comp_eq`, `Iso.comp_inv_eq`, and `Category.assoc` to express the three SCPb⁻¹
   factors on the RHS of the post-split goal (the `FZ[SCPb(h≫f)⁻¹]` on the LHS plus
   `FZ[SCPb h⁻¹]` and `ph_h(FY[SCPb f⁻¹])` on the RHS) in terms of the Sq1 equation.
   State as:
     have hSCPb : <LHS SCPb-slice> = <RHS SCPb-slice> := by
       have h1 := sheafificationCompPullback_comp h f W.val
       -- invert, reassociate, cancel

   **Sub-coherence 2 — counit reassembly (blueprint `lem:pullback_val_iso_comp_counit`).**
   Use naturality of the sheafification adjunction counit
     `(PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Z.ringCatSheaf))).counit`
   across the morphism `(pullbackComp h f).app W` (in the category of presheaves of modules
   over Z), which moves `FZ[(pullbackComp h f).app W .hom]` past the pulled-back counit factors.
   Apply via `NatTrans.naturality` (or equivalently `Adjunction.counit_naturality`).
   State as:
     have hCounit : <LHS counit-slice> = <RHS counit-slice> := by
       have h2 := (PresheafOfModules.sheafificationAdjunction
         (𝟙 (Sheaf.val Z.ringCatSheaf))).counit.naturality
         ((pullbackComp h f).app W)   -- or the appropriate component
       -- reassociate as needed

   **Assembly.**  After both `have`s, rewrite using `hSCPb` and `hCounit`, then close by
   `Functor.map_comp`, `Category.assoc`, and — for any remaining instance-boundary
   reassociation — a `refine`+`exact` against one of the abstract generic lemmas above.

   **INSTANCE-BOUNDARY DEVICE** (reuse pattern documented throughout the file): whenever a `≫`
   in the concrete goal joins terms whose types are definitionally but not syntactically equal
   (e.g. `SheafOfModules Z.ringCatSheaf` vs `Scheme.Modules Z`), stating the required
   reassociation or cancellation as a fresh `private` single-`[Category C]` lemma (analogous to
   `comp_cancel_mid`, `comp_slide_three`, `map_comp_slide`) and discharging by `exact` (pure
   defeq unification, no rewriting) is the correct device.  Keep ALL new helpers as `private`
   at top-level — the carrier-instance trap is an elaboration-time problem that only bites at
   top level when the type ascription fixes the concrete category; it does NOT bite inside an
   in-proof `have` whose type is inferred.  If the in-proof chase hits a class that the
   `exact`-device cannot cross, report: exact tactic used, full elaborated goal — do NOT pile
   on additional `erw` layers. -/
set_option maxHeartbeats 1600000 in
/-- **Sq4 — the per-leg `pullbackValIso` composition coherence** (blueprint `lem:pullback_val_iso_comp`).
For composable `h : Z ⟶ Y`, `f : Y ⟶ X` and `W : X.Modules`, the canonical "sheafification-unit into the
underlying presheaf of the pullback" — `η ≫ forget (pullbackValIso · W).hom` — composes
pseudofunctorially across `h ≫ f`, reconciling `pullbackValIso (h ≫ f)`, `pullbackValIso h`,
`pullbackValIso f`, the presheaf coherence `PresheafOfModules.pullbackComp` and the sheaf coherence
`pullbackComp h f`. This is the single per-leg residual of the merged Sq3/Sq4 presheaf core of
`pullbackTensorMap_restrict` (applied once for `M` and once for `N`).

By `def:pullback_val_iso`, `pullbackValIso f W = (sheafificationCompPullback f).symm.app W.val ≪≫
(pullback f).mapIso (sheafification counit at W)`; substituting this factorisation on every leg, the
`sheafCompPb⁻¹` parts reassemble via the Sq1 coherence `sheafificationCompPullback_comp` and the counit
parts via counit naturality. -/
lemma pullbackValIso_comp_leg {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X) (W : X.Modules) :
    (PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
          (Hom.toRingCatSheafHom h).hom).hom.app W.val ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Z.ringCatSheaf))).unit.app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom (h ≫ f)).hom).obj W.val) ≫
          (SheafOfModules.forget Z.ringCatSheaf).map (pullbackValIso (h ≫ f) W).hom
      = (PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Y.ringCatSheaf))).unit.app
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
              (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom) ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Z.ringCatSheaf))).unit.app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).obj
                ((pullback f).obj W).val) ≫
            (SheafOfModules.forget Z.ringCatSheaf).map (pullbackValIso h ((pullback f).obj W)).hom ≫
              (SheafOfModules.forget Z.ringCatSheaf).map ((pullbackComp h f).app W).hom := by
  -- ITER-019+ (prover): full chase via the SHEAF-LEVEL cocycle `hH` (blueprint `lem:pullback_val_iso_comp`).
  -- The leading sheafification unit `η^Z_{phh(phf W.val)}` and the forgetful functor `forget Z` are
  -- factored out by unit naturality; what remains is the clean `SheafOfModules Z`-level identity `hH`,
  -- proved by Sq4a (`sheafificationCompPullback_comp`, inverted), naturality of `pullbackComp h f` at the
  -- counit `ε^X_W`, naturality of `sheafificationCompPullback h`, and the adjunction triangle
  -- `adj_unit_map_counit` (the (T) step).  See task_results for the paper proof.
  -- Abbreviations used in comments: aZ/aY = sheafification, FZ/FY = forget, phf/phh/phhf = presheaf
  -- pullbacks, ηZ/ηY = sheafification units, εX/εY = sheafification counits, Pc = PrPbComp.hom.app W.val,
  -- b = ηY.app(phf W.val) ≫ FY.map (pVI f W).hom, SCg = sheafificationCompPullback, PBg = sheaf pullback.
  -- Unit naturality of η^Z at `Pc` (LHS) and at `phh.map b` (RHS).
  have hUZ1 :
      (PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
            (Hom.toRingCatSheafHom h).hom).hom.app W.val ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Z.ringCatSheaf))).unit.app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom (h ≫ f)).hom).obj W.val)
        = (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Z.ringCatSheaf))).unit.app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).obj
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val)) ≫
            (SheafOfModules.forget Z.ringCatSheaf).map
              ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.val)).map
                ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
                  (Hom.toRingCatSheafHom h).hom).hom.app W.val)) := by
    simpa only [Functor.id_map, Functor.comp_map, restrictScalarsId_map]
      using (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Sheaf.val Z.ringCatSheaf))).unit.naturality
          ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
            (Hom.toRingCatSheafHom h).hom).hom.app W.val)
  have hUZ2 :
      (PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Y.ringCatSheaf))).unit.app
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
              (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom) ≫
          (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Z.ringCatSheaf))).unit.app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).obj
              ((pullback f).obj W).val)
        = (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Z.ringCatSheaf))).unit.app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).obj
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val)) ≫
            (SheafOfModules.forget Z.ringCatSheaf).map
              ((PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.val)).map
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
                  ((PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Y.ringCatSheaf))).unit.app
                      ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
                    (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom))) := by
    simpa only [Functor.id_map, Functor.comp_map, restrictScalarsId_map]
      using (PresheafOfModules.sheafificationAdjunction
        (𝟙 (Sheaf.val Z.ringCatSheaf))).unit.naturality
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
            ((PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Y.ringCatSheaf))).unit.app
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
              (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom))
  -- The sheaf-level cocycle (H): the genuine content, in `SheafOfModules Z`.
  have hH :
      (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.val)).map
            ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
              (Hom.toRingCatSheafHom h).hom).hom.app W.val) ≫
          (pullbackValIso (h ≫ f) W).hom
        = (PresheafOfModules.sheafification (𝟙 Z.ringCatSheaf.val)).map
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map
                ((PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Y.ringCatSheaf))).unit.app
                    ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
                  (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom)) ≫
            (pullbackValIso h ((pullback f).obj W)).hom ≫ ((pullbackComp h f).app W).hom := by
    set b := (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Y.ringCatSheaf))).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val) ≫
        (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f W).hom with hb
    -- Unfold pVI on the (h≫f)- and h-legs (the f-leg is hidden inside the opaque `b`).
    simp only [pullbackValIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    have h1 := sheafificationCompPullback_comp_inv h f W.val
    have h2 := ((Scheme.Modules.pullbackComp h f).hom.naturality
      (((asIso (PresheafOfModules.sheafificationAdjunction
        (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).counit).app W).hom)).symm
    have h3 := (SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).inv.naturality b
    -- (T): the adjunction triangle for the sheafification adjunction on `Y`.
    have h4 : (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.val)).map b ≫
          (((asIso (PresheafOfModules.sheafificationAdjunction
            (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).counit).app ((pullback f).obj W)).hom)
        = (pullbackValIso f W).hom :=
      adj_unit_map_counit
        (PresheafOfModules.sheafificationAdjunction (𝟙 (Sheaf.val Y.ringCatSheaf)))
        ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj W.val)
        ((pullback f).obj W) (pullbackValIso f W).hom
    exact cocycle_assemble (Scheme.Modules.pullback h) _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4
  -- Reduction: rewrite each side as `η^Z_{phh(phf W.val)} ≫ forget Z (·)` and close by `hH`.
  slice_lhs 1 2 => rw [hUZ1]
  slice_rhs 1 2 => rw [hUZ2]
  exact comp_forget_cocycle (SheafOfModules.forget Z.ringCatSheaf) _ _ _ _ _ _ hH

set_option maxHeartbeats 3200000 in
/-- **D3′ — composition coherence of the sheaf-level pullback–tensor comparison `pullbackTensorMap`**
(blueprint `lem:pullback_tensor_map_basechange`).

This is the *tensorator* analog of the unit composition coherence
`pullbackObjUnitToUnit_comp`: for composable scheme morphisms `h : Z ⟶ Y`, `f : Y ⟶ X` and
arbitrary `M N : X.Modules`, the comparison `δ_sheaf = pullbackTensorMap (h ≫ f)` of the composite
factors through the comparisons of `f` and `h` and the pullback pseudofunctor coherence
`pullbackComp`:
`pullbackTensorMap (h≫f) M N = (pullbackComp h f).inv ≫ (pullback h).map (pullbackTensorMap f) ≫
  pullbackTensorMap h (f^*M) (f^*N) ≫ tensorObjIsoOfIso (pullbackComp h f) (pullbackComp h f)`.

  The base-change-square form of the blueprint (`f ∘ j' = j ∘ g` with `j, j'` open immersions) is the
  specialisation `h := j'`, `f`, applied to the two factorisations `j' ≫ f = g ≫ j` of the equal
  underlying morphisms; the displayed identity of the restricted comparisons follows by equating the
  two instances of this coherence. Consumed by D4′ `pullbackTensorIsoOfLocallyTrivial`.

Mathlib-absent at the pinned commit; NOT a sectionwise statement (the left-adjoint pullback exposes
no sectionwise value). Proved by the mate calculus through the oplax comparison `δ` of a composite of
left adjoints (`Functor.OplaxMonoidal.comp_δ`) and the adjunction-mate identity
`conjugateEquiv_pullbackComp_inv` (`pullbackComp` for the left adjoints ↔ `pushforwardComp` for the
right adjoints), exactly mirroring `pullbackObjUnitToUnit_comp`. -/
lemma pullbackTensorMap_restrict {X Y Z : Scheme.{u}} (h : Z ⟶ Y) (f : Y ⟶ X)
    (M N : X.Modules) :
    pullbackTensorMap (h ≫ f) M N =
      (Scheme.Modules.pullbackComp h f).inv.app (tensorObj M N) ≫
      (Scheme.Modules.pullback h).map (pullbackTensorMap f M N) ≫
      pullbackTensorMap h ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) ≫
      (tensorObjIsoOfIso ((Scheme.Modules.pullbackComp h f).app M)
        ((Scheme.Modules.pullbackComp h f).app N)).hom := by
  -- ROADMAP (iter-256 handoff). Unfolding `pullbackTensorMap` on both sides (verified) exposes the
  -- four-fold composite `S1 ≫ a.map δ ≫ S3 ≫ S4` with
  --   S1 = (sheafificationCompPullback φ_{·}).app (M.val ⊗ₚ N.val) .hom,
  --   S2 = a_·.map (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ'_{·}) M.val N.val),
  --   S3 = (sheafifyTensorUnitIso (Fp M.val) (Fp N.val)).hom,
  --   S4 = a_·.map (forget(pullbackValIso · M).hom ⊗ₘ forget(pullbackValIso · N).hom).
  -- Unlike D1′ (naturality, a 4-square *paste*), this is a 4-square *composition*-coherence: the LHS
  -- is the composite-morphism `· = h ≫ f` instance, the RHS interleaves the `f` instance (pushed
  -- forward by `(pullback h).map`) with the `h` instance (on the pulled-back modules `(pullback f).obj`),
  -- all conjugated by the pseudofunctoriality iso `pullbackComp h f`.
  --
  -- **Why the unit-analog mirror does NOT transfer.** `pullbackObjUnitToUnit_comp` (L907) works because
  -- `pullbackObjUnitToUnit` is BY DEFINITION an adjunction transpose, so its composition coherence is
  -- obtained by transposing through `pullbackPushforwardAdjunction.homEquiv` and invoking the bridge
  -- `pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`. `pullbackTensorMap` is NOT a
  -- transpose — it is the hand-built 4-fold composite above — and there is NO analogous
  -- `…homEquiv_pullbackTensorMap` bridge. Hence the mirror's very first move
  -- (`(pullbackPushforwardAdjunction (h≫f)).homEquiv.injective`) leaves an un-evaluable transpose of a
  -- concrete composite and stalls. This is the planner's anticipated "genuinely new obstacle beyond the
  -- unit-analog pattern" — per the iter-256 reversing signal, the scaffolded statement is retained with
  -- this typed `sorry` rather than forcing a non-applicable device.
  --
  -- **The genuine route (four composition-coherence squares; each its own sub-lemma).**
  --  • Sq2 (the δ core): `δ (PresheafOfModules.pullback φ'_{h≫f})` decomposes via
  --    `CategoryTheory.Functor.OplaxMonoidal.comp_δ` once `pullback φ'_{h≫f}` is identified with
  --    `pullback φ'_f ⋙ pullback φ'_h` through the Mathlib presheaf coherence
  --    `PresheafOfModules.pullbackComp φ'_f ψ` (verified to exist; composite ring map
  --    `φ'_f ≫ F.op.whiskerLeft ψ`), which requires the ring-map reconciliation
  --    `(toRingCatSheafHom (h≫f)).hom = φ'_f ≫ (Opens.map f.base).op.whiskerLeft φ'_h` (functoriality
  --    of `toRingCatSheafHom` under `≫`).  `PresheafOfModules.{pullbackId, pullback_assoc}` are the
  --    coherence-bookkeeping lemmas.
  --  • Sq1 (sheafification ↔ pullback): the composition coherence of
  --    `SheafOfModules.sheafificationCompPullback` across `h≫f` (analog of `pullbackComp` for the
  --    `sheafification ⋙ pullback` natural iso) — Mathlib-absent, a project sub-lemma.
  --  • Sq3: `sheafifyTensorUnitIso` carried through the same `pullbackComp` identification.
  --  • Sq4 (the connecting iso): a Scheme-level `pullbackValIso` composition coherence relating
  --    `pullbackValIso (h≫f) M` to `(pullback h).map (pullbackValIso f M)`, `pullbackValIso h (f^*M)`
  --    and `(pullbackComp h f).app M` — Mathlib-absent, the second project sub-lemma; it is the
  --    bookkeeping that produces the final `tensorObjIsoOfIso (pullbackComp h f) (pullbackComp h f)`.
  -- The two project sub-lemmas (Sq1, Sq4 composition coherences) + the Sq2 ring-map reconciliation are
  -- the missing ingredients; they are the iter-257 work items (each ~40-120 LOC, mate-calculus style).
  --
  -- ITER-257 FINDINGS (prover):
  --  (1) The Sq2 RING-MAP RECONCILIATION IS DEFINITIONAL — `toRingCatSheafHom_comp_hom_reconcile`
  --      (just above) closes by `rfl`: `(toRingCatSheafHom (h≫f)).hom =
  --      (toRingCatSheafHom f).hom ≫ (Opens.map f.base).op.whiskerLeft (toRingCatSheafHom h).hom`.
  --      The blueprint's "non-trivial because the two sides live in functor categories that agree only
  --      up to Opens.map_comp" is in fact a `rfl` (the `Opens.map`/`Scheme` comp defeqs hold). This
  --      means `PresheafOfModules.pullbackComp φ'_f φ'_h` lands in `pullback φ'_{h≫f}` ON THE NOSE.
  --  (2) The genuine Sq2 content is "Sq2b": the MONOIDALITY of `pullbackComp` — that `δ` of the single
  --      `pullback φ'_{h≫f}` (leftAdjoint-oplax of the composite adjunction) transports, through
  --      `pullbackComp`, to `δ` of the composite functor `pullback φ'_f ⋙ pullback φ'_h`
  --      (`Functor.OplaxMonoidal.comp_δ`). Mathlib has NO ready lemma for the δ-transport of
  --      `Adjunction.leftAdjointCompIso` (searched: no `leftAdjointOplaxMonoidal`-of-composite lemma).
  --      It must be proved by the mate calculus (mirror `Adjunction.isMonoidal_comp`, Functor.lean:990).
  --  (3) STATEMENT-LEVEL FRICTION to budget for: (a) `Functor.OplaxMonoidal.δ (pullback φ')` needs the
  --      CommRingCat/forget₂ monoidal-instance pinning (the D1′ `show … from`/`let φ' : … ⋙ forget₂`
  --      device — bare `δ (pullback (toRingCatSheafHom f).hom)` leaves `MonoidalCategory` metavars
  --      stuck); (b) `pullbackComp φ'_f φ'_h` pins `(F := Opens.map f.base ⋙ Opens.map h.base)` with the
  --      morphism `φ'_f ≫ whiskerLeft (Opens.map f.base).op φ'_h`, and unifying the standalone δ's
  --      pullback against that codomain needs explicit `(F := …)` + the associativity defeq
  --      `(F⋙G).op⋙T = F.op⋙(G.op⋙T)` — write the LHS δ over `pullback (F := _ ⋙ _) (toRingCatSheafHom
  --      (h≫f)).hom` (typechecks) and bridge the RHS connecting object by `eqToHom` via finding (1).
  -- ITER-261 (prover): the proof is now OPENED to the paste-ready form.  `simp only` unfolds
  -- `pullbackTensorMap` on BOTH sides into the four-fold composite `S1 ≫ a.map δ ≫ S3 ≫ S4`; the RHS
  -- `(pullback h).map (S1_f ≫ … ≫ S4_f)` is distributed by `Functor.map_comp` and everything
  -- right-associated.  The goal is then the explicit 4-vs-10 factor identity
  --   S1_{hf} ≫ a_Z.map δ_{hf} ≫ S3_{hf} ≫ S4_{hf}
  --     = R0 ≫ (pullback h).map S1_f ≫ (pullback h).map (a_Y.map δ_f) ≫ (pullback h).map S3_f
  --        ≫ (pullback h).map S4_f ≫ S1_h ≫ a_Z.map δ_h ≫ S3_h ≫ S4_h ≫ a_Z.mapIso(pbComp ⊗ pbComp).hom
  -- with R0 = (pullbackComp h f).inv.app (M⊗N).  This is the four-square *composition* paste:
  --   • Sq1 (the S1 connecting iso):  `sheafificationCompPullback_comp` (stated+opened just above —
  --     the foundational Mathlib-absent coherence; LHS already reduced to the unit identity).
  --   • Sq2b (the δ core):           `pullbackComp_δ` (CLOSED, axiom-clean) under `a_Z.map`.
  --   • Sq3 (the unit iso):          `sheafifyTensorUnitIso` carried through `pullbackComp`.
  --   • Sq4 (the connecting iso):    a `pullbackValIso` composition coherence (Mathlib-absent; it
  --     factors through Sq1 since `pullbackValIso = sheafCompPb.symm ≪≫ pullback.mapIso counit`).
  -- The squares INTERLEAVE (e.g. `S1_h` here acts on `tensorObj ((pullback f).obj M) …`, NOT on
  -- `PrPb_f (M⊗N)`), so the paste slides factors past each other by `δ_natural` / NatTrans naturality
  -- exactly as the D1′ naturality paste (`pullbackTensorMap_natural`, L2007) does — merging
  -- `a.map δ ≫ S3 ≫ S4` into a single `a.map Ψ` to move S1 by its mate coherence.  The remaining work
  -- is: finish Sq1's unit reassembly, build Sq4, then run the interleaved merge.  Typed sorry retained
  -- (race-safe: file compiles; `DualInverse.lean` imports it).
  simp only [pullbackTensorMap, tensorObjIsoOfIso]
  rw [Functor.map_comp, Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc]
  -- ITER-013 (prover) — PREFIX RE-CANONICALIZED.  The iter-006 prefix spliced `h1` via
  -- `erw [reassoc_of% h1]`, which introduced a NON-`Category.toCategoryStruct` boundary `≫` separating
  -- the cancellable pair `D = aZ.map (PrPbComp.hom.app P)` (last factor of the expanded S1) from
  -- `E = aZ.map (pb.inv.app P)` (head of the `hδ` group); no canonical-assoc tactic could bring them
  -- adjacent.  We now KEEP S1 FOLDED in the goal and discharge step (i) through the clean combined
  -- brick `hcancel : S1 ≫ E = R0 ≫ R1 ≫ R5` proved in a fresh `have`-context (where `rw [h1]` +
  -- `Category.assoc` stay canonical and `sheafifyMap_pullbackComp_hom_inv_id` cancels `D ≫ E`).  No
  -- `reassoc_of%`, so no instance drift.
  have h1 := sheafificationCompPullback_comp h f (PresheafOfModules.Monoidal.tensorObj M.val N.val)
  letI instMSX : MonoidalCategoryStruct (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :=
    inferInstance
  letI instMSZ : MonoidalCategoryStruct (_root_.PresheafOfModules (Z.presheaf ⋙ forget₂ CommRingCat RingCat)) :=
    inferInstance
  -- ITER-013 (prover): `aZ`/`pb` are spelled out EXPLICITLY below (no `let`-fvar) so that `hδ`'s `E`,
  -- `h1`'s `D`, the Brick-1 lemma `sheafifyMap_pullbackComp_hom_inv_id`, and `hcancel` ALL share the
  -- identical sheafification/pullbackComp spelling — `cod D = dom E` then matches SYNTACTICALLY and a
  -- plain `rw [Category.assoc]` reassociates the `D ≫ E` cancellation (a `let`-fvar `aZ.obj …` vs
  -- explicit `(sheafification …).obj …` mismatch was what blocked the keyed `rw`/`simp` and forced the
  -- `whnf`-bombing `erw [Category.assoc]`).
  set_option maxHeartbeats 1600000 in
  let φfh := (Hom.toRingCatSheafHom (h ≫ f)).hom
  let φf := (Hom.toRingCatSheafHom f).hom
  let φh := (Hom.toRingCatSheafHom h).hom
  let pb := PresheafOfModules.pullbackComp φf φh
  let δfh := Functor.OplaxMonoidal.δ
    (F := PresheafOfModules.pullback
      (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map (h ≫ f).base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
        from (Hom.toRingCatSheafHom (h ≫ f)).hom))
    M.val N.val
  let δcomp := Functor.OplaxMonoidal.δ
    (F := PresheafOfModules.pullback
      (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
        from (Hom.toRingCatSheafHom f).hom) ⋙
      PresheafOfModules.pullback
        (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
            (TopologicalSpace.Opens.map h.base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
          from (Hom.toRingCatSheafHom h).hom))
    M.val N.val
  let tcomp :=
    MonoidalCategory.tensorHom
      (C := _root_.PresheafOfModules (Z.presheaf ⋙ forget₂ CommRingCat RingCat))
      (pb.hom.app M.val) (pb.hom.app N.val)
  have hδ :
      (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map δfh =
        (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map
            ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
              (Hom.toRingCatSheafHom h).hom).inv.app
              (PresheafOfModules.Monoidal.tensorObj M.val N.val)) ≫
        (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map δcomp ≫
        (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map tcomp := by
    -- RESOLVED (iter-006): the Sq2b content is exactly the CLOSED `pullbackComp_δ` under
    -- `congrArg aZ.map`.  The forward `rw [Functor.map_comp] at` route does NOT fire (the inner
    -- `≫` lives at the `Sheaf.val Z` spelling of the presheaf category, an instance-level
    -- mismatch); instead FOLD the goal's RHS by `← Functor.map_comp` (the explicit `aZ.map _ ≫
    -- aZ.map _` heads match syntactically) and close by defeq against the congrArg image
    -- (`show`-pinned ring maps are defeq to the bare `(Hom.toRingCatSheafHom ·).hom`, and
    -- `φfh = φf ≫ whiskerLeft φh` is `rfl` by `toRingCatSheafHom_comp_hom_reconcile`).
    have hd := pullbackComp_δ
      (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
        from (Hom.toRingCatSheafHom f).hom)
      (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
          (TopologicalSpace.Opens.map h.base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
        from (Hom.toRingCatSheafHom h).hom) M.val N.val
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map hd
  -- ── STEP (i) — the combined `S1 ≫ a.map δfh` brick (`hmain`), proved in a CLEAN context ──
  -- iter-015 root-cause: in the *main* goal `S1` came from `simp only [pullbackTensorMap]`, whose
  -- internal spelling is defeq-but-not-syntactic to `h1`'s LHS, so `rw [h1]` could not fire there and
  -- `erw [h1]` left a non-canonical `D ≫ E` boundary that `Category.assoc` could not cross.  The fix is
  -- to AVOID splicing `h1` into the unfolded main goal: state `hmain` with `S1`/`a.map δfh` written
  -- *verbatim* as `h1`/`hδ`'s LHS, so inside `hmain` plain `rw [h1, hδ]` fires (syntactic match) and the
  -- connecting `≫` stays the canonical `SheafOfModules Z` comp.  Then `simp only [Category.assoc]`
  -- flattens, `reassoc_of% sheafifyMap_pullbackComp_hom_inv_id` cancels the now-adjacent `D ≫ E`, and the
  -- WHOLE brick is spliced into the main goal by `erw [reassoc_of% hmain]` (defeq matching crosses the
  -- main goal's hidden-instance `S1` — verified to land the canonical step-(i) form in iter-015).
  have hmain :
      ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).app
          (PresheafOfModules.Monoidal.tensorObj M.val N.val)).hom ≫
        (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map δfh =
      (SheafOfModules.pullbackComp (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).inv.app
          ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.val)).obj
            (PresheafOfModules.Monoidal.tensorObj M.val N.val)) ≫
        (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
          ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app
            (PresheafOfModules.Monoidal.tensorObj M.val N.val)).hom ≫
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj
            (PresheafOfModules.Monoidal.tensorObj M.val N.val))).hom ≫
        (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map δcomp ≫
        (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map tcomp := by
    -- `rw [h1]` cannot fire: `h1` is the lemma `sheafificationCompPullback_comp` applied with `P`
    -- substituted, so its LHS instance differs (defeq, not syntactic) from the goal's `S1`.  Re-state it
    -- as `h1'` with a FRESHLY-elaborated type (accepted from `h1` up to defeq) so its LHS matches the
    -- goal's `S1` syntactically and plain `rw` fires, keeping every `≫` the canonical `SheafOfModules Z`
    -- comp.  Then `simp [Category.assoc]` flattens and `reassoc_of% (D ≫ E = 𝟙)` cancels the now-adjacent
    -- pair.
    have h1' :
        ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom (h ≫ f))).app
            (PresheafOfModules.Monoidal.tensorObj M.val N.val)).hom =
          (SheafOfModules.pullbackComp (Hom.toRingCatSheafHom f) (Hom.toRingCatSheafHom h)).inv.app
              ((PresheafOfModules.sheafification (𝟙 (Sheaf.val X.ringCatSheaf))).obj
                (PresheafOfModules.Monoidal.tensorObj M.val N.val)) ≫
            (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
              ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom f)).app
                (PresheafOfModules.Monoidal.tensorObj M.val N.val)).hom ≫
            ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj
                (PresheafOfModules.Monoidal.tensorObj M.val N.val))).hom ≫
            (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map
              ((PresheafOfModules.pullbackComp (Hom.toRingCatSheafHom f).hom
                (Hom.toRingCatSheafHom h).hom).hom.app
                (PresheafOfModules.Monoidal.tensorObj M.val N.val)) := h1
    -- Expose `S1` (via `h1'`) and `a.map δfh` (via `erw [hδ]`) as the explicit `(R0 ≫ R1 ≫ R5 ≫ D) ≫
    -- (E ≫ a.map δcomp ≫ a.map tcomp)`.  The cancelling pair `D ≫ E` is now in place but buried under a
    -- DEFEQ-but-not-syntactic `SheafOfModules` instance boundary, so no `rw/simp [Category.assoc]` can
    -- bring it adjacent.  `comp_cancel_mid` does the reassociation+cancellation generically (one
    -- instance) and is `exact`-applied: `exact` unifies up to defeq, crossing the instance gap that
    -- blocks `rw`, and `sheafifyMap_pullbackComp_hom_inv_id` supplies `D ≫ E = 𝟙`.
    rw [h1']
    erw [hδ]
    exact comp_cancel_mid _ _ _ _ _ _
      (sheafifyMap_pullbackComp_hom_inv_id h f (PresheafOfModules.Monoidal.tensorObj M.val N.val))
  -- Splice the step-(i) brick into the main goal; lands the canonical
  -- `R0 ≫ R1 ≫ R5 ≫ a.map δcomp ≫ a.map tcomp ≫ S3 ≫ S4` form.
  erw [reassoc_of% hmain]
  -- ── STEP (i) CLOSED (iter-015). ───────────────────────────────────────────────────────────────
  -- The long-standing `D ≫ E = 𝟙` cancellation wall (blocking iters 012–015) is GONE: `hmain` packages
  -- `S1 ≫ a.map δfh = R0 ≫ R1 ≫ R5 ≫ a.map δcomp ≫ a.map tcomp` and is spliced by `erw [reassoc_of%
  -- hmain]`.  The breakthrough is the instance-agnostic skeleton `comp_cancel_mid` applied by `exact`
  -- (not `rw`): the `sheafificationCompPullback`/`pullbackComp` `.app`-components compose through
  -- DEFEQ-but-not-syntactic `SheafOfModules` instances, which defeats every `rw/simp [Category.assoc]`
  -- and bombs `erw [Category.assoc]` (mate-`whnf`); `exact` unifies up to defeq and crosses it cleanly.
  --
  -- ── REMAINING: steps (ii) + (iii) — the interleaved four-square merge. ─────────────────────────
  -- The goal is now `R0 ≫ R1 ≫ R5 ≫ a.map δcomp ≫ a.map tcomp ≫ S3 ≫ S4 = RHS`, where the RHS is the
  -- distributed `(pullback h).map (S1_f ≫ a_Y.map δ_f ≫ S3_f ≫ S4_f) ≫ S1_h ≫ a.map δ_h ≫ S3_h ≫ S4_h ≫
  -- a.mapIso(pbComp ⊗ pbComp).hom` (R0 cancels on both sides).  To finish:
  --   (ii) split `a.map δcomp` via `Functor.OplaxMonoidal.comp_δ` (δcomp = `δ (pullback φf ⋙ pullback φh)
  --        M.val N.val`) into `(pullback φh).map (δ_f) ≫ δ_h`, then `Functor.map_comp` under `a.map`.
  --        Support: `pullbackComp_δ` (L2282, CLOSED) already gives the `δ`-twin; the friction is the
  --        monoidal-instance pinning (iter-257 finding (3)).
  --   (iii) the Sq3/Sq4 bricks DO NOT EXIST as Lean decls yet — they must be built first:
  --        • `sheafifyTensorUnitIso_comp` (Sq3, blueprint `lem:sheafify_tensor_unit_iso_comp`): hom-leg
  --          is one `a.map (η ⊗ η)` via `sheafifyTensorUnitIso_hom_eq'` (L1860, EXISTS), reduces to
  --          η-naturality vs `PrPbComp` recombined by `⊗` bifunctoriality.
  --        • `pullbackValIso_comp` (Sq4, blueprint `lem:pullback_val_iso_comp`): substitute
  --          `pullbackValIso = sheafCompPb.symm ≪≫ pullback.mapIso counit`; `sheafCompPb⁻¹` parts
  --          reassemble by `sheafificationCompPullback_comp` (now usable — see step (i) device), counit
  --          parts by counit naturality.
  --        Then interleave (slide `S1_h` past the `f`-block by `δ_natural` + `sheafificationCompPullback h`
  --          naturality, exactly as the D1′ paste `pullbackTensorMap_natural`).  Every splice is `erw`
  --          (the `Sheaf.val Z` carrier-spelling).  The `comp_cancel_mid`-`exact` device generalises to
  --          any further instance-boundary cancellation in this merge.
  -- STEP (ii) SPLICED (this iter): split `a_Z.map δcomp` by the `comp_δ` brick
  -- `sheafifyMap_δcomp_split` (`erw` unfolds the `δcomp` let to match the brick's unfolded LHS).
  -- Goal now reads `R0 ≫ R1 ≫ R5 ≫ a.map ((pullback φh).map δ_f) ≫ a.map δ_h ≫ a.map tcomp ≫ S3 ≫ S4
  --   = RHS`, the paste-ready form for the step-(iii) interleave.
  erw [sheafifyMap_δcomp_split h f M N]
  -- ── STEP (iii) — REMAINING: the interleaved four-square merge. ─────────────────────────────────
  -- Exact post-step-(ii) goal (extracted iter-016 via a forced type-mismatch). Writing
  --   a? = sheafification, Fp_· = PresheafOfModules.pullback φ'_·, S1_· = sheafCompPb · .app _ .hom,
  --   δ_· = Functor.OplaxMonoidal.δ (Fp_·), S3_· = sheafifyTensorUnitIso _ _ .hom,
  --   S4_· = a.map (forget (pullbackValIso · _).hom ⊗ₘ forget (pullbackValIso · _).hom):
  --
  -- LHS = R0 ≫ R1 ≫ R5 ≫ aZ.map (Fp_h.map δ_f) ≫ aZ.map δ_h' ≫ aZ.map tcomp ≫ S3_g ≫ S4_g
  --   R0 = (SheafOfModules.pullbackComp φf φh).inv.app (aX (M.val⊗N.val))
  --   R1 = (pullback h).map (S1_f at (M.val⊗N.val)),  R5 = S1_h at (Fp_f (M.val⊗N.val))
  --   δ_h' = δ_h (Fp_f M.val) (Fp_f N.val),  tcomp = (pb.hom.app M.val ⊗ₘ pb.hom.app N.val),
  --     pb = PresheafOfModules.pullbackComp φf φh
  --   S3_g = sheafifyTensorUnitIso (Fp_{h≫f} M.val) (Fp_{h≫f} N.val) .hom
  --   S4_g = aZ.map (forget(pullbackValIso (h≫f) M).hom ⊗ₘ forget(pullbackValIso (h≫f) N).hom)
  -- RHS = R0' ≫ (pullback h).map S1_f ≫ (pullback h).map (aY.map δ_f) ≫ (pullback h).map S3_f
  --        ≫ (pullback h).map S4_f ≫ S1_h'' ≫ aZ.map δ_h'' ≫ S3_h ≫ S4_h ≫ Tfinal
  --   R0' = (pullbackComp h f).inv.app (M.tensorObj N)  [Scheme.Modules spelling of R0, defeq]
  --   S3_f = sheafifyTensorUnitIso (Fp_f M.val) (Fp_f N.val) .hom  [over Y]
  --   S1_h'' = S1_h at (Monoidal.tensorObj ((pullback f).obj M).val ((pullback f).obj N).val)
  --   δ_h'' = δ_h ((pullback f).obj M).val ((pullback f).obj N).val
  --   S3_h = sheafifyTensorUnitIso (Fp_h ((pullback f).obj M).val) (Fp_h ((pullback f).obj N).val) .hom
  --   S4_h = aZ.map (forget(pullbackValIso h ((pullback f).obj M)).hom ⊗ₘ forget(pullbackValIso h …N).hom)
  --   Tfinal = (aZ.mapIso (forget.mapIso (pullbackComp h f .app M) ⊗ᵢ forget.mapIso (pullbackComp h f .app N))).hom
  --
  -- NEXT CONCRETE STEP (the first slide, mirroring the D1′ paste): R0/R1 match the RHS heads (defeq,
  -- SheafOfModules vs Scheme.Modules spelling).  The LHS middle `R5 ≫ aZ.map (Fp_h.map δ_f)` is the RHS
  -- of the `sheafCompPb h` NATURALITY square at `δ_f`:
  --   (pullback h).map (aY.map δ_f) ≫ (S1_h at (Fp_f M ⊗ Fp_f N))  =  R5 ≫ aZ.map (Fp_h.map δ_f),
  -- which slides S1_h from before δ to after it (`(sheafificationCompPullback (toRingCatSheafHom h)).hom.naturality δ_f`,
  -- `erw` to bridge the `have this:=` ascription on δ_f).  After the slide the residual is exactly
  -- Sq3 (`sheafifyTensorUnitIso_comp`) + Sq4 (`pullbackValIso_comp`) + bifunctoriality, whose arguments
  -- on the RHS use the SHEAF-pullback underlying presheaf `((pullback f).obj M).val` while the LHS uses the
  -- PRESHEAF pullback `Fp_f M.val`; the two are bridged by `pullbackValIso f` (the S4_f factor) — this is
  -- why Sq3/Sq4 are *interleaved* (not separately pluggable) and must be discharged together with the slide.
  -- RISK flag (progress-critic conv016): the `pullbackValIso`-bridged Sq3/Sq4 entanglement is a NEW class
  -- of boundary beyond the `comp_cancel_mid` device — flagged for the next pass per the escalation protocol.
  -- FIRST-SLIDE ATTEMPT (iter-016, FAILED — exact failing tactic recorded for the next pass):
  --   simp only [Category.assoc]
  --   erw [← reassoc_of% ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).hom.naturality
  --     (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback (show … from (Hom.toRingCatSheafHom f).hom))
  --       M.val N.val))]
  -- → `rewrite failed: Did not find an occurrence of the pattern` (NOT a whnf-bomb — benign mismatch).
  -- Cause: the naturality RHS pattern is `(sheafCompPb h).hom.app P ≫ (pullback φ'_h ⋙ a_Z).map δ_f`, but
  -- the goal carries `R5 = ((sheafCompPb h).app P).hom` (the `.app _ .hom` spelling, not `.hom.app _`) and
  -- `a_Z.map (Fp_h.map δ_f)` (the `Functor.comp_map`-UNFOLDED form `G.map (F.map δ_f)`, not `(F⋙G).map δ_f`).
  -- FIX for next pass: state the slide as a bespoke `have hslide : R5 ≫ a_Z.map (Fp_h.map δ_f) =
  --   (pullback h).map (a_Y.map δ_f) ≫ (sheafCompPb h .app (Fp_f M ⊗ Fp_f N)).hom` in the goal's EXACT
  --   `.app _ .hom`/unfolded spelling (proved from `.hom.naturality` + `Functor.comp_map` + the NatIso
  --   `.app.hom = .hom.app` defeq), then `erw [reassoc_of% hslide]` — mirrors how D1′
  --   `pullbackTensorMap_natural` discharges its S1 square via the `.hom.naturality_assoc` forward form.
  -- SLIDE (iter-016, bespoke `hslide` in the goal's exact spelling, proved by `.symm` of the naturality
  -- up to defeq): moves `S1_h` from before `δ_f` to after it.
  have hslide :
      ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
            ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj
              (PresheafOfModules.Monoidal.tensorObj M.val N.val))).hom ≫
          (PresheafOfModules.sheafification (𝟙 (Sheaf.val Z.ringCatSheaf))).map
            ((PresheafOfModules.pullback
                (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                    (TopologicalSpace.Opens.map h.base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
                  from (Hom.toRingCatSheafHom h).hom)).map
              (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback
                (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                    (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                  from (Hom.toRingCatSheafHom f).hom)) M.val N.val))
        = (SheafOfModules.pullback (Hom.toRingCatSheafHom h)).map
              ((PresheafOfModules.sheafification (𝟙 (Sheaf.val Y.ringCatSheaf))).map
                (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback
                  (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
                      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
                    from (Hom.toRingCatSheafHom f).hom)) M.val N.val)) ≫
            ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).app
              (PresheafOfModules.Monoidal.tensorObj
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val)
                ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val))).hom :=
    ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).hom.naturality
      (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback
        (show (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
            (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat)
          from (Hom.toRingCatSheafHom f).hom)) M.val N.val)).symm
  -- `hslide` TYPECHECKS (the `.symm`-of-naturality term has the stated goal-spelling type by defeq), so
  -- the slide equation is PROVEN.  The remaining gap is purely splicing it: `rw`/`erw [reassoc_of% hslide]`
  -- (even after `simp only [Category.assoc]`) reports `Did not find an occurrence of the pattern`, i.e. the
  -- post-`sheafifyMap_δcomp_split` goal does not present `R5 ≫ a_Z.map (Fp_h.map δ_f)` in `hslide`'s LHS
  -- spelling.  NEXT PASS: re-extract the post-split goal (forced type-mismatch) and adjust `hslide`'s LHS to
  -- the verbatim goal spelling so `erw [reassoc_of% hslide]` keys; then continue the interleave with Sq3/Sq4.
  -- ── STEP (iii)a — THE SLIDE IS SPLICED (this iter). ────────────────────────────────────────────
  -- The `S1^h` slide is now landed in the main goal via the generic nested-slide device
  -- `comp_slide_nested` applied by `refine … hslide ?_`.  The breakthrough over iters 016–017: EVERY
  -- keyed-matching tactic (`simp only [Category.assoc]`, `rw`/`erw [reassoc_of% hslide]`) whnf-BOMBS on
  -- the post-step-(ii) goal — the `erw [sheafifyMap_δcomp_split]` of step (ii) introduced a
  -- defeq-but-not-syntactic `SheafOfModules Z` instance boundary that the discrimination-tree matcher
  -- whnf-loops across.  `comp_slide_nested` sidesteps it: its conclusion mirrors the goal's *literal*
  -- nesting `(r0 ≫ r1 ≫ r5 ≫ (p ≫ q) ≫ rtc) ≫ s3 ≫ s4`, so `refine` unifies by metavariable
  -- *assignment only* (no whnf), and the slide `rw` runs on the lemma's own clean `[Category C]` vars.
  -- (NB: `hslide` MUST keep its `show … from` ring-map ascriptions — the `have this := …; this` spelling
  -- makes its `:= …naturality.symm` defeq-check whnf-bomb.)
  refine comp_slide_nested _ _ _ _ _ _ _ _ _ _ _ hslide ?_
  -- ── STEP (iii)b — REMAINING: the merged Sq3/Sq4 core (post-slide goal, extracted this iter). ────
  -- After the slide, R0, R1, U match the RHS heads (defeq):
  --   R0 = (pullbackComp φf φh).inv.app (aX (M⊗N))                = R0' (Scheme.Modules spelling)
  --   R1 = (pullback h).map (S1_f at M⊗N)                          = (pullback h).map S1_f
  --   U  = (pullback h).map (a_Y.map δ_f)                          = (pullback h).map (a_Y.map δ_f)
  -- so the residual core (after cancelling R0 ≫ R1 ≫ U on both sides) is:
  --   V ≫ a_Z.map δ_h' ≫ a_Z.map tcomp ≫ S3_g ≫ S4_g
  --     = (pullback h).map S3_f ≫ (pullback h).map S4_f ≫ S1_h'' ≫ a_Z.map δ_h'' ≫ S3_h ≫ S4_h ≫ Tfinal
  -- where (KEY MISMATCH, the `pullbackValIso` bridge — blueprint "merged Sq3/Sq4 chase"):
  --   • V       = S1_h on the *presheaf*-pullback tensor args  (sheafCompPb h).app (Fp_f M ⊗ Fp_f N) .hom
  --   • S1_h''  = S1_h on the *sheaf*-pullback   tensor args  (sheafCompPb h).app (((pb f).obj M).val ⊗ …) .hom
  --     V ≠ S1_h'' — bridged by `pullbackValIso f` (the (pullback h).map S4_f / S4 factors).
  --   • a_Z.map δ_h'  has presheaf args (Fp_f M.val)(Fp_f N.val); a_Z.map δ_h'' has sheaf args
  --     (((pb f).obj M).val)(((pb f).obj N).val) — same `pullbackValIso f` bridge.
  --   • S3_g = sheafifyTensorUnitIso (Fp_{h≫f} M)(Fp_{h≫f} N).hom; S4_g = a_Z.map (forget(pVI (h≫f) M) ⊗ₘ …);
  --     Tfinal = (a_Z.mapIso (forget.mapIso(pbComp.app M) ⊗ᵢ forget.mapIso(pbComp.app N))).hom.
  -- This is the genuine D1′-style naturality paste of `pullbackTensorMap_natural` (L2007), now for the
  -- *composition* coherence: slide V (=S1_h, presheaf-args) rightward past `(pullback h).map S3_f ≫
  -- (pullback h).map S4_f` by the naturality of `sheafificationCompPullback h` (converting presheaf→sheaf
  -- args, i.e. realigning V to S1_h''), then fold `a.map δ ≫ S3 ≫ S4` into a single `a.map Ψ` on each side
  -- and reduce to a presheaf identity closed by `presheaf_pullback_oplaxmonoidal` (δ-naturality) +
  -- `sheafifyTensorUnitIso_hom_eq'` (L1860) + the `pullbackValIso` factorisation (`def:pullback_val_iso`).
  -- DEVICE THAT CROSSES THE BOUNDARY: continue with generic single-`[Category C]` lemmas whose conclusions
  -- mirror the goal nesting, applied by `refine`/`exact` (assignment-only unification) — NOT `simp`/`rw`/
  -- `erw`, which all whnf-bomb here.  The slide above is the worked template.
  -- STEP (iii)b.1 — cancel the R0 ≫ R1 ≫ U prefix (defeq to R0' ≫ m1 ≫ m2) via the generic
  -- L/R-cancellation device; the three `rfl`s discharge the SheafOfModules-vs-Scheme.Modules leaf defeqs.
  refine comp_cancel_three_lr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl rfl rfl ?_
  -- THE PURE MERGED Sq3/Sq4 CORE (post-prefix-cancellation):
  --   V ≫ a_Z.map δ_h' ≫ a_Z.map tcomp ≫ S3_g ≫ S4_g
  --     = (pullback h).map S3_f ≫ (pullback h).map S4_f ≫ S1_h'' ≫ a_Z.map δ_h'' ≫ S3_h ≫ S4_h ≫ Tfinal
  -- (notation as in the STEP (iii)b block above).  This is the D1′-style naturality paste of
  -- `pullbackTensorMap_natural`, now for the composition coherence and `pullbackValIso`-bridged.  Next:
  -- slide V (=S1_h on presheaf args) rightward past `(pullback h).map (S3_f ≫ S4_f)` by the naturality
  -- of `sheafificationCompPullback h`, realigning it to S1_h'' (sheaf args); then fold each side's
  -- `a.map δ ≫ S3 ≫ S4` tail into a single `a.map Ψ` and reduce to a presheaf identity closed by
  -- `presheaf_pullback_oplaxmonoidal` + `sheafifyTensorUnitIso_hom_eq'` + the `pullbackValIso` factn.
  -- ── STEP (iii)b.2 — THE SLIDE OF V (S1_h presheaf-args → S1_h'' sheaf-args). ──────────────────
  -- The RHS prefix `m3 ≫ m4 ≫ vv = (pullback h).map S3_f ≫ (pullback h).map S4_f ≫ S1_h''` is, by the
  -- naturality of the connecting iso `sheafificationCompPullback h` at the presheaf morphism `gg`
  -- (`a_Y.map gg = S3_f ≫ S4_f`), equal to `v ≫ a_Z.map (Fp_h.map gg)` with `v = S1_h` on the PRESHEAF
  -- args.  Splicing this (`hcomb`) via the generic `comp_slide_three` leaves the folded presheaf core
  -- `hcore2 : a.map δ_h' ≫ a.map tcomp ≫ S3_g ≫ S4_g = a_Z.map (Fp_h.map gg) ≫ a.map δ_h'' ≫ S3_h ≫ S4_h
  --   ≫ Tfinal`, all `a_Z.map`-foldable.  `gg = (η ⊗ η) ≫ (forget pVI_M ⊗ forget pVI_N)` over Y.
  set gg :
      PresheafOfModules.Monoidal.tensorObj
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val)
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val) ⟶
        PresheafOfModules.Monoidal.tensorObj ((pullback f).obj M).val ((pullback f).obj N).val :=
    MonoidalCategory.tensorHom
        (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
        ((PresheafOfModules.sheafificationAdjunction
          (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val))
        ((PresheafOfModules.sheafificationAdjunction
          (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val)) ≫
      MonoidalCategory.tensorHom
        (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
        ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
        ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom)
    with hgg
  -- `a_Y.map gg = S3_f ≫ S4_f` (first factor by `sheafifyTensorUnitIso_hom_eq'`, second is `S4_f`).
  have hg :
      (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map gg
        = (sheafifyTensorUnitIso
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val)
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val)).hom ≫
          (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
            (MonoidalCategory.tensorHom
              (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
              ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
              ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom)) := by
    -- Split `a_Y.map (A ≫ B)` as a defeq `exact` (the `≫` in `gg` lives in the `forget₂`-carrier
    -- monoidal instance, defeq-but-not-syntactic to `a_Y`'s domain — bridged by `exact`, not `rw`).
    have hsplit :
        (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map gg
          = (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
              (MonoidalCategory.tensorHom
                (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
                ((PresheafOfModules.sheafificationAdjunction
                  (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).unit.app
                  ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val))
                ((PresheafOfModules.sheafificationAdjunction
                  (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).unit.app
                  ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val))) ≫
            (PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map
              (MonoidalCategory.tensorHom
                (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
                ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
                ((SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom)) := by
      rw [hgg]
      exact (PresheafOfModules.sheafification
        (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map_comp _ _
    rw [hsplit]
    congr 1
    exact (sheafifyTensorUnitIso_hom_eq' _ _).symm
  -- Splice the slide: `m3 ≫ m4 ≫ vv = v ≫ a_Z.map (Fp_h.map gg)` from `hg` + naturality of
  -- `sheafificationCompPullback h` at `gg`.
  refine comp_slide_three _ _ _ _ _ _ _ _ _ _ _ _
    ((PresheafOfModules.sheafification (R := Z.ringCatSheaf) (𝟙 Z.ringCatSheaf.val)).map
      ((PresheafOfModules.pullback (Hom.toRingCatSheafHom h).hom).map gg)) ?_ ?_
  · -- hcomb : m3 ≫ m4 ≫ vv = v ≫ a_Z.map (Fp_h.map gg).  The merge/reassoc runs inside the abstract
    -- `map_comp_slide` (clean vars), then naturality of `sheafificationCompPullback h` at `gg` closes it.
    exact map_comp_slide (Scheme.Modules.pullback h) _ _
      ((PresheafOfModules.sheafification (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).map gg)
      _ _ hg
      ((SheafOfModules.sheafificationCompPullback (Hom.toRingCatSheafHom h)).hom.naturality gg)
  · -- ── STEP (iii)b.3 — THE FOLDED Sq3/Sq4 PRESHEAF CORE (the sole remaining residual). ──────────
    -- Verbatim goal (extracted iter-018 via forced type-mismatch); a_Z = sheafification over Z,
    -- Fp_· = PresheafOfModules.pullback φ'_·, δ_· = Functor.OplaxMonoidal.δ (Fp_·):
    --   a_Z.map (δ_h (Fp_f M.val) (Fp_f N.val))                       -- δ_h'  (presheaf-f args)
    --     ≫ a_Z.map tcomp                                              -- tcomp = pb.hom.app M.val ⊗ₘ pb.hom.app N.val
    --     ≫ (sheafifyTensorUnitIso (Fp_{h≫f} M.val) (Fp_{h≫f} N.val)).hom        -- S3_g
    --     ≫ a_Z.map (forget (pVI (h≫f) M).hom ⊗ₘ forget (pVI (h≫f) N).hom)        -- S4_g
    --   = a_Z.map (Fp_h.map gg)                                        -- vtail (the slid factor)
    --     ≫ a_Z.map (δ_h ((pb f).obj M).val ((pb f).obj N).val)        -- δ_h'' (sheaf-f args)
    --     ≫ (sheafifyTensorUnitIso (Fp_h ((pb f).obj M).val) (Fp_h ((pb f).obj N).val)).hom    -- S3_h
    --     ≫ a_Z.map (forget (pVI h ((pb f).obj M)).hom ⊗ₘ forget (pVI h ((pb f).obj N)).hom)   -- S4_h
    --     ≫ (a_Z.mapIso (forget.mapIso (pbComp h f .app M) ⊗ᵢ forget.mapIso (pbComp h f .app N))).hom  -- Tfinal
    -- RECIPE (D1′-mirror, `pullback_tensor_map_natural` L1984): fold each side into one `a_Z.map Ψ`
    -- (`sheafifyTensorUnitIso_hom_eq'` turns S3_g,S3_h into `a_Z.map (η⊗η)`; `Tfinal =
    -- a_Z.map (tensorHom (forget pbComp.app M)(forget pbComp.app N))`; the δ's,tcomp,S4's,vtail are
    -- already `a_Z.map`), MERGE via `← Functor.map_comp` (as a defeq `exact`/generic lemma — NOT `rw`,
    -- which whnf-bombs the instance boundary, cf. `map_comp_slide`), `congr 1` to the PRESHEAF identity
    -- `Ψ_L = Ψ_R` over Z, and close it by δ-naturality (`presheaf_pullback_oplaxmonoidal` / `δ_natural`
    -- of `δ_h` at `gg`) + `MonoidalCategory.tensorHom_comp_tensorHom` bifunctoriality + the
    -- `pullbackValIso` factorisation (`def:pullback_val_iso`: `pVI = sheafCompPb.symm ≪≫ pullback.mapIso
    -- counit`) reconciling `pVI (h≫f)`, `pVI h`, `pVI f`, and `pbComp h f`.
    rw [sheafifyTensorUnitIso_hom_eq', sheafifyTensorUnitIso_hom_eq']
    simp only [Functor.mapIso_hom, MonoidalCategory.tensorIso_hom]
    refine map_comp4_eq_comp5 _ _ _ _ _ _ _ _ _ _ ?_
    -- Now the pure PRESHEAF identity `Ψ_L = Ψ_R` over `Z`. Expose `gg = u ⊗ v` (`u`, `v` the per-leg
    -- composites `η ≫ forget pVI_f`) and apply δ-naturality of `δ_h = δ (pullback φh)` at `gg`,
    -- aligning both heads to `δ_h (Fp_f M.val) (Fp_f N.val)`.
    have hgg2 : gg =
        MonoidalCategory.tensorHom
          (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
          ((PresheafOfModules.sheafificationAdjunction
              (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).unit.app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val) ≫
            (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
          ((PresheafOfModules.sheafificationAdjunction
              (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).unit.app
              ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val) ≫
            (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom) := by
      rw [hgg]
      exact MonoidalCategory.tensorHom_comp_tensorHom
        (C := _root_.PresheafOfModules (Y.presheaf ⋙ forget₂ CommRingCat RingCat)) _ _ _ _
    rw [hgg2]
    -- δ-naturality of `δ_h` at the legs `u`, `v` as a CONCRETE fully-applied equation (the
    -- `OplaxMonoidal` instance on `pullback φh` is resolved ONCE here via the `show … from` pin), so the
    -- subsequent `rw` matches syntactically and never re-synthesises the instance under the matcher
    -- (which whnf-bombs `erw [reassoc_of% δ_natural]`).
    have hδnat := Functor.OplaxMonoidal.δ_natural
      (F := PresheafOfModules.pullback
        (show (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
            (TopologicalSpace.Opens.map h.base).op ⋙ (Z.presheaf ⋙ forget₂ CommRingCat RingCat)
          from (Hom.toRingCatSheafHom h).hom))
      ((PresheafOfModules.sheafificationAdjunction
          (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj M.val) ≫
        (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f M).hom)
      ((PresheafOfModules.sheafificationAdjunction
          (R := Y.ringCatSheaf) (𝟙 Y.ringCatSheaf.val)).unit.app
          ((PresheafOfModules.pullback (Hom.toRingCatSheafHom f).hom).obj N.val) ≫
        (SheafOfModules.forget Y.ringCatSheaf).map (pullbackValIso f N).hom)
    erw [← reassoc_of% hδnat]
    -- Both sides now share the head `δ_h (Fp_f M.val) (Fp_f N.val)`; cancel it and expose `tcomp` as a
    -- `tensorHom`.  Every remaining factor is a `tensorHom`, so bifunctoriality collapses each side to a
    -- single `tensorHom` of per-leg composites; `congr 1` then splits into the two per-leg identities.
    rw [show tcomp = MonoidalCategory.tensorHom
      (C := _root_.PresheafOfModules (Z.presheaf ⋙ forget₂ CommRingCat RingCat))
      (pb.hom.app M.val) (pb.hom.app N.val) from rfl]
    congr 1
    refine tensorHom_collapse_3_4
      (C := _root_.PresheafOfModules (Z.presheaf ⋙ forget₂ CommRingCat RingCat))
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · -- per-leg M (the `pullbackValIso` composition coherence, Sq4): the canonical "unit into the
      -- pullback's underlying presheaf" composes pseudofunctorially across `h ≫ f`.
      exact pullbackValIso_comp_leg h f M
    · exact pullbackValIso_comp_leg h f N

/- Planner strategy (iter-020): D4′ — Pullback commutes with ⊗ on locally-trivial pairs.
   Blueprint: `lem:pullback_tensor_iso_loctriv` (Picard_TensorObjSubstrate.tex, ~L3659).
   \uses{def:IsLocallyTrivial, lem:pullback_tensor_map, lem:pullback_tensor_map_natural,
         lem:pullback_tensor_iso_unit, lem:pullback_tensor_map_basechange,
         lem:isiso_of_isiso_restrict, lem:tensorobj_preserves_locally_trivial,
         lem:IsLocallyTrivial_pullback}

   OVERALL STRATEGY: promote `pullbackTensorMap f M N` to an isomorphism via
   `isIso_of_isIso_restrict` (this file, L590), then return `asIso (pullbackTensorMap f M N)`.
   The sorry is exactly `haveI : IsIso (pullbackTensorMap f M N) := sorry`.

   STEP-BY-STEP RECIPE (chart-chase over Y; sources: Stacks `lemma-tensor-product-pullback`
   + `lemma-pullback-locally-free`):

   The morphism `pullbackTensorMap f M N` lives in **`Y.Modules`**, so the cover is over Y
   (preimages `f⁻¹Uᵢ` of a trivialising cover of X).

   STEP 1 — Apply `isIso_of_isIso_restrict (φ := pullbackTensorMap f M N)` (L590):
     Supply a cover `U : Y → Y.Opens` and `hxU : ∀ y, y ∈ U y`.  The per-point obligation is
       `IsIso ((Scheme.Modules.restrictFunctor (U y).ι).map (pullbackTensorMap f M N))`.

   STEP 2 — Pick a common trivialising chart over X for each y : Y:
     Set `x := f.base y`.  Apply `hM x` and `hN x` to get opens `U₀ ∋ x` and `U₀' ∋ x`
     trivialising M resp. N.  Refine to a COMMON affine open `V ∋ x` with `V ≤ U₀ ⊓ U₀'`
     exactly as `tensorObj_isLocallyTrivial` (L559) does:
       obtain ⟨U₀, hxU₀, _, ⟨eM⟩⟩ := hM x
       obtain ⟨U₀', hxU₀', _, ⟨eN⟩⟩ := hN x
       obtain ⟨W, hW_aff, hxW, hWsub⟩ :=
         exists_isAffineOpen_mem_and_subset (x := x) (U := U₀ ⊓ U₀') ⟨hxU₀, hxU₀'⟩
     So M.restrict W.ι ≅ 𝒪_W (via `restrictIsoUnitOfLE hWU eM`) and similarly for N.
     Set `U y := (Opens.map f.base).obj W` (the preimage open); `y ∈ U y` because `f.base y ∈ W`.
     Let `j'_W : (U y).toScheme ⟶ Y` and `j_W : W.toScheme ⟶ X` be the open immersions,
     and `g_W : (U y).toScheme ⟶ W.toScheme` the induced map with `j'_W ≫ f = g_W ≫ j_W`.

   STEP 3 — Restrict via `pullbackTensorMap_restrict` (D3′, L3465, CLOSED):
     `pullbackTensorMap_restrict j'_W f M N` states (for composite `j'_W ≫ f`):
       pullbackTensorMap (j'_W ≫ f) M N
         = (pullbackComp j'_W f).inv.app (tensorObj M N)
           ≫ (pullback j'_W).map (pullbackTensorMap f M N)
           ≫ pullbackTensorMap j'_W ((pullback f).obj M) ((pullback f).obj N)
           ≫ (tensorObjIsoOfIso (pullbackComp j'_W f .app M) (pullbackComp j'_W f .app N)).hom
     The commutation `j'_W ≫ f = g_W ≫ j_W` then relates this to `pullbackTensorMap g_W (j_W^*M) (j_W^*N)`
     via the second factorisation, reducing the per-chart obligation to
       `IsIso (pullbackTensorMap g_W (j_W^*M) (j_W^*N))`.

     CAUTION FOR THE PROVER: The restriction-functor map `(restrictFunctor j'_W.ι).map φ` equals
     `pullbackTensorMap (j'_W ≫ f) M N` only up to a `pullbackComp`/`pseudofunctoriality` rewrite.
     A small private helper or a `show … from` cast (the D1′ device) may be needed to establish
     this boundary identity without heartbeat-bombing.  Similarly, equating the two factorisations
     of `j'_W ≫ f = g_W ≫ j_W` needs the `pullbackComp` naturality square.

   STEP 4 — Transport `IsIso` via `pullbackTensorMap_natural` (D1′, L2000, CLOSED):
     The trivialization isos `eM' : j_W^*M ≅ 𝒪` and `eN' : j_W^*N ≅ 𝒪` (obtained from
     `restrictIsoUnitOfLE` applied to the W-chart data) together with `pullbackTensorMap_natural`
     yield a conjugation square:
       pullbackTensorMap g_W (j_W^*M) (j_W^*N)
         = (g_W^*eM' ⊗ g_W^*eN')⁻¹ ≫ pullbackTensorMap g_W 𝒪 𝒪 ≫ (g_W^*eM' ⊗ g_W^*eN')
     Since `(pullback g_W).map eM'.hom` and `(pullback g_W).map eN'.hom` are isos (functors
     preserve isos), conjugation preserves and reflects `IsIso` via
     `isIso_of_isIso_comp_left` + `isIso_of_isIso_comp_right` (Mathlib).  So it suffices to show
       `IsIso (pullbackTensorMap g_W 𝒪 𝒪)`.

   STEP 5 — Close by `pullbackTensorMap_unit_isIso` (D2′, L1844, CLOSED axiom-clean):
     `pullbackTensorMap_unit_isIso g_W : IsIso (pullbackTensorMap g_W 𝒪 𝒪)`.
     This closes the per-chart obligation.

   SORRY STRUCTURE CHOSEN:
     `haveI : IsIso (pullbackTensorMap f M N) := sorry`
     `exact asIso (pullbackTensorMap f M N)`
   The sorry is exactly the `IsIso` instance; the iso follows by `asIso`.
   Downstream consumers receive `pullbackTensorMap f M N` as the underlying hom (as expected).

   GLUE NOTES FOR THE PROVER (flag; do NOT solve in this stub):
   (a) RESTRICTION-FUNCTOR BOUNDARY: establishing
         `(restrictFunctor j'_W.ι).map (pullbackTensorMap f M N)
           = ... ≫ pullbackTensorMap g_W (j_W^*M) (j_W^*N) ≫ ...`
       requires the identity between `(pullback (j'_W ≫ f)).obj` and the composite.
       The `pullbackTensorMap_restrict j'_W f M N` equation plus the factorisation
       `j'_W ≫ f = g_W ≫ j_W` bridge this; a small `conv` or `show` rewrite is expected.
   (b) ISISO TRANSPORT ACROSS NATURALITY: The `pullbackTensorMap_natural g_W eM'.hom eN'.hom`
       equation has four factors; use `isIso_of_isIso_comp_left`/`isIso_of_isIso_comp_right`
       applied twice (or `IsIso.of_isIso_comp_…` lemmas) to strip the iso conjugation.
   (c) Note `pullbackTensorMap_restrict` is stated with EXPLICIT `(M N : X.Modules)` binders
       (not implicit), and `pullbackTensorMap_natural` with implicit `{M M' N N' : X.Modules}`.
       Match argument style accordingly.
-/
/-- **Generic middle-factor isolation for a 4-fold composite.** If `a ≫ b ≫ c ≫ d` is an iso
and the three flanking factors `a, c, d` are isos, then the middle factor `b` is an iso.
Pure category theory; used to extract the wanted comparison factor from the
`pullbackTensorMap_restrict` (D3′) base-change identity. -/
private lemma isIso_of_isIso_comp4_mid {C : Type*} [Category C] {W₀ X₀ Y₀ Z₀ T₀ : C}
    {a : W₀ ⟶ X₀} {b : X₀ ⟶ Y₀} {c : Y₀ ⟶ Z₀} {d : Z₀ ⟶ T₀}
    (h : IsIso (a ≫ b ≫ c ≫ d)) (ha : IsIso a) (hc : IsIso c) (hd : IsIso d) : IsIso b := by
  haveI := h; haveI := ha; haveI := hc; haveI := hd
  haveI : IsIso (b ≫ c ≫ d) := IsIso.of_isIso_comp_left a (b ≫ c ≫ d)
  exact IsIso.of_isIso_comp_right b (c ≫ d)

/-- **Helper (trivial-base reduction): `pullbackTensorMap` is an iso when both base modules
are trivial.** For `f : Y ⟶ X` and `P Q : X.Modules` each isomorphic to the unit `𝒪_X`, the
comparison `pullbackTensorMap f P Q` is an isomorphism. Proof: conjugate the unit-pair iso
`pullbackTensorMap_unit_isIso` by the trivialisations `eP, eQ` through the naturality square
`pullbackTensorMap_natural`. Both flanking factors of that square are isos (functor-images and
`tensorObjIsoOfIso` of isos), so the unit-pair iso transports to `pullbackTensorMap f P Q`. -/
private lemma pullbackTensorMap_isIso_of_base_unit {X Y : Scheme.{u}} (f : Y ⟶ X)
    {P Q : X.Modules} (eP : P ≅ SheafOfModules.unit X.ringCatSheaf)
    (eQ : Q ≅ SheafOfModules.unit X.ringCatSheaf) :
    IsIso (pullbackTensorMap f P Q) := by
  have hnat := pullbackTensorMap_natural f eP.hom eQ.hom
  -- the `tensorObj_functoriality` of two isos is the `.hom` of `tensorObjIsoOfIso`, hence iso.
  haveI : IsIso (tensorObj_functoriality eP.hom eQ.hom) :=
    (tensorObjIsoOfIso eP eQ).isIso_hom
  haveI : IsIso (pullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf)) := pullbackTensorMap_unit_isIso f
  haveI : IsIso ((Scheme.Modules.pullback f).map (tensorObj_functoriality eP.hom eQ.hom)) :=
    Functor.map_isIso _ _
  haveI hG : IsIso (tensorObj_functoriality ((Scheme.Modules.pullback f).map eP.hom)
      ((Scheme.Modules.pullback f).map eQ.hom)) :=
    (tensorObjIsoOfIso ((Scheme.Modules.pullback f).mapIso eP)
      ((Scheme.Modules.pullback f).mapIso eQ)).isIso_hom
  haveI hL : IsIso ((Scheme.Modules.pullback f).map (tensorObj_functoriality eP.hom eQ.hom) ≫
      pullbackTensorMap f (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.unit X.ringCatSheaf)) := inferInstance
  rw [hnat] at hL
  exact IsIso.of_isIso_comp_right (pullbackTensorMap f P Q)
    (tensorObj_functoriality ((Scheme.Modules.pullback f).map eP.hom)
      ((Scheme.Modules.pullback f).map eQ.hom))

/-- **K1: `pullbackTensorMap` is an isomorphism for an open immersion.**
For an open immersion `f : Y ⟶ X` (e.g. an `Opens.ι`) and arbitrary `M N : X.Modules`,
the comparison `pullbackTensorMap f M N` is an isomorphism. Geometric content: pullback
along an open immersion is restriction, which is *strong* monoidal (it is sectionwise the
structure-ring iso `f.appIso`, cf. `tensorObj_restrict_iso`), so the oplax comparison `δ`
is invertible. We reduce to the sheafified presheaf `δ` via
`isIso_pullbackTensorMap_of_isIso_sheafifyDelta`. -/
private lemma pullbackTensorMap_isIso_of_isOpenImmersion {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsOpenImmersion f] (M N : X.Modules) :
    IsIso (pullbackTensorMap f M N) := by
  apply isIso_pullbackTensorMap_of_isIso_sheafifyDelta
  -- RESIDUAL (the sole open brick of D4′).  Goal: `IsIso (a_Y.map δ)` where `δ` is the
  -- presheaf-level oplax comparison of `PresheafOfModules.pullback φ'`
  -- (φ' = `(Hom.toRingCatSheafHom f).hom`).
  -- STEP A (sheafification preserves isos).  It suffices to show the PRESHEAF-level
  -- `IsIso (δ (pullback φ') M.val N.val)`; then `a_Y.map` of an iso is an iso
  -- (`Functor.map_isIso`).
  letI φ' : (X.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
      (TopologicalSpace.Opens.map f.base).op ⋙ (Y.presheaf ⋙ forget₂ CommRingCat RingCat) :=
      (f.toRingCatSheafHom).hom
  haveI hRA : (PresheafOfModules.pushforward φ').IsRightAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction φ').isRightAdjoint
  haveI hδ : IsIso (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val) := by
    -- STEP B (strong-monoidal witness, mirroring `tensorObj_restrict_iso`).
    -- The open-immersion structure ring ISO `β` (sectionwise `f.appIso⁻¹`) presents
    -- `pushforward β` as a STRONG monoidal functor, and `H1 : pushforward β ≅ pullback φ'`.
    let α : Y.presheaf ⟶ f.opensFunctor.op ⋙ X.presheaf :=
      { app := fun U => (f.appIso U.unop).inv }
    let β : Y.ringCatSheaf.obj ⟶ f.opensFunctor.op ⋙ X.ringCatSheaf.obj :=
      Functor.whiskerRight α (forget₂ CommRingCat RingCat)
    have hadj : PresheafOfModules.pushforward β ⊣ PresheafOfModules.pushforward φ' :=
      PresheafOfModules.pushforwardPushforwardAdj f.isOpenEmbedding.isOpenMap.adjunction β φ'
        (by ext U x; exact congr($((f.app_appIso_inv _).symm).hom x))
        (by ext U x; exact congr($(f.appIso_inv_app_presheafMap U.unop) x))
    -- H1 : pushforward β ≅ pullback φ'  (both are left adjoints of `pushforward φ'`).
    let H1 := hadj.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction φ')
    -- pushforward β strong monoidal (object-level μIso), as in `tensorObj_restrict_iso` H2.
    have hβ : ∀ U, Function.Bijective (β.app U).hom := by
      intro U
      haveI : IsIso (β.app U) :=
        inferInstanceAs (IsIso ((forget₂ CommRingCat RingCat).map (f.appIso U.unop).inv))
      exact ConcreteCategory.bijective_of_isIso (β.app U)
    let β' : (Y.presheaf ⋙ forget₂ CommRingCat RingCat) ⟶
        (f.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat := β
    haveI hMonβ : (PresheafOfModules.restrictScalars β').Monoidal :=
      PresheafOfModules.restrictScalarsMonoidalOfBijective β' hβ
    -- the strong-monoidal tensorator μIso of `pushforward β` (over the syntactic forget₂ base).
    let μIsoβ := Functor.Monoidal.μIso
      (PresheafOfModules.pushforward₀OfCommRingCat f.opensFunctor X.presheaf
        ⋙ PresheafOfModules.restrictScalars β')
      (M.val : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
      (N.val : _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    -- The candidate iso `e`, of the SAME type as `δ (pullback φ') M.val N.val`:
    --   (pullback φ').obj (M.val ⊗ N.val)
    --     ≅[H1.symm]  (pushforward β).obj (M.val ⊗ N.val)
    --     ≅[μIsoβ.symm]  (pushforward β).obj M.val ⊗ (pushforward β).obj N.val
    --     ≅[H1 ⊗ H1]  (pullback φ').obj M.val ⊗ (pullback φ').obj N.val.
    let e : (PresheafOfModules.pullback φ').obj
            (PresheafOfModules.Monoidal.tensorObj M.val N.val) ≅
          MonoidalCategory.tensorObj
            ((PresheafOfModules.pullback φ').obj M.val)
            ((PresheafOfModules.pullback φ').obj N.val) :=
      (H1.app (PresheafOfModules.Monoidal.tensorObj M.val N.val)).symm ≪≫ μIsoβ.symm ≪≫
        MonoidalCategory.tensorIso (H1.app M.val) (H1.app N.val)
    -- COMPATIBILITY (the sole residual K1 content): the adjunction-mate oplax comparison `δ`
    -- agrees with the strong-monoidal witness `e.hom`.  This is the monoidal-naturality of the
    -- `leftAdjointUniq` iso H1 (its `Adjunction.IsMonoidal` compatibility), the δ-side analogue
    -- of the unit-side `presheafUnit_comp_map_eta`.
    have hcompat :
        Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val = e.hom := by
      -- Transpose across `adj := pullbackPushforwardAdjunction φ'` (`homEquiv` is injective).
      -- `δ` is the adjunction-mate of `μ (pushforward φ')` (`leftAdjointOplaxMonoidal_δ`), so after
      -- `Equiv.symm_apply_eq` + `homEquiv_unit` the sheafification-free residual (**) is:
      --   `(adj.unit M ⊗ₘ adj.unit N) ≫ μ(pushforward φ') (FM) (FN)
      --      = adj.unit (M ⊗ N) ≫ (pushforward φ').map e.hom`.
      rw [Adjunction.leftAdjointOplaxMonoidal_δ, Equiv.symm_apply_eq, Adjunction.homEquiv_unit]
      -- RESIDUAL K1 CONTENT (**) — the strong-monoidal mate compatibility of `H1`.
      -- Substituting `adj.unit = hadj.unit ≫ (pushforward φ').map H1.hom`
      -- (`Adjunction.unit_leftAdjointUniq_hom_app`) and using `μ`-naturality reduces (**) to the
      -- statement that the strong-monoidal tensorator `μIsoβ.inv` of `pushforward β` is the
      -- `hadj`-mate of `μ (pushforward φ')` — i.e. the project lax structure
      -- `presheafPushforwardLaxMonoidal` on `pushforward φ'` agrees, through `hadj`, with the
      -- strong-monoidal structure `restrictScalarsMonoidalOfBijective` on `pushforward β`.
      -- This is the δ-side analogue of the unit-side `presheafUnit_comp_map_eta` (D2′) and the
      -- open-immersion analogue of the D3′ base-change mate calculus.  It is the SOLE residual
      -- content of K1; closing it is a `mathlib-build`-scale reconciliation of the two monoidal
      -- structures on `pushforward φ'` (the explicit composite one and the hadj-mate one).
      sorry
    rw [hcompat]
    exact e.isIso_hom
  exact Functor.map_isIso _ (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val)

/-- **Per-chart isomorphism (D4′ chart-chase core).** For `f : Y ⟶ X`, modules `M N : X.Modules`
trivialised on the open `W ⊆ X` (via `eM, eN`), the restriction of `pullbackTensorMap f M N`
to the preimage chart `f ⁻¹ᵁ W` is an isomorphism.  This is the body of the cover argument of
`pullbackTensorIsoOfLocallyTrivial`.  Route: transport `restrictFunctor (f⁻¹W).ι` to
`pullback (f⁻¹W).ι` (`restrictFunctorIsoPullback`); apply the base-change identity
`pullbackTensorMap_restrict` (D3′) for the open immersion `(f⁻¹W).ι` to isolate the wanted factor
`(pullback (f⁻¹W).ι).map (pullbackTensorMap f M N)` from `pullbackTensorMap ((f⁻¹W).ι ≫ f) M N`,
where the two flanking factors are isos (K1 on `(f⁻¹W).ι`).  The composite map is shown iso via
the *second* factorisation `(f⁻¹W).ι ≫ f = g ≫ W.ι` (`g = f.resLE`), where again D3′ splits it into
K1 (on `W.ι`) and the trivial-base case (K2, since `W.ι^*M ≅ 𝒪_W`). -/
private lemma chart_isIso {X Y : Scheme.{u}} (f : Y ⟶ X) (M N : X.Modules) (W : X.Opens)
    (eM : M.restrict W.ι ≅ SheafOfModules.unit (W : Scheme).ringCatSheaf)
    (eN : N.restrict W.ι ≅ SheafOfModules.unit (W : Scheme).ringCatSheaf) :
    IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ W).ι).map (pullbackTensorMap f M N)) := by
  -- Notation: `j' = (f⁻¹W).ι : f⁻¹W ⟶ Y`, `g = f.resLE W (f⁻¹W) : f⁻¹W ⟶ W`,
  -- with `g ≫ W.ι = j' ≫ f`.
  set V : Y.Opens := f ⁻¹ᵁ W with hV
  set j' : (V : Scheme) ⟶ Y := V.ι with hj'
  set g : (V : Scheme) ⟶ (W : Scheme) := f.resLE W V le_rfl with hg
  have hgcomp : g ≫ W.ι = j' ≫ f := Scheme.Hom.resLE_comp_ι f le_rfl
  -- Step 1: transport `restrictFunctor j'` to `pullback j'`.
  rw [NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback j') (pullbackTensorMap f M N)]
  -- Goal: `IsIso ((pullback j').map (pullbackTensorMap f M N))`.
  -- K1 instances for the open immersions `j'` and `W.ι`.
  haveI hK1j' : IsIso (pullbackTensorMap j' ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N)) :=
    pullbackTensorMap_isIso_of_isOpenImmersion j' _ _
  haveI hK1W : IsIso (pullbackTensorMap W.ι M N) :=
    pullbackTensorMap_isIso_of_isOpenImmersion W.ι M N
  -- K2 instance: `pullbackTensorMap g (W.ι^*M) (W.ι^*N)` (the base modules are trivial over W).
  haveI hK2 : IsIso (pullbackTensorMap g ((Scheme.Modules.pullback W.ι).obj M)
      ((Scheme.Modules.pullback W.ι).obj N)) :=
    pullbackTensorMap_isIso_of_base_unit g
      (((Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).symm ≪≫ eM)
      (((Scheme.Modules.restrictFunctorIsoPullback W.ι).app N).symm ≪≫ eN)
  -- LHS iso: `pullbackTensorMap (j' ≫ f) M N` via the `g ≫ W.ι` factorisation (D3′ + K1 + K2).
  -- The composite of the four iso-factors (`IsIso.comp_isIso'`, since composite-iso is not an
  -- auto instance); proofs supplied explicitly to avoid metavariable-ordered instance search.
  haveI hLHS : IsIso (pullbackTensorMap (j' ≫ f) M N) := by
    rw [← hgcomp, pullbackTensorMap_restrict g W.ι M N]
    have hA2 : IsIso ((Scheme.Modules.pullbackComp g W.ι).inv.app (M.tensorObj N)) := inferInstance
    have hB2 : IsIso ((Scheme.Modules.pullback g).map (pullbackTensorMap W.ι M N)) :=
      Functor.map_isIso (Scheme.Modules.pullback g) (pullbackTensorMap W.ι M N)
    have hD2 : IsIso (tensorObjIsoOfIso ((Scheme.Modules.pullbackComp g W.ι).app M)
        ((Scheme.Modules.pullbackComp g W.ι).app N)).hom := inferInstance
    exact IsIso.comp_isIso' hA2 (IsIso.comp_isIso' hB2 (IsIso.comp_isIso' hK2 hD2))
  -- Isolate the wanted middle factor from the `j' ≫ f` factorisation (D3′): the two flanking
  -- factors are isos (`pullbackComp` inv-component and `tensorObjIsoOfIso`), `hK1j'` is the third.
  have hEq := pullbackTensorMap_restrict j' f M N
  rw [hEq] at hLHS
  -- the two flanking factors are isos: the `pullbackComp` inverse-component (cast from the
  -- `.app _ |>.inv` form) and the `tensorObjIsoOfIso` hom; `hK1j'` is the third.
  have hAj' : IsIso ((Scheme.Modules.pullbackComp j' f).inv.app (M.tensorObj N)) :=
    inferInstanceAs (IsIso (((Scheme.Modules.pullbackComp j' f).app (M.tensorObj N)).inv))
  have hDj' : IsIso (tensorObjIsoOfIso ((Scheme.Modules.pullbackComp j' f).app M)
      ((Scheme.Modules.pullbackComp j' f).app N)).hom := inferInstance
  exact isIso_of_isIso_comp4_mid hLHS hAj' hK1j' hDj'

/-- **D4′ — Pullback commutes with `⊗` on locally-trivial pairs** (blueprint
`lem:pullback_tensor_iso_loctriv`). For a morphism `f : Y ⟶ X` and locally-trivial
`M N : X.Modules`, promotes the comparison map `pullbackTensorMap f M N` to an isomorphism
via a chart-chase with `isIso_of_isIso_restrict` (over a common trivialising cover of Y),
`pullbackTensorMap_restrict` (D3′), `pullbackTensorMap_natural` (D1′), and
`pullbackTensorMap_unit_isIso` (D2′). The hom of the returned iso is `pullbackTensorMap f M N`. -/
noncomputable def pullbackTensorIsoOfLocallyTrivial {X Y : Scheme.{u}} (f : Y ⟶ X)
    {M N : X.Modules} (hM : LineBundle.IsLocallyTrivial M) (hN : LineBundle.IsLocallyTrivial N) :
    (Scheme.Modules.pullback f).obj (tensorObj M N) ≅
      tensorObj ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) := by
  -- The `IsIso` instance is the sole obligation; the iso is `asIso`.
  haveI : IsIso (pullbackTensorMap f M N) := by
    classical
    -- For each `y : Y`, a common trivialising affine chart `W ∋ f.base y` for both `M` and `N`,
    -- obtained by refining the two trivialising opens to a common affine sub-open
    -- (`exists_isAffineOpen_mem_and_subset`) and transporting via `restrictIsoUnitOfLE`.
    have hchart : ∀ y : Y, ∃ W : X.Opens, f.base y ∈ W ∧
        Nonempty (M.restrict W.ι ≅ SheafOfModules.unit (W : Scheme).ringCatSheaf) ∧
        Nonempty (N.restrict W.ι ≅ SheafOfModules.unit (W : Scheme).ringCatSheaf) := by
      intro y
      obtain ⟨UM, hxUM, _, ⟨eM⟩⟩ := hM (f.base y)
      obtain ⟨UN, hxUN, _, ⟨eN⟩⟩ := hN (f.base y)
      obtain ⟨W, _, hxW, hWsub⟩ :=
        exists_isAffineOpen_mem_and_subset (X := X) (x := f.base y) (U := UM ⊓ UN) ⟨hxUM, hxUN⟩
      exact ⟨W, hxW, ⟨restrictIsoUnitOfLE (le_trans hWsub inf_le_left) eM⟩,
        ⟨restrictIsoUnitOfLE (le_trans hWsub inf_le_right) eN⟩⟩
    choose W hxW eM eN using hchart
    -- The cover `{f⁻¹W y}` of `Y`; each chart obligation is the closed `chart_isIso`.
    refine isIso_of_isIso_restrict (pullbackTensorMap f M N)
      (fun y => f ⁻¹ᵁ (W y)) (fun y => hxW y) (fun y => ?_)
    exact chart_isIso f M N (W y) (eM y).some (eN y).some
  exact asIso (pullbackTensorMap f M N)

end LocTrivPullbackTensor

end Modules

end Scheme

end AlgebraicGeometry
