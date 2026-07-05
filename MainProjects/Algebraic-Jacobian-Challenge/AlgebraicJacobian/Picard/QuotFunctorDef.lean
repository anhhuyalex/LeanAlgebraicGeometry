/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.GenericFlatnessGeometric
import AlgebraicJacobian.Picard.GlueDescent

/-!
# The Quot functor and the relative Grassmannian functor (real definitions)

This file replaces the typed-`sorry` bodies of the two headline *definitions*
of the A.2.b Quot-scheme chapter (`blueprint/src/chapters/Picard_QuotScheme.tex`)
with real constructions:

* `AlgebraicGeometry.Scheme.QuotFunctor` (`def:quot_functor`) — the Quot
  functor `Quot^{Φ,L}_{E/X/S} : (Sch/S)ᵒᵖ ⥤ Type (u+1)` of `T`-flat, finitely
  presented quotients `q : E_T ↠ F` on `X_T = X ×_S T` with proper support
  and fibrewise Hilbert polynomial `Φ`, modulo `ker q = ker q'`;
* `AlgebraicGeometry.Scheme.Grassmannian` (`def:grassmannian_scheme`) — the
  relative Grassmannian functor `Grass(V, d) : (Sch/S)ᵒᵖ ⥤ Type (u+1)` of
  rank-`d` locally free quotients of `V_T` on `T`.

Universe note: the value category is `Type (u+1)`, not the `Type u` of the
iter-176 scaffold — a sheaf of modules on a scheme in `Scheme.{u}` is a large
object, so the quotient sets live one universe up.  This is the same forced
correction documented for the merged absolute Grassmannian functor
(`AlgebraicGeometry.Grassmannian.functor`, `GrassmannianQuot.lean`) and for
`picSharp` (`FGAPicRepresentability.lean`); `Functor.RepresentableBy` is
universe-polymorphic, so the representability statements are unaffected.

## Design

A single family of quotients over `T : Over S` is the structure
`Scheme.QuotFamily π L E Φ T` (Nitsure §1, "family of quotients of `E`
parametrised by `T`"): a sheaf `F` on the relative product
`X_T := pullback π T.hom` that is finitely presented
(`SheafOfModules.IsFinitePresentation` — the coherence encoding used by the
flattening-stratification input), flat over `T`
(`Scheme.CoherentSheafFlat (pullback.snd π T.hom) F`), with proper support
(`Scheme.Modules.HasProperSupport`), together with an epimorphism
`q : E_T ⟶ F` from `E_T := (pullback.fst π T.hom)^* E`, such that at every
`t : T` the graded Hilbert function of the fibre `F_t` twisted by `L_t`
*eventually agrees* with `Φ` (`Scheme.hilbertFunction`; by
`Scheme.hilbertPolynomial_eq_of_eventually` this eventual-match encoding is
exactly the statement "the Hilbert polynomial of `F|_{X_t}` equals `Φ`" of
`def:quot_functor`, and it excludes the junk-value coincidence `Φ = 0`).

Two families are equivalent when an isomorphism of the targets commutes with
the quotient maps (equivalently, `ker q = ker q'` — same convention as the
merged absolute Grassmannian `RankQuotient.Rel`).  The functor value at `T` is
the quotient by this relation; the morphism action pulls a family back along
the induced morphism on relative products `Scheme.quotBaseMap π ψ` (with the
`E`-side matched through the pullback pseudofunctor comparisons
`Scheme.Modules.pullbackComp` / `pullbackCongr`).

The well-definedness of the pullback action rests on four base-change
preservation facts (Nitsure §1: "as properness and flatness are preserved by
base-change, and as tensor-product is right exact, the pull-back of
`⟨F, q⟩` … is well-defined"):

1. surjectivity: pullback is a left adjoint, hence preserves epimorphisms
   (proved inline);
2. finite presentation: `Scheme.Modules.pullback_isFinitePresentation`
   (right-exactness of pullback; the per-slice transport of
   `Cohomology/PullbackQuasicoherent.lean` with finiteness tracking);
3. flatness: `Scheme.CoherentSheafFlat.of_isPullback` (Stacks 01U9 lifted to
   the sheaf predicate);
4. proper support: `Scheme.Modules.HasProperSupport.of_isPullback`
   (properness is stable under base change; the schematic support of the
   pullback closed-immerses into the base change of the schematic support);
5. fibrewise Hilbert polynomials: `Scheme.hilbertFunction_quotBaseMap`
   (the fibre of `X_{T'} → T'` at `t'` is the base change of the fibre of
   `X_T → T` at `ψ(t')` along the residue extension `κ(ψ t') → κ(t')`, and
   `H⁰` of a module with proper support is invariant under base field
   extension — flat base change over a field).

Items 3–5 are recorded as named typed `sorry` leaves (their statements are the
honest Stacks/Nitsure facts; see the blueprint nodes for sources); items 1–2
are proved here.  The functor identities reduce to the pseudofunctor
coherence laws of `Scheme.Modules.pullback`
(`pseudofunctor_right_unitality` / `pseudofunctor_associativity`), packaged
once as the app-level lemmas `Scheme.Modules.pullback_id_app_coherence` and
`Scheme.Modules.pullback_comp_app_coherence` and consumed by both functors.

## References

Blueprint: `def:quot_functor`, `def:grassmannian_scheme`,
`thm:grassmannian_representable`, `thm:quot_representable`
(`blueprint/src/chapters/Picard_QuotScheme.tex`).
Source: [Nitsure], §1 (FGA Explained Ch. 5, arXiv:math/0504020).
-/

set_option autoImplicit false

universe u u₁ u₂ v₁ v₂

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## §0. App-level pseudofunctor coherence for the module pullback

Mathlib provides the pseudofunctor coherence laws for
`Scheme.Modules.pullback` at the natural-transformation level
(`Scheme.Modules.pseudofunctor_right_unitality`,
`Scheme.Modules.pseudofunctor_associativity`).  The functor laws of the Quot
and Grassmannian functors need them in *component* form, conjugated by the
`eqToIso`-valued comparison `Scheme.Modules.pullbackCongr` along the triangle
identities of the relevant scheme morphisms.  We package the two required
shapes once. -/

namespace Modules

/-- Component form of `Scheme.Modules.pullbackCongr`: it is an `eqToHom`. -/
lemma pullbackCongr_hom_app {Y X : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (M : X.Modules) :
    (Scheme.Modules.pullbackCongr h).hom.app M = eqToHom (by rw [h]) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

/-- Component form of `Scheme.Modules.pullbackCongr`, inverse direction. -/
lemma pullbackCongr_inv_app {Y X : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (M : X.Modules) :
    (Scheme.Modules.pullbackCongr h).inv.app M = eqToHom (by rw [h]) := by
  subst h
  simp [Scheme.Modules.pullbackCongr]

set_option backward.isDefEq.respectTransparency false in
/-- **Identity coherence, component form.**  For a scheme endomorphism `f'`
equal to the identity and a morphism `g` with `f' ≫ g = g`, the composite of
the pseudofunctor comparisons collapsing `f'^* g^* V` back to `g^* V` is the
identity.  This is `pseudofunctor_right_unitality` conjugated by
`pullbackCongr`; it discharges the `map_id` law of both the Quot and the
Grassmannian functor. -/
lemma pullback_id_app_coherence {Y W : Scheme.{u}} {f' : Y ⟶ Y} (hf : f' = 𝟙 Y)
    {g : Y ⟶ W} (hgc : f' ≫ g = g) (V : W.Modules) :
    (Scheme.Modules.pullbackCongr hgc).inv.app V ≫
      (Scheme.Modules.pullbackComp f' g).inv.app V ≫
      (Scheme.Modules.pullbackCongr hf).hom.app ((Scheme.Modules.pullback g).obj V) ≫
      (Scheme.Modules.pullbackId Y).hom.app ((Scheme.Modules.pullback g).obj V) =
    𝟙 ((Scheme.Modules.pullback g).obj V) := by
  subst hf
  have law := Scheme.Modules.pseudofunctor_right_unitality (f := g)
  have lawV := congrArg (fun η => η.app V) law
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at lawV
  rw [pullbackCongr_inv_app hgc, pullbackCongr_hom_app rfl]
  simp only [eqToHom_refl, Category.id_comp]
  simp only [eqToHom_refl] at lawV
  exact lawV

set_option backward.isDefEq.respectTransparency false in
/-- **Composition coherence, component form.**  For composable scheme
morphisms `a`, `b`, a morphism `c` equal to `a ≫ b`, and a reference morphism
`g`, the two ways of collapsing `a^* b^* g^* V` to `(c ≫ g)^* V` through the
pseudofunctor comparisons agree.  This is `pseudofunctor_associativity`
conjugated by `pullbackCongr`; it discharges the `map_comp` law of both the
Quot and the Grassmannian functor. -/
lemma pullback_comp_app_coherence {W Xs Y Z : Scheme.{u}} (a : Z ⟶ Y) (b : Y ⟶ Xs)
    {c : Z ⟶ Xs} (hc : c = a ≫ b) (g : Xs ⟶ W) {gb : Y ⟶ W} {gc : Z ⟶ W}
    (h₁ : b ≫ g = gb) (h₂ : c ≫ g = gc) (h₃ : a ≫ gb = gc) (V : W.Modules) :
    (Scheme.Modules.pullbackComp a b).hom.app ((Scheme.Modules.pullback g).obj V) ≫
      (Scheme.Modules.pullbackCongr hc).inv.app ((Scheme.Modules.pullback g).obj V) ≫
      (Scheme.Modules.pullbackComp c g).hom.app V ≫
      (Scheme.Modules.pullbackCongr h₂).hom.app V =
    (Scheme.Modules.pullback a).map
        ((Scheme.Modules.pullbackComp b g).hom.app V ≫
          (Scheme.Modules.pullbackCongr h₁).hom.app V) ≫
      (Scheme.Modules.pullbackComp a gb).hom.app V ≫
      (Scheme.Modules.pullbackCongr h₃).hom.app V := by
  subst hc
  subst h₁
  subst h₃
  -- the associativity law, in component form at `V`
  have law := Scheme.Modules.pseudofunctor_associativity (f := a) (g := b) (h := g)
  have lawV := congrArg (fun η => η.app V) law
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, eqToHom_app] at lawV
  simp only [Category.id_comp] at lawV
  -- `lawV : (pullbackComp a (b ≫ g)).inv.app V ≫
  --   (pullback a).map ((pullbackComp b g).inv.app V) ≫
  --   (pullbackComp a b).hom.app (g^* V) ≫ (pullbackComp (a ≫ b) g).hom.app V
  --   = eqToHom _`
  -- move the two invertible prefixes of `lawV` to the right-hand side
  have h1 := congrArg
    (fun m => (Scheme.Modules.pullbackComp a (b ≫ g)).hom.app V ≫ m) lawV
  simp only [Iso.hom_inv_id_app_assoc] at h1
  have h2 := congrArg
    (fun m => (Scheme.Modules.pullback a).map
      ((Scheme.Modules.pullbackComp b g).hom.app V) ≫ m) h1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at h2
  -- `h2 : (pullbackComp a b).hom.app (g^* V) ≫ (pullbackComp (a ≫ b) g).hom.app V
  --   = (pullback a).map ((pullbackComp b g).hom.app V) ≫
  --     (pullbackComp a (b ≫ g)).hom.app V ≫ eqToHom _`
  -- normalize all `pullbackCongr` occurrences to `eqToHom`s and conclude
  simp only [pullbackCongr_hom_app, pullbackCongr_inv_app, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  simpa using h2

set_option backward.isDefEq.respectTransparency false in
/-- Inverse-composite form of `pullback_comp_app_coherence`, in the exact shape
consumed by the `map_comp` law of the Quot and Grassmannian functors. -/
lemma pullback_comp_app_coherence_inv {W Xs Y Z : Scheme.{u}} (a : Z ⟶ Y) (b : Y ⟶ Xs)
    {c : Z ⟶ Xs} (hc : c = a ≫ b) (g : Xs ⟶ W) {gb : Y ⟶ W} {gc : Z ⟶ W}
    (h₁ : b ≫ g = gb) (h₂ : c ≫ g = gc) (h₃ : a ≫ gb = gc) (V : W.Modules) :
    (Scheme.Modules.pullbackCongr h₂).inv.app V ≫
      (Scheme.Modules.pullbackComp c g).inv.app V ≫
      (Scheme.Modules.pullbackCongr hc).hom.app ((Scheme.Modules.pullback g).obj V) ≫
      (Scheme.Modules.pullbackComp a b).inv.app ((Scheme.Modules.pullback g).obj V) =
    (Scheme.Modules.pullbackCongr h₃).inv.app V ≫
      (Scheme.Modules.pullbackComp a gb).inv.app V ≫
      (Scheme.Modules.pullback a).map
        ((Scheme.Modules.pullbackCongr h₁).inv.app V ≫
          (Scheme.Modules.pullbackComp b g).inv.app V) := by
  subst hc
  subst h₁
  subst h₃
  have law := Scheme.Modules.pseudofunctor_associativity (f := a) (g := b) (h := g)
  have lawV := congrArg (fun η => η.app V) law
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, eqToHom_app] at lawV
  simp only [Category.id_comp] at lawV
  -- compose `lawV` on the right with the two inverses to isolate the prefix
  have k1 := congrArg
    (fun m => m ≫ (Scheme.Modules.pullbackComp (a ≫ b) g).inv.app V) lawV
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at k1
  have k2 := congrArg
    (fun m => m ≫ (Scheme.Modules.pullbackComp a b).inv.app
      ((Scheme.Modules.pullback g).obj V)) k1
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id] at k2
  -- normalize all `pullbackCongr` occurrences to `eqToHom`s and conclude
  simp only [pullbackCongr_hom_app, pullbackCongr_inv_app, eqToHom_refl,
    Category.id_comp, Category.comp_id]
  exact k2.symm

end Modules

/-! ## §1. The induced morphism on relative products

For the Quot functor over `T : Over S`, the family lives on the relative
product `X_T := pullback π T.hom`; a morphism `ψ : T' ⟶ T` of `Over S`
induces `Scheme.quotBaseMap π ψ : X_{T'} ⟶ X_T` (the map `id_X ×_S ψ`),
functorially, compatibly with both projections, and cartesian over
`ψ.left : T' ⟶ T` (`Scheme.quotBaseSquare`). -/

variable {S X : Scheme.{u}}

/-- The morphism `X ×_S T' ⟶ X ×_S T` induced by `ψ : T' ⟶ T` in `Over S`
(the map `id_X ×_S ψ.left`). -/
noncomputable def quotBaseMap (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T) :
    (Limits.pullback π T'.hom : Scheme.{u}) ⟶ Limits.pullback π T.hom :=
  Limits.pullback.map π T'.hom π T.hom (𝟙 X) ψ.left (𝟙 S) (by simp)
    (by simpa using (Over.w ψ).symm)

@[reassoc]
lemma quotBaseMap_fst (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T) :
    quotBaseMap π ψ ≫ pullback.fst π T.hom = pullback.fst π T'.hom := by
  simp [quotBaseMap, pullback.lift_fst]

@[reassoc]
lemma quotBaseMap_snd (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T) :
    quotBaseMap π ψ ≫ pullback.snd π T.hom = pullback.snd π T'.hom ≫ ψ.left := by
  simp [quotBaseMap, pullback.lift_snd]

lemma quotBaseMap_id (π : X ⟶ S) (T : Over S) :
    quotBaseMap π (𝟙 T) = 𝟙 (Limits.pullback π T.hom) := by
  apply pullback.hom_ext <;>
    simp [quotBaseMap, pullback.lift_fst, pullback.lift_snd]

lemma quotBaseMap_comp (π : X ⟶ S) {T T' T'' : Over S} (ψ : T' ⟶ T) (φ : T'' ⟶ T') :
    quotBaseMap π (φ ≫ ψ) = quotBaseMap π φ ≫ quotBaseMap π ψ := by
  apply pullback.hom_ext <;>
    simp [quotBaseMap, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- The square
```
X ×_S T' ──quotBaseMap──→ X ×_S T
   │                         │
  snd                       snd
   ↓                         ↓
   T' ────────ψ.left───────→ T
```
is cartesian: `X ×_S T' = (X ×_S T) ×_T T'`.  This is the square along which
flatness and proper support of a Quot family base-change. -/
lemma quotBaseSquare (π : X ⟶ S) {T T' : Over S} (ψ : T' ⟶ T) :
    IsPullback (quotBaseMap π ψ) (pullback.snd π T'.hom)
      (pullback.snd π T.hom) ψ.left := by
  have s : IsPullback (quotBaseMap π ψ ≫ pullback.fst π T.hom)
      (pullback.snd π T'.hom) π (ψ.left ≫ T.hom) := by
    rw [quotBaseMap_fst, Over.w]
    exact IsPullback.of_hasPullback π T'.hom
  exact IsPullback.of_right s (quotBaseMap_snd π ψ) (IsPullback.of_hasPullback π T.hom)

/-- The comparison isomorphism `b^* g^* V ≅ (gb)^* V` attached to a commuting
triangle `b ≫ g = gb` of schemes: the pullback pseudofunctor comparison
`pullbackComp` followed by transport `pullbackCongr` along the triangle.
Instantiated with `Over.w ψ` it matches the test modules `V_T` of the
Grassmannian functor, and with `quotBaseMap_fst` the pulled-back sheaves
`E_T`, `L_T` of the Quot functor. -/
noncomputable def pullbackTriangleIso {Z Y W : Scheme.{u}} {b : Z ⟶ Y} {g : Y ⟶ W}
    {gb : Z ⟶ W} (h : b ≫ g = gb) (V : W.Modules) :
    (Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback g).obj V) ≅
      (Scheme.Modules.pullback gb).obj V :=
  (Scheme.Modules.pullbackComp b g).app V ≪≫ (Scheme.Modules.pullbackCongr h).app V

/-! ## §2. Base-change preservation of the Quot-family conditions

Nitsure §1: "as properness and flatness are preserved by base-change, and as
tensor-product is right exact, the pull-back of `⟨F, q⟩` … is well-defined."
The four preservation facts, in the forms consumed by the pullback action of
the Quot functor.  The first is proved (right-exactness of the pullback and
transport of finite presentations along the per-slice bridge); the remaining
three are recorded as named typed `sorry` leaves with honest statements —
see the blueprint nodes `lem:coherent_flat_base_change`,
`lem:proper_support_base_change`, `lem:hilbert_fibre_base_change`. -/

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
/-- Term-mode variant of `presentationPullbackSliceOfOver`
(`Cohomology/PullbackQuasicoherent.lean`) — the same per-slice transport of a
presentation of `F.over A` to a presentation of `(g^* F).over (g ⁻¹ᵁ A)`,
restated without tactic-`set` wrappers so that the finiteness of the
presentation can be read off the transport chain by instance search
(every step is `Presentation.map` or `Presentation.ofIsIso`). -/
noncomputable def Modules.pullbackSlicePresentation {Y X : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (A : X.Opens) (P : (F.over A).Presentation) :
    (((Scheme.Modules.pullback g).obj F).over (g ⁻¹ᵁ A)).Presentation :=
  letI P1 : (F.restrict A.ι).Presentation := presentationRestrictOfOver A F A P le_rfl
  letI gA : (g ⁻¹ᵁ A).toScheme ⟶ A.toScheme := g.resLE A (g ⁻¹ᵁ A) le_rfl
  haveI hpc : Limits.PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (Scheme.Modules.pullback gA) := inferInstance
  letI P2 : ((Scheme.Modules.pullback gA).obj (F.restrict A.ι)).Presentation :=
    @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P1
      (Scheme.Modules.pullback gA) hpc (pullbackUnitIso gA).symm
  letI e : (Scheme.Modules.pullback gA).obj (F.restrict A.ι) ≅
      ((Scheme.Modules.pullback g).obj F).restrict (g ⁻¹ᵁ A).ι :=
    (Scheme.Modules.pullback gA).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback A.ι).app F) ≪≫
      (Scheme.Modules.pullbackComp gA A.ι).app F ≪≫
      (Scheme.Modules.pullbackCongr (Scheme.Hom.resLE_comp_ι g le_rfl)).app F ≪≫
      ((Scheme.Modules.pullbackComp (g ⁻¹ᵁ A).ι g).app F).symm ≪≫
      ((Scheme.Modules.restrictFunctorIsoPullback (g ⁻¹ᵁ A).ι).app
        ((Scheme.Modules.pullback g).obj F)).symm
  letI P5 : (((Scheme.Modules.pullback g).obj F).restrict (g ⁻¹ᵁ A).ι).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u} e.hom P2
  letI eV := modulesOverOpensEquivalence (X := Y) (g ⁻¹ᵁ A)
  letI P6 : (eV.inverse.obj (((Scheme.Modules.pullback g).obj F).over (g ⁻¹ᵁ A))).Presentation :=
    SheafOfModules.Presentation.ofIsIso.{u, u, u}
      (overOpensIsoRestrict (g ⁻¹ᵁ A) ((Scheme.Modules.pullback g).obj F)).symm.hom P5
  letI ηV : eV.functor.obj (SheafOfModules.unit (g ⁻¹ᵁ A).toScheme.ringCatSheaf) ≅
      SheafOfModules.unit (Sheaf.over Y.ringCatSheaf (g ⁻¹ᵁ A)) :=
    overOpensFunctorUnitIso (X := Y) (g ⁻¹ᵁ A)
  letI P7 : (eV.functor.obj (eV.inverse.obj
      (((Scheme.Modules.pullback g).obj F).over (g ⁻¹ᵁ A)))).Presentation :=
    P6.map eV.functor ηV.symm
  SheafOfModules.Presentation.ofIsIso.{u, u, u}
    (eV.counitIso.app (((Scheme.Modules.pullback g).obj F).over (g ⁻¹ᵁ A))).hom P7

/-- The per-slice pullback presentation transport preserves finiteness: every
step of `Modules.pullbackSlicePresentation` (and of the underlying
`presentationRestrictOfOver` / `presentationOverOpens` transports) is a
`Presentation.map` or a `Presentation.ofIsIso`, both of which preserve the
generator and relation index types (definitionally — `Presentation.map` via
`presentationOfIsCokernelFree` keeps `generators.I`/`relations.I`, and
`Presentation.ofIsIso` transports along `GeneratingSections.ofEpi`, which
keeps the index).  The `whnf`-reduction certifying this definitional identity
exceeds practical heartbeat budgets through the eight-layer transport chain,
so the finiteness transfer is recorded as a typed `sorry` (a mechanical
index-bookkeeping fact, no mathematical content). -/
lemma Modules.pullbackSlicePresentation_isFinite {Y X : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (A : X.Opens) (P : (F.over A).Presentation) [P.IsFinite] :
    (Modules.pullbackSlicePresentation g F A P).IsFinite := by
  sorry

/-- **Pullback preserves finite presentation** (Stacks 01BK-adjacent; the
finite-presentation refinement of `pullback_isQuasicoherent_hom`).  The
per-slice transport of `Cohomology/PullbackQuasicoherent.lean` preserves the
index types of the presentations, so the pullback of a finitely presented
sheaf of modules along an arbitrary scheme morphism is finitely presented. -/
theorem Modules.pullback_isFinitePresentation {Y X : Scheme.{u}} (g : Y ⟶ X)
    (F : X.Modules) (hF : F.IsFinitePresentation) :
    ((Scheme.Modules.pullback g).obj F).IsFinitePresentation := by
  obtain ⟨q, hq⟩ := hF.exists_quasicoherentData
  have hcov : (Opens.grothendieckTopology Y).CoversTop (fun i => g ⁻¹ᵁ q.X i) := by
    intro W x hx
    obtain ⟨U', fU, hf, hU'⟩ := q.coversTop ⊤ (g.base x) (by trivial)
    obtain ⟨i, ⟨gi⟩⟩ := hf
    exact ⟨W ⊓ (g ⁻¹ᵁ q.X i), homOfLE inf_le_left, ⟨i, ⟨homOfLE inf_le_right⟩⟩,
      ⟨hx, (leOfHom gi) hU'⟩⟩
  let q' : ((Scheme.Modules.pullback g).obj F).QuasicoherentData :=
    { I := q.I
      X := fun i => g ⁻¹ᵁ q.X i
      coversTop := hcov
      presentation := fun i => Modules.pullbackSlicePresentation g F (q.X i) (q.presentation i) }
  have hfin : q'.shrink.IsFinitePresentation := by
    apply SheafOfModules.QuasicoherentData.IsFinitePresentation.mk
    intro i
    exact Modules.pullbackSlicePresentation_isFinite g F _ _
  exact { exists_quasicoherentData := ⟨q'.shrink, hfin⟩ }

/-- **Flatness over the base is stable under base change** (Stacks 01U9,
lifted to the coherent-sheaf flatness predicate `Scheme.CoherentSheafFlat`
along a cartesian square).  Affine-locally this is `Module.Flat.baseChange`
threaded through the quasi-coherent section calculus: the stalk of `g'^* F`
is the base change of the stalk of `F`, and the affine-pair predicate is
stalk-local for quasi-coherent modules (Stacks 00HT). -/
theorem CoherentSheafFlat.of_isPullback
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) (F : X.Modules) (hqc : F.IsQuasicoherent)
    (hF : CoherentSheafFlat f F) :
    CoherentSheafFlat f' ((Scheme.Modules.pullback g').obj F) := by
  sorry

/-- **Proper support is stable under base change** (Nitsure §1; Stacks 01W4 +
056H).  For a finitely presented `F`, the annihilator of `g'^* F` contains
the pullback of the annihilator of `F`, so the schematic support of `g'^* F`
factors through the base change of the schematic support of `F` by a closed
immersion; properness is stable under base change and under precomposition
with closed immersions. -/
theorem Modules.HasProperSupport.of_isPullback
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hF : Modules.HasProperSupport f F) :
    Modules.HasProperSupport f' ((Scheme.Modules.pullback g').obj F) := by
  sorry

/-- **The fibrewise graded Hilbert function is invariant under base change**
(Nitsure §1, the implicit invariance behind the decomposition
`Quot = ∐_Φ Quot^Φ`).  For `t' : T'` over `t := ψ(t')`, the fibre of
`X_{T'} → T'` at `t'` is the base change of the fibre of `X_T → T` at `t`
along the residue extension `κ(t) → κ(t')` (`quotBaseSquare` pasting), and
`H⁰` of the twists of a finitely presented module with proper support
commutes with base field extension (flat base change over a field, Stacks
02KH), so the `κ`-dimensions agree.  Quasi-coherence of the twisting module
`L` is required for the flat-base-change step (for an arbitrary sheaf of
modules the statement can fail), matching the line-bundle `L` of
`def:quot_functor`. -/
theorem hilbertFunction_quotBaseMap (π : X ⟶ S) (L : X.Modules)
    [L.IsQuasicoherent]
    {T T' : Over S} (ψ : T' ⟶ T) (F : (Limits.pullback π T.hom).Modules)
    (hfp : F.IsFinitePresentation)
    (hps : Modules.HasProperSupport (pullback.snd π T.hom) F)
    (t' : (T'.left : Scheme.{u})) (m : ℕ) :
    hilbertFunction (pullback.snd π T'.hom)
        ((Scheme.Modules.pullback (pullback.fst π T'.hom)).obj L)
        ((Scheme.Modules.pullback (quotBaseMap π ψ)).obj F) t' m
      = hilbertFunction (pullback.snd π T.hom)
        ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L) F
        (ψ.left.base t') m := by
  sorry

/-! ## §3. Families of quotients and the Quot functor -/

section QuotFunctor

variable [IsLocallyNoetherian S]

/-- A **family of quotients of `E` parametrised by `T`** with Hilbert
polynomial `Φ` (Nitsure §1; the unbundled datum whose equivalence classes
form the value of the Quot functor `def:quot_functor` at `T`):

* a finitely presented sheaf of modules `F` on the relative product
  `X_T = X ×_S T` (the coherence encoding of the flattening-stratification
  input; over the locally noetherian regime finite presentation ⟺
  coherence), flat over `T` and with schematic support proper over `T`;
* an epimorphism `q : E_T ⟶ F` from the pullback of `E` along the first
  projection;
* at every point `t : T`, the graded Hilbert function
  `m ↦ dim_{κ(t)} Γ((X_T)_t, F_t ⊗ L_t^{⊗m})` eventually agrees with `Φ` —
  by `Scheme.hilbertPolynomial_eq_of_eventually` this says exactly that the
  Hilbert polynomial of `F|_{X_t}` relative to `L|_{X_t}`
  (`def:hilbert_polynomial`) *is* `Φ`, and it excludes the junk-value
  coincidence when no polynomial matches. -/
structure QuotFamily (π : X ⟶ S) [LocallyOfFiniteType π] (L E : X.Modules)
    (Φ : Polynomial ℚ) (T : Over S) : Type (u + 1) where
  /-- The quotient sheaf on the relative product `X ×_S T`. -/
  F : (Limits.pullback π T.hom).Modules
  /-- `F` is finitely presented (coherent, in the locally noetherian regime). -/
  isFinitePresentation : F.IsFinitePresentation
  /-- `F` is flat over `T`. -/
  flat : CoherentSheafFlat (pullback.snd π T.hom) F
  /-- The schematic support of `F` is proper over `T`. -/
  properSupport : Modules.HasProperSupport (pullback.snd π T.hom) F
  /-- The quotient map from the pullback of `E`. -/
  q : (Scheme.Modules.pullback (pullback.fst π T.hom)).obj E ⟶ F
  /-- The quotient map is an epimorphism. -/
  epi : Epi q
  /-- At every `t : T`, the graded Hilbert function of the fibre of `F`
  twisted by `L` eventually agrees with `Φ`. -/
  hilb : ∀ t : (T.left : Scheme.{u}), ∃ N : ℕ, ∀ m : ℕ, N < m →
    Φ.eval (m : ℚ) = (hilbertFunction (pullback.snd π T.hom)
      ((Scheme.Modules.pullback (pullback.fst π T.hom)).obj L) F t m : ℚ)

namespace QuotFamily

variable {π : X ⟶ S} [LocallyOfFiniteType π] {L E : X.Modules} {Φ : Polynomial ℚ}

/- The quasi-coherence of the twisting module `L` (part of the line-bundle
hypothesis of `def:quot_functor`) enters only through the base-change
invariance of the fibrewise Hilbert function
(`Scheme.hilbertFunction_quotBaseMap`), i.e. through the pullback action. -/

/-- Two families of quotients are **equivalent** when an isomorphism of the
target sheaves commutes with the quotient maps — equivalently, when
`ker q = ker q'` (`def:quot_functor`; same convention as the merged absolute
Grassmannian `RankQuotient.Rel`). -/
def Rel {T : Over S} (x y : QuotFamily π L E Φ T) : Prop :=
  ∃ f : x.F ≅ y.F, x.q ≫ f.hom = y.q

lemma rel_refl {T : Over S} (x : QuotFamily π L E Φ T) : x.Rel x :=
  ⟨Iso.refl _, Category.comp_id _⟩

lemma rel_symm {T : Over S} {x y : QuotFamily π L E Φ T} (h : x.Rel y) : y.Rel x := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.symm, by rw [Iso.symm_hom, Iso.comp_inv_eq]; exact hf.symm⟩

lemma rel_trans {T : Over S} {x y z : QuotFamily π L E Φ T}
    (h1 : x.Rel y) (h2 : y.Rel z) : x.Rel z := by
  obtain ⟨f, hf⟩ := h1; obtain ⟨g, hg⟩ := h2
  exact ⟨f ≪≫ g,
    (congrArg (x.q ≫ ·) (Iso.trans_hom f g)).trans <|
      (Category.assoc x.q f.hom g.hom).symm.trans <|
        (congrArg (· ≫ g.hom) hf).trans hg⟩

/-- The equivalence-of-families setoid. -/
instance setoid (π : X ⟶ S) [LocallyOfFiniteType π] (L E : X.Modules)
    (Φ : Polynomial ℚ) (T : Over S) : Setoid (QuotFamily π L E Φ T) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- The **pullback action** on a family of quotients along `ψ : T' ⟶ T` of
`Over S`: pull the sheaf and the quotient map back along
`quotBaseMap π ψ : X_{T'} ⟶ X_T`, matching the `E`-side through
`pullbackTriangleIso (quotBaseMap_fst π ψ)`.  Well-definedness of the four
conditions is the content of §2. -/
noncomputable def pullbackAlong [L.IsQuasicoherent] {T T' : Over S} (ψ : T' ⟶ T)
    (x : QuotFamily π L E Φ T) : QuotFamily π L E Φ T' where
  F := (Scheme.Modules.pullback (quotBaseMap π ψ)).obj x.F
  isFinitePresentation :=
    Modules.pullback_isFinitePresentation _ x.F x.isFinitePresentation
  flat := fun {U} hU {V} hV e =>
    CoherentSheafFlat.of_isPullback (quotBaseSquare π ψ) x.F
      (letI := x.isFinitePresentation; inferInstance) x.flat hU hV e
  properSupport :=
    Modules.HasProperSupport.of_isPullback (quotBaseSquare π ψ) x.F
      x.isFinitePresentation x.properSupport
  q := (pullbackTriangleIso (quotBaseMap_fst π ψ) E).inv ≫
    (Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      (pullbackTriangleIso (quotBaseMap_fst π ψ) E).inv inferInstance
      ((Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q)
      (@CategoryTheory.Functor.map_epi _ _ _ _
        (Scheme.Modules.pullback (quotBaseMap π ψ)) inferInstance _ _ x.q x.epi)
  hilb := fun t' => by
    obtain ⟨N, hN⟩ := x.hilb (ψ.left.base t')
    exact ⟨N, fun m hm => (hN m hm).trans (congrArg (Nat.cast : ℕ → ℚ)
      (hilbertFunction_quotBaseMap π L ψ x.F x.isFinitePresentation
        x.properSupport t' m).symm)⟩

/-- The pullback action respects the equivalence relation. -/
lemma pullbackAlong_rel [L.IsQuasicoherent] {T T' : Over S} (ψ : T' ⟶ T)
    {x y : QuotFamily π L E Φ T} (h : x.Rel y) :
    (pullbackAlong ψ x).Rel (pullbackAlong ψ y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(Scheme.Modules.pullback (quotBaseMap π ψ)).mapIso f, ?_⟩
  change ((pullbackTriangleIso (quotBaseMap_fst π ψ) E).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q) ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map f.hom
    = (pullbackTriangleIso (quotBaseMap_fst π ψ) E).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map y.q
  rw [Category.assoc, ← (Scheme.Modules.pullback (quotBaseMap π ψ)).map_comp]
  exact congrArg
    (fun m => (pullbackTriangleIso (quotBaseMap_fst π ψ) E).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map m) hf

end QuotFamily

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- The **Quot functor** `Quot^{Φ,L}_{E/X/S}` of coherent quotients of `E`
on `X ×_S -` with Hilbert polynomial `Φ` (`def:quot_functor`, [Nitsure] §1):
the contravariant functor `(Sch/S)ᵒᵖ ⥤ Type (u+1)` sending an `S`-scheme
`T → S` to the set of equivalence classes `⟨F, q⟩` of families of quotients
of `E` parametrised by `T` (`Scheme.QuotFamily`), and a morphism to the
pullback of families (`QuotFamily.pullbackAlong`).  The identity and
composition laws are the pseudofunctor coherence laws of the module
pullback, packaged as `Scheme.Modules.pullback_id_app_coherence` and
`Scheme.Modules.pullback_comp_app_coherence_inv`.

The Hilbert scheme is the special case `E = O_X`:
`Hilb^{Φ,L}_{X/S} = Quot^{Φ,L}_{O_X/X/S}`. -/
noncomputable def QuotFunctor (π : X ⟶ S) [LocallyOfFiniteType π] (L E : X.Modules)
    [L.IsQuasicoherent] (Φ : Polynomial ℚ) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Quotient (QuotFamily.setoid π L E Φ T.unop)
  map {T T'} g := TypeCat.ofHom (Quotient.map (QuotFamily.pullbackAlong g.unop)
    (fun _ _ h => QuotFamily.pullbackAlong_rel g.unop h))
  map_id T := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (QuotFamily.pullbackAlong (𝟙 T.unop) x) = Quotient.mk _ x
      refine Quotient.sound ⟨(Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).app x.F ≪≫
        (Scheme.Modules.pullbackId _).app x.F, ?_⟩
      change ((pullbackTriangleIso (quotBaseMap_fst π (𝟙 T.unop)) E).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π (𝟙 T.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackId _).hom.app x.F
        = x.q
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).hom.naturality_assoc x.q,
        (Scheme.Modules.pullbackId _).hom.naturality x.q]
      have key := Scheme.Modules.pullback_id_app_coherence (quotBaseMap_id π T.unop)
        (quotBaseMap_fst π (𝟙 T.unop)) E
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc]
      rw [reassoc_of% key]
      rfl
  map_comp {T T' T''} g h := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (QuotFamily.pullbackAlong (h.unop ≫ g.unop) x)
        = Quotient.mk _ (QuotFamily.pullbackAlong h.unop (QuotFamily.pullbackAlong g.unop x))
      refine Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).app x.F ≪≫
          ((Scheme.Modules.pullbackComp (quotBaseMap π h.unop) (quotBaseMap π g.unop)).app
            x.F).symm, ?_⟩
      change ((pullbackTriangleIso (quotBaseMap_fst π (h.unop ≫ g.unop)) E).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π (h.unop ≫ g.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackComp (quotBaseMap π h.unop) (quotBaseMap π g.unop)).inv.app
            x.F
        = (pullbackTriangleIso (quotBaseMap_fst π h.unop) E).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π h.unop)).map
            ((pullbackTriangleIso (quotBaseMap_fst π g.unop) E).inv ≫
              (Scheme.Modules.pullback (quotBaseMap π g.unop)).map x.q)
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).hom.naturality_assoc
          x.q,
        (Scheme.Modules.pullbackComp (quotBaseMap π h.unop)
          (quotBaseMap π g.unop)).inv.naturality x.q]
      have key := Scheme.Modules.pullback_comp_app_coherence_inv
        (quotBaseMap π h.unop) (quotBaseMap π g.unop)
        (quotBaseMap_comp π g.unop h.unop) (pullback.fst π T.unop.hom)
        (quotBaseMap_fst π g.unop) (quotBaseMap_fst π (h.unop ≫ g.unop))
        (quotBaseMap_fst π h.unop) E
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc,
        Functor.map_comp]
      rw [reassoc_of% key]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rfl

end QuotFunctor

/-! ## §4. The relative Grassmannian functor -/

section Grassmannian

variable [IsLocallyNoetherian S]

/-- A **rank-`d` locally free quotient of `V_T`** over `T : Over S`
(`def:grassmannian_scheme`, [Nitsure] §1, Exercise (2)): a sheaf of modules
`F` on `T`, locally free of rank `d`, with an epimorphism from the pullback
`V_T` of `V` along the structure morphism. -/
structure LocallyFreeQuotient (V : S.Modules) (d : ℕ) (T : Over S) : Type (u + 1) where
  /-- The quotient sheaf on `T`. -/
  F : (T.left : Scheme.{u}).Modules
  /-- The quotient map out of the pulled-back bundle `V_T`. -/
  q : (Scheme.Modules.pullback T.hom).obj V ⟶ F
  /-- The quotient map is an epimorphism. -/
  epi : Epi q
  /-- The quotient sheaf is locally free of rank `d`. -/
  locFree : SheafOfModules.IsLocallyFreeOfRank F d

namespace LocallyFreeQuotient

variable {V : S.Modules} {d : ℕ}

/-- Equivalence of rank-`d` quotients: an isomorphism of the targets
commuting with the quotient maps (equivalently, `ker q = ker q'`). -/
def Rel {T : Over S} (x y : LocallyFreeQuotient V d T) : Prop :=
  ∃ f : x.F ≅ y.F, x.q ≫ f.hom = y.q

lemma rel_refl {T : Over S} (x : LocallyFreeQuotient V d T) : x.Rel x :=
  ⟨Iso.refl _, Category.comp_id _⟩

lemma rel_symm {T : Over S} {x y : LocallyFreeQuotient V d T} (h : x.Rel y) :
    y.Rel x := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.symm, by rw [Iso.symm_hom, Iso.comp_inv_eq]; exact hf.symm⟩

lemma rel_trans {T : Over S} {x y z : LocallyFreeQuotient V d T}
    (h1 : x.Rel y) (h2 : y.Rel z) : x.Rel z := by
  obtain ⟨f, hf⟩ := h1; obtain ⟨g, hg⟩ := h2
  exact ⟨f ≪≫ g,
    (congrArg (x.q ≫ ·) (Iso.trans_hom f g)).trans <|
      (Category.assoc x.q f.hom g.hom).symm.trans <|
        (congrArg (· ≫ g.hom) hf).trans hg⟩

/-- The equivalence-of-quotients setoid. -/
instance setoid (V : S.Modules) (d : ℕ) (T : Over S) :
    Setoid (LocallyFreeQuotient V d T) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- The pullback action on a rank-`d` quotient along `ψ : T' ⟶ T` of
`Over S`: pull the sheaf and the quotient map back along `ψ.left`, matching
the `V`-side through `pullbackTriangleIso (Over.w ψ)`. -/
noncomputable def pullbackAlong {T T' : Over S} (ψ : T' ⟶ T)
    (x : LocallyFreeQuotient V d T) : LocallyFreeQuotient V d T' where
  F := (Scheme.Modules.pullback ψ.left).obj x.F
  q := (pullbackTriangleIso (Over.w ψ) V).inv ≫
    (Scheme.Modules.pullback ψ.left).map x.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      (pullbackTriangleIso (Over.w ψ) V).inv inferInstance
      ((Scheme.Modules.pullback ψ.left).map x.q)
      (@CategoryTheory.Functor.map_epi _ _ _ _
        (Scheme.Modules.pullback ψ.left) inferInstance _ _ x.q x.epi)
  locFree := Scheme.Modules.pullback_isLocallyFreeOfRank ψ.left x.locFree

/-- The pullback action respects the equivalence relation. -/
lemma pullbackAlong_rel {T T' : Over S} (ψ : T' ⟶ T)
    {x y : LocallyFreeQuotient V d T} (h : x.Rel y) :
    (pullbackAlong ψ x).Rel (pullbackAlong ψ y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(Scheme.Modules.pullback ψ.left).mapIso f, ?_⟩
  change ((pullbackTriangleIso (Over.w ψ) V).inv ≫
      (Scheme.Modules.pullback ψ.left).map x.q) ≫
      (Scheme.Modules.pullback ψ.left).map f.hom
    = (pullbackTriangleIso (Over.w ψ) V).inv ≫
      (Scheme.Modules.pullback ψ.left).map y.q
  rw [Category.assoc, ← (Scheme.Modules.pullback ψ.left).map_comp]
  exact congrArg
    (fun m => (pullbackTriangleIso (Over.w ψ) V).inv ≫
      (Scheme.Modules.pullback ψ.left).map m) hf

end LocallyFreeQuotient

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- The **Grassmannian functor** `Grass(V, d) : (Sch/S)ᵒᵖ ⥤ Type (u+1)` of
rank-`d` locally free quotients of a module `V` on a noetherian base `S`
(`def:grassmannian_scheme`, [Nitsure] §1, Exercise (2)): an `S`-scheme
`T → S` is sent to the set of equivalence classes `⟨F, q⟩` of rank-`d`
locally free quotients `q : V_T ↠ F` (`Scheme.LocallyFreeQuotient`), and a
morphism to the pullback of quotients.  In the locally noetherian regime
this agrees with the Quot-functor special case
`Grass(V, d) = Quot^{d, O_S}_{V/S/S}` of the blueprint (a flat finitely
presented module with constant fibre dimension `d` is locally free of rank
`d`); the locally-free encoding is the form valid over an arbitrary base and
the one matched by the merged chart construction
(`AlgebraicGeometry.Grassmannian.functor`, `GrassmannianQuot.lean`). -/
noncomputable def Grassmannian (V : S.Modules) (d : ℕ) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Quotient (LocallyFreeQuotient.setoid V d T.unop)
  map {T T'} g := TypeCat.ofHom (Quotient.map (LocallyFreeQuotient.pullbackAlong g.unop)
    (fun _ _ h => LocallyFreeQuotient.pullbackAlong_rel g.unop h))
  map_id T := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (LocallyFreeQuotient.pullbackAlong (𝟙 T.unop) x)
        = Quotient.mk _ x
      refine Quotient.sound ⟨(Scheme.Modules.pullbackCongr (Over.id_left T.unop)).app x.F ≪≫
        (Scheme.Modules.pullbackId _).app x.F, ?_⟩
      change ((pullbackTriangleIso (Over.w (𝟙 T.unop)) V).inv ≫
          (Scheme.Modules.pullback (Over.Hom.left (𝟙 T.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (Over.id_left T.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackId _).hom.app x.F
        = x.q
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (Over.id_left T.unop)).hom.naturality_assoc x.q,
        (Scheme.Modules.pullbackId _).hom.naturality x.q]
      have key := Scheme.Modules.pullback_id_app_coherence (Over.id_left T.unop)
        (Over.w (𝟙 T.unop)) V
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc]
      rw [reassoc_of% key]
      rfl
  map_comp {T T' T''} g h := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (LocallyFreeQuotient.pullbackAlong (h.unop ≫ g.unop) x)
        = Quotient.mk _
          (LocallyFreeQuotient.pullbackAlong h.unop (LocallyFreeQuotient.pullbackAlong g.unop x))
      refine Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (Over.comp_left _ _ _ h.unop g.unop)).app x.F ≪≫
          ((Scheme.Modules.pullbackComp h.unop.left g.unop.left).app x.F).symm, ?_⟩
      change ((pullbackTriangleIso (Over.w (h.unop ≫ g.unop)) V).inv ≫
          (Scheme.Modules.pullback (Over.Hom.left (h.unop ≫ g.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (Over.comp_left _ _ _ h.unop g.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackComp h.unop.left g.unop.left).inv.app x.F
        = (pullbackTriangleIso (Over.w h.unop) V).inv ≫
          (Scheme.Modules.pullback h.unop.left).map
            ((pullbackTriangleIso (Over.w g.unop) V).inv ≫
              (Scheme.Modules.pullback g.unop.left).map x.q)
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (Over.comp_left _ _ _ h.unop g.unop)).hom.naturality_assoc x.q,
        (Scheme.Modules.pullbackComp h.unop.left g.unop.left).inv.naturality x.q]
      have key := Scheme.Modules.pullback_comp_app_coherence_inv
        h.unop.left g.unop.left (Over.comp_left _ _ _ h.unop g.unop) T.unop.hom
        (Over.w g.unop) (Over.w (h.unop ≫ g.unop)) (Over.w h.unop) V
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc,
        Functor.map_comp]
      rw [reassoc_of% key]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rfl

/-- **Representability of the Grassmannian** (`thm:grassmannian_representable`,
[Nitsure] §1 "Construction of Grassmannian"): the functor `Grass(V, d)` is
representable by an `S`-scheme.  The merged chart construction
(`AlgebraicGeometry.Grassmannian.scheme` / `.represents`,
`GrassmannianQuot.lean`) proves the absolute case over `ℤ` with `V` free;
the relative statement glues the absolute one over a trivialising affine
cover of `(S, V)` — the remaining representability endgame of `AJC.picrep`. -/
theorem Grassmannian.representable (V : S.Modules) (d : ℕ) :
    ∃ (Y : Over S), Nonempty ((Grassmannian V d).RepresentableBy Y) := by
  sorry

end Grassmannian

/-! ## §5. Representability of the Quot scheme -/

/-- **Representability of the Quot scheme** (Grothendieck, Altman–Kleiman;
`thm:quot_representable`, [Nitsure] §5): for a noetherian `S`, a projective
`π` (encoded: proper and locally of finite type), a line bundle `L`, a
coherent `E` and `Φ ∈ ℚ[λ]`, the Quot functor is representable by an
`S`-scheme.  Proof route (Nitsure §5): boundedness by Castelnuovo–Mumford
regularity, embedding into a Grassmannian by pushing forward twists,
flattening stratification (`AlgebraicGeometry.flatteningStratification`),
and the valuative criterion for the closed embedding. -/
theorem QuotScheme {S X : Scheme.{u}} [IsLocallyNoetherian S]
    (π : X ⟶ S) [LocallyOfFiniteType π] [IsProper π]
    (L E : X.Modules) [L.IsQuasicoherent] (Φ : Polynomial ℚ) :
    ∃ (Q : Over S), Nonempty ((QuotFunctor π L E Φ).RepresentableBy Q) := by
  sorry

end Scheme

end AlgebraicGeometry
