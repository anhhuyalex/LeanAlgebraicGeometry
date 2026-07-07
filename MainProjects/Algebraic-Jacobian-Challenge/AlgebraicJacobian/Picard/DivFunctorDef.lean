/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.QuotFunctorDef
import AlgebraicJacobian.Picard.LineBundlePullback
import AlgebraicJacobian.Picard.FlatKernelBase

/-!
# The relative-divisor functor `Div_{X/S}` (real definition)

This file constructs the relative-effective-divisor functor
`AlgebraicGeometry.Scheme.DivFunctor π : (Sch/S)ᵒᵖ ⥤ Type (u+1)` of Kleiman,
"The Picard scheme", §3 (Def. `df:red` + Def. `df:div`; FGA Explained Ch. 9,
arXiv:math/0504020), the source of the Abel map of the A.2.c FGA assembly
(`Picard/FGAPicRepresentability.lean`, whose `divFunctor` carrier this file
makes real).

## Encoding decision (quotient encoding)

Kleiman §3 Def. `df:red`/`df:div`: a *relative effective divisor* on `X_T/T`
is a closed subscheme `D ⊆ X_T` whose ideal `I` is **invertible** and which is
**`T`-flat**; `Div_{X/S}(T)` is the set of such `D`.  We encode a divisor by
its structure-sheaf quotient — the same encoding by which `Div ⊆ Hilb =
Quot_{O}` sits inside the Quot functor (Kleiman §3 Thm. `th:repDiv`): a
`DivFamily π T` is a `Scheme.QuotFamily`-shaped structure with `E` the unit
module `O_X` (so `q : O_{X_T} ⟶ F` up to the canonical isomorphism
`(pr₁)^* O_X ≅ O_{X_T}`; we state the source of `q` verbatim as the pullback
of the unit, exactly as `QuotFamily` does for a general `E`, so that the whole
pullback/functoriality skeleton of `QuotFunctorDef.lean` is reusable), and the
**divisor condition** is: the kernel ideal `I = ker q` is invertible, encoded
by the project-side line-bundle predicate
`Scheme.LineBundle.IsLocallyTrivial (kernel q)` (locally trivial of rank one,
Stacks 01HK — the same predicate that carves the line bundles out of
`Scheme.Modules` in `Picard/LineBundlePullback.lean`).  Between the two
candidate encodings of invertibility (a bundled mono `ι : I ⟶ O` with a
cokernel identification, versus the predicate on the categorical kernel) we
choose the **kernel predicate**: `X.Modules` is abelian, so `ker q` is
available functorially with no extra data fields, the equivalence relation on
families stays literally that of the Quot functor (`ker q = ker q'` — no
well-definedness burden for extra fields), and invertibility-of-an-object is
exactly what `IsLocallyTrivial` and its proved pullback-stability
(`IsLocallyTrivial.pullback`, Stacks 01HH) speak about.

Two families are equivalent iff an isomorphism of the targets commutes with
the quotient maps — equivalently `ker q = ker q'` as subobjects of `O_{X_T}`,
i.e. the two quotients cut out the same closed subscheme `D`.  The value
`DivFunctor π |_T` is the quotient by this relation, so it is Kleiman's *set*
of relative effective divisors on `X_T/T`, not a groupoid of quotients.

Faithfulness notes (Kleiman §3):

* the fields `isFinitePresentation` and `properSupport` do not shrink the set
  of divisors in the intended regime: `F = O_D = coker(I ⟶ O)` with `I`
  invertible is automatically finitely presented, and for the FGA
  instantiation (`π` proper, e.g. the curve `C/k`) the schematic support `D`
  is a closed subscheme of the `T`-proper `X_T`, hence automatically proper
  over `T`.  They are included to keep the family shape identical to
  `QuotFamily` (Div sits inside Hilb) and to reuse its base-change lemmas
  verbatim;
* there is **no Hilbert-polynomial field**: Kleiman's `Div_{X/S}` (`df:div`)
  is not filtered by `Φ` — the degree decomposition `Div = ∐_m Div^m`
  (Kleiman §3 Ex. `ex:DivC`) is a later, separate refinement;
* no hypotheses on `π` are needed for the *functor* (Kleiman `df:div` imposes
  none; projectivity/flatness enter only in the representability theorem
  `th:repDiv`, which is not stated in this file).

## Base-change well-definedness

The pullback action reuses the `QuotFamily` base-change lemmas for the shared
fields (finite presentation: `Modules.pullback_isFinitePresentation`, proved;
flatness: `CoherentSheafFlat.of_isPullback`, proved; proper support:
`Modules.HasProperSupport.of_isPullback`, pinned leaf) and needs exactly ONE
new fact for the divisor condition, recorded as the named typed-`sorry` leaf
`Scheme.Modules.pullback_kernel_isLocallyTrivial` (blueprint
`lem:relative_divisor_base_change`): the kernel of the pulled-back quotient
is the pullback of the kernel — because `0 → I → O → O_D → 0` stays exact
after base change, `Tor_1` against the `T`-flat `O_D` vanishing (Kleiman §3,
functoriality note after `df:div`: "Since `D` is `T`-flat, `p_{X_T}^* I`
equals the ideal of `D_{T'}`") — and pullback preserves invertibility
(`IsLocallyTrivial.pullback`, Stacks 01HH).  The leaf carries a
quasi-coherence hypothesis on the source of the quotient (removable once
extension-closure of quasi-coherence, Stacks 01LA, is available; see the
declaration docstring), discharged here by `pullback_isQuasicoherent_hom` +
`Modules.unit_isQuasicoherent` since the source is the pulled-back unit.
The supporting bricks — the Stacks 00HL algebra heart
`Module.Flat.rTensor_injective_of_exact`, the comparison map
`Modules.pullbackKernelComparison`, and the chart-shrinking lemmas — live in
`Picard/FlatKernelBase.lean`; the derivation of the pinned statement from
the isomorphism form of the comparison is
`Modules.pullback_kernel_isLocallyTrivial_of_isIso_kernelComparison` (§0).

The functor laws are verbatim the pseudofunctor-coherence argument of
`Scheme.QuotFunctor` (`Modules.pullback_id_app_coherence`,
`Modules.pullback_comp_app_coherence_inv`), which was stated in
`QuotFunctorDef.lean` for arbitrary modules and so applies to the unit.

## References

Blueprint: `def:div_family`, `lem:relative_divisor_base_change`,
`def:div_functor` (`blueprint/src/chapters/Picard_QuotScheme.tex`);
consumed by `def:div_functor_carrier`
(`blueprint/src/chapters/Picard_FGAPicRepresentability.tex`).
Source: [Kleiman], "The Picard scheme", §3 (arXiv:math/0504020).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme

/-! ## §0. Invertibility is invariant under isomorphism -/

/-- **Local triviality of rank one is invariant under isomorphism.**  If
`M ≅ N` in `X.Modules` and `M` is locally trivial of rank one
(`Scheme.LineBundle.IsLocallyTrivial`, Stacks 01HK), then so is `N`: restrict
the isomorphism to each trivialising affine chart of `M` (restriction along
an open immersion is functorial). -/
lemma LineBundle.IsLocallyTrivial.of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (hM : LineBundle.IsLocallyTrivial M) :
    LineBundle.IsLocallyTrivial N := by
  intro x
  obtain ⟨U, hxU, hUaff, ⟨t⟩⟩ := hM x
  exact ⟨U, hxU, hUaff, ⟨(Scheme.Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ t⟩⟩

/-- **Read-off along the kernel–pullback comparison**: if the comparison map
`Scheme.Modules.pullbackKernelComparison g' q : g'^*(ker q) ⟶ ker (g'^* q)`
(`Picard/FlatKernelBase.lean`) is an isomorphism, then local triviality of
`ker q` transports to `ker (g'^* q)`: pullback preserves local triviality
(`IsLocallyTrivial.pullback`, Stacks 01HH) and local triviality is invariant
under isomorphism (`IsLocallyTrivial.of_iso`).  This derives the pinned
base-change statement `Modules.pullback_kernel_isLocallyTrivial` from the
isomorphism form of the comparison (the route of blueprint
`lem:relative_divisor_base_change`). -/
lemma Modules.pullback_kernel_isLocallyTrivial_of_isIso_kernelComparison
    {X' X : Scheme.{u}} (g' : X' ⟶ X) {E F : X.Modules} (q : E ⟶ F)
    (hcomp : IsIso (Modules.pullbackKernelComparison g' q))
    (hker : LineBundle.IsLocallyTrivial (Limits.kernel q)) :
    LineBundle.IsLocallyTrivial
      (Limits.kernel ((Scheme.Modules.pullback g').map q)) :=
  haveI := hcomp
  LineBundle.IsLocallyTrivial.of_iso
    (asIso (Modules.pullbackKernelComparison g' q))
    (hker.pullback g')

/-! ## §1. Base change of the ideal of a relative effective divisor

The one NEW base-change fact the divisor functor needs beyond the Quot-family
lemmas of `QuotFunctorDef.lean` §2: the invertible kernel ideal of a `T`-flat
quotient of `O` pulls back to the (again invertible) kernel ideal of the
pulled-back quotient.  Blueprint node: `lem:relative_divisor_base_change`. -/

/-- **The invertible kernel of a base-flat quotient stays invertible under
base change** (Kleiman §3, the functoriality of `Div_{X/S}` — the note after
Def. `df:div`: "Since `D` is `T`-flat, `p_{X_T}^* \mathcal I` equals the
ideal of `D_{T'}`.  But, since `\mathcal I` is invertible, so is
`p_{X_T}^* \mathcal I`").

For a cartesian square `sq : X' = X ×_S S'` and an epimorphism `q : E ⟶ F` of
`O_X`-modules with `E` quasi-coherent and `F` finitely presented and flat
over `S` (`Scheme.CoherentSheafFlat`), if `ker q` is locally trivial of rank
one then so is `ker (g'^* q)`.  Mathematical content: the short exact
sequence `0 → ker q → E → F → 0` stays exact after applying the right-exact
`g'^*`, because affine-locally the failure of left exactness is
`Tor_1^{Γ(S,U)}(Γ(F,V), Γ(S',U_t))`, which vanishes by base-flatness of `F`
(Stacks 00HL, `Module.Flat.rTensor_injective_of_exact`);
hence `ker (g'^* q) ≅ g'^* (ker q)`, and pullback preserves local triviality
of rank one (`Scheme.LineBundle.IsLocallyTrivial.pullback`, Stacks 01HH).
See the blueprint node `lem:relative_divisor_base_change` for the complete
proof.

The hypothesis `hE : E.IsQuasicoherent` is needed by the affine-local section
calculus (`pullback_app_isoTensor`); the statement is true without it —
`E` is an extension of the quasi-coherent `F` by the locally trivial (hence
quasi-coherent, `LineBundle.IsLocallyTrivial.isFinitePresentation`) `ker q`,
and an extension of quasi-coherents is quasi-coherent (Stacks 01LA) — but
extension-closure of `IsQuasicoherent` is not yet available, and the sole
consumer (`DivFamily.pullbackAlong`) instantiates `E` at a pullback of the
unit module, quasi-coherent by `pullback_isQuasicoherent_hom` +
`Modules.unit_isQuasicoherent`. -/
theorem Modules.pullback_kernel_isLocallyTrivial
    {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    (sq : IsPullback g' f' f g) {E F : X.Modules} (q : E ⟶ F) (hq : Epi q)
    (hE : E.IsQuasicoherent)
    (hfp : F.IsFinitePresentation) (hflat : CoherentSheafFlat f F)
    (hker : LineBundle.IsLocallyTrivial (Limits.kernel q)) :
    LineBundle.IsLocallyTrivial
      (Limits.kernel ((Scheme.Modules.pullback g').map q)) := by
  -- The comparison `κ = pullbackKernelComparison g' q : g'^*(ker q) ⟶ ker (g'^* q)`
  -- is always epi (`q` epi, `g'^*` right exact: `epi_pullbackKernelComparison`).
  -- Once `κ` is shown to be an isomorphism, the read-off lemma
  -- `pullback_kernel_isLocallyTrivial_of_isIso_kernelComparison` (§0) transports the
  -- rank-one local triviality of `ker q` across it.  By
  -- `isIso_pullbackKernelComparison_of_mono` (`FlatKernelBase.lean`) `κ` is an iso as
  -- soon as `g'^*` keeps the kernel inclusion `ker q ↪ E` monic, so the ENTIRE
  -- remaining content is the single flat-base-change monomorphism below.
  haveI := hq
  refine Modules.pullback_kernel_isLocallyTrivial_of_isIso_kernelComparison g' q
    (Modules.isIso_pullbackKernelComparison_of_mono g' q ?_) hker
  -- **REMAINING (Stacks 00HL, blueprint `lem:relative_divisor_base_change`):**
  -- `g'^*` preserves the kernel inclusion `ker q ↪ E` as a monomorphism, because the
  -- cokernel `F` is `S`-flat.  Affine-locally on a piece `W = g'⁻¹V ⊓ f'⁻¹Ut` over a
  -- trivialising affine `V` this is `Module.Flat.rTensor_injective_of_exact`
  -- (`FlatKernelBase.lean`) applied to the section SES
  -- `0 → Γ(ker q, V) → Γ(E, V) → Γ(F, V) → 0` tensored with `Γ(S', Ut)` over
  -- `Γ(S, U)` (`Γ(F, V)` flat, so `Tor₁` vanishes and the left map stays injective);
  -- section-surjectivity of `Γ(E,V) → Γ(F,V)` over the trivialising affine is the
  -- `H¹(V, ker q) = 0` content, and the section base-change identifications are the
  -- `pullback_app_isoTensor` calculus.  Globalisation is stalk-/basis-local
  -- (`Modules.isIso_of_isIso_app_of_isBasis`), using `exists_affine_trivializing_le`
  -- to shrink `V` into each piece.  Hypotheses `sq`, `hE`, `hfp`, `hflat` feed this step.
  sorry

/-! ## §2. Families of relative effective divisors -/

variable {S X : Scheme.{u}}

/-- A **family of relative effective divisors on `X ×_S T / T`** (Kleiman §3
Def. `df:red`/`df:div`, in the quotient encoding — see the module docstring):
a `T`-flat, finitely presented quotient `q` of the structure sheaf of the
relative product `X_T = X ×_S T` with proper support, whose kernel ideal
`I = ker q` is invertible (`Scheme.LineBundle.IsLocallyTrivial`).  The
associated divisor is the schematic support `D` of `F = O_{X_T}/I = O_D`;
conversely a relative effective divisor `D ⊆ X_T` yields the family
`q : O_{X_T} ↠ O_D`.

The source of `q` is stated as the pullback of the unit module `O_X` along
the first projection — canonically isomorphic to `O_{X_T}` — verbatim the
`E`-slot of `Scheme.QuotFamily` at `E = O_X`, so the Quot-family base-change
lemmas and pseudofunctor-coherence functor laws apply unchanged.  The fields
`isFinitePresentation` and `properSupport` are automatic for divisors on a
`T`-proper `X_T` (the FGA regime); see the module docstring. -/
structure DivFamily (π : X ⟶ S) (T : Over S) : Type (u + 1) where
  /-- The structure sheaf `O_D` of the divisor, as a quotient module on the
  relative product `X ×_S T`. -/
  F : (Limits.pullback π T.hom).Modules
  /-- `F` is finitely presented (automatic for an invertible ideal's
  quotient; kept to match the Quot-family shape). -/
  isFinitePresentation : F.IsFinitePresentation
  /-- `F = O_D` is flat over `T` — the divisor is a *relative* effective
  divisor (Kleiman §3 Def. `df:red`). -/
  flat : CoherentSheafFlat (pullback.snd π T.hom) F
  /-- The schematic support (the divisor `D` itself) is proper over `T`
  (automatic when `π` is proper; kept to match the Quot-family shape). -/
  properSupport : Modules.HasProperSupport (pullback.snd π T.hom) F
  /-- The quotient map `O_{X_T} ⟶ O_D` (source stated as the pulled-back
  unit, as in `QuotFamily` with `E = O_X`). -/
  q : (Scheme.Modules.pullback (pullback.fst π T.hom)).obj
      (SheafOfModules.unit X.ringCatSheaf) ⟶ F
  /-- The quotient map is an epimorphism. -/
  epi : Epi q
  /-- **The divisor condition** (Kleiman §3 Def. `df:red`): the kernel ideal
  `I = ker q` is invertible, i.e. locally trivial of rank one. -/
  kerLocallyTrivial : LineBundle.IsLocallyTrivial (Limits.kernel q)

namespace DivFamily

variable {π : X ⟶ S}

/-- Two families of divisors are **equivalent** when an isomorphism of the
target sheaves commutes with the quotient maps — equivalently, when
`ker q = ker q'` as subobjects of `O_{X_T}`, i.e. when they cut out the same
closed subscheme (same convention as `QuotFamily.Rel`). -/
def Rel {T : Over S} (x y : DivFamily π T) : Prop :=
  ∃ f : x.F ≅ y.F, x.q ≫ f.hom = y.q

lemma rel_refl {T : Over S} (x : DivFamily π T) : x.Rel x :=
  ⟨Iso.refl _, Category.comp_id _⟩

lemma rel_symm {T : Over S} {x y : DivFamily π T} (h : x.Rel y) : y.Rel x := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.symm, by rw [Iso.symm_hom, Iso.comp_inv_eq]; exact hf.symm⟩

lemma rel_trans {T : Over S} {x y z : DivFamily π T}
    (h1 : x.Rel y) (h2 : y.Rel z) : x.Rel z := by
  obtain ⟨f, hf⟩ := h1; obtain ⟨g, hg⟩ := h2
  exact ⟨f ≪≫ g,
    (congrArg (x.q ≫ ·) (Iso.trans_hom f g)).trans <|
      (Category.assoc x.q f.hom g.hom).symm.trans <|
        (congrArg (· ≫ g.hom) hf).trans hg⟩

/-- The equivalence-of-families setoid. -/
instance setoid (π : X ⟶ S) (T : Over S) : Setoid (DivFamily π T) where
  r := Rel
  iseqv := ⟨rel_refl, rel_symm, rel_trans⟩

/-- The **pullback action** on a family of divisors along `ψ : T' ⟶ T` of
`Over S`: pull the sheaf and the quotient map back along
`quotBaseMap π ψ : X_{T'} ⟶ X_T`, matching the `O`-side through
`pullbackTriangleIso (quotBaseMap_fst π ψ)` — exactly
`QuotFamily.pullbackAlong` at `E = O_X`.  The divisor condition base-changes
by `Modules.pullback_kernel_isLocallyTrivial`
(`lem:relative_divisor_base_change`). -/
noncomputable def pullbackAlong {T T' : Over S} (ψ : T' ⟶ T)
    (x : DivFamily π T) : DivFamily π T' where
  F := (Scheme.Modules.pullback (quotBaseMap π ψ)).obj x.F
  isFinitePresentation :=
    Modules.pullback_isFinitePresentation _ x.F x.isFinitePresentation
  flat := fun {U} hU {V} hV e =>
    CoherentSheafFlat.of_isPullback (quotBaseSquare π ψ) x.F
      (letI := x.isFinitePresentation; inferInstance) x.flat hU hV e
  properSupport :=
    Modules.HasProperSupport.of_isPullback (quotBaseSquare π ψ) x.F
      x.isFinitePresentation x.properSupport
  q := (pullbackTriangleIso (quotBaseMap_fst π ψ)
      (SheafOfModules.unit X.ringCatSheaf)).inv ≫
    (Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q
  epi :=
    @CategoryTheory.epi_comp _ _ _ _ _
      (pullbackTriangleIso (quotBaseMap_fst π ψ)
        (SheafOfModules.unit X.ringCatSheaf)).inv inferInstance
      ((Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q)
      (@CategoryTheory.Functor.map_epi _ _ _ _
        (Scheme.Modules.pullback (quotBaseMap π ψ)) inferInstance _ _ x.q x.epi)
  kerLocallyTrivial :=
    LineBundle.IsLocallyTrivial.of_iso
      (kernelIsIsoComp
        (pullbackTriangleIso (quotBaseMap_fst π ψ)
          (SheafOfModules.unit X.ringCatSheaf)).inv
        ((Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q)).symm
      (Modules.pullback_kernel_isLocallyTrivial (quotBaseSquare π ψ) x.q x.epi
        (pullback_isQuasicoherent_hom (pullback.fst π T.hom)
          (SheafOfModules.unit X.ringCatSheaf) inferInstance)
        x.isFinitePresentation x.flat x.kerLocallyTrivial)

/-- The pullback action respects the equivalence relation. -/
lemma pullbackAlong_rel {T T' : Over S} (ψ : T' ⟶ T)
    {x y : DivFamily π T} (h : x.Rel y) :
    (pullbackAlong ψ x).Rel (pullbackAlong ψ y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(Scheme.Modules.pullback (quotBaseMap π ψ)).mapIso f, ?_⟩
  change ((pullbackTriangleIso (quotBaseMap_fst π ψ)
        (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map x.q) ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map f.hom
    = (pullbackTriangleIso (quotBaseMap_fst π ψ)
        (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map y.q
  rw [Category.assoc, ← (Scheme.Modules.pullback (quotBaseMap π ψ)).map_comp]
  exact congrArg
    (fun m => (pullbackTriangleIso (quotBaseMap_fst π ψ)
        (SheafOfModules.unit X.ringCatSheaf)).inv ≫
      (Scheme.Modules.pullback (quotBaseMap π ψ)).map m) hf

end DivFamily

/-! ## §3. The relative-divisor functor -/

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1600000 in
/-- The **relative-divisor functor** `Div_{X/S}` (Kleiman §3 Def. `df:div`):
the contravariant functor `(Sch/S)ᵒᵖ ⥤ Type (u+1)` sending an `S`-scheme
`T → S` to the set of relative effective divisors on `X_T/T` — encoded as
equivalence classes of families of invertible-kernel quotients of `O_{X_T}`
(`Scheme.DivFamily`; two families are identified iff `ker q = ker q'`, i.e.
iff they cut out the same divisor) — and a morphism to the pullback of
families (`DivFamily.pullbackAlong`).  The identity and composition laws are
the pseudofunctor coherence laws of the module pullback, packaged as
`Scheme.Modules.pullback_id_app_coherence` and
`Scheme.Modules.pullback_comp_app_coherence_inv` in `QuotFunctorDef.lean`. -/
noncomputable def DivFunctor (π : X ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := Quotient (DivFamily.setoid π T.unop)
  map {T T'} g := TypeCat.ofHom (Quotient.map (DivFamily.pullbackAlong g.unop)
    (fun _ _ h => DivFamily.pullbackAlong_rel g.unop h))
  map_id T := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (DivFamily.pullbackAlong (𝟙 T.unop) x) = Quotient.mk _ x
      refine Quotient.sound ⟨(Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).app x.F ≪≫
        (Scheme.Modules.pullbackId _).app x.F, ?_⟩
      change ((pullbackTriangleIso (quotBaseMap_fst π (𝟙 T.unop))
            (SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π (𝟙 T.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackId _).hom.app x.F
        = x.q
      rw [Category.assoc,
        (Scheme.Modules.pullbackCongr (quotBaseMap_id π T.unop)).hom.naturality_assoc x.q,
        (Scheme.Modules.pullbackId _).hom.naturality x.q]
      have key := Scheme.Modules.pullback_id_app_coherence (quotBaseMap_id π T.unop)
        (quotBaseMap_fst π (𝟙 T.unop)) (SheafOfModules.unit X.ringCatSheaf)
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc]
      rw [reassoc_of% key]
      rfl
  map_comp {T T' T''} g h := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (DivFamily.pullbackAlong (h.unop ≫ g.unop) x)
        = Quotient.mk _ (DivFamily.pullbackAlong h.unop (DivFamily.pullbackAlong g.unop x))
      refine Quotient.sound
        ⟨(Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).app x.F ≪≫
          ((Scheme.Modules.pullbackComp (quotBaseMap π h.unop) (quotBaseMap π g.unop)).app
            x.F).symm, ?_⟩
      change ((pullbackTriangleIso (quotBaseMap_fst π (h.unop ≫ g.unop))
            (SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π (h.unop ≫ g.unop))).map x.q) ≫
          (Scheme.Modules.pullbackCongr (quotBaseMap_comp π g.unop h.unop)).hom.app x.F ≫
          (Scheme.Modules.pullbackComp (quotBaseMap π h.unop) (quotBaseMap π g.unop)).inv.app
            x.F
        = (pullbackTriangleIso (quotBaseMap_fst π h.unop)
            (SheafOfModules.unit X.ringCatSheaf)).inv ≫
          (Scheme.Modules.pullback (quotBaseMap π h.unop)).map
            ((pullbackTriangleIso (quotBaseMap_fst π g.unop)
              (SheafOfModules.unit X.ringCatSheaf)).inv ≫
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
        (quotBaseMap_fst π h.unop) (SheafOfModules.unit X.ringCatSheaf)
      simp only [pullbackTriangleIso, Iso.trans_inv, Iso.app_inv, Category.assoc,
        Functor.map_comp]
      rw [reassoc_of% key]
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rfl

end Scheme

end AlgebraicGeometry
