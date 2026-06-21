/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Genus
import AlgebraicJacobian.RiemannRoch.WeilDivisor
import AlgebraicJacobian.RiemannRoch.OCofP
import AlgebraicJacobian.RiemannRoch.CurveKrullDim
import AlgebraicJacobian.Albanese.CoheightBridge

/-!
# The invertible sheaf `𝒪_C(D)` of a Weil divisor (RR.2_*)

This file is the **RR.2_*** satellite sub-build chapter for the project's
headline `genusZero_curve_iso_P1` (the "smooth proper geometrically
irreducible genus-`0` curve over `k̄` is isomorphic to `ℙ¹`" lemma in
`AlgebraicJacobian.AbelianVarietyRigidity`).

Together with `RR.1` (`WeilDivisor.lean`), `RR.2`
(`RRFormula.lean`), `RR.3` (`OCofP.lean`), and `RR.4`
(`RationalCurveIso.lean`), the present chapter forms the four-stage
sub-build closing the project's headline **RR bridge**.

The Hartshorne IV.1.3.5 chain consumed by `genusZero_curve_iso_P1` of
`AbelianVarietyRigidity.lean` relies on the invertible-sheaf functor
`𝒪_C(-) : Div(C) → 𝐒𝐡(C, 𝐌𝐨𝐝_k̄)` sending a Weil divisor
`D = Σᵢ nᵢ · [Pᵢ]` to its associated invertible sheaf `𝒪_C(D)` on `C`.

This file hosts the four pinned declarations of the chapter
`RiemannRoch_OcOfD.tex`:

1. `AlgebraicGeometry.Scheme.WeilDivisor.sheafOf` — the invertible sheaf
   `𝒪_C(D)` of a Weil divisor `D` on a smooth proper curve `C / k̄`,
   realised as Hartshorne's subsheaf of the function-field constant
   sheaf `K_C` (II §6 p. 144). Replaces the iter-174 typed-`sorry`
   placeholder currently living at `RiemannRoch/RRFormula.lean:168`.
2. `AlgebraicGeometry.Scheme.WeilDivisor.sheafOf_zero` — the zero
   divisor `D = 0` gives the structure sheaf `𝒪_C(0) = 𝒪_C`.
3. `AlgebraicGeometry.Scheme.WeilDivisor.sheafOf_singlePoint` — the
   closed-point specialisation `𝒪_C([P]) = lineBundleAtClosedPoint P`
   of `RR.3` (`OCofP.lean`).
4. `AlgebraicGeometry.Scheme.WeilDivisor.sheafOf_ses_single_add` — the
   Hartshorne IV.1.3 inductive-step short exact sequence
   `0 → 𝒪_C(D) → 𝒪_C(D + [P]) → k(P) → 0` consumed by Lane H's
   `RRFormula` induction.

## Status

The headline `sheafOf` now carries its **full** subsheaf-of-`K_C` body for the
general `D ≠ 0` branch: a per-open `Submodule k̄ K(C)` cut out by the order
conditions `-(D Q) ≤ ord_Q(f)` (or `f = 0`), bundled as a presheaf functor with
identity-on-`K(C)` restrictions and a complete sheaf-property proof via
stalk-locality / irreducibility of `C.left` (the `sheafOf.carrier*` private
helpers below, all sorry-free, generalising `RR.3`'s `lineBundleAtClosedPoint`).
The localized `Scheme.IsRegularInCodimensionOne C.left` witness (smooth ⟹ DVR at
codim-1 stalks) is now **CLOSED axiom-clean** (iter-014 S1b-wire): the global
instance `instIsRegularInCodimensionOneOfSmooth` assembles it from the
cotangent pin `finrank_cotangentSpace_stalk_eq_one_of_smooth` and the
curve-dimension bound `krullDim_curve_le_one` (both axiom-clean, imported from
`CurveKrullDim`), so `sheafOf` itself is now sorry-free.
The remaining `sorry`s are:
`sheafOf_singlePoint`'s strict-equality core (blocked on OCofP `private`
internals; would need a `≅` restatement); and `sheafOf_ses_single_add` (the full
skyscraper-cokernel SES). The construction is `noncomputable`.

**3-tier disclosure** (per iter-181 vocabulary): each of the four
declarations is a **Tier-3 honest typed sorry** — the body is a
substantive mathematical construction (Hartshorne subsheaf-of-`K_C`)
whose closure is iter-184+ work; the types encode genuine claims about
the invertible sheaf, its specialisations, and its SES additivity.

## References

Blueprint: `blueprint/src/chapters/RiemannRoch_OcOfD.tex`.
Source: Hartshorne, *Algebraic Geometry*, II §6 pp. 144–145 (definition of
`ℒ(D)`; Propositions 6.13, 6.15, 6.18; Remark 6.17.1) and IV §1 p. 296
(the `D ↝ D + [Y]` SES). Stacks Project tags 02RW (Weil divisors),
0AUW (sheaf `𝒪_X(D)`), 0BE3 (degree-zero of a principal divisor).
-/

set_option autoImplicit false

universe u

open CategoryTheory Limits TopCat
open scoped Classical

namespace AlgebraicGeometry

/-! ## §1. The invertible sheaf `𝒪_C(D)` of a Weil divisor -/

/-! ## Project-local Mathlib supplement — codimension-one regularity substrate

The general (`D ≠ 0`) branch of `sheafOf` requires every codimension-one stalk of
`C.left` to be a discrete valuation ring (the `Scheme.IsRegularInCodimensionOne`
hypothesis). This section builds the
smooth `⟹` regular `⟹` DVR chain at each codimension-one point, following the
blueprint chapter §"The codimension-one regularity substrate". Steps 2 and 3
below are axiom-clean and project-local (they package Mathlib lemmas that have no
single-call form); step 1 (smooth `⟹` regular local stalk, Stacks 056S/00TT) is a
genuine Mathlib gap and is documented in the task result. -/

/-- **Krull dimension of a stalk at a codimension-one point is one.** A direct
consequence of Mathlib's `ringKrullDim_stalk_eq_coheight`; project-local because
the coheight-`= 1` specialisation has no single-call Mathlib form. Blueprint:
`lem:coheight_eq_ringKrullDim_stalk`. -/
theorem ringKrullDim_stalk_eq_one_of_coheight_eq_one
    {X : Scheme.{u}} (x : X) (hx : Order.coheight x = 1) :
    ringKrullDim (X.presheaf.stalk x) = 1 := by
  rw [Scheme.ringKrullDim_stalk_eq_coheight X x, hx]
  rfl

/-- **A regular local domain of Krull dimension one is a discrete valuation
ring.** Cotangent-space route: `IsRegularLocalRing.iff_finrank_cotangentSpace`
reduces regularity to `dim_κ (m/m²) = dim R = 1`, then Mathlib's
`IsLocalRing.finrank_CotangentSpace_eq_one_iff` upgrades to
`IsDiscreteValuationRing`. Project-local: bridges the two Mathlib equivalences
that have no combined form. Blueprint: `lem:regularLocal_dim_one_isDVR`. -/
theorem isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsRegularLocalRing R]
    (h : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hfr := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp ‹IsRegularLocalRing R›
  rw [h] at hfr
  have hone : Module.finrank (IsLocalRing.ResidueField R)
      (IsLocalRing.CotangentSpace R) = 1 := by exact_mod_cast hfr
  exact IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hone

/-- **DVR stalk at a point with one-dimensional cotangent space** (the DVR
endpoint of the rational-point cotangent route, blueprint
`lem:stalk_isDVR_of_smooth` / `lem:finrank_cotangentSpace_eq_one_iff_isDVR`).

On an integral, locally Noetherian scheme `X`, a point `x` whose cotangent
space `m_x / m_x²` is one-dimensional over the residue field has a discrete
valuation ring stalk. Project-local because it packages the three stalk
typeclass facts (`IsLocalRing`, `IsNoetherianRing`, `IsDomain`) required by
Mathlib's `IsLocalRing.finrank_CotangentSpace_eq_one_iff` into a single
scheme-level entry point. This isolates the entire codimension-one DVR
substrate of `sheafOf` to the single numeric input
`finrank κ(x) (m_x/m_x²) = 1`, which on a smooth curve over `k̄` is supplied
at the (k̄-rational, by alg. closedness) codim-1 point via the conormal
isomorphism `m_x/m_x² ≅ Ω_{C/k̄,x} ⊗ κ(x)` (Hartshorne II.8.7) together with
local-freeness of rank one of `Ω_{C/k̄}` (Hartshorne II.8.15). -/
theorem isDiscreteValuationRing_stalk_of_finrank_cotangentSpace_eq_one
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] (x : X)
    (h : Module.finrank (IsLocalRing.ResidueField (X.presheaf.stalk x))
        (IsLocalRing.CotangentSpace (X.presheaf.stalk x)) = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) :=
  IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp h

/-- **DVR stalk at a codimension-one point of a smooth proper curve over `k̄`**
(blueprint `RiemannRoch_OcOfD.tex`, `lem:stalk_isDVR_of_smooth`).

For the smooth proper curve `C / k̄` and a point `x : C.left` of coheight one,
the stalk `C.left.presheaf.stalk x` is a discrete valuation ring. This is the
codimension-one regularity substrate of `sheafOf`, assembled from the three
axiom-clean ingredients now available: the cotangent pin
`finrank_cotangentSpace_stalk_eq_one_of_smooth` (S1b, iter-011), the
curve-dimension bound `krullDim_curve_le_one` (S1b, iter-013) and the in-file
DVR endpoint `isDiscreteValuationRing_stalk_of_finrank_cotangentSpace_eq_one`.
`IsLocallyNoetherian C.left` and `LocallyOfFiniteType C.hom` are derived on the
nose from properness, exactly as `sheafOf` does. -/
theorem isDiscreteValuationRing_stalk_of_smooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))} [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left]
    (x : C.left) (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (C.left.presheaf.stalk x) := by
  haveI : LocallyOfFiniteType C.hom := IsProper.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian C.left :=
    LocallyOfFiniteType.isLocallyNoetherian C.hom
  exact isDiscreteValuationRing_stalk_of_finrank_cotangentSpace_eq_one (X := C.left) x
    (finrank_cotangentSpace_stalk_eq_one_of_smooth x hx krullDim_curve_le_one)

/-- **A smooth proper curve over `k̄` is regular in codimension one**
(blueprint `RiemannRoch_OcOfD.tex`, `thm:smooth_isRegularInCodimOne`).

Every prime divisor `Y` of `C.left` carries a codimension-one witness
`Y.coheight : Order.coheight Y.point = 1`, so its stalk is a discrete valuation
ring by `isDiscreteValuationRing_stalk_of_smooth`. This is the global instance
consumed by `sheafOf` (and any other consumer of the codimension-one regularity
substrate). -/
instance instIsRegularInCodimensionOneOfSmooth
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))} [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [IsIntegral C.left] :
    Scheme.IsRegularInCodimensionOne C.left :=
  ⟨fun Y => isDiscreteValuationRing_stalk_of_smooth Y.point Y.coheight⟩

namespace Scheme.WeilDivisor

variable {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
  {C : Over (Spec (.of kbar))} [IsProper C.hom]
  [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] [IsIntegral C.left]

/-! ### Hartshorne subsheaf-of-`K_C` carrier for a general Weil divisor `D`

This block generalises the `lineBundleAtClosedPoint.carrier*` machinery of
`RR.3` (`OCofP.lean`) from a single closed point `P` to an arbitrary Weil
divisor `D = Σ_Q n_Q · [Q]`. A section of `𝒪_C(D)` over an open `U` is a
rational function `f ∈ K(C)` that is either `0` or satisfies the order
condition `ord_Q(f) ≥ −n_Q` at every prime divisor `Q` with `Q.point ∈ U`
(Hartshorne II §6 p. 144, the definition of `ℒ(D)` as a subsheaf of the
constant sheaf at the function field). The `{0} ∪ …` disjunctive shape (vs.
`RR.3`'s pure-`∧` shape) is necessary because for a divisor with a negative
coefficient `n_Q < 0` the bound `−n_Q` is positive, so the junk value
`ord_Q(0) = 0` no longer satisfies the bound automatically.

The closure proofs reduce to `Ring.ordFrac_add` (the non-archimedean
inequality on the DVR valuation) and `Ring.ordFrac_ge_one_of_ne_zero`
(scalars from `k̄` are units, hence order `≥ 0`); the sheaf property reduces
to stalk-locality of the order conditions, discharged exactly as in `RR.3`
via the `Subfunctor`-of-`K_C` packaging and irreducibility of `C.left`. -/

/-- **Carrier set** of `𝒪_C(D)` over an open `U`: rational functions that are
`0` or satisfy `ord_Q(f) ≥ −D(Q)` for every prime divisor `Q` with
`Q.point ∈ U`. -/
private def sheafOf.carrierSet
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ)
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    Set C.left.functionField :=
  { f | f = 0 ∨ ∀ Q : C.left.PrimeDivisor, Q.point ∈ U.unop.1 →
          -(D Q) ≤ Scheme.RationalMap.order Q f }

omit [IsAlgClosed kbar] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] in
/-- **Monotonicity of `carrierSet` in `U`**: a smaller open imposes fewer
order constraints, so the carrier on `U` is included in the carrier on `V`
when `V ⊆ U`. -/
private lemma sheafOf.carrierSet_mono
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ)
    {U V : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ}
    (hUV : V.unop.1 ⊆ U.unop.1) :
    sheafOf.carrierSet (C := C) D U ⊆ sheafOf.carrierSet (C := C) D V := by
  intro f hf
  rcases hf with rfl | hf
  · exact Or.inl rfl
  · exact Or.inr (fun Q hQV => hf Q (hUV hQV))

/-- **Carrier submodule** of `𝒪_C(D)` over an open `U`: the carrier set
upgraded to a `Submodule k̄ K(C)` via the three closure proofs. -/
private noncomputable def sheafOf.carrierSubmodule
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ)
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    Submodule kbar C.left.functionField where
  carrier := sheafOf.carrierSet (C := C) D U
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro a b (rfl | ha) (rfl | hb)
    · exact Or.inl (by simp)
    · exact Or.inr (by simpa using hb)
    · exact Or.inr (by simpa using ha)
    · by_cases hane : a = 0
      · subst hane; exact Or.inr (by simpa using hb)
      by_cases hbne : b = 0
      · subst hbne; exact Or.inr (by simpa using ha)
      by_cases hab : a + b = 0
      · exact Or.inl hab
      refine Or.inr (fun Q hQ => ?_)
      set R := C.left.presheaf.stalk Q.point
      have hMNZ : ∀ (x : C.left.functionField), x ≠ 0 →
          Ring.ordFrac R x ≠ 0 := fun x hx => by simp [hx]
      have hoa : Ring.ordFrac R a ≠ 0 := hMNZ a hane
      have hob : Ring.ordFrac R b ≠ 0 := hMNZ b hbne
      have hoab : Ring.ordFrac R (a + b) ≠ 0 := hMNZ _ hab
      have hmin : Ring.ordFrac R a ⊓ Ring.ordFrac R b ≤ Ring.ordFrac R (a + b) :=
        Ring.ordFrac_add (R := R) a b hab
      have hlog : (Ring.ordFrac R a ⊓ Ring.ordFrac R b).log ≤
          Scheme.RationalMap.order Q (a + b) := by
        rcases min_cases (Ring.ordFrac R a) (Ring.ordFrac R b) with
            ⟨heq, _⟩ | ⟨heq, _⟩
        · rw [heq]; exact (WithZero.log_le_log hoa hoab).mpr (heq ▸ hmin)
        · rw [heq]; exact (WithZero.log_le_log hob hoab).mpr (heq ▸ hmin)
      have hminbd : -(D Q) ≤ (Ring.ordFrac R a ⊓ Ring.ordFrac R b).log := by
        rcases min_cases (Ring.ordFrac R a) (Ring.ordFrac R b) with
            ⟨heq, _⟩ | ⟨heq, _⟩
        · rw [heq]; exact ha Q hQ
        · rw [heq]; exact hb Q hQ
      linarith
  smul_mem' := by
    intro c x hx
    rcases eq_or_ne c 0 with rfl | hc
    · simp only [zero_smul]; exact Or.inl rfl
    rcases hx with rfl | hx
    · simp only [smul_zero]; exact Or.inl rfl
    by_cases hx0 : x = 0
    · subst hx0; simp only [smul_zero]; exact Or.inl rfl
    refine Or.inr ?_
    have hsmul : c • x = (algebraMap kbar C.left.functionField c) * x :=
      Algebra.smul_def c x
    have hαne : (algebraMap kbar C.left.functionField c) ≠ 0 := by
      have hinj := FaithfulSMul.algebraMap_injective kbar C.left.functionField
      simpa using hinj.ne_iff.mpr hc
    have hMNZ : ∀ (Q : C.left.PrimeDivisor) (y : C.left.functionField),
        y ≠ 0 → Ring.ordFrac (C.left.presheaf.stalk Q.point) y ≠ 0 := by
      intro Q y hy; simp [hy]
    have key_alpha_ge : ∀ (Q : C.left.PrimeDivisor),
        0 ≤ Scheme.RationalMap.order Q
              (algebraMap kbar C.left.functionField c) := by
      intro Q
      set R := C.left.presheaf.stalk Q.point
      let β : R := (C.left.presheaf.germ (⊤ : C.left.Opens) Q.point trivial).hom
        ((Scheme.toModuleKSheaf.kToSection C
            (Opposite.op (⊤ : C.left.Opens))).hom c)
      have hα_eq : (algebraMap kbar C.left.functionField c) =
          algebraMap R C.left.functionField β := by
        change ((Scheme.germToFunctionField C.left (⊤ : C.left.Opens)).hom
            ((Scheme.toModuleKSheaf.kToSection C
                (Opposite.op (⊤ : C.left.Opens))).hom c)) =
            (C.left.presheaf.stalkSpecializes
              ((genericPoint_spec C.left).specializes trivial)).hom β
        rw [← TopCat.Presheaf.germ_stalkSpecializes_apply
          (h := (genericPoint_spec C.left).specializes trivial)]
      have hβne : β ≠ 0 := by
        intro hzero; apply hαne; rw [hα_eq, hzero, map_zero]
      have hαord_ne : Ring.ordFrac R
          (algebraMap kbar C.left.functionField c) ≠ 0 := hMNZ Q _ hαne
      have hge : (1 : WithZero (Multiplicative ℤ)) ≤
          Ring.ordFrac R (algebraMap kbar C.left.functionField c) := by
        rw [hα_eq]; exact Ring.ordFrac_ge_one_of_ne_zero hβne
      unfold Scheme.RationalMap.order
      rw [show (0 : ℤ) = WithZero.log (1 : WithZero (Multiplicative ℤ)) by simp]
      exact (WithZero.log_le_log (by norm_num) hαord_ne).mpr hge
    intro Q hQ
    rw [hsmul]
    set R := C.left.presheaf.stalk Q.point
    have hαnez := hMNZ Q _ hαne
    have hxnez := hMNZ Q x hx0
    unfold Scheme.RationalMap.order
    rw [map_mul, WithZero.log_mul hαnez hxnez]
    have hge := key_alpha_ge Q
    have hxn := hx Q hQ
    unfold Scheme.RationalMap.order at hge hxn
    linarith

/-- **Bot-trivialization submodule**: equals `⊥` at `U = ⊥` and `⊤` otherwise.
The factor `carrierSubmodule ⊓ trivAtBot` enforces `F(⊥) = 0`, required by the
`Opens.grothendieckTopology` sheaf condition (the empty cover of `⊥`). -/
private def sheafOf.trivAtBot
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    Submodule kbar C.left.functionField where
  carrier := {f | U.unop ≠ (⊥ : TopologicalSpace.Opens C.left.toTopCat) ∨ f = 0}
  zero_mem' := Or.inr rfl
  add_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl ha
    · exact Or.inl ha
    · exact Or.inl hb
    · right; rw [ha, hb]; ring
  smul_mem' := by
    rintro c x (hx | hx)
    · exact Or.inl hx
    · right; rw [hx]; simp

/-- **Sheaf-corrected carrier submodule** `carrierSubmodule D U ⊓ trivAtBot U`.
At `U ≠ ⊥` equals `carrierSubmodule D U`; at `U = ⊥` equals `⊥`. -/
private noncomputable def sheafOf.carrierSubmoduleSheaf
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ)
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    Submodule kbar C.left.functionField :=
  sheafOf.carrierSubmodule (C := C) D U ⊓ sheafOf.trivAtBot (C := C) U

/-- **Monotonicity of `carrierSubmoduleSheaf` in `U` when the target `V` is
non-empty.** -/
private lemma sheafOf.carrierSubmoduleSheaf_le
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ)
    {U V : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ}
    (hUV : V.unop.1 ⊆ U.unop.1)
    (hV : V.unop ≠ (⊥ : TopologicalSpace.Opens C.left.toTopCat)) :
    sheafOf.carrierSubmoduleSheaf (C := C) D U
      ≤ sheafOf.carrierSubmoduleSheaf (C := C) D V := by
  intro x ⟨hx_carr, _⟩
  exact ⟨sheafOf.carrierSet_mono (C := C) D hUV hx_carr, Or.inl hV⟩

/-- **Type-level Subfunctor presentation of the carrier** (generalising
`RR.3`'s `lineBundleAtClosedPoint.carrierTypeSubfunctor`). A section over `U`
is a constant function valued in `carrierSubmoduleSheaf D U`. -/
private noncomputable def sheafOf.carrierTypeSubfunctor
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) :
    CategoryTheory.Subfunctor
      (TopCat.presheafToType C.left.toTopCat C.left.functionField) where
  obj U := { g : U.unop → C.left.functionField |
    ∃ f : C.left.functionField,
      f ∈ sheafOf.carrierSubmoduleSheaf (C := C) D U ∧ g = fun _ => f }
  map := by
    classical
    intro U V i g hg
    obtain ⟨f, hf, hgf⟩ := hg
    by_cases hV : V.unop = (⊥ : TopologicalSpace.Opens C.left.toTopCat)
    · refine ⟨0, ?_, ?_⟩
      · exact (sheafOf.carrierSubmoduleSheaf (C := C) D V).zero_mem
      · funext x
        have hsub : (V.unop : Set C.left.toTopCat) ⊆ ∅ := by
          rw [show V.unop = ⊥ from hV]; simp
        exact absurd x.2 (fun h => hsub h)
    · refine ⟨f, ?_, ?_⟩
      · exact sheafOf.carrierSubmoduleSheaf_le (C := C) D
          (CategoryTheory.leOfHom i.unop) hV hf
      · subst hgf; rfl

/-- **The carrier presheaf of `𝒪_C(D)`**: bundles `carrierSubmoduleSheaf D U`
as a functor `(Opens C.left)ᵒᵖ ⥤ ModuleCat k̄`, with the restriction map the
zero map at `V = ⊥` and `Submodule.inclusion` otherwise. -/
private noncomputable def sheafOf.carrierPresheaf
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) :
    (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ ⥤ ModuleCat.{u} kbar where
  obj U := ModuleCat.of kbar ↥(sheafOf.carrierSubmoduleSheaf (C := C) D U)
  map {U V} f := ModuleCat.ofHom <| by
    classical
    by_cases hV : V.unop = (⊥ : TopologicalSpace.Opens C.left.toTopCat)
    · exact 0
    · exact Submodule.inclusion
        (sheafOf.carrierSubmoduleSheaf_le (C := C) D
          (CategoryTheory.leOfHom f.unop) hV)
  map_id U := by
    classical
    by_cases hU : U.unop = (⊥ : TopologicalSpace.Opens C.left.toTopCat)
    · ext ⟨x, hx⟩
      simp only [dif_pos hU]
      have h0 : x = 0 := by
        rcases hx.2 with hne | heq
        · exact (hne hU).elim
        · exact heq
      subst h0; rfl
    · ext ⟨x, _⟩
      simp only [dif_neg hU]; rfl
  map_comp {U V W} f g := by
    classical
    by_cases hW : W.unop = (⊥ : TopologicalSpace.Opens C.left.toTopCat)
    · ext ⟨x, _⟩
      simp only [dif_pos hW]
      by_cases hV : V.unop = (⊥ : TopologicalSpace.Opens C.left.toTopCat)
      · simp only [dif_pos hV]; rfl
      · simp only [dif_neg hV]; rfl
    · have hVW : W.unop.1 ⊆ V.unop.1 := CategoryTheory.leOfHom g.unop
      have hV : V.unop ≠ (⊥ : TopologicalSpace.Opens C.left.toTopCat) := by
        intro h; apply hW; apply le_antisymm
        · rw [← h]; exact CategoryTheory.leOfHom g.unop
        · exact bot_le
      ext ⟨x, _⟩
      simp only [dif_neg hW, dif_neg hV]; rfl

/-- **Sheaf property of `carrierPresheaf`** (generalising
`RR.3`'s `lineBundleAtClosedPoint.carrierPresheaf_isSheaf`). The order
conditions are stalk-local; the sheaf property follows from irreducibility of
`C.left` exactly as for the single-point case. -/
private lemma sheafOf.carrierPresheaf_isSheaf
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) :
    Presheaf.IsSheaf (Opens.grothendieckTopology C.left.toTopCat)
      (sheafOf.carrierPresheaf (C := C) D) := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := C.left.toTopCat)
    (F := sheafOf.carrierPresheaf (C := C) D)).mpr
  intro ι U sf hcompat
  have htrivBot : ∀ (V : TopologicalSpace.Opens C.left.toTopCat) (_hV : V = ⊥),
      sheafOf.trivAtBot (C := C) (Opposite.op V) = ⊥ := by
    intro V hV
    apply Submodule.ext
    intro f
    constructor
    · rintro (h | h)
      · exact (h hV).elim
      · exact h
    · intro h
      change V ≠ ⊥ ∨ f = 0
      exact Or.inr h
  have hcsBot : ∀ (V : TopologicalSpace.Opens C.left.toTopCat) (hV : V = ⊥),
      sheafOf.carrierSubmoduleSheaf (C := C) D (Opposite.op V) = ⊥ := by
    intro V hV
    change sheafOf.carrierSubmodule (C := C) D _ ⊓
      sheafOf.trivAtBot (C := C) _ = ⊥
    rw [htrivBot V hV, inf_bot_eq]
  have hSubAt0 : ∀ (V : TopologicalSpace.Opens C.left.toTopCat) (hV : V = ⊥)
      (s : ↥(sheafOf.carrierSubmoduleSheaf (C := C) D (Opposite.op V))),
      s.1 = 0 := by
    intro V hV s
    have h0 : s.1 ∈ (⊥ : Submodule kbar C.left.functionField) := by
      rw [← hcsBot V hV]; exact s.2
    exact (Submodule.mem_bot kbar).mp h0
  by_cases hSup : iSup U = (⊥ : TopologicalSpace.Opens C.left.toTopCat)
  · have hUi : ∀ i, U i = (⊥ : TopologicalSpace.Opens C.left.toTopCat) := by
      intro i
      apply le_antisymm _ bot_le
      calc U i ≤ iSup U := le_iSup U i
        _ = ⊥ := hSup
    refine ⟨⟨0, ?_⟩, ?_, ?_⟩
    · exact (sheafOf.carrierSubmoduleSheaf (C := C) D _).zero_mem
    · intro i
      have hsfi : (sf i).1 = 0 := hSubAt0 (U i) (hUi i) (sf i)
      apply Subtype.ext
      rw [hsfi]
      change (((sheafOf.carrierPresheaf (C := C) D).map
        (homOfLE (le_iSup U i)).op).hom ⟨0, _⟩).1 = 0
      exact hSubAt0 (U i) (hUi i) _
    · intro s' _
      apply Subtype.ext
      exact (hSubAt0 _ hSup s').trans rfl
  · have map_val : ∀ {Uo Vo : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ}
        (g : Uo ⟶ Vo) (hV : Vo.unop ≠ ⊥)
        (x : ↥(sheafOf.carrierSubmoduleSheaf (C := C) D Uo)),
        (((sheafOf.carrierPresheaf (C := C) D).map g).hom x).1 = x.1 := by
      intros Uo Vo g hV x
      simp only [sheafOf.carrierPresheaf, dif_neg hV, ModuleCat.hom_ofHom]
      rfl
    have hexists_ne_bot : ∃ i, U i ≠ ⊥ := by
      by_contra h
      exact hSup (iSup_eq_bot.mpr (fun i => not_not.mp (not_exists.mp h i)))
    obtain ⟨i₀, hUi₀⟩ := hexists_ne_bot
    set v : C.left.functionField := (sf i₀).1 with hv_def
    have hIrr : IrreducibleSpace ↑C.left := inferInstance
    have hPre : PreirreducibleSpace ↑C.left := hIrr.toPreirreducibleSpace
    have inter_ne_bot : ∀ i j, U i ≠ ⊥ → U j ≠ ⊥ →
        (U i ⊓ U j : TopologicalSpace.Opens C.left.toTopCat) ≠ ⊥ := by
      intro i j hi hj h
      apply (TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mpr h
      have ni : ((U i).1).Nonempty := by
        by_contra hh
        exact hi ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hh)
      have nj : ((U j).1).Nonempty := by
        by_contra hh
        exact hj ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp hh)
      exact @nonempty_preirreducible_inter _ _ _ _ hPre
        (U i).isOpen (U j).isOpen ni nj
    have key_val : ∀ i, U i ≠ ⊥ → (sf i).1 = v := by
      intro i hUi
      have hint : (U i ⊓ U i₀ : TopologicalSpace.Opens C.left.toTopCat) ≠ ⊥ :=
        inter_ne_bot i i₀ hUi hUi₀
      have hc := hcompat i i₀
      have h1 : (((sheafOf.carrierPresheaf (C := C) D).map
            (TopologicalSpace.Opens.infLELeft (U i) (U i₀)).op).hom (sf i)).1 = (sf i).1 :=
        map_val _ hint (sf i)
      have h2 : (((sheafOf.carrierPresheaf (C := C) D).map
            (TopologicalSpace.Opens.infLERight (U i) (U i₀)).op).hom (sf i₀)).1 = (sf i₀).1 :=
        map_val _ hint (sf i₀)
      have hc_val := congr_arg Subtype.val hc
      simp only at hc_val
      rw [h1, h2] at hc_val
      exact hc_val
    have hv_mem : v ∈ sheafOf.carrierSubmoduleSheaf (C := C) D
        (Opposite.op (iSup U)) := by
      refine ⟨?_, Or.inl hSup⟩
      by_cases hv0 : v = 0
      · exact Or.inl hv0
      refine Or.inr (fun Q hQ => ?_)
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hQ
      have hUi : U i ≠ ⊥ := by
        intro hh
        rw [hh] at hi
        exact (TopologicalSpace.Opens.mem_bot.mp hi).elim
      have hsfeq : (sf i).1 = v := key_val i hUi
      rcases (sf i).2.1 with h0 | hall
      · rw [hsfeq] at h0; exact absurd h0 hv0
      · rw [← hsfeq]; exact hall Q hi
    refine ⟨⟨v, hv_mem⟩, ?_, ?_⟩
    · intro i
      apply Subtype.ext
      by_cases hUi : U i = ⊥
      · have hsfi : (sf i).1 = 0 := hSubAt0 (U i) hUi (sf i)
        change (((sheafOf.carrierPresheaf (C := C) D).map
          (CategoryTheory.homOfLE (le_iSup U i)).op).hom ⟨v, hv_mem⟩).1 = (sf i).1
        rw [hsfi]
        exact hSubAt0 (U i) hUi _
      · change (((sheafOf.carrierPresheaf (C := C) D).map
          (CategoryTheory.homOfLE (le_iSup U i)).op).hom ⟨v, hv_mem⟩).1 = (sf i).1
        rw [map_val _ hUi ⟨v, hv_mem⟩, key_val i hUi]
    · intro s' hgluing
      apply Subtype.ext
      have hi₀g := hgluing i₀
      have h_apply :
          (((sheafOf.carrierPresheaf (C := C) D).map
              (TopologicalSpace.Opens.leSupr U i₀).op).hom s').1 = s'.1 :=
        map_val _ hUi₀ s'
      have := congr_arg Subtype.val hi₀g
      simp only at this
      rw [h_apply] at this
      exact this

/-- **The invertible sheaf `𝒪_C(D)` of a Weil divisor `D` on a smooth
proper curve `C / k̄`** (Hartshorne II §6 p. 144, definition of `ℒ(D)`).

For a Weil divisor `D = Σ_Q n_Q · [Q] ∈ Div(C)` on a smooth proper
geometrically irreducible curve `C / k̄`, the invertible sheaf
`𝒪_C(D) := ℒ(D)` is the sub-`𝒪_C`-module of the function-field constant
sheaf `𝒦_C ≅ K(C)` (Hartshorne Proposition 6.15: on an integral scheme
the sheaf of total quotient rings is the constant sheaf at the function
field) defined section-wise on each open `U ⊆ C` as
`Γ(U, 𝒪_C(D)) = { f ∈ K(C) | f = 0 ∨ ord_Q(f) ≥ −n_Q ∀ prime divisor Q
∈ U }`, with restriction along `V ⊆ U` given by the identity on `K(C)`.

The signature returns a `Sheaf (Opens.grothendieckTopology C.left.toTopCat)
(ModuleCat.{u} kbar)`: the same `ModuleCat k̄`-flavoured sheaf carrier used
by the project's `Scheme.HModule` cohomology pipeline (so that `H⁰` and
`H¹` of `𝒪_C(D)` are accessible via
`Scheme.HModule kbar (sheafOf D) 0/1`).

**iter-183 Lane K status** — Tier-3 honest typed sorry. The iter-184+
body recipe (per chapter `RiemannRoch_OcOfD.tex` §"Sheaf-property
correctness"): per-open `Submodule kbar K(C)` cut out by the order
conditions (the closure proofs reduce to `Ring.ordFrac`-multiplicativity
and the non-archimedean inequality of the DVR valuation at each prime
divisor); presheaf functor via the identity-on-`K(C)` restriction; sheaf
property via gluing-by-stalks (stalk-locality of the order conditions at
each prime divisor). The construction parallels the project's existing
`Scheme.toModuleKPresheaf` / `toModuleKPresheaf_isSheaf` template in
`AlgebraicJacobian/Cohomology/StructureSheafModuleK/`.

**Coordination with `RRFormula.lean:168`.** The iter-174 typed-`sorry`
placeholder `Scheme.WeilDivisor.sheafOf` in `RRFormula.lean` is
slated to be retired (Lane H) by re-export of this declaration. Both
files compile in isolation; cross-imports are coordinated by Lane H.

Blueprint reference: `def:sheafOf` (Hartshorne II §6 p. 144;
Propositions 6.13, 6.15; Remark 6.17.1).

**iter-185 Lane K body fragment.** The case `D = 0` is implemented on the
nose as the structure sheaf `Scheme.toModuleKSheaf C` (Hartshorne's
``\(\mathcal O_C(0) = \mathcal O_C\)'' identification; chapter
`RiemannRoch_OcOfD.tex`, Lemma `lem:sheafOf_zero`). The general case
remains an honest typed `sorry` pending the iter-186+ Hartshorne
subsheaf-of-`K_C` construction described in the docstring above. The
`if`-branching uses `Classical.dec` (via `open Classical in`) on the
`WeilDivisor = (PrimeDivisor →₀ ℤ)` carrier, which has no canonical
decidable equality. -/
noncomputable def sheafOf (D : C.left.WeilDivisor) :
    Sheaf (Opens.grothendieckTopology C.left.toTopCat)
      (ModuleCat.{u} kbar) :=
  open Classical in
  if D = 0 then Scheme.toModuleKSheaf C else
    -- The two regularity/Noetherian instances required by the order-condition
    -- carrier are not in the `sheafOf` signature (they would break the
    -- cross-file `RRFormula.lean` consumers, which carry only the smooth/proper
    -- package). `IsLocallyNoetherian C.left` is derived on the nose from
    -- properness (a proper — hence locally-of-finite-type — morphism to the
    -- Noetherian base `Spec k̄` has locally-Noetherian source). The
    -- `IsRegularInCodimensionOne C.left` witness — that every codim-1 stalk of
    -- a smooth dimension-1 curve is a DVR — is the one genuinely deep
    -- ingredient. **RE-SCOPED iter-004 to the rational-point cotangent route.**
    -- `IsLocallyNoetherian C.left` is derived on the nose from properness; with
    -- it in scope the DVR endpoint is the axiom-clean wiring lemma
    -- `isDiscreteValuationRing_stalk_of_finrank_cotangentSpace_eq_one` above,
    -- which packages the `IsLocalRing`/`IsNoetherianRing`/`IsDomain` stalk facts
    -- and feeds Mathlib's `IsLocalRing.finrank_CotangentSpace_eq_one_iff`. This
    -- isolates the entire substrate to the SINGLE numeric input
    -- `finrank κ(Y.point) (m/m²) = 1`, BYPASSING the general
    -- smooth ⟹ regular-local theory (Stacks 056S/00TT) and the
    -- coheight ⟹ ringKrullDim comparison (02IZ) of the old route — both of which
    -- remain available as off-path infra
    -- (`ringKrullDim_stalk_eq_one_of_coheight_eq_one`,
    -- `isDiscreteValuationRing_of_isRegularLocalRing_of_ringKrullDim_eq_one`).
    -- The residual `sorry` is now exactly this cotangent-dimension fact: over
    -- `k̄` (alg. closed) every codim-1 point of the curve is a k̄-rational
    -- closed point, where smoothness makes `Ω_{C/k̄}` locally free of rank one
    -- (Hartshorne II.8.15) and the conormal iso `m/m² ≅ Ω ⊗ κ` (Hartshorne
    -- II.8.7) transports rank one to the cotangent space. No Mathlib bridge for
    -- this conormal iso ships (snapshot `b80f227`); it is the project's deepest
    -- remaining substrate gap. The entire subsheaf-of-`K_C` construction below
    -- it is sorry-free.
    haveI : IsLocallyNoetherian (Spec (CommRingCat.of kbar)) := inferInstance
    haveI : LocallyOfFiniteType C.hom := IsProper.toLocallyOfFiniteType
    haveI : IsLocallyNoetherian C.left :=
      LocallyOfFiniteType.isLocallyNoetherian C.hom
    -- The codimension-one regularity witness is now the global instance
    -- `instIsRegularInCodimensionOneOfSmooth` above (smooth ⟹ DVR at every
    -- codim-1 stalk, assembled from the S1b cotangent pin + curve-dim bound).
    haveI : Scheme.IsRegularInCodimensionOne C.left := inferInstance
    ⟨sheafOf.carrierPresheaf (C := C) D,
      sheafOf.carrierPresheaf_isSheaf (C := C) D⟩

/-! ## §2. Immediate corollaries -/

/-- **Sheaf of the zero divisor is the structure sheaf**
(chapter `RiemannRoch_OcOfD.tex`, Lemma `sheafOf_zero`).

At `D = 0` the coefficient `n_Q = 0` at every prime divisor `Q`, so the
section condition of `sheafOf` reduces to the standard
"non-negative-order = regular" identification of the structure sheaf on
an integral scheme (Hartshorne II §6 immediately before Proposition 6.11).
Both sides are sub-`𝒪_C`-modules of `𝒦_C` with identity restriction
maps, so the equality of presheaves promotes to an equality of sheaves
of `ModuleCat k̄`-modules.

**iter-183 Lane K status** — Tier-3 honest typed sorry. The body closes
on iter-184+ closure of `sheafOf` together with the standard `Γ(U, 𝒪_C)`
identification.

**iter-185 Lane K body**: closes via the explicit `D = 0` branch in the
`sheafOf` def above (modified iter-185 to land the structure-sheaf value
on the `0` divisor on the nose). Unfolding `sheafOf` exposes the
`if 0 = 0 then toModuleKSheaf C else sorry` and `if_pos rfl` picks the
true branch.

Blueprint reference: `lem:sheafOf_zero`. -/
lemma sheafOf_zero :
    sheafOf (C := C) (0 : C.left.WeilDivisor) = Scheme.toModuleKSheaf C := by
  unfold sheafOf
  exact if_pos rfl

/-- **Sheaf at a single closed point is isomorphic to the line bundle of
`RR.3`** (chapter `RiemannRoch_OcOfD.tex`, Lemma `sheafOf_singlePoint`,
`\lean{AlgebraicGeometry.sheafOf_singlePoint_iso}`).

For a closed point `P ∈ C` viewed as a Weil divisor `[P] ∈ Div(C)` via
`Scheme.WeilDivisor.ofClosedPoint`, the invertible sheaf `𝒪_C([P])` of
`sheafOf` is canonically *isomorphic* (identity on the common carrier `K(C)`)
to the closed-point line bundle `lineBundleAtClosedPoint P` of `RR.3`
(`OCofP.lean`).

The comparison is by section-wise equality of carriers: at `D = [P]`, the
order conditions of `sheafOf` (`ord_Q(f) ≥ 0` for `Q ≠ P`, `ord_P(f) ≥ −1`,
plus the `f = 0` clause) are exactly those characterising sections of
`lineBundleAtClosedPoint P` (via `lineBundleAtClosedPoint.globalSections_iff`
of `OCofP.lean`, opened up to arbitrary `U`). Both sides carry the identity
restriction on `K(C)`, so the section-wise identity maps assemble into a
mutually-inverse pair of sheaf morphisms.

**iter-005 restatement (Lane S3).** The previous strict-equality target
`sheafOf (ofClosedPoint P hP) = lineBundleAtClosedPoint P hP hPcoh`
(blueprint demoted) is **not** provable from this file: the right-hand side
is bundled from OCofP's `private` `carrierPresheaf` / `carrierSubmoduleSheaf`
defs, so neither a definitional nor a propositional carrier equality can be
named here. The blueprint (`lem:sheafOf_singlePoint`) therefore pins the
comparison at the level of an *isomorphism* `≅`, which is all the downstream
`χ`-identity and degree arguments require.

**Residual gap (genuine, cross-file).** Constructing even a single morphism
into/out of `lineBundleAtClosedPoint` requires naming its per-open section
submodule, which is OCofP-`private`. Resolution (handed to the plan agent):
OCofP must expose either (a) a public per-open carrier identification, or
(b) a public inclusion `Scheme.lineBundleAtClosedPoint P hP hPcoh ⟶ 𝒦_C`
of the line bundle into the constant function-field sheaf (the analogue of
this file's identity-on-`K(C)` restriction maps). With either in scope the
identity-on-`K(C)` iso is immediate from `carrierSet`-equality at every `U`.

Blueprint reference: `lem:sheafOf_singlePoint`. -/
lemma sheafOf_singlePoint_iso [IsLocallyNoetherian C.left]
    [Scheme.IsRegularInCodimensionOne C.left]
    (P : C.left) (hP : IsClosed ({P} : Set C.left))
    (hPcoh : Order.coheight P = 1) :
    Nonempty (sheafOf (C := C) (ofClosedPoint P hP) ≅
      lineBundleAtClosedPoint (C := C) P hP hPcoh) := by
  -- `[P] = single ⟨P,hPcoh⟩ 1 ≠ 0`, so `sheafOf [P]` lands in the general
  -- subsheaf-of-`K_C` `else`-branch (not the structure-sheaf `D = 0` branch).
  have hne : ofClosedPoint P hP ≠ (0 : C.left.WeilDivisor) := by
    rw [ofClosedPoint_eq_single P hP hPcoh]
    intro h
    exact one_ne_zero (Finsupp.single_eq_zero.mp h)
  -- The two sides have *equal section sets* on every open `U`: at
  -- `D = single ⟨P,hPcoh⟩ 1` the order bound `-(D Q) = (if Q = ⟨P,hPcoh⟩
  -- then -1 else 0)` is exactly `RR.3`'s split condition `(ord_Q ≥ 0 for
  -- Q ≠ P) ∧ (ord_P ≥ -1)`, and the disjunctive `f = 0` clause matches
  -- because `ord_Q(0) = 0` already satisfies both `≥ 0` and `≥ -1`. The
  -- identity-on-`K(C)` maps in both directions would assemble into the iso.
  --
  -- BLOCKER (genuine, cross-file): the RHS `lineBundleAtClosedPoint` is
  -- bundled from OCofP's `private` `carrierPresheaf` / `carrierSubmoduleSheaf`
  -- defs, so its per-open section submodule is unnameable from this file and
  -- no morphism into/out of it can be built here. Awaiting OCofP exposing a
  -- public carrier identification or a public inclusion into the constant
  -- `K_C` sheaf (see docstring). The typed `Nonempty (≅)` placeholder records
  -- the achievable claim.
  sorry

omit [IsAlgClosed kbar] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] in
/-- **Adding `[Y]` relaxes the order bound**: the carrier set of `𝒪_C(D)`
over an open `U` is contained in that of `𝒪_C([Y] + D)`, because the extra
prime divisor `[Y]` only *weakens* the order bound `-(D Q) ≤ ord_Q(f)` at
`Q = Y` (and leaves all other bounds unchanged). This is the section-wise
heart of the `X₁ ↪ X₂` inclusion arm of `sheafOf_ses_single_add`. -/
private lemma sheafOf.carrierSet_le_add_single
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (Y : C.left.PrimeDivisor)
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    sheafOf.carrierSet (C := C) D U ⊆
      sheafOf.carrierSet (C := C) (Finsupp.single Y 1 + D) U := by
  intro f hf
  rcases hf with rfl | hf
  · exact Or.inl rfl
  · refine Or.inr (fun Q hQ => ?_)
    have hsingle : (0 : ℤ) ≤ (Finsupp.single Y (1 : ℤ)) Q := by
      rw [Finsupp.single_apply]; split <;> norm_num
    have hle : -((Finsupp.single Y 1 + D : C.left.PrimeDivisor →₀ ℤ) Q)
        ≤ -(D Q) := by
      rw [Finsupp.add_apply]; linarith
    exact le_trans hle (hf Q hQ)

omit [IsAlgClosed kbar] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] in
/-- **Sheaf-corrected carrier inclusion in the divisor variable**:
`carrierSubmoduleSheaf D U ≤ carrierSubmoduleSheaf ([Y] + D) U` on every open
`U`. The bot-trivialisation factor is unchanged (same `U` on both sides), so
the inclusion reduces to `carrierSet_le_add_single`. This is the per-open
`Submodule` inclusion underlying the restriction-natural sheaf monomorphism
`𝒪_C(D) ↪ 𝒪_C([Y] + D)` consumed by `sheafOf_ses_single_add`. -/
private lemma sheafOf.carrierSubmoduleSheaf_le_add_single
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (Y : C.left.PrimeDivisor)
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ) :
    sheafOf.carrierSubmoduleSheaf (C := C) D U ≤
      sheafOf.carrierSubmoduleSheaf (C := C) (Finsupp.single Y 1 + D) U := by
  rintro x ⟨hx_carr, hx_triv⟩
  exact ⟨sheafOf.carrierSet_le_add_single (C := C) D Y U hx_carr, hx_triv⟩

/-- **Inclusion morphism of carrier presheaves** `𝒪_C(D) ↪ 𝒪_C([Y] + D)` at
the presheaf level: the section-wise `Submodule.inclusion` of
`carrierSubmoduleSheaf_le_add_single`, natural in the open `U`. This is the
genuine `X₁ ↪ X₂` monomorphism arm of `sheafOf_ses_single_add`, modulo the
`if D = 0` unwrapping that relates `sheafOf D` to `carrierPresheaf D`. -/
private noncomputable def sheafOf.carrierPresheaf_le_hom
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (Y : C.left.PrimeDivisor) :
    sheafOf.carrierPresheaf (C := C) D ⟶
      sheafOf.carrierPresheaf (C := C) (Finsupp.single Y 1 + D) where
  app U := ModuleCat.ofHom (Submodule.inclusion
    (sheafOf.carrierSubmoduleSheaf_le_add_single (C := C) D Y U))
  naturality U V g := by
    classical
    by_cases hV : V.unop = (⊥ : TopologicalSpace.Opens C.left.toTopCat)
    · -- At `V = ⊥` the codomain carrier is `⊥`, hence a subsingleton, so both
      -- composites agree.
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      have hbot : sheafOf.carrierSubmoduleSheaf (C := C) (Finsupp.single Y 1 + D) V
          = ⊥ := by
        change sheafOf.carrierSubmodule (C := C) _ _ ⊓
          sheafOf.trivAtBot (C := C) _ = ⊥
        have htriv : sheafOf.trivAtBot (C := C) V = ⊥ := by
          apply Submodule.ext; intro f
          constructor
          · rintro (h | h)
            · exact (h hV).elim
            · exact h
          · intro h; exact Or.inr h
        rw [htriv, inf_bot_eq]
      have hsub : Subsingleton
          ↑((sheafOf.carrierPresheaf (C := C) (Finsupp.single Y 1 + D)).obj V) := by
        change Subsingleton
          ↥(sheafOf.carrierSubmoduleSheaf (C := C) (Finsupp.single Y 1 + D) V)
        rw [hbot]; infer_instance
      exact Subsingleton.elim _ _
    · -- At `V ≠ ⊥` both restriction maps are `Submodule.inclusion` (identity on
      -- `K(C)`), so naturality is `rfl`.
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      rintro ⟨x, hx⟩
      simp only [sheafOf.carrierPresheaf, ModuleCat.hom_ofHom, dif_neg hV,
        ModuleCat.hom_comp]
      rfl

/-- **`sheafOf` on a nonzero divisor is its carrier sheaf.** Unwraps the
`if D = 0` case-split in the body of `sheafOf`: on the `else` branch the value
is `⟨carrierPresheaf D, carrierPresheaf_isSheaf D⟩`. The regularity/Noetherian
instances derived internally by `sheafOf` agree by proof irrelevance with the
ambient `[IsLocallyNoetherian] [IsRegularInCodimensionOne]` (both `Prop`
classes), so the equation holds definitionally once the branch is selected.
This bridge lets the presheaf-level inclusion `carrierPresheaf_le_hom` be
transported to a `sheafOf`-level morphism in `sheafOf_ses_single_add`. -/
private lemma sheafOf_eq_carrier_of_ne_zero
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.WeilDivisor) (hD : D ≠ 0) :
    sheafOf (C := C) D =
      ⟨sheafOf.carrierPresheaf (C := C) D,
        sheafOf.carrierPresheaf_isSheaf (C := C) D⟩ := by
  unfold sheafOf
  rw [if_neg hD]

/-! ### Carrier-sheaf SES bricks (Lane S3, iter-006)

The following bricks build the inductive-step short exact sequence
`0 → 𝒪_C(D) → 𝒪_C([P]+D) → k(P) → 0` at the level of the **carrier sheaf**
`⟨carrierPresheaf D, carrierPresheaf_isSheaf D⟩` (the value of `sheafOf D` on
the `D ≠ 0` branch, by `sheafOf_eq_carrier_of_ne_zero`). They are stated with
the regularity/Noetherian instances as hypotheses, so they compile
independently of the S1-gated `IsRegularInCodimensionOne` instance (the L635
`finrank` `sorry`). The final assembly of `sheafOf_ses_single_add` (which must
also handle the `D = 0` / `[P]+D = 0` corner cases and synthesize the
regularity instance) is gated on Lane A landing that instance. -/

/-- **The carrier sheaf** `⟨carrierPresheaf D, carrierPresheaf_isSheaf D⟩`
packaged as an object of `Sheaf J (ModuleCat k̄)`; this is the value of
`sheafOf D` on the general (`D ≠ 0`) branch. -/
private noncomputable def sheafOf.carrierSheaf
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) :
    Sheaf (Opens.grothendieckTopology C.left.toTopCat) (ModuleCat.{u} kbar) :=
  ⟨sheafOf.carrierPresheaf (C := C) D, sheafOf.carrierPresheaf_isSheaf (C := C) D⟩

/-- **The sheaf-level inclusion** `𝒪_C(D) ↪ 𝒪_C([P]+D)`, obtained by promoting
the presheaf morphism `carrierPresheaf_le_hom` to the sheaf category (a sheaf
morphism is precisely a morphism of underlying presheaves). -/
private noncomputable def sheafOf.carrierSheafHom_le_add_single
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    sheafOf.carrierSheaf (C := C) D ⟶
      sheafOf.carrierSheaf (C := C) (Finsupp.single P 1 + D) :=
  ⟨sheafOf.carrierPresheaf_le_hom (C := C) D P⟩

/-- **The carrier-level inclusion is a monomorphism.** Section-wise it is the
injective `Submodule.inclusion`, hence each component is a mono in
`ModuleCat k̄`; a natural transformation that is component-wise mono is mono in
the presheaf category, and `Sheaf.Hom.mono_of_presheaf_mono` lifts this to the
sheaf category. Blueprint `lem:sheafOf_mono_single_add`. -/
private lemma sheafOf.carrierSheafHom_le_add_single_mono
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    CategoryTheory.Mono (sheafOf.carrierSheafHom_le_add_single (C := C) D P) := by
  haveI happ : ∀ U, CategoryTheory.Mono
      ((sheafOf.carrierSheafHom_le_add_single (C := C) D P).hom.app U) := by
    intro U
    rw [ModuleCat.mono_iff_injective]
    apply Submodule.inclusion_injective
    exact sheafOf.carrierSubmoduleSheaf_le_add_single (C := C) D P U
  haveI hmono :
      CategoryTheory.Mono (sheafOf.carrierSheafHom_le_add_single (C := C) D P).hom :=
    CategoryTheory.NatTrans.mono_of_mono_app _
  exact CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono _ _ _

/-! ### Away-from-`P` collapse of the inclusion (Lane S3 stalk substrate)

The cokernel of `𝒪_C(D) ↪ 𝒪_C([P]+D)` is computed stalk-wise. The first half
of that computation is *away from `P`*: on any open `U` with `P.point ∉ U` the
two carrier submodules of `K(C)` coincide, because the only coefficient that
differs between `D` and `[P]+D` is at `P`, and `P` imposes no order constraint
on sections over `U ∌ P`. These section-level equalities feed the
stalk-vanishing of the cokernel at every point `≠ P.point`. -/

omit [IsAlgClosed kbar] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] in
/-- **Carrier sets agree away from `P`.** If `P.point ∉ U` then
`carrierSet ([P]+D) U = carrierSet D U`: every prime divisor `Q` with
`Q.point ∈ U` is `≠ P` (else `P.point ∈ U`), so `(single P 1 + D) Q = D Q`,
and the defining order conditions are identical. -/
private lemma sheafOf.carrierSet_add_single_eq_of_not_mem
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor)
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ)
    (hP : P.point ∉ U.unop.1) :
    sheafOf.carrierSet (C := C) (Finsupp.single P 1 + D) U =
      sheafOf.carrierSet (C := C) D U := by
  have hcoeff : ∀ Q : C.left.PrimeDivisor, Q.point ∈ U.unop.1 →
      (Finsupp.single P 1 + D : C.left.PrimeDivisor →₀ ℤ) Q = D Q := by
    intro Q hQ
    have hPQ : P ≠ Q := by
      rintro rfl; exact hP hQ
    rw [Finsupp.add_apply, Finsupp.single_apply, if_neg hPQ, zero_add]
  ext f
  simp only [sheafOf.carrierSet, Set.mem_setOf_eq]
  constructor
  · rintro (rfl | hf)
    · exact Or.inl rfl
    · exact Or.inr (fun Q hQ => (hcoeff Q hQ) ▸ hf Q hQ)
  · rintro (rfl | hf)
    · exact Or.inl rfl
    · exact Or.inr (fun Q hQ => (hcoeff Q hQ).symm ▸ hf Q hQ)

omit [IsAlgClosed kbar] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] in
/-- **Carrier submodules agree away from `P`.** The submodule packaging of
`carrierSet_add_single_eq_of_not_mem`. -/
private lemma sheafOf.carrierSubmodule_add_single_eq_of_not_mem
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor)
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ)
    (hP : P.point ∉ U.unop.1) :
    sheafOf.carrierSubmodule (C := C) (Finsupp.single P 1 + D) U =
      sheafOf.carrierSubmodule (C := C) D U :=
  SetLike.ext' (sheafOf.carrierSet_add_single_eq_of_not_mem (C := C) D P U hP)

omit [IsAlgClosed kbar] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] in
/-- **Sheaf-corrected carrier submodules agree away from `P`.** Both sides
intersect with the same `trivAtBot U` factor, so equality reduces to
`carrierSubmodule_add_single_eq_of_not_mem`. This is the section-level form of
"the cokernel of `𝒪_C(D) ↪ 𝒪_C([P]+D)` has zero stalk away from `P`". -/
private lemma sheafOf.carrierSubmoduleSheaf_add_single_eq_of_not_mem
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor)
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ)
    (hP : P.point ∉ U.unop.1) :
    sheafOf.carrierSubmoduleSheaf (C := C) (Finsupp.single P 1 + D) U =
      sheafOf.carrierSubmoduleSheaf (C := C) D U := by
  unfold sheafOf.carrierSubmoduleSheaf
  rw [sheafOf.carrierSubmodule_add_single_eq_of_not_mem (C := C) D P U hP]

/-- **The inclusion is an isomorphism on sections away from `P`.** When
`P.point ∉ U`, the component `(carrierPresheaf_le_hom D P).app U` is the
inclusion of two *equal* submodules of `K(C)`
(`carrierSubmoduleSheaf_add_single_eq_of_not_mem`), hence a bijection and an
isomorphism in `ModuleCat k̄`. Since the opens `U ∌ P.point` form a
neighbourhood basis of any point `x ≠ P.point` (the complement of the closed
point `P.point` is open and contains `x`), this is the section-level input to
the stalk-vanishing of `cokernel f` at every `x ≠ P.point`. -/
private lemma sheafOf.carrierPresheaf_le_hom_app_isIso_of_not_mem
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor)
    (U : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ)
    (hP : P.point ∉ U.unop.1) :
    IsIso ((sheafOf.carrierPresheaf_le_hom (C := C) D P).app U) := by
  -- The component is the inclusion of two *equal* submodules; the reverse
  -- inclusion (from `heq`) is a two-sided inverse, both composites being the
  -- identity on the underlying subtype (`rfl` after unfolding).
  have heq := sheafOf.carrierSubmoduleSheaf_add_single_eq_of_not_mem (C := C) D P U hP
  refine ⟨ModuleCat.ofHom (Submodule.inclusion (le_of_eq heq)), ?_, ?_⟩ <;>
    (apply ModuleCat.hom_ext; apply LinearMap.ext; rintro ⟨x, hx⟩; rfl)

/-! ### S3 decomposition (iter-015): stalk-of-carrier-sheaf chain

The deep cokernel-≅-skyscraper isomorphism is decomposed here into atomic named
leaves matching the blueprint chapter §"Immediate corollaries":
  • `orderAtPSubmodule` — the fractional ideal `π_P^{-n}·𝒪_{C,P} ⊆ K(C)`,
    expressed via the single order constraint `ord_P g ≥ -(D P)` (the only
    constraint surviving the colimit at `P` on a smooth curve);
  • `carrierSheaf_stalk_eq` — (binding deep leaf, STUBBED) the stalk of the
    carrier sheaf at `P.point` is that fractional ideal;
  • `cokernel_stalk_at_iso_kbar` — (G2, STUBBED) the cokernel stalk at `P` is
    `k̄`, via multiplication by `π_P^{n+1}` and `residueField_eq_of_coheight_eq_one`;
  • `cokernel_skyscraper_hom` (+`_isIso`) — (G3) the residue-evaluation
    comparison morphism and its stalkwise-iso proof;
  • the retargeted `cokernel_carrierSheafHom_iso_skyscraper` then assembles the
    `≅` from the morphism + its `IsIso` via `asIso`. -/

/-- **The fractional ideal `π_P^{-n}·𝒪_{C,P} ⊆ K(C)`** of the stalk of
`carrierSheaf D` at `P.point`, expressed via the single order constraint at `P`
(`ord_P g ≥ -(D P)`, or `g = 0`). On a smooth curve every other order
constraint of `carrierSet D U` is discarded as `U` shrinks to `P.point`, so this
is exactly the colimit (stalk) submodule of `K(C)`. The closure proofs mirror
`carrierSubmodule` specialised to the single prime `P`. Blueprint:
`lem:carrierSheaf_stalk_eq_fractionalIdeal` (target submodule). -/
private noncomputable def sheafOf.orderAtPSubmodule
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    Submodule kbar C.left.functionField where
  carrier := { f | f = 0 ∨ -(D P) ≤ Scheme.RationalMap.order P f }
  zero_mem' := Or.inl rfl
  add_mem' := by
    rintro a b (rfl | ha) (rfl | hb)
    · exact Or.inl (by simp)
    · exact Or.inr (by simpa using hb)
    · exact Or.inr (by simpa using ha)
    · by_cases hane : a = 0
      · subst hane; exact Or.inr (by simpa using hb)
      by_cases hbne : b = 0
      · subst hbne; exact Or.inr (by simpa using ha)
      by_cases hab : a + b = 0
      · exact Or.inl hab
      refine Or.inr ?_
      set R := C.left.presheaf.stalk P.point
      have hMNZ : ∀ (x : C.left.functionField), x ≠ 0 →
          Ring.ordFrac R x ≠ 0 := fun x hx => by simp [hx]
      have hoa : Ring.ordFrac R a ≠ 0 := hMNZ a hane
      have hob : Ring.ordFrac R b ≠ 0 := hMNZ b hbne
      have hoab : Ring.ordFrac R (a + b) ≠ 0 := hMNZ _ hab
      have hmin : Ring.ordFrac R a ⊓ Ring.ordFrac R b ≤ Ring.ordFrac R (a + b) :=
        Ring.ordFrac_add (R := R) a b hab
      have hlog : (Ring.ordFrac R a ⊓ Ring.ordFrac R b).log ≤
          Scheme.RationalMap.order P (a + b) := by
        rcases min_cases (Ring.ordFrac R a) (Ring.ordFrac R b) with
            ⟨heq, _⟩ | ⟨heq, _⟩
        · rw [heq]; exact (WithZero.log_le_log hoa hoab).mpr (heq ▸ hmin)
        · rw [heq]; exact (WithZero.log_le_log hob hoab).mpr (heq ▸ hmin)
      have hminbd : -(D P) ≤ (Ring.ordFrac R a ⊓ Ring.ordFrac R b).log := by
        rcases min_cases (Ring.ordFrac R a) (Ring.ordFrac R b) with
            ⟨heq, _⟩ | ⟨heq, _⟩
        · rw [heq]; exact ha
        · rw [heq]; exact hb
      linarith
  smul_mem' := by
    intro c x hx
    rcases eq_or_ne c 0 with rfl | hc
    · simp only [zero_smul]; exact Or.inl rfl
    rcases hx with rfl | hx
    · simp only [smul_zero]; exact Or.inl rfl
    by_cases hx0 : x = 0
    · subst hx0; simp only [smul_zero]; exact Or.inl rfl
    refine Or.inr ?_
    have hsmul : c • x = (algebraMap kbar C.left.functionField c) * x :=
      Algebra.smul_def c x
    have hαne : (algebraMap kbar C.left.functionField c) ≠ 0 := by
      have hinj := FaithfulSMul.algebraMap_injective kbar C.left.functionField
      simpa using hinj.ne_iff.mpr hc
    set R := C.left.presheaf.stalk P.point
    have hMNZ : ∀ (y : C.left.functionField), y ≠ 0 →
        Ring.ordFrac R y ≠ 0 := fun y hy => by simp [hy]
    have key_alpha_ge : 0 ≤ Scheme.RationalMap.order P
          (algebraMap kbar C.left.functionField c) := by
      let β : R := (C.left.presheaf.germ (⊤ : C.left.Opens) P.point trivial).hom
        ((Scheme.toModuleKSheaf.kToSection C
            (Opposite.op (⊤ : C.left.Opens))).hom c)
      have hα_eq : (algebraMap kbar C.left.functionField c) =
          algebraMap R C.left.functionField β := by
        change ((Scheme.germToFunctionField C.left (⊤ : C.left.Opens)).hom
            ((Scheme.toModuleKSheaf.kToSection C
                (Opposite.op (⊤ : C.left.Opens))).hom c)) =
            (C.left.presheaf.stalkSpecializes
              ((genericPoint_spec C.left).specializes trivial)).hom β
        rw [← TopCat.Presheaf.germ_stalkSpecializes_apply
          (h := (genericPoint_spec C.left).specializes trivial)]
      have hβne : β ≠ 0 := by
        intro hzero; apply hαne; rw [hα_eq, hzero, map_zero]
      have hαord_ne : Ring.ordFrac R
          (algebraMap kbar C.left.functionField c) ≠ 0 := hMNZ _ hαne
      have hge : (1 : WithZero (Multiplicative ℤ)) ≤
          Ring.ordFrac R (algebraMap kbar C.left.functionField c) := by
        rw [hα_eq]; exact Ring.ordFrac_ge_one_of_ne_zero hβne
      unfold Scheme.RationalMap.order
      rw [show (0 : ℤ) = WithZero.log (1 : WithZero (Multiplicative ℤ)) by simp]
      exact (WithZero.log_le_log (by norm_num) hαord_ne).mpr hge
    rw [hsmul]
    have hαnez := hMNZ _ hαne
    have hxnez := hMNZ x hx0
    unfold Scheme.RationalMap.order
    rw [map_mul, WithZero.log_mul hαnez hxnez]
    have hge := key_alpha_ge
    have hxn := hx
    unfold Scheme.RationalMap.order at hge hxn
    linarith

/-- **Underlying `K(C)`-value of a `carrierPresheaf` restriction map.** Away from
`⊥` the restriction is `Submodule.inclusion`, i.e. the identity on the underlying
`K(C)`-element. This is the reusable extraction of the local `map_val` helper in
`carrierPresheaf_isSheaf`; the stalk-colimit descent (`carrierSheaf_stalk_iso_iSup`)
relies on it for the descent-cocone naturality. -/
private lemma sheafOf.carrierPresheaf_map_coe
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ)
    {Uo Vo : (TopologicalSpace.Opens C.left.toTopCat)ᵒᵖ} (g : Uo ⟶ Vo)
    (hV : Vo.unop ≠ ⊥) (x : ↥(sheafOf.carrierSubmoduleSheaf (C := C) D Uo)) :
    (((sheafOf.carrierPresheaf (C := C) D).map g).hom x).1 = x.1 := by
  simp only [sheafOf.carrierPresheaf, dif_neg hV, ModuleCat.hom_ofHom]; rfl

/- Planner strategy (A): Stalk-colimit ≅ iSup via germ-API bijective descent.
   Build comparison map `φ : stalk (carrierSheaf D) P.point → ⨆ U, Γ(U)` via
   the universal property of the stalk colimit: each section leg `Γ(U) → iSup`
   is `Submodule.inclusion` into the supremum, compatible with the
   (identity-on-K(C)) restriction maps. On the germ of `s ∈ Γ(U)`, `φ` returns
   `s` as an element of the iSup.
   Injectivity: compose `φ` with the inclusion `iSup ↪ K(C)` (identity on
   representatives); two germs with equal underlying element in K(C) agree on a
   common smaller neighbourhood → equal in the colimit by separatedness.
   Surjectivity: every `x ∈ iSup` lies in some `Γ(U)` with `U ∋ P.point`
   (directed-union characterisation; directedness uses `carrierSubmoduleSheaf_le`).
   Directedness of `OpenNhds P.point`: index nonempty (`⊤ ∋ P.point`); for
   `U, V ∋ P.point` the intersection `U ⊓ V ∋ P.point` and `Γ(U), Γ(V) ≤ Γ(U ⊓ V)`
   by `carrierSubmoduleSheaf_le` (note `U ⊓ V ≠ ⊥` since `P.point ∈ U ⊓ V`).
   Promote bijective k̄-linear map to `≅` via `LinearEquiv.toModuleIso`, or via
   `ConcreteCategory.isIso_iff_bijective` +
   `ModuleCat.instReflectsIsomorphismsForget` → `asIso`.
   Key Lean API: `TopCat.Presheaf.germ`, `TopCat.Presheaf.germ_exist`,
   `TopCat.Presheaf.germ_eq`, `TopCat.Presheaf.section_ext`. -/
omit [IsAlgClosed kbar] [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] in
/-- **Stalk of the carrier sheaf is the directed iSup of section submodules.**
The stalk of `carrierSheaf D` at `P.point` is isomorphic (as a `kbar`-module)
to the directed supremum of `carrierSubmoduleSheaf D U` over open neighbourhoods
`U` of `P.point`. Blueprint: `lem:carrierSheaf_stalk_iso_iSup`. -/
private noncomputable def sheafOf.carrierSheaf_stalk_iso_iSup
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    TopCat.Presheaf.stalk (sheafOf.carrierSheaf (C := C) D).1 P.point ≅
      ModuleCat.of kbar ((⨆ (U : TopologicalSpace.OpenNhds P.point),
          sheafOf.carrierSubmoduleSheaf (C := C) D (Opposite.op U.1)) :
        Submodule kbar C.left.functionField) := by
  classical
  -- The underlying presheaf and the target supremum submodule.
  set F := (sheafOf.carrierSheaf (C := C) D).1 with hF
  set Mfam : TopologicalSpace.OpenNhds P.point →
      Submodule kbar C.left.functionField :=
    fun V => sheafOf.carrierSubmoduleSheaf (C := C) D (Opposite.op V.1) with hMfam
  set M : Submodule kbar C.left.functionField := ⨆ V, Mfam V with hM
  -- A point of `V.1` for `V : OpenNhds P.point` makes `V.1 ≠ ⊥`.
  have hVne : ∀ V : TopologicalSpace.OpenNhds P.point,
      (V.1 : TopologicalSpace.Opens C.left.toTopCat) ≠ ⊥ := by
    intro V h
    have : P.point ∈ (⊥ : TopologicalSpace.Opens C.left.toTopCat) := h ▸ V.2
    exact this
  -- Descent cocone: legs = inclusion of each section submodule into `M`.
  let c : Limits.Cocone ((TopologicalSpace.OpenNhds.inclusion P.point).op ⋙ F) :=
    { pt := ModuleCat.of kbar M
      ι :=
      { app := fun U => ModuleCat.ofHom (Submodule.inclusion (le_iSup Mfam U.unop))
        naturality := fun U V f => by
          apply ModuleCat.hom_ext
          apply LinearMap.ext
          intro x
          apply Subtype.ext
          simp only [Functor.comp_map, ModuleCat.hom_comp, Functor.const_obj_obj,
            Functor.const_obj_map, Category.comp_id]
          exact sheafOf.carrierPresheaf_map_coe (C := C) D
            ((TopologicalSpace.OpenNhds.inclusion P.point).op.map f) (hVne V.unop) x } }
  -- The descent map `φ : stalk F P.point ⟶ ModuleCat.of kbar M`.
  let φ : TopCat.Presheaf.stalk F P.point ⟶ ModuleCat.of kbar M :=
    Limits.colimit.desc _ c
  -- `φ` on a germ is the inclusion of the section into `M`.
  have hφgerm : ∀ (U : TopologicalSpace.OpenNhds P.point)
      (s : F.obj (Opposite.op U.1)),
      φ.hom ((TopCat.Presheaf.germ F U.1 P.point U.2).hom s) =
        ⟨s.1, le_iSup Mfam U s.2⟩ := by
    intro U s
    have hd : TopCat.Presheaf.germ F U.1 P.point U.2 ≫ φ = c.ι.app (Opposite.op U) :=
      Limits.colimit.ι_desc c (Opposite.op U)
    have := congrArg (fun m => m.hom s) hd
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      Submodule.coe_inclusion] using this
  -- `φ.hom` is injective: a germ in the kernel has zero underlying value.
  have hinj : Function.Injective φ.hom := by
    apply (injective_iff_map_eq_zero _).mpr
    intro t ht
    obtain ⟨U, m, s, rfl⟩ := TopCat.Presheaf.germ_exist (F := F) P.point t
    rw [hφgerm ⟨U, m⟩ s] at ht
    have hs0 : s.1 = 0 := congrArg Subtype.val ht
    have : s = 0 := Subtype.ext hs0
    rw [this, map_zero]
  -- `φ.hom` is surjective: any `m ∈ M` lies in some `Mfam U`, then `φ (germ U) = m`.
  have hdir : Directed (· ≤ ·) Mfam := by
    intro U V
    refine ⟨⟨U.1 ⊓ V.1, ⟨U.2, V.2⟩⟩, ?_, ?_⟩
    · exact sheafOf.carrierSubmoduleSheaf_le (C := C) D
        (by exact inf_le_left) (hVne ⟨U.1 ⊓ V.1, ⟨U.2, V.2⟩⟩)
    · exact sheafOf.carrierSubmoduleSheaf_le (C := C) D
        (by exact inf_le_right) (hVne ⟨U.1 ⊓ V.1, ⟨U.2, V.2⟩⟩)
  have hsurj : Function.Surjective φ.hom := by
    rintro ⟨y, hy⟩
    rw [Submodule.mem_iSup_of_directed _ hdir] at hy
    obtain ⟨U, hyU⟩ := hy
    refine ⟨(TopCat.Presheaf.germ F U.1 P.point U.2).hom ⟨y, hyU⟩, ?_⟩
    rw [hφgerm U ⟨y, hyU⟩]
  -- A bijective `kbar`-linear map of modules is an isomorphism.
  haveI : IsIso φ := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨hinj, hsurj⟩
  exact asIso φ

omit [IsAlgClosed kbar] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIrreducible C.hom] in
/-- **Finitely many prime divisors in an affine open violate the order constraint.**
Given an affine open `W` and `g : K(C)`, the set of prime divisors `Q` with
`Q.point ∈ W` and `¬ (−(D Q) ≤ ord_Q g)` is finite.
Blueprint: `lem:finite_orderConstraintFail_affine`.

The blueprint argues affine-locally via `finite_order_support_affine`; here we
use the *global* finiteness of the order support on the proper curve `C` —
`{Q | ord_Q g ≠ 0}` is the support of the principal divisor `div g`
(`Scheme.WeilDivisor.principal`, finite by `Finsupp`), which is a strictly
stronger fact and avoids the affine bridge. A violator `Q` has
`ord_Q g < -(D Q)`, so it cannot have both `ord_Q g = 0` and `D Q = 0`; hence it
lies in the (finite) order support of `g` or the (finite) support of `D`. -/
private lemma sheafOf.finite_orderConstraintFail_affine
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ)
    (W : C.left.Opens) (hW : IsAffineOpen W) (g : C.left.functionField) :
    {Q : C.left.PrimeDivisor | Q.point ∈ W ∧
      ¬ (-(D Q) ≤ Scheme.RationalMap.order Q g)}.Finite := by
  -- Global finiteness of the order support `{Q | ord_Q g ≠ 0}` via `principal`.
  have hfin_order : {Q : C.left.PrimeDivisor |
      Scheme.RationalMap.order Q g ≠ 0}.Finite := by
    by_cases hg : g = 0
    · subst hg
      refine Set.Finite.subset Set.finite_empty ?_
      intro Q hQ
      simp only [Set.mem_setOf_eq, Scheme.RationalMap.order_zero, ne_eq,
        not_true_eq_false] at hQ
    · refine (Scheme.WeilDivisor.principal (X := C.left) g hg).support.finite_toSet.subset
        ?_
      intro Q hQ
      rw [Finset.mem_coe, Finsupp.mem_support_iff, principal_apply]
      exact hQ
  -- Finiteness of `{Q | D Q ≠ 0}` (the support of the Weil divisor `D`).
  have hfin_D : {Q : C.left.PrimeDivisor | D Q ≠ 0}.Finite :=
    D.support.finite_toSet.subset
      (by intro Q hQ; rw [Finset.mem_coe, Finsupp.mem_support_iff]; exact hQ)
  -- A violator lies in the union of the two finite sets.
  refine (hfin_order.union hfin_D).subset ?_
  rintro Q ⟨-, hviol⟩
  rw [Set.mem_union]
  by_contra hcon
  push_neg at hcon
  obtain ⟨ho, hd⟩ := hcon
  simp only [Set.mem_setOf_eq, ne_eq, not_not] at ho hd
  exact hviol (by rw [hd, ho]; simp)

omit [GeometricallyIrreducible C.hom] in
/-- **Order constraint at `P` is realised on a small open.** Given
`g ∈ orderAtPSubmodule D P`, there exists an open `U ∋ P.point` with
`g ∈ carrierSubmoduleSheaf D U`. Blueprint: `lem:exists_open_mem_carrierSubmoduleSheaf`.

Construction: for `g = 0` take `U = ⊤`. For `g ≠ 0`, pick an affine open
`W ∋ P.point`; by `finite_orderConstraintFail_affine` only finitely many prime
divisors `Q` with `Q.point ∈ W` violate the order constraint. On the curve every
prime divisor's point is closed (`isClosed_singleton_of_coheight_eq_one` with
`krullDim_curve_le_one`), so the union `Z` of those finitely many bad points is
closed; set `U := W ⊓ Zᶜ`. Then `P.point ∈ U` (it is in `W` and, since the order
constraint holds at `P`, `P ∉` the bad set so `P.point ∉ Z`); and every prime
divisor `Q'` with `Q'.point ∈ U` is not bad (else `Q'.point ∈ Z`), so the order
constraint holds, i.e. `g ∈ carrierSubmoduleSheaf D U`. -/
private lemma sheafOf.exists_open_mem_carrierSubmoduleSheaf
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor)
    (g : C.left.functionField) (hg : g ∈ sheafOf.orderAtPSubmodule (C := C) D P) :
    ∃ (U : C.left.Opens) (_ : P.point ∈ U),
      g ∈ sheafOf.carrierSubmoduleSheaf (C := C) D (Opposite.op U) := by
  classical
  haveI : LocallyOfFiniteType C.hom := IsProper.toLocallyOfFiniteType
  by_cases hg0 : g = 0
  · exact ⟨⊤, trivial, by
      subst hg0; exact (sheafOf.carrierSubmoduleSheaf (C := C) D _).zero_mem⟩
  -- The order constraint holds at `P` (from `g ∈ orderAtPSubmodule` and `g ≠ 0`).
  have hgP : -(D P) ≤ Scheme.RationalMap.order P g := by
    rcases hg with h0 | hP
    · exact absurd h0 hg0
    · exact hP
  -- An affine open `W ∋ P.point`.
  obtain ⟨W, hW, hPW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := C.left) (U := ⊤) (x := P.point) trivial
  -- The bad set `B` of order-constraint violators inside `W` is finite.
  have hBfin := sheafOf.finite_orderConstraintFail_affine (C := C) D W hW g
  set B : Set C.left.PrimeDivisor := {Q : C.left.PrimeDivisor | Q.point ∈ W ∧
      ¬ (-(D Q) ≤ Scheme.RationalMap.order Q g)} with hBdef
  -- The union `Z` of the (closed) bad points is closed; `Zc` its open complement.
  have hZclosed : IsClosed (⋃ Q ∈ B, ({Q.point} : Set C.left)) :=
    hBfin.isClosed_biUnion (fun Q _ =>
      isClosed_singleton_of_coheight_eq_one Q.point Q.coheight krullDim_curve_le_one)
  set Zc : C.left.Opens :=
    ⟨(⋃ Q ∈ B, ({Q.point} : Set C.left))ᶜ, hZclosed.isOpen_compl⟩ with hZc
  -- `P.point ∉ Z`: a bad `Q` with `P.point = Q.point` would force `P = Q ∈ B`,
  -- contradicting that the order constraint holds at `P`.
  have hPZc : P.point ∉ (⋃ Q ∈ B, ({Q.point} : Set C.left)) := by
    intro hmem
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hmem
    obtain ⟨Q, hQB, hPeq⟩ := hmem
    have hQP : Q = P := Scheme.PrimeDivisor.ext hPeq.symm
    rw [hQP] at hQB
    exact hQB.2 hgP
  refine ⟨W ⊓ Zc, ⟨hPW, hPZc⟩, ?_⟩
  -- `g ∈ carrierSubmoduleSheaf D (op (W ⊓ Zc))`.
  refine ⟨Or.inr ?_, Or.inl ?_⟩
  · -- Order constraint holds at every prime divisor with point in `W ⊓ Zc`.
    intro Q' hQ'
    obtain ⟨hQ'W, hQ'Z⟩ := hQ'
    by_contra hcon
    exact hQ'Z (Set.mem_biUnion (show Q' ∈ B from ⟨hQ'W, hcon⟩) rfl)
  · -- `W ⊓ Zc ≠ ⊥` since `P.point ∈ W ⊓ Zc`.
    intro hbot
    have hbot' : (W ⊓ Zc : C.left.Opens) = ⊥ := hbot
    have hmem : P.point ∈ (W ⊓ Zc : C.left.Opens) := ⟨hPW, hPZc⟩
    rw [hbot'] at hmem
    exact hmem

/- Planner strategy (B): iSup = orderAtPSubmodule via two-sided containment.
   (≤): Each leg `Γ(U) ≤ orderAtPSubmodule D P` for `U ∋ P.point`: if `g ∈ Γ(U)`
   is nonzero, the order constraint at Q=P is among those enforced over U
   (since `P.point ∈ U`), giving `-(D P) ≤ ord_P g`. Apply `Submodule.iSup_le`.
   (≥): For any `g ∈ orderAtPSubmodule D P`, use `exists_open_mem_carrierSubmoduleSheaf`
   (#3) to find `U ∋ P.point` with `g ∈ Γ(U)`, then `g ∈ iSup` by `Submodule.le_iSup`.
   Directed family: use `Submodule.mem_iSup_of_directed`; directedness as in #1. -/
omit [GeometricallyIrreducible C.hom] in
/-- **The directed iSup of carrier sections at `P` equals the order submodule.**
`⨆ (U : OpenNhds P.point), carrierSubmoduleSheaf D U = orderAtPSubmodule D P`
as `kbar`-submodules of `K(C)`. Blueprint:
`lem:iSup_carrierSubmoduleSheaf_eq_orderAtPSubmodule`. -/
private lemma sheafOf.iSup_carrierSubmoduleSheaf_eq_orderAtPSubmodule
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    (⨆ (U : TopologicalSpace.OpenNhds P.point),
        sheafOf.carrierSubmoduleSheaf (C := C) D (Opposite.op U.1)) =
      sheafOf.orderAtPSubmodule (C := C) D P := by
  apply le_antisymm
  · -- `≤`: each leg `Γ(U) ≤ orderAtP D P`, using the order constraint at `Q = P`.
    refine iSup_le (fun U => ?_)
    intro g hg
    rcases hg.1 with h0 | hc
    · exact Or.inl h0
    · exact Or.inr (hc P U.2)
  · -- `≥`: realise any `g ∈ orderAtP D P` on a small open via B1, then `le_iSup`.
    intro g hg
    obtain ⟨U, hPU, hgU⟩ :=
      sheafOf.exists_open_mem_carrierSubmoduleSheaf (C := C) D P g hg
    exact Submodule.mem_iSup_of_mem ⟨U, hPU⟩ hgU

/-- **Stalk of the carrier sheaf is the fractional ideal `π_P^{-n}·𝒪_{C,P}`.**
The stalk of `carrierSheaf D` at `P.point` is the filtered colimit (= union
inside `K(C)`, the restriction maps being the identity) of the section
submodules; on a smooth curve only the order constraint at `P` survives, giving
`orderAtPSubmodule D P`. Blueprint: `lem:carrierSheaf_stalk_eq_fractionalIdeal`.

**iter-016 ASSEMBLY (B-seam landed).** Composes the stalk-colimit iso
`carrierSheaf_stalk_iso_iSup` (seam A) with the directed-supremum identification
`iSup_carrierSubmoduleSheaf_eq_orderAtPSubmodule` (B-seam, now sorry-free): the
stalk is the directed iSup of the section submodules, and that iSup equals
`orderAtPSubmodule D P`. The only remaining deep leaf is seam A (the germ-API
descent `stalk ≅ ⨆ Γ(U)`). -/
private noncomputable def sheafOf.carrierSheaf_stalk_eq
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    TopCat.Presheaf.stalk (sheafOf.carrierSheaf (C := C) D).val P.point ≅
      ModuleCat.of kbar (sheafOf.orderAtPSubmodule (C := C) D P) :=
  sheafOf.carrierSheaf_stalk_iso_iSup (C := C) D P ≪≫
    eqToIso (by rw [sheafOf.iSup_carrierSubmoduleSheaf_eq_orderAtPSubmodule])

/-- **The stalk of the carrier inclusion `𝒪_C(D) ↪ 𝒪_C([P]+D)` is epi away from
`P`.** For `x ≠ P.point`, the stalk map at `x` of `carrierPresheaf_le_hom` is
surjective: any germ at `x` is represented on a small open `V ∋ x` avoiding the
closed point `P.point`, on which the two carrier submodules of `K(C)` coincide
(`carrierSubmoduleSheaf_add_single_eq_of_not_mem`), so the representing section
already lies in the smaller sheaf. Being surjective in `ModuleCat`, it is epi —
the section-level engine of "`coker f` has zero stalk away from `P`". -/
private lemma sheafOf.stalkFunctor_map_carrierPresheaf_le_hom_epi_of_ne
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor)
    (x : C.left) (hx : x ≠ P.point) :
    CategoryTheory.Epi ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} kbar) x).map
      (sheafOf.carrierPresheaf_le_hom (C := C) D P)) := by
  classical
  haveI : LocallyOfFiniteType C.hom := IsProper.toLocallyOfFiniteType
  -- `P.point` is a closed point of the curve.
  have hPcl : IsClosed ({P.point} : Set C.left) :=
    isClosed_singleton_of_coheight_eq_one P.point P.coheight krullDim_curve_le_one
  rw [ModuleCat.epi_iff_surjective]
  -- Surjectivity via germs on a small open avoiding `P.point`.
  intro t
  obtain ⟨U, hxU, s, rfl⟩ := TopCat.Presheaf.germ_exist
    (F := sheafOf.carrierPresheaf (C := C) (Finsupp.single P 1 + D)) x t
  -- The shrunken open `V = U ⊓ {P.point}ᶜ ∋ x` avoids `P.point`.
  set V : C.left.Opens := U ⊓ ⟨({P.point} : Set C.left)ᶜ, hPcl.isOpen_compl⟩ with hVdef
  have hxV : x ∈ V := ⟨hxU, by simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hx⟩
  have hPV : P.point ∉ (Opposite.op V).unop.1 := by
    rintro ⟨-, h2⟩; exact h2 rfl
  have hle : V ≤ U := inf_le_left
  -- Restrict `s` to `V`; on `V` the two carrier submodules coincide.
  have heq := sheafOf.carrierSubmoduleSheaf_add_single_eq_of_not_mem (C := C) D P
    (Opposite.op V) hPV
  set s' := (ConcreteCategory.hom
    ((sheafOf.carrierPresheaf (C := C) (Finsupp.single P 1 + D)).map
      (CategoryTheory.homOfLE hle).op)) s with hs'def
  have hmem : (s'.1 : C.left.functionField) ∈ sheafOf.carrierSubmoduleSheaf (C := C) D (Opposite.op V) := by
    rw [← heq]; exact s'.2
  set w : ↥(sheafOf.carrierSubmoduleSheaf (C := C) D (Opposite.op V)) := ⟨s'.1, hmem⟩ with hwdef
  -- The inclusion sends `w` to `s'` (identity on the `K(C)` value).
  have hcompat : (ConcreteCategory.hom
      ((sheafOf.carrierPresheaf_le_hom (C := C) D P).app (Opposite.op V))) w = s' := by
    apply Subtype.ext; rfl
  have e1 := TopCat.Presheaf.stalkFunctor_map_germ_apply (C := ModuleCat.{u} kbar) V x hxV
    (sheafOf.carrierPresheaf_le_hom (C := C) D P) w
  have e2 := TopCat.Presheaf.germ_res_apply
    (sheafOf.carrierPresheaf (C := C) (Finsupp.single P 1 + D))
    (CategoryTheory.homOfLE hle) x hxV s
  refine ⟨(ConcreteCategory.hom
    (TopCat.Presheaf.germ (sheafOf.carrierPresheaf (C := C) D) V x hxV)) w, e1.trans ?_⟩
  exact (congrArg (fun y => (ConcreteCategory.hom
    (TopCat.Presheaf.germ (sheafOf.carrierPresheaf (C := C) (Finsupp.single P 1 + D)) V x hxV)) y)
    (hcompat.trans hs'def)).trans e2

/-- **At `P` the cokernel stalk is `k̄`.** Writing `n = D P`, the stalk
inclusion is `π_P^{-n}𝒪_{C,P} ⊆ π_P^{-(n+1)}𝒪_{C,P}`; multiplication by
`π_P^{n+1}` carries it onto `𝔪_P ⊆ 𝒪_{C,P}`, whose quotient is the residue
field `𝒪_{C,P}/𝔪_P = k̄` (codimension-one ⟹ `k̄`-rational,
`residueField_eq_of_coheight_eq_one`). Blueprint:
`lem:cokernel_sheafOf_single_add_stalkAtP_iso_kbar`.

**STUBBED (iter-015 plan).** Depends on `carrierSheaf_stalk_eq`; the
multiplication-by-`π^{n+1}` automorphism and the residue identification are the
next-iter `mathlib-build` task once the binding stalk leaf lands. -/
private noncomputable def sheafOf.cokernel_stalk_at_iso_kbar
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    TopCat.Presheaf.stalk
        (CategoryTheory.Limits.cokernel
          (sheafOf.carrierSheafHom_le_add_single (C := C) D P)).val P.point ≅
      ModuleCat.of kbar kbar :=
  sorry

/-- **The residue-evaluation comparison morphism** `coker f ⟶ k(P)`. On a small
open `U ∋ P.point` it sends the class of `g ∈ 𝒪_C([P]+D)(U)` to its leading
Laurent coefficient `(π_P^{n+1} g) mod 𝔪_P ∈ k̄`; it is zero away from `P`.
Blueprint: `def:cokernel_skyscraper_hom`.

**iter-017.** Built as the adjunction transpose under
`stalkSkyscraperSheafAdjunction P.point` of the cokernel-stalk iso `G2`
(`cokernel_stalk_at_iso_kbar`): a stalk map `stalk_P (coker f) ⟶ k̄` corresponds
to a sheaf morphism `coker f ⟶ skyscraperSheaf P.point k̄`. The residue-evaluation
description of the blueprint is exactly this transpose (the unit of the
stalk–skyscraper adjunction sends a germ to its image under the stalk map). -/
private noncomputable def sheafOf.cokernel_skyscraper_hom
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    CategoryTheory.Limits.cokernel
        (sheafOf.carrierSheafHom_le_add_single (C := C) D P) ⟶
      skyscraperSheaf (C := ModuleCat.{u} kbar)
        P.point (ModuleCat.of kbar kbar) :=
  (stalkSkyscraperSheafAdjunction (C := ModuleCat.{u} kbar) P.point).homEquiv
    (CategoryTheory.Limits.cokernel (sheafOf.carrierSheafHom_le_add_single (C := C) D P))
    (ModuleCat.of kbar kbar)
    (sheafOf.cokernel_stalk_at_iso_kbar (C := C) D P).hom

/-- **The residue-evaluation morphism is an isomorphism.** Stalkwise: the zero
map (between zero stalks) at every `Q ≠ P.point` (via
`carrierPresheaf_le_hom_app_isIso_of_not_mem`, so `coker f` has zero stalk away
from `P`), and the residue isomorphism `𝒪_{C,P}/𝔪_P = k̄` at `P.point` (via
`cokernel_stalk_at_iso_kbar`). A stalkwise iso of sheaves is an iso. Blueprint:
`lem:cokernel_skyscraper_hom_isIso`.

**iter-017.** Stalkwise iso via `isIso_of_stalkFunctor_map_iso`. At `P.point`:
the adjunction triangle `homEquiv_counit` identifies the stalk map of the
transpose with `G2 ≫ counit⁻¹` (both isos). Away from `P.point`: the source
stalk vanishes (`coker` of the epi stalk map `stalkFunctor_map_…_epi_of_ne`, via
`PreservesCokernel.iso` for the left-adjoint `Sheaf.forget ⋙ stalkFunctor`) and
the target skyscraper stalk vanishes (`skyscraperPresheafStalkOfNotSpecializes`,
since `P.point` is closed), so the map between zero objects is an iso. -/
private lemma sheafOf.cokernel_skyscraper_hom_isIso
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    IsIso (sheafOf.cokernel_skyscraper_hom (C := C) D P) := by
  classical
  haveI hPstalk : ∀ x : ↑C.left.toTopCat,
      IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} kbar) x).map
        (sheafOf.cokernel_skyscraper_hom (C := C) D P).hom) := by
    intro x
    set A := ModuleCat.of kbar kbar with hA
    set Co := CategoryTheory.Limits.cokernel
      (sheafOf.carrierSheafHom_le_add_single (C := C) D P) with hCo
    set adj := stalkSkyscraperSheafAdjunction (C := ModuleCat.{u} kbar) P.point with hadj
    by_cases hx : x = P.point
    · subst hx
      -- Triangle identity for the stalk–skyscraper adjunction.
      have htri : (adj.homEquiv Co A).symm (sheafOf.cokernel_skyscraper_hom (C := C) D P)
          = (sheafOf.cokernel_stalk_at_iso_kbar (C := C) D P).hom :=
        (adj.homEquiv Co A).symm_apply_apply _
      rw [adj.homEquiv_counit] at htri
      -- The counit at `A` is an isomorphism (stalk of the skyscraper at `P.point`).
      haveI hcounit : IsIso (adj.counit.app A) := by
        rw [show adj.counit.app A
            = (skyscraperPresheafStalkOfSpecializes P.point A specializes_rfl).hom from rfl]
        infer_instance
      -- Hence the transpose's stalk map equals `G2 ≫ counit⁻¹`, an iso.
      have key : IsIso ((Sheaf.forget (ModuleCat.{u} kbar) _ ⋙
          TopCat.Presheaf.stalkFunctor (ModuleCat.{u} kbar) P.point).map
          (sheafOf.cokernel_skyscraper_hom (C := C) D P)) := by
        have heq : (Sheaf.forget (ModuleCat.{u} kbar) _ ⋙
            TopCat.Presheaf.stalkFunctor (ModuleCat.{u} kbar) P.point).map
            (sheafOf.cokernel_skyscraper_hom (C := C) D P)
            = (sheafOf.cokernel_stalk_at_iso_kbar (C := C) D P).hom ≫
              CategoryTheory.inv (adj.counit.app A) := by
          rw [← htri, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
        rw [heq]; infer_instance
      exact key
    · -- Away from `P.point`: both stalks vanish.
      sorry
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso _

/-- **The cokernel of the carrier-level inclusion `𝒪_C(D) ↪ 𝒪_C([P]+D)` is the
skyscraper sheaf at `P` with stalk `k̄`** (Hartshorne IV.1.3; blueprint
`lem:cokernel_sheafOf_single_add_iso_skyscraper`).

**Deep gap (deferred, per iter-006 plan).** This is the SOLE remaining deep
ingredient of the SES. Mathlib (snapshot `b80f227`) has no skyscraper-cokernel
API. The stalk computation runs as follows:

*Away from `P`.* At a prime divisor `Q ≠ P` the coefficients of `Q` in `D` and
in `[P]+D` agree, so on a small open `U ∌ P` the inclusion is the identity
`carrierSet D U = carrierSet ([P]+D) U`; the cokernel presheaf has zero stalk
at every point other than `P.point`, matching the skyscraper's terminal value
there.

*At `P`.* The stalk `𝒪_{C,P}` is a DVR with uniformiser `π_P` and residue
field `k̄`. Writing `n = D P`, the stalk of `𝒪_C(D)` is `π_P^{-n}·𝒪_{C,P}` and
that of `𝒪_C([P]+D)` is `π_P^{-(n+1)}·𝒪_{C,P}`; multiplication by `π_P^{n+1}`
carries the inclusion to `𝔪_P ⊆ 𝒪_{C,P}`, whose quotient is `k̄`. So the
cokernel stalk at `P` is one-dimensional over `k̄`, equal to the skyscraper's
stalk.

A precise sub-decomposition for the next iteration:
  1. the cokernel presheaf `U ↦ carrierSubmoduleSheaf ([P]+D) U / carrierSubmoduleSheaf D U`;
  2. an explicit residue evaluation `carrierSubmoduleSheaf ([P]+D) U → k̄`
     (leading Laurent coefficient at the order-`(n+1)` pole at `P`), with
     kernel `carrierSubmoduleSheaf D U`, giving a presheaf epimorphism onto the
     skyscraper presheaf;
  3. sheafification: the comparison map of presheaves is a stalk-wise iso (zero
     away from `P`, the residue iso at `P`), hence an iso of sheaves via
     `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` (a sheaf morphism inducing
     isos on all stalks is an iso); the stalk of `cokernel f` is the presheaf
     cokernel stalk `(π_P^{-(n+1)}𝒪_{C,P}) / (π_P^{-n}𝒪_{C,P}) ≅ 𝒪_{C,P}/𝔪_P`.

**iter-007 progress (Lane S3).** The *away-from-`P`* half is now realised at the
section level by the bricks proved just above:
  • `carrierSet_add_single_eq_of_not_mem` — `carrierSet ([P]+D) U = carrierSet D U`
    when `P.point ∉ U` (every prime divisor `Q` with `Q.point ∈ U` differs from
    `P`, so the `P`-coefficient drops out: uses `Scheme.PrimeDivisor.ext` for the
    point-injectivity `Q.point ≠ P.point ⟹ Q ≠ P`, and `Finsupp.single_apply`);
  • `carrierSubmodule_add_single_eq_of_not_mem` / `carrierSubmoduleSheaf_add_single_eq_of_not_mem`
    — the `Submodule`/sheaf-corrected packaging of that equality;
  • `carrierPresheaf_le_hom_app_isIso_of_not_mem` — consequently the comparison
    component `(carrierPresheaf_le_hom D P).app U` is an isomorphism in
    `ModuleCat k̄` for `P.point ∉ U` (explicit two-sided inverse = the reverse
    `Submodule.inclusion`), the precise section-level input to "the cokernel has
    zero stalk away from `P`".

**Remaining gaps (each names a concrete missing ingredient).**
  (G1) *Away-from-`P` stalk iso* — promote `carrierPresheaf_le_hom_app_isIso_of_not_mem`
    to `IsIso ((stalkFunctor (ModuleCat k̄) x).map (carrierPresheaf_le_hom D P))`
    for every `x ≠ P.point`. This needs an open `U ∋ x` with `P.point ∉ U`, i.e.
    the geometric fact **`P.point` is a closed point of the curve** (prime
    divisors on a smooth dim-1 curve are closed points); then a colimit-cofinality
    argument (Mathlib has `stalkFunctor_map_injective_of_isBasis` for injectivity,
    but no off-the-shelf surjective/iso-from-basis lemma — needs a local helper
    `colimMap`-of-iso on the cofinal subsystem `{U ∋ x // P.point ∉ U}`).
  (G2) *At-`P` stalk iso* `coker(stalk_P f) ≅ k̄` — THE deep blocker. Requires the
    carrier-sheaf stalk computation `stalk_{P.point}(carrierSheaf D) ≅ π_P^{-n}𝒪_{C,P}`
    (as a sub-`𝒪`-module of `K(C)`), then `π_P^{-(n+1)}𝒪/π_P^{-n}𝒪 ≅ 𝒪/𝔪 = k̄`
    via the DVR structure at `P` (available from `[IsRegularInCodimensionOne]`,
    `Scheme.WeilDivisor.IsRegularInCodimensionOne.out`). No carrier-stalk lemma
    exists in the project yet; this is a separate ~200–400 LOC development.
  (G3) *Assembly* — build `g : coker f ⟶ skyscraper P.point k̄` from a stalk map
    `stalk_{P}(coker f) ⟶ k̄` via `stalkSkyscraperSheafAdjunction`, then conclude
    `IsIso g` from (G1)+(G2) through `isIso_of_stalkFunctor_map_iso` and take
    `asIso`. Friction to watch: `coker f` lives in
    `Sheaf (Opens.grothendieckTopology …) (ModuleCat k̄)` whereas the adjunction/
    stalk API is phrased for `TopCat.Sheaf`; these are defeq (the iso statement
    already typechecks) but the `.val`/`.hom` morphism accessors must be matched. -/
private noncomputable def sheafOf.cokernel_carrierSheafHom_iso_skyscraper
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    CategoryTheory.Limits.cokernel
        (sheafOf.carrierSheafHom_le_add_single (C := C) D P) ≅
      skyscraperSheaf (C := ModuleCat.{u} kbar)
        P.point (ModuleCat.of kbar kbar) :=
  -- Assemble the `≅` from the residue-evaluation morphism and its `IsIso`,
  -- isolating the deep stalk work in `cokernel_skyscraper_hom(_isIso)`.
  haveI := sheafOf.cokernel_skyscraper_hom_isIso (C := C) D P
  asIso (sheafOf.cokernel_skyscraper_hom (C := C) D P)

/-- **The carrier sheaf of the zero divisor is the structure sheaf.**
`carrierSheaf 0 ≅ toModuleKSheaf C` in `Sh(C, Mod k̄)`. Over an open `U` the
carrier sections of the zero divisor are the rational functions with `ord_Q ≥ 0`
at every prime divisor `Q ∈ U`; on a smooth (hence normal) curve these are
exactly the regular functions `Γ(U, 𝒪_C)` (Hartshorne II.6.3A,
`A = ⋂_{ht 𝔭 = 1} A_𝔭`), and the identifications are compatible with restriction.
Blueprint: `lem:carrierSheaf_zero_iso_toModuleKSheaf`.

**STUBBED (iter-015 plan).** The regular-functions = order-`≥ 0`-everywhere
identification (Hartshorne 6.3A on the normal curve) has no single-call Mathlib
form; this corner bridge is the deep input to the `D = 0` / `[P]+D = 0` corner
cases of `sheafOf_ses_single_add`. Created here at the pinned name; the
section-wise equality + sheaf-iso assembly is the next-iter lane. -/
private noncomputable def sheafOf.carrierSheaf_zero_iso_toModuleKSheaf
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left] :
    sheafOf.carrierSheaf (C := C) 0 ≅ Scheme.toModuleKSheaf C :=
  sorry

/-- **Short exact sequence for `D ↝ D + [P]` at the carrier-sheaf level.**
The canonical mono–cokernel short exact sequence attached to the monomorphism
`carrierSheafHom_le_add_single`, with the third term identified as the
skyscraper at `P` via `cokernel_carrierSheafHom_iso_skyscraper`. This is the
faithful Lean form of `sheafOf_ses_single_add` modulo the
`sheafOf D = carrierSheaf D` unwrapping (which requires `D ≠ 0`) and the
regularity-instance synthesis. Blueprint `lem:sheafOf_ses_single_add`. -/
private theorem sheafOf.carrierSheaf_ses_single_add
    [IsLocallyNoetherian C.left] [Scheme.IsRegularInCodimensionOne C.left]
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    ∃ S : CategoryTheory.ShortComplex
        (Sheaf (Opens.grothendieckTopology C.left.toTopCat)
          (ModuleCat.{u} kbar)),
      S.ShortExact ∧
      S.X₁ = sheafOf.carrierSheaf (C := C) D ∧
      S.X₂ = sheafOf.carrierSheaf (C := C) (Finsupp.single P 1 + D) ∧
      Nonempty (S.X₃ ≅ skyscraperSheaf (C := ModuleCat.{u} kbar)
        P.point (ModuleCat.of kbar kbar)) := by
  letI f := sheafOf.carrierSheafHom_le_add_single (C := C) D P
  haveI : CategoryTheory.Mono f :=
    sheafOf.carrierSheafHom_le_add_single_mono (C := C) D P
  refine ⟨CategoryTheory.ShortComplex.mk f (CategoryTheory.Limits.cokernel.π f),
    ?_, rfl, rfl,
    ⟨sheafOf.cokernel_carrierSheafHom_iso_skyscraper (C := C) D P⟩⟩
  exact CategoryTheory.ShortComplex.ShortExact.mk
    (CategoryTheory.ShortComplex.exact_cokernel f)

/-- **Short exact sequence for `D ↝ D + [P]`** (Hartshorne IV.1.3
inductive step, p. 296; chapter `RiemannRoch_OcOfD.tex`, Lemma
`sheafOf_ses_single_add`).

For a Weil divisor `D ∈ Div(C)` and a prime divisor `P` of `C`
(equivalently, a closed point on a smooth curve), the inclusion
`𝒪_C(D) ↪ 𝒪_C(D + [P])` of sub-`𝒪_C`-modules of `𝒦_C` fits into a short
exact sequence
`0 → 𝒪_C(D) → 𝒪_C(D + [P]) → k(P) → 0`
in `Sh(C, 𝐌𝐨𝐝_k̄)`, where `k(P)` is the skyscraper sheaf at `P` with
stalk `k̄`.

The statement bundles the existence of a `ShortComplex` whose `X₁ ↦ X₂`
arm matches `sheafOf D ↪ sheafOf (Finsupp.single P 1 + D)` and that is
`ShortExact` (mono + epi + exact). The third term `X₃` is the
skyscraper `k(P)` — encoded here as a (nonempty) isomorphism class with
`Mathlib`'s `skyscraperSheaf` (decidability of `P.point ∈ U` supplied
classically). Lane H's `RRFormula` consumes this sequence via
χ-additivity to derive `χ(𝒪_C(D + [P])) = χ(𝒪_C(D)) + 1`.

**iter-183 Lane K status** — Tier-3 honest typed sorry. The iter-184+
body recipe (per chapter `RiemannRoch_OcOfD.tex` §"Immediate
corollaries", Beat 1 + Beat 2): build the ideal-sheaf SES
`0 → 𝒪_C(−[P]) → 𝒪_C → k(P) → 0`, tensor with `𝒪_C(D + [P])` (which is
locally free of rank 1, hence the tensor is exact), and identify the
three terms via `𝒪_C(−[P]) ⊗ 𝒪_C(D + [P]) ≅ 𝒪_C(D)` (Hartshorne 6.13(b)),
`𝒪_C ⊗ 𝒪_C(D + [P]) ≅ 𝒪_C(D + [P])` (tensor unit), and
`k(P) ⊗ 𝒪_C(D + [P]) ≅ k(P)` (rank-1 stalk at `P`).

The argument `D` carries the underlying `Finsupp` type rather than
`Scheme.WeilDivisor` so that the `Finsupp.single P 1 + D` term elaborates
cleanly (the addition is in the unambiguous Finsupp instance); the result
is consumed via the definitional equality `WeilDivisor = (PrimeDivisor →₀
ℤ)`, matching the pattern of `Scheme.eulerCharacteristic_sheafOf_single_add`
in `RRFormula.lean`.

Blueprint reference: `lem:sheafOf_ses_single_add` (Hartshorne IV.1, p. 296). -/
theorem sheafOf_ses_single_add
    (D : C.left.PrimeDivisor →₀ ℤ) (P : C.left.PrimeDivisor) :
    ∃ S : CategoryTheory.ShortComplex
        (Sheaf (Opens.grothendieckTopology C.left.toTopCat)
          (ModuleCat.{u} kbar)),
      S.ShortExact ∧
      S.X₁ = sheafOf (C := C) D ∧
      S.X₂ = sheafOf (C := C) (Finsupp.single P 1 + D) ∧
      Nonempty (S.X₃ ≅ skyscraperSheaf (C := ModuleCat.{u} kbar)
        P.point (ModuleCat.of kbar kbar)) := by
  -- ════ iter-006 (Lane S3) progress: carrier-level SES fully assembled ════
  --
  -- The faithful cokernel-route decomposition (pieces A/B/C) is now BUILT at
  -- the level of the **carrier sheaf** `sheafOf.carrierSheaf D` (the value of
  -- `sheafOf D` on the `D ≠ 0` branch). All of it lives above this theorem and
  -- compiles:
  --   • `sheafOf.carrierSheaf`                       — the carrier sheaf object;
  --   • `sheafOf.carrierSheafHom_le_add_single`      — (A) the sheaf-level
  --       inclusion `𝒪_C(D) ↪ 𝒪_C([P] + D)`, promoting `carrierPresheaf_le_hom`
  --       to `Sheaf J (ModuleCat k̄)`;
  --   • `sheafOf.carrierSheafHom_le_add_single_mono` — (A) PROVEN: the inclusion
  --       is a monomorphism (section-wise `Submodule.inclusion` injective →
  --       `NatTrans.mono_of_mono_app` → `Sheaf.Hom.mono_of_presheaf_mono`);
  --   • `sheafOf.carrierSheaf_ses_single_add`        — (A)+(B) PROVEN (modulo
  --       (C)): the canonical mono–cokernel `ShortComplex` is `ShortExact`
  --       (`ShortComplex.exact_cokernel` + `ShortExact.mk`), with `X₁/X₂` the
  --       carrier sheaves and `X₃ ≅ skyscraper` via (C).
  --   • `sheafOf.cokernel_carrierSheafHom_iso_skyscraper` — (C), the SOLE deep
  --       gap (honest typed `sorry`): cokernel ≅ skyscraper at `P`. No Mathlib
  --       skyscraper-cokernel API; route = build the residue presheaf morphism
  --       and apply `TopCat.Presheaf.isIso_of_stalkFunctor_map_iso` (stalk-iso
  --       criterion). Precise 3-step sub-decomposition in its docstring.
  --
  -- REMAINING for this `sheafOf`-level statement (deferred, S1-gated):
  --   1. Synthesize `[Scheme.IsRegularInCodimensionOne C.left]` — gated on Lane
  --      A landing the L635 `finrank` fact (planner directive: do NOT force it
  --      here with a duplicate `sorry`). With it in scope, also derive
  --      `[IsLocallyNoetherian C.left]` from properness (as `sheafOf` does).
  --   2. Connect `sheafOf` to `carrierSheaf`: for `D ≠ 0` and
  --      `single P 1 + D ≠ 0`, `sheafOf_eq_carrier_of_ne_zero` rewrites both
  --      objects to `carrierSheaf`, then `carrierSheaf_ses_single_add` closes.
  --   3. Corner cases `D = 0` (then `sheafOf 0 = toModuleKSheaf C` via
  --      `sheafOf_zero`, NOT `carrierSheaf 0` — needs the structure-sheaf↔carrier
  --      iso) and `single P 1 + D = 0` (i.e. `D = single P (-1)`; then
  --      `X₂ = toModuleKSheaf C`). These need a `carrierSheaf 0 ≅ toModuleKSheaf C`
  --      bridge, queued with step 1.
  -- ════ iter-014 (S1b-wire) progress: main case closed via delegation ════
  -- With `[Scheme.IsRegularInCodimensionOne C.left]` now a GLOBAL instance
  -- (`instIsRegularInCodimensionOneOfSmooth`) and `IsLocallyNoetherian C.left`
  -- derived from properness, the general (`D ≠ 0`, `[P]+D ≠ 0`) case delegates
  -- directly to `carrierSheaf_ses_single_add`, rewriting `carrierSheaf → sheafOf`
  -- via `sheafOf_eq_carrier_of_ne_zero`. The X₃ ≅ skyscraper component is carried
  -- through that lemma (its only remaining gap is the internal cokernel iso
  -- `cokernel_carrierSheafHom_iso_skyscraper`, deferred to iter-015 — NOT
  -- re-introduced here).
  haveI : LocallyOfFiniteType C.hom := IsProper.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian C.left :=
    LocallyOfFiniteType.isLocallyNoetherian C.hom
  by_cases hD : D = 0
  · -- Corner case `D = 0`: `sheafOf 0 = toModuleKSheaf C` (`sheafOf_zero`), so the
    -- SES is `0 → 𝒪_C → 𝒪_C([P]) → k(P) → 0`. `carrierSheaf_ses_single_add` gives
    -- `X₁ = carrierSheaf 0`, but `carrierSheaf 0 ≠ toModuleKSheaf C` definitionally
    -- (the `D = 0` if-branch of `sheafOf` selects the structure sheaf directly, not
    -- the order-`≥ 0` carrier).
    --
    -- iter-015: the bridge `sheafOf.carrierSheaf_zero_iso_toModuleKSheaf`
    -- (`carrierSheaf 0 ≅ toModuleKSheaf C`, Hartshorne II.6.3A) is now in scope as
    -- a typed stub. Wiring recipe (next-iter, once the bridge body lands):
    --   obtain ⟨S₀, hSE₀, h1, h2, h3⟩ := carrierSheaf_ses_single_add 0 P;
    --   let e := carrierSheaf_zero_iso_toModuleKSheaf;
    --   build S₂ := ShortComplex.mk (e.inv ≫ eqToHom h1.symm ≫ S₀.f) S₀.g (by
    --     simp [Category.assoc, S₀.zero]) with X₁ = toModuleKSheaf C = sheafOf 0;
    --   transport ShortExact via `ShortComplex.shortExact_of_iso` along
    --   `isoMk (eqToIso h1 ≪≫ e) (Iso.refl _) (Iso.refl _) …`; X₂ = sheafOf [P]
    --   via `sheafOf_eq_carrier_of_ne_zero` (since `single P 1 + 0 ≠ 0`).
    sorry
  by_cases hPD : Finsupp.single P 1 + D = 0
  · -- Corner case `[P]+D = 0` (i.e. `D = single P (-1)`): `X₂ = sheafOf 0 =
    -- toModuleKSheaf C`. Same `carrierSheaf_zero_iso_toModuleKSheaf` bridge, applied
    -- to the X₂ component (transport S₀.g's target along `e`); X₁ = sheafOf D via
    -- `sheafOf_eq_carrier_of_ne_zero` (since `D = single P (-1) ≠ 0`).
    sorry
  -- Main case `D ≠ 0` and `[P]+D ≠ 0`: full close via the carrier-level SES.
  obtain ⟨S, hSE, hX1, hX2, hX3⟩ := sheafOf.carrierSheaf_ses_single_add (C := C) D P
  refine ⟨S, hSE, ?_, ?_, hX3⟩
  · rw [hX1]; exact (sheafOf_eq_carrier_of_ne_zero (C := C) D hD).symm
  · rw [hX2]
    exact (sheafOf_eq_carrier_of_ne_zero (C := C) (Finsupp.single P 1 + D) hPD).symm

end Scheme.WeilDivisor

end AlgebraicGeometry
