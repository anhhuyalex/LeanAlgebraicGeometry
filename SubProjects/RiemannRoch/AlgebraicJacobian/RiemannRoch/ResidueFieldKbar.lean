/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Codimension-one points are `k̄`-rational

Blueprint: `blueprint/src/chapters/RiemannRoch_OcOfD.tex`,
§"The codimension-one regularity substrate"
(`lem:codimOne_point_residueField_eq_kbar`).

For an integral curve `C` of finite type over an algebraically closed field
`k̄`, a point `x` with `Order.coheight x = 1` is a closed point whose residue
field `κ(x)` is canonically `k̄` (Nullstellensatz / Jacobson, then alg-closed
triviality of the resulting finite extension).  This file builds the bridge
bottom-up from the pure-algebra core (Zariski's lemma over a Jacobson ring
plus algebraic-closure triviality) up to the scheme-level statement consumed
by `RiemannRoch/SmoothStalkDVR.lean`.
-/

open AlgebraicGeometry CategoryTheory

/-! ## Project-local Mathlib supplement — residue rationality over `k̄`

The pure-algebra heart of the codimension-one rationality statement: a field
`K` that is finite type as an algebra over an algebraically closed field `k̄`
is `k̄` itself (the structure map is an isomorphism).  Mathlib ships the two
halves — `finite_of_finite_type_of_isJacobsonRing` (Zariski/Nullstellensatz)
and `IsAlgClosed.algebraMap_bijective_of_isIntegral` — but not the composite,
which is exactly what the geometric residue-field computation reads back. -/

/-- **A finite-type field extension of an algebraically closed field is trivial.**
If `K` is a field and a finite-type `k`-algebra with `k` algebraically closed,
then the structure map `k → K` is bijective.  Project-local composite of
Zariski's lemma (`finite_of_finite_type_of_isJacobsonRing`) and
`IsAlgClosed.algebraMap_bijective_of_isIntegral`. -/
theorem IsAlgClosed.algebraMap_bijective_of_finiteType
    (k K : Type*) [Field k] [Field K] [IsAlgClosed k] [Algebra k K]
    [Algebra.FiniteType k K] : Function.Bijective (algebraMap k K) := by
  haveI : Module.Finite k K := finite_of_finite_type_of_isJacobsonRing k K
  haveI : Algebra.IsIntegral k K := Algebra.IsIntegral.of_finite k K
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral

/-- **Residue field at a maximal ideal of a finite-type `k̄`-algebra is `k̄`.**
For `k̄` algebraically closed and `A` a finite-type `k̄`-algebra, the structure
map `k̄ → κ(𝔭) = A_𝔭/𝔭A_𝔭` into the residue field at a maximal ideal `𝔭` is
bijective.  This is the affine-local heart of the codimension-one rationality
statement: the residue field is finite type over `k̄` (surjective image of `A`,
via `Ideal.algebraMap_residueField_surjective`), hence `k̄` itself by
`IsAlgClosed.algebraMap_bijective_of_finiteType`. -/
theorem IsAlgClosed.algebraMap_residueField_bijective_of_isMaximal
    (kbar A : Type*) [Field kbar] [IsAlgClosed kbar] [CommRing A] [Algebra kbar A]
    [Algebra.FiniteType kbar A] (p : Ideal A) [p.IsMaximal] :
    Function.Bijective (algebraMap kbar p.ResidueField) := by
  haveI : Algebra.FiniteType kbar p.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom kbar A p.ResidueField)
      (Ideal.algebraMap_residueField_surjective p)
  exact IsAlgClosed.algebraMap_bijective_of_finiteType kbar p.ResidueField

/-! ## Project-local Mathlib supplement — rationality corollaries

The downstream conormal comparison of `RiemannRoch/SmoothStalkDVR.lean` reads
the residue rationality not as a bijection but through three vanishing facts
(`Subsingleton Ω`, `Subsingleton H1Cotangent`, `FormallySmooth`), all of which
follow formally once the structure map `k̄ → K` is bijective — i.e. `K ≅ k̄`
as a `k̄`-algebra.  These are stated abstractly (keyed on bijectivity of the
structure map) so the geometric application can apply them to `K = κ(x)` once
the scheme-level identification `κ(x) ≅ k̄` is available. -/

/-- The `k̄`-algebra isomorphism `k̄ ≃ₐ[k̄] K` packaged from a bijective
structure map.  Project-local helper for the rationality corollaries below. -/
noncomputable def algEquivOfAlgebraMapBijective
    {kbar K : Type*} [Field kbar] [Field K] [Algebra kbar K]
    (h : Function.Bijective (algebraMap kbar K)) : kbar ≃ₐ[kbar] K :=
  AlgEquiv.ofBijective (Algebra.ofId kbar K) h

/-- If the structure map `k̄ → K` is bijective then `K` is formally smooth over
`k̄` (it is `k̄` up to isomorphism).  Project-local: the `Algebra.FormallySmooth`
half of the residue-rationality interface. -/
theorem formallySmooth_of_algebraMap_bijective
    {kbar K : Type*} [Field kbar] [Field K] [Algebra kbar K]
    (h : Function.Bijective (algebraMap kbar K)) : Algebra.FormallySmooth kbar K :=
  Algebra.FormallySmooth.of_equiv (algEquivOfAlgebraMapBijective h)

/-- If the structure map `k̄ → K` is bijective then `Ω[K⁄k̄]` is trivial.
Project-local: the Kähler-vanishing half of the residue-rationality interface. -/
theorem subsingleton_kaehlerDifferential_of_algebraMap_bijective
    {kbar K : Type*} [Field kbar] [Field K] [Algebra kbar K]
    (h : Function.Bijective (algebraMap kbar K)) : Subsingleton (Ω[K⁄kbar]) := by
  haveI : Algebra.FormallyUnramified kbar K :=
    Algebra.FormallyUnramified.of_equiv (algEquivOfAlgebraMapBijective h)
  exact Algebra.FormallyUnramified.subsingleton_kaehlerDifferential

/-- If the structure map `k̄ → K` is bijective then `H¹` of the cotangent
complex of `K` over `k̄` vanishes.  Project-local: the `H1Cotangent`-vanishing
half of the residue-rationality interface. -/
theorem subsingleton_h1Cotangent_of_algebraMap_bijective
    {kbar K : Type*} [Field kbar] [Field K] [Algebra kbar K]
    (h : Function.Bijective (algebraMap kbar K)) :
    Subsingleton (Algebra.H1Cotangent kbar K) := by
  haveI := formallySmooth_of_algebraMap_bijective h
  exact Algebra.FormallySmooth.subsingleton_h1Cotangent

/-! ## Project-local Mathlib supplement — closed points via coheight

The topological half of the codimension-one rationality statement: on a scheme
of (topological) Krull dimension at most one, a point of coheight one is closed.
This is the "codimension-one points are exactly the closed points" step of the
blueprint, isolated from the residue-field computation.  No single Mathlib
lemma packages the coheight-`=1` ⇒ closed implication; it is assembled from the
order-theoretic `krullDim = ⨆ (height + coheight)` identity (forcing
`height x = 0`, i.e. `IsMin x` in the specialisation order) and the
sober/`T0` identification of specialisation-minimal points with closed points. -/

/-- **A coheight-one point of a dimension-`≤ 1` scheme is closed.**
If `Order.coheight x = 1` and the underlying space of `X` has Krull dimension
at most one (in the specialisation order), then `{x}` is closed.  Project-local
topological substrate for `residueField_eq_of_coheight_eq_one`. -/
theorem AlgebraicGeometry.isClosed_singleton_of_coheight_eq_one
    {X : Scheme.{u}} (x : X) (hco : Order.coheight x = 1)
    (hdim : Order.krullDim (α := X) ≤ 1) : IsClosed ({x} : Set X) := by
  haveI : Nonempty X := ⟨x⟩
  have h1 : Order.height x + Order.coheight x ≤ ⨆ a, Order.height a + Order.coheight a :=
    le_iSup (fun a => Order.height a + Order.coheight a) x
  have h2 : (Order.height x + Order.coheight x : WithBot ℕ∞) ≤ Order.krullDim (α := X) := by
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact_mod_cast h1
  rw [hco] at h2
  have h4 : Order.height x + 1 ≤ (1 : ℕ∞) := by exact_mod_cast (le_trans h2 hdim)
  have hh0 : Order.height x = 0 := by
    have hn : Order.height x ≠ ⊤ := by rintro hT; rw [hT] at h4; simp at h4
    exact ENat.lt_one_iff_eq_zero.mp ((ENat.add_one_le_iff hn).mp h4)
  have hmin : IsMin x := Order.height_eq_zero.mp hh0
  have hcl : closure ({x} : Set X) = {x} := by
    apply subset_antisymm _ subset_closure
    intro y hy
    have hxy : x ⤳ y := specializes_iff_mem_closure.mpr hy
    have hyx2 : y ⤳ x := hmin (show y ≤ x from hxy)
    exact ((hxy.antisymm hyx2).eq).symm ▸ rfl
  rw [← hcl]; exact isClosed_closure

/-! ## Scheme-level residue-field rationality — pinned target

Scheme-level assembly of `lem:codimOne_point_residueField_eq_kbar`:
a codimension-one point of an integral `k̄`-curve has residue field `k̄`. -/

/-- Canonical `k̄`-algebra structure on the residue field `κ(x)` at a point `x`
of a `k̄`-scheme, induced by the structure morphism `C.hom : C.left ⟶ Spec (.of k̄)`.
Not automatically synthesizable (Lean cannot infer `C` from `C.left` alone);
introduced as a `noncomputable def` so that `residueField_eq_of_coheight_eq_one`
can refer to `algebraMap kbar (C.left.residueField x)` via explicit instance passing. -/
@[reducible]
noncomputable def AlgebraicGeometry.residueFieldAlgebra
    {kbar : Type u} [Field kbar]
    {C : Over (Spec (.of kbar))} (x : C.left) :
    Algebra kbar (C.left.residueField x) :=
  RingHom.toAlgebra <|
    (C.hom.residueFieldMap x).hom.comp <|
      (Scheme.Spec.residueFieldIso (.of kbar) (C.hom.base x)).inv.hom.comp
        (algebraMap kbar (C.hom.base x).asIdeal.ResidueField)

/- Planner strategy for `residueField_eq_of_coheight_eq_one`:
   (1) CLOSED: `isClosed_singleton_of_coheight_eq_one x hx hdim` (this file, L122)
       gives `IsClosed {x}` immediately.
   (2) AFFINE CHART (from `LocallyOfFiniteType C.hom`): pick affine opens
       `U ⊆ Spec (.of kbar)` and `V ⊆ C.left` with `x ∈ V` and the induced ring hom
       `appLE := (C.hom.appLE U V e).hom : Γ(Spec (.of kbar), U) →+* Γ(C.left, V)`.
       Since `Unique (Spec (.of kbar))` forces `U = ⊤`, use `Scheme.ΓSpecIso kbar`
       to identify `Γ(Spec (.of kbar), ⊤) ≅ kbar` and compose to get
       `ψ : kbar →+* A` where `A := Γ(C.left, V)`.
       `A` is finite type over `kbar` (from `LocallyOfFiniteType C.hom`);
       `algebraize [ψ]` emits `[Algebra kbar A]`.
   (3) MAXIMALITY: map `x ↦ p ∈ PrimeSpectrum A`; `{x}` closed ⟹ `p` is maximal.
   (4) BIJECTIVITY: `IsAlgClosed.algebraMap_residueField_bijective_of_isMaximal kbar A p`
       (this file, L54) gives `Function.Bijective (algebraMap kbar p.ResidueField)`.
   (5) STALK/RESIDUE ISO: `IsAffineOpen.isLocalization_stalk hV ⟨x, hxV⟩` gives
       `C.left.stalk x ≅ Localization.AtPrime p`, hence
       `C.left.residueField x ≅ p.asIdeal.ResidueField`;
       transport bijectivity along this iso.
   (6) ALGEBRA MATCH: identify `residueFieldAlgebra x` with the affine-chart algebra
       via uniqueness of `k̄`-algebra maps between fields with bijective structure map.
   Full recipe: `analogies/chart-extraction.md`. -/
theorem AlgebraicGeometry.residueField_eq_of_coheight_eq_one
    {kbar : Type u} [Field kbar] [IsAlgClosed kbar]
    {C : Over (Spec (.of kbar))} [IsIntegral C.left] [LocallyOfFiniteType C.hom]
    (x : C.left) (hx : Order.coheight x = 1)
    (hdim : Order.krullDim (α := C.left) ≤ 1) :
    IsClosed ({x} : Set C.left) ∧
    @Function.Bijective kbar (C.left.residueField x)
      (@algebraMap kbar (C.left.residueField x) _ _
        (residueFieldAlgebra (C := C) x)) := by
  have hcl : IsClosed ({x} : Set C.left) :=
    isClosed_singleton_of_coheight_eq_one x hx hdim
  refine ⟨hcl, ?_⟩
  -- The structure map `k̄ → κ(x)` coincides with the inverse of the iso
  -- `residueFieldIsoBase C.hom x hcl : κ(x) ≅ k̄` (a closed-point residue field over an
  -- algebraically closed base is the base), which is bijective.
  have hm : (residueFieldIsoBase C.hom x hcl).inv
      = CommRingCat.ofHom (algebraMap kbar (C.hom.base x).asIdeal.ResidueField)
        ≫ (Scheme.Spec.residueFieldIso (.of kbar) (C.hom.base x)).inv
        ≫ C.hom.residueFieldMap x := by
    apply Spec.map_injective
    rw [SpecMap_residueFieldIsoBase_inv, Spec.map_comp, Spec.map_comp, Category.assoc,
      Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  have key : (@algebraMap kbar (C.left.residueField x) _ _ (residueFieldAlgebra (C := C) x))
      = (residueFieldIsoBase C.hom x hcl).inv.hom := by
    rw [hm]; rfl
  rw [key]
  exact (ConcreteCategory.bijective_of_isIso (residueFieldIsoBase C.hom x hcl).inv)
