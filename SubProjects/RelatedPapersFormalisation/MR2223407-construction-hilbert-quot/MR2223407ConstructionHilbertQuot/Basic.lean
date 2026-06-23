/-
Copyright (c) 2024 Archon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon
-/
import Mathlib

/-!
# MR2223407: Construction of Hilbert and Quot Schemes — Foundations

This file scaffolds the foundational *dependency anchors* of the project, following
the blueprint chapter `chapters/Basic.tex` (Nitsure, "Construction of Hilbert and
Quot Schemes", MR2223407 / arXiv:math/0504590).

Each declaration corresponds to a `\lean{...}`-tagged block in the blueprint:

* `projectiveSpace`            — `def:projective-space`
* `relativeProj`               — `def:relative-proj`
* `RelativelyVeryAmple`        — `def:very-ample`
* `coherent_higher_direct_image` — `thm:coherent-higher-direct-image`
* `serre_vanishing`            — `thm:serre-vanishing`
* `cohomology_and_base_change` — `thm:cohomology-base-change`
* `valuativeCriterion_proper`  — `thm:valuative-criterion-properness`
* `faithfullyFlatDescent`      — `thm:ffdescent`

Several of these (the EGA III §7 cohomology anchors and the relative `Proj` of a
graded sheaf) are *Mathlib gaps*: the genuinely faithful statement is not yet
expressible, so we state the closest honest approximation with a `sorry` body and
record the precise stating-gap in a comment. No `axiom` is introduced.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

universe u

namespace MR2223407ConstructionHilbertQuot

-- The grading of `R[x₀,…,xₙ]` by total degree is not a global instance in Mathlib
-- (one may want other gradings), so we activate it locally to form `Proj`.
attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Projective space and relative Proj -/

/-- **Projective `n`-space over a base** (`def:projective-space`).

`ℙⁿ_S` is the base change to `S` of `ℙⁿ_ℤ = Proj ℤ[x₀,…,xₙ]`.  Since every scheme
has a unique morphism to the terminal object `Spec ℤ`, the fibre product over
`Spec ℤ` is the categorical product, which we realise as a pullback over the
terminal scheme — exactly as `AlgebraicGeometry.AffineSpace` is built. -/
noncomputable def projectiveSpace (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S)
    (terminal.from (Proj (homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))))

/-- The structure morphism `ℙⁿ_S ⟶ S`. -/
noncomputable def projectiveSpace.structureMorphism (n : ℕ) (S : Scheme.{u}) :
    projectiveSpace n S ⟶ S :=
  pullback.fst _ _

/-- `ℙⁿ_S` is canonically a scheme over `S`. -/
noncomputable instance (n : ℕ) (S : Scheme.{u}) : (projectiveSpace n S).Over S where
  hom := projectiveSpace.structureMorphism n S

/-- **Relative `Proj` of a graded sheaf / projective bundle** (`def:relative-proj`).

For a quasi-coherent sheaf (e.g. a vector bundle) `V` on `S`, the projective bundle
`ℙ(V) = Proj_S (Sym_{O_S} V)` is the relative `Proj` of the symmetric algebra.

MATHLIB GAP: relative `Proj` of a graded sheaf of `O_S`-algebras is **not** in
Mathlib (only the absolute graded-ring `AlgebraicGeometry.Proj` exists; STRATEGY.md
foundational-anchor table marks this a BUILD item — glue affine `Proj`s over a
trivialising cover of `S`).  We give a def-stub returning the scheme; the
construction is deferred. -/
noncomputable def relativeProj (S : Scheme.{u}) (_V : S.Modules) : Scheme.{u} :=
  sorry

/-- The structure morphism `ℙ(V) ⟶ S` of a projective bundle. -/
noncomputable def relativeProj.structureMorphism (S : Scheme.{u}) (V : S.Modules) :
    relativeProj S V ⟶ S :=
  sorry

/-- **Relatively very ample line bundle** (`def:very-ample`).

A line bundle `L` on `X/S` is relatively very ample when there is a closed immersion
`X ↪ ℙ(V)` over `S`, for some sheaf `V` on `S`, pulling `O_{ℙ(V)}(1)` back to `L`.

STATING-GAP: the clause "`i^* O_{ℙ(V)}(1) ≅ L`" cannot yet be stated, because the
tautological line bundle `O_{ℙ(V)}(1)` lives on the stub `relativeProj` and the
Serre twisting sheaves are a Mathlib gap.  We capture faithfully the part that *is*
expressible — a closed immersion into a projective bundle, compatible with the
structure morphisms — and defer the `O(1)`-pullback condition. -/
def RelativelyVeryAmple {X S : Scheme.{u}} (f : X ⟶ S) (_L : X.Modules) : Prop :=
  ∃ (V : S.Modules) (i : X ⟶ relativeProj S V),
    IsClosedImmersion i ∧ i ≫ relativeProj.structureMorphism S V = f

/-! ## Cohomology of projective morphisms — foundational anchors (EGA III) -/

/-- **Coherence and finiteness of higher direct images** (`thm:coherent-higher-direct-image`).

For a projective morphism `π : X ⟶ S` of noetherian schemes and a coherent sheaf
`F` on `X`, each `Rⁱπ_* F` is coherent on `S` and vanishes above the fibre
dimension.

MATHLIB GAP: higher direct images `Rⁱπ_*` (derived pushforward) and a
coherence/finite-type predicate for sheaves of modules are absent.  The closest
honest approximation expressible with the available API (`IsProper`,
`Scheme.Modules.pushforward`, `IsQuasicoherent`) is the `i = 0`, quasi-coherence
shadow: the underived direct image of a quasi-coherent sheaf along a proper
morphism is quasi-coherent.  The full coherence + `Rⁱ` + fibre-dimension-vanishing
statement is tracked for discharge once derived pushforward lands in Mathlib. -/
theorem coherent_higher_direct_image {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (F : X.Modules) (_hF : F.IsQuasicoherent) :
    ((Scheme.Modules.pushforward f).obj F).IsQuasicoherent :=
  sorry

/-- **Serre vanishing and global generation** (`thm:serre-vanishing`).

For a coherent sheaf `F` on `ℙⁿ_S` with `S` noetherian affine, there is `r₀` such
that for all `r ≥ r₀` the twist `F(r)` is globally generated and
`Hⁱ(ℙⁿ_S, F(r)) = 0` for `i ≥ 1`.

MATHLIB GAP: the Serre twisting sheaves `O(r)` (hence `F(r)`) and coherent sheaf
cohomology `Hⁱ` are both absent.  The twist family `F(·)` is therefore taken as
abstract input data `twist : ℤ → (ℙⁿ_S).Modules`.  The clause we can state
honestly is **global generation**: for `r` large, `twist r` is generated by finitely
many global sections (an epimorphism from a finite free sheaf).  The `Hⁱ = 0` clause
is the remaining stating-gap, deferred until coherent cohomology is available. -/
theorem serre_vanishing {S : Scheme.{u}} (_hS : IsAffine S) (n : ℕ)
    (F : (projectiveSpace n S).Modules) (_hF : F.IsQuasicoherent)
    (twist : ℤ → (projectiveSpace n S).Modules) :
    ∃ r₀ : ℕ, ∀ r : ℤ, (r₀ : ℤ) ≤ r →
      ∃ (k : ℕ)
        (g : SheafOfModules.free (R := (projectiveSpace n S).ringCatSheaf)
              (ULift.{u} (Fin k)) ⟶ twist r),
        Epi g :=
  sorry

/-- **Cohomology and base change** (`thm:cohomology-base-change`).

For `π : X ⟶ S` projective with `F` coherent on `X` and flat over `S`, there is a
bounded complex `K•` of finite locally free `O_S`-modules computing the cohomology
of `F` universally: for every base change `φ : T ⟶ S`,
`Rⁱπ_{T*} F_T ≅ Hⁱ(φ^* K•)`.

MATHLIB GAP: the Grothendieck complex and derived pushforward `Rⁱ` are absent.  The
expressible honest shadow is the `i = 0` **flat base change isomorphism**: for the
underived pushforward, `φ^* (π_* F) ≅ π_{T*} (F_T)`, where `X_T = X ×_S T`,
`π_T = pr_T`, and `F_T = pr_X^* F`.  The universal-complex / `Rⁱ` form is deferred. -/
theorem cohomology_and_base_change {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (_hF : F.IsQuasicoherent) {T : Scheme.{u}} (φ : T ⟶ S) :
    Nonempty
      ((Scheme.Modules.pullback φ).obj ((Scheme.Modules.pushforward f).obj F) ≅
        (Scheme.Modules.pushforward (pullback.snd f φ)).obj
          ((Scheme.Modules.pullback (pullback.fst f φ)).obj F)) :=
  sorry

/-! ## Valuative criterion and descent -/

/-- **Valuative criterion of properness** (`thm:valuative-criterion-properness`).

A quasi-compact, quasi-separated, locally-of-finite-type morphism satisfying the
valuative criterion is proper.  This is a thin wrapper around Mathlib's
`AlgebraicGeometry.IsProper.of_valuativeCriterion` (Mathlib anchor — no proof
obligation; review will mark `\mathlibok`). -/
theorem valuativeCriterion_proper {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    (H : ValuativeCriterion f) : IsProper f :=
  IsProper.of_valuativeCriterion f H

/-- **Faithfully flat descent for quasi-coherent sheaves** (`thm:ffdescent`).

Quasi-coherent sheaves descend along faithfully flat quasi-compact morphisms; only
the qualitative "the functor is a sheaf" form is used downstream.

MATHLIB GAP: the full fppf-descent equivalence (descent data ⥤ sheaves on the base)
is not packaged in Mathlib.  The expressible qualitative shadow is conservativity of
pullback: for a faithfully flat (`Flat` + surjective) quasi-compact morphism, the
pullback functor on sheaves of modules is faithful — isomorphisms (and morphisms)
can be checked after pulling back to the cover.  The full descent equivalence is
deferred. -/
theorem faithfullyFlatDescent {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [QuasiCompact f]
    (_hf : Function.Surjective f.base) :
    (Scheme.Modules.pullback f).Faithful :=
  sorry

/-! ## Project-local Mathlib supplement — relativeProj single-chart model

This section builds the **single affine chart** of the relative `Proj` (projective
bundle) construction: over an affine `Spec A` on which the sheaf `V` is free of rank
`n + 1`, the symmetric algebra `Sym_{O_S} V` restricts to the polynomial ring
`A[t₀,…,tₙ]` with its standard `ℕ`-grading by total degree, and the chart model of
`ℙ(V)` is the Mathlib graded-ring `Proj A[t₀,…,tₙ]`.

Everything here is project-local glue assembling Mathlib anchors (`Proj`,
`Proj.toSpecZero`, `Proj.isSeparated`, the proper instance) into the named
single-chart objects that the later gluing step (`relativeProj`) will consume. No
new mathematics — the heavy lifting is all in Mathlib. -/

section ProjChart

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The standard `ℕ`-grading on `A[t₀,…,tₙ] = MvPolynomial (Fin (n+1)) A` by total
degree, as the family of homogeneous submodules.  Its degree-zero part is `A`
(`MvPolynomial.homogeneousSubmodule_zero` : `… 0 = 1`).  Project-local name for the
chart grading of the relative-`Proj` build. -/
abbrev projChartGrading : ℕ → Submodule A (MvPolynomial (Fin (n + 1)) A) :=
  homogeneousSubmodule (Fin (n + 1)) A

/-- The single trivialising chart of the projective bundle `ℙ(V)` over an affine
`Spec A` on which `V` is free of rank `n + 1`: the graded-ring `Proj` of the
polynomial ring `A[t₀,…,tₙ]`.  Project-local; the relative `Proj` is glued from
copies of this over a trivialising affine cover of the base. -/
noncomputable def projChart : Scheme.{u} :=
  Proj (projChartGrading A n)

/-- The structure morphism `Proj A[t•] ⟶ Spec (A[t•]₀)` of the single chart, via the
Mathlib anchor `AlgebraicGeometry.Proj.toSpecZero`.  The degree-zero part `A[t•]₀` is
`A` (it is the unit submodule, `homogeneousSubmodule_zero`).  Project-local. -/
noncomputable def projChartToSpecZero :
    projChart A n ⟶ Spec (.of (projChartGrading A n 0)) :=
  Proj.toSpecZero _

/-- The base ring `A` acts on `A[t•]` through its degree-zero piece `A[t•]₀`:
`A → A[t•]₀ ↪ A[t•]` is the constant-coefficient inclusion `C`.  Needed to transfer
finiteness of `A[t•]` from base `A` to base `A[t•]₀`. -/
instance : IsScalarTower A (projChartGrading A n 0) (MvPolynomial (Fin (n + 1)) A) :=
  IsScalarTower.of_algebraMap_eq fun a => by
    rw [SetLike.GradeZero.algebraMap_apply, SetLike.GradeZero.coe_algebraMap]

/-- `A[t₀,…,tₙ]` is of finite type over its degree-zero subring `A[t•]₀` (it is
generated by the `n+1` variables).  This is the hypothesis that makes the chart
structure morphism proper.  Project-local: Mathlib has the finite-type instance only
over the *base* `A`, so we transfer it down the tower `A → A[t•]₀ → A[t•]`. -/
instance projChart_finiteType :
    Algebra.FiniteType (projChartGrading A n 0) (MvPolynomial (Fin (n + 1)) A) :=
  Algebra.FiniteType.of_restrictScalars_finiteType A _ _

/-- The single-chart structure morphism is **separated** (unconditional Mathlib fact
`AlgebraicGeometry.Proj.isSeparated`). -/
instance projChartToSpecZero_isSeparated : IsSeparated (projChartToSpecZero A n) :=
  Proj.isSeparated _

/-- The single-chart structure morphism is **proper** (Mathlib `Proj` properness under
finite type of the graded ring over its degree-zero part, supplied above). -/
instance projChartToSpecZero_isProper : IsProper (projChartToSpecZero A n) :=
  inferInstanceAs (IsProper (Proj.toSpecZero _))

/-- The canonical map `A → A[t•]₀` (constants into the degree-zero part) is bijective:
this is the formal content of "`A[t•]₀ = A`".  Injective because it is `C` followed by
the (injective) subtype coercion; surjective because every degree-zero homogeneous
polynomial is a constant (`homogeneousSubmodule_zero`). -/
lemma algebraMap_projChartGradeZero_bijective :
    Function.Bijective (algebraMap A (projChartGrading A n 0)) := by
  refine ⟨fun a b h => ?_, fun y => ?_⟩
  · apply MvPolynomial.C_injective (Fin (n + 1)) A
    have h' := congrArg (Subtype.val) h
    rwa [SetLike.GradeZero.coe_algebraMap, SetLike.GradeZero.coe_algebraMap,
      MvPolynomial.algebraMap_eq] at h'
  · have hy : (y : MvPolynomial (Fin (n + 1)) A) ∈ homogeneousSubmodule (Fin (n + 1)) A 0 := y.2
    rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.one_eq_range] at hy
    obtain ⟨a, ha⟩ := hy
    refine ⟨a, Subtype.ext ?_⟩
    rw [SetLike.GradeZero.coe_algebraMap, ← Algebra.linearMap_apply]
    exact ha

/-- The ring isomorphism `A ≃+* A[t•]₀` identifying the base ring `A` with the
degree-zero part of `A[t₀,…,tₙ]`.  Project-local witness of "`A[t•]₀ = A`", used to
retarget the chart structure morphism from `Spec A[t•]₀` to `Spec A`. -/
noncomputable def projChartGradeZeroEquiv : A ≃+* projChartGrading A n 0 :=
  RingEquiv.ofBijective (algebraMap A (projChartGrading A n 0))
    (algebraMap_projChartGradeZero_bijective A n)

/-- The retargeting isomorphism `Spec A[t•]₀ ≅ Spec A` of affine schemes, induced by
`projChartGradeZeroEquiv`.  Composing the chart structure morphism with it lands the
chart over the honest base `Spec A`. -/
noncomputable def specGradeZeroIsoSpecBase :
    Spec (.of (projChartGrading A n 0)) ≅ Spec (.of A) :=
  asIso (Spec.map (projChartGradeZeroEquiv A n).toCommRingCatIso.hom)

/-- The single chart's structure morphism **to the honest base** `Spec A`:
`Proj A[t₀,…,tₙ] ⟶ Spec A`, obtained from `Proj.toSpecZero` by identifying
`A[t•]₀` with `A`.  This is the affine-local model of the relative-`Proj` structure
morphism `ℙ(V) ⟶ S` (blueprint `def:relative-proj` step 1 / step 5). -/
noncomputable def projChartToSpecBase : projChart A n ⟶ Spec (.of A) :=
  projChartToSpecZero A n ≫ (specGradeZeroIsoSpecBase A n).hom

/-- The chart structure morphism over `Spec A` is **separated** (composition of the
separated `Proj.toSpecZero` with the iso `Spec A[t•]₀ ≅ Spec A`). -/
instance projChartToSpecBase_isSeparated : IsSeparated (projChartToSpecBase A n) := by
  rw [projChartToSpecBase]; infer_instance

/-- The chart structure morphism over `Spec A` is **proper** (composition of the proper
`Proj.toSpecZero` with the iso `Spec A[t•]₀ ≅ Spec A`).  This is the affine-local
properness fact gating `lem:quot-properness` once the charts are glued. -/
instance projChartToSpecBase_isProper : IsProper (projChartToSpecBase A n) := by
  rw [projChartToSpecBase]; infer_instance

end ProjChart

/-! ## Project-local Mathlib supplement — relativeProj frame-change transition isos

The relative `Proj` is glued from the affine charts `projChart A n = Proj A[t₀,…,tₙ]`
over a trivialising affine cover of the base `S`.  On an overlap of two trivialising
opens the sheaf `V` is identified two ways, differing by an invertible frame change
`g ∈ GLₙ₊₁(A)`.  This section builds the induced **transition automorphism** of the
chart `Proj A[t•]`:

* `projChartFrameHom g` — the graded ring endomorphism of `A[t•]` given by the linear
  change of variables `tᵢ ↦ Σⱼ gᵢⱼ tⱼ` (degree-preserving, hence graded).
* `projChartFrameHom_comp` / `projChartFrameHom_one` — the functoriality identities
  `frameHom g₂ ∘ frameHom g₁ = frameHom (g₁ * g₂)` and `frameHom 1 = id`.  These are
  the **matrix cocycle** at the level of the substitution maps.
* `projChartFrameMapIso g (h := g⁻¹)` — the resulting isomorphism of schemes
  `Proj A[t•] ≅ Proj A[t•]`, via Mathlib's `AlgebraicGeometry.Proj.map` functoriality,
  with inverse the frame-change for `g⁻¹`.

This realises `def:relative-proj` step 3 (transition isomorphisms of charts).  The
eventual cross-`S` `GlueData` will use `projChartFrameMapIso` as its transition field
`t` and `projChartFrameHom_comp` as the cocycle; both are project-local glue over the
Mathlib `Proj.map` anchor (no new mathematics). -/

section ProjChartFrame

variable (A : Type u) [CommRing A] (n : ℕ)

/-- The degree-`1` substitution vector of a frame change `g`: the `i`-th variable
`tᵢ` is sent to the linear form `Σⱼ gᵢⱼ tⱼ`.  Feeding it to `MvPolynomial.aeval`
produces the graded ring endomorphism `projChartFrameHom g`. -/
noncomputable def projChartFrameSubst (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) A :=
  fun i => ∑ j, C (g i j) * X j

/-- Each component `Σⱼ gᵢⱼ tⱼ` of the frame-change substitution is homogeneous of
degree `1` (a sum of the degree-`1` monomials `gᵢⱼ · tⱼ`).  This is what makes the
induced `aeval` graded. -/
lemma projChartFrameSubst_isHomogeneous (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (i : Fin (n + 1)) : (projChartFrameSubst A n g i).IsHomogeneous 1 := by
  rw [projChartFrameSubst]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
  simpa using (MvPolynomial.isHomogeneous_C _ (g i j)).mul (MvPolynomial.isHomogeneous_X A j)

/-- The transition endomorphism of the chart `A[t₀,…,tₙ]` attached to a frame change
`g ∈ Matₙ₊₁(A)`: the graded ring hom `tᵢ ↦ Σⱼ gᵢⱼ tⱼ`.  Graded because the
substitution lands each variable in degree `1`, so `aeval` preserves total degree
(`MvPolynomial.IsHomogeneous.aeval`). -/
noncomputable def projChartFrameHom (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) :
    projChartGrading A n →+*ᵍ projChartGrading A n where
  toRingHom := (aeval (projChartFrameSubst A n g)).toRingHom
  map_mem := by
    intro d x hx
    rw [projChartGrading, MvPolynomial.mem_homogeneousSubmodule] at hx ⊢
    simpa using hx.aeval (projChartFrameSubst A n g) (projChartFrameSubst_isHomogeneous A n g)

/-- The underlying function of `projChartFrameHom g` is `aeval` of the substitution
vector — definitional unfolding used to compute composites. -/
lemma projChartFrameHom_apply (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (x : MvPolynomial (Fin (n + 1)) A) :
    projChartFrameHom A n g x = aeval (projChartFrameSubst A n g) x := rfl

/-- The substitution maps compose by matrix multiplication: substituting
`tᵢ ↦ Σⱼ (g₁)ᵢⱼ tⱼ` and then `tⱼ ↦ Σₖ (g₂)ⱼₖ tₖ` is the single substitution
`tᵢ ↦ Σₖ (g₁·g₂)ᵢₖ tₖ`.  This is the entrywise matrix-cocycle computation. -/
lemma projChartFrameSubst_comp (g₁ g₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (i : Fin (n + 1)) :
    aeval (projChartFrameSubst A n g₂) (projChartFrameSubst A n g₁ i) =
      projChartFrameSubst A n (g₁ * g₂) i := by
  simp only [projChartFrameSubst, map_sum, map_mul, aeval_C, aeval_X,
    MvPolynomial.algebraMap_eq, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_assoc]

/-- **Functoriality / cocycle of the frame-change homs.**
`frameHom g₂ ∘ frameHom g₁ = frameHom (g₁ * g₂)`.  The transition maps of the chart
compose by matrix multiplication — the cocycle datum for the eventual `GlueData`. -/
lemma projChartFrameHom_comp (g₁ g₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) A) :
    (projChartFrameHom A n g₂).comp (projChartFrameHom A n g₁) =
      projChartFrameHom A n (g₁ * g₂) := by
  ext x
  rw [GradedRingHom.comp_apply, projChartFrameHom_apply, projChartFrameHom_apply,
    projChartFrameHom_apply, ← AlgHom.comp_apply, comp_aeval]
  have hfun : (fun i => aeval (projChartFrameSubst A n g₂) (projChartFrameSubst A n g₁ i)) =
      projChartFrameSubst A n (g₁ * g₂) := funext (projChartFrameSubst_comp A n g₁ g₂)
  rw [hfun]

/-- The identity frame change `g = 1` induces the identity graded ring hom. -/
lemma projChartFrameHom_one :
    projChartFrameHom A n (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) =
      GradedRingHom.id (projChartGrading A n) := by
  ext x
  rw [projChartFrameHom_apply, GradedRingHom.id_apply]
  have : projChartFrameSubst A n (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) A) = X := by
    funext i
    simp [projChartFrameSubst, Matrix.one_apply, Finset.sum_ite_eq]
  rw [this, aeval_X_left, AlgHom.id_apply]

/-- The frame change `g` together with a left inverse `h` (`h * g = 1`) satisfies the
irrelevant-ideal hypothesis `𝒜₊ ≤ 𝒜₊.map (frameHom g)` required by
`AlgebraicGeometry.Proj.map`.  Reason: `frameHom g` is surjective with section
`frameHom h` (from `projChartFrameHom_comp` + `projChartFrameHom_one`), and it
preserves the grading, so every positive-degree homogeneous `a` is `frameHom g` of the
same-degree `frameHom h a ∈ 𝒜₊`. -/
lemma projChartFrameHom_irrelevant_le
    (g h : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (hgh : h * g = 1) :
    HomogeneousIdeal.irrelevant (projChartGrading A n) ≤
      (HomogeneousIdeal.irrelevant (projChartGrading A n)).map (projChartFrameHom A n g) := by
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi a ha
  have ha' : a ∈ projChartGrading A n i := ha
  have hb_mem : projChartFrameHom A n h a ∈ projChartGrading A n i :=
    (projChartFrameHom A n h).map_mem ha'
  have hb_irr : projChartFrameHom A n h a ∈
      HomogeneousIdeal.irrelevant (projChartGrading A n) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ hi hb_mem
  have hfg : projChartFrameHom A n g (projChartFrameHom A n h a) = a := by
    have hc := congrArg (fun φ : _ →+*ᵍ _ => φ a) (projChartFrameHom_comp A n h g)
    simp only [GradedRingHom.comp_apply] at hc
    rw [hc, hgh, projChartFrameHom_one, GradedRingHom.id_apply]
  have hmem : projChartFrameHom A n g (projChartFrameHom A n h a) ∈
      ((HomogeneousIdeal.irrelevant (projChartGrading A n)).map
        (projChartFrameHom A n g)).toIdeal := by
    rw [HomogeneousIdeal.toIdeal_map]
    exact Ideal.mem_map_of_mem _ hb_irr
  rw [hfg] at hmem
  exact hmem

/-- Two chart transition morphisms with equal underlying graded ring homs agree: the
irrelevant-ideal hypothesis of `Proj.map` is a `Prop`, hence proof-irrelevant.  Used to
collapse `frameHom g₂ ∘ frameHom g₁ = frameHom (g₁·g₂)` down to the scheme level. -/
lemma projChartFrameMap_congr
    {f₁ f₂ : projChartGrading A n →+*ᵍ projChartGrading A n}
    (hf₁ : HomogeneousIdeal.irrelevant (projChartGrading A n) ≤
      (HomogeneousIdeal.irrelevant (projChartGrading A n)).map f₁)
    (hf₂ : HomogeneousIdeal.irrelevant (projChartGrading A n) ≤
      (HomogeneousIdeal.irrelevant (projChartGrading A n)).map f₂)
    (he : f₁ = f₂) :
    Proj.map f₁ hf₁ = Proj.map f₂ hf₂ := by
  subst he; rfl

/-- The **chart transition morphism** `Proj A[t•] ⟶ Proj A[t•]` attached to a frame
change `g` with left inverse `h` (`h * g = 1`): the `AlgebraicGeometry.Proj.map`
functoriality applied to the graded ring hom `projChartFrameHom g`.  This is the
GlueData transition field `t` of the relative-`Proj` construction (`def:relative-proj`
step 3). -/
noncomputable def projChartFrameMap
    (g h : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (hgh : h * g = 1) :
    projChart A n ⟶ projChart A n :=
  Proj.map (projChartFrameHom A n g) (projChartFrameHom_irrelevant_le A n g h hgh)

/-- **Scheme-level cocycle** of the chart transition morphisms: composing the
transition for `g₁` with the transition for `g₂` is the transition for the matrix
product `g₂ * g₁`.  This is the GlueData cocycle field `t i j ≫ t j k = t i k` at the
level of the chart `Proj`, descended from `projChartFrameHom_comp` via
`AlgebraicGeometry.Proj.map_comp`. -/
lemma projChartFrameMap_comp
    (g₁ h₁ g₂ h₂ : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (hg1 : h₁ * g₁ = 1) (hg2 : h₂ * g₂ = 1) :
    projChartFrameMap A n g₁ h₁ hg1 ≫ projChartFrameMap A n g₂ h₂ hg2 =
      projChartFrameMap A n (g₂ * g₁) (h₁ * h₂)
        (by rw [mul_assoc, ← mul_assoc h₂, hg2, one_mul, hg1]) := by
  refine ((Proj.map_comp (projChartFrameHom A n g₂) (projChartFrameHom A n g₁)
    _ _).symm).trans ?_
  exact projChartFrameMap_congr A n _ _ (projChartFrameHom_comp A n g₂ g₁)

/-- The chart transition morphism for an **invertible** frame change `g` is an
isomorphism `Proj A[t•] ≅ Proj A[t•]`, with inverse the transition for `g⁻¹ = ⅟g`.
The two round-trips collapse to `Proj.map` of the identity via `projChartFrameHom_comp`
+ `projChartFrameHom_one` and `Proj.map_id`.  This realises the cocycle-compatible
transition isos of `def:relative-proj` step 3. -/
noncomputable def projChartFrameMapIso
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) [Invertible g] :
    projChart A n ≅ projChart A n where
  hom := Proj.map (projChartFrameHom A n g)
    (projChartFrameHom_irrelevant_le A n g (⅟g) (invOf_mul_self g))
  inv := Proj.map (projChartFrameHom A n (⅟g))
    (projChartFrameHom_irrelevant_le A n (⅟g) g (mul_invOf_self g))
  hom_inv_id := by
    refine ((Proj.map_comp (projChartFrameHom A n (⅟g)) (projChartFrameHom A n g)
      _ _).symm).trans ?_
    refine (projChartFrameMap_congr A n _ (HomogeneousIdeal.map_id.ge) ?_).trans Proj.map_id
    rw [projChartFrameHom_comp, invOf_mul_self, projChartFrameHom_one]
  inv_hom_id := by
    refine ((Proj.map_comp (projChartFrameHom A n g) (projChartFrameHom A n (⅟g))
      _ _).symm).trans ?_
    refine (projChartFrameMap_congr A n _ (HomogeneousIdeal.map_id.ge) ?_).trans Proj.map_id
    rw [projChartFrameHom_comp, mul_invOf_self, projChartFrameHom_one]

end ProjChartFrame

/-! ## Project-local Mathlib supplement — relativeProj base-change transition (step 4)

In the cross-`S` `Scheme.GlueData` (`def:relative-proj` step 4), an overlap of two
trivialising affines `Spec A_α, Spec A_β` of `S` is itself covered by affines
`Spec A_{αβ}`, and the chart over the overlap is `Proj A_{αβ}[t•]`.  Passing from a
chart `Proj A_α[t•]` to the overlap chart is induced by the base ring map
`A_α → A_{αβ}` applied to coefficients.  This section builds that induced
**base-change transition morphism**, mirroring the frame-change chain:

* `projChartBaseHom φ` — the graded ring hom `A[t•] →+*ᵍ A'[t•]` given by
  `MvPolynomial.map φ` (apply `φ` to coefficients).  Graded because applying `φ`
  to coefficients preserves each monomial's total degree
  (`MvPolynomial.IsHomogeneous.map`).
* `projChartBaseHom_irrelevant_le` — the irrelevant-ideal hypothesis of `Proj.map`:
  every variable `tᵢ` maps to `tᵢ`, so the irrelevant generators are in the image.
* `projChartBaseMap φ` — the resulting morphism `Proj A'[t•] ⟶ Proj A[t•]` via
  `AlgebraicGeometry.Proj.map`, contravariant in `φ`.

Composed with `projChartFrameMap` over the overlap ring `A_{αβ}` this is the full
chart transition of the cross-`S` GlueData.  All project-local glue over the Mathlib
`Proj.map` anchor — no new mathematics. -/

section ProjChartBase

variable (A A' : Type u) [CommRing A] [CommRing A'] (n : ℕ)

/-- The **base-change graded ring hom** of the chart attached to a ring hom
`φ : A →+* A'`: the graded ring hom `A[t•] →+*ᵍ A'[t•]` applying `φ` to coefficients
(`MvPolynomial.map φ`).  Graded because `φ` acts on coefficients only, so the total
degree of every monomial is preserved (`MvPolynomial.IsHomogeneous.map`).  This is the
coefficient-base-change half of the cross-`S` chart transition (`def:relative-proj`
step 4). -/
noncomputable def projChartBaseHom (φ : A →+* A') :
    projChartGrading A n →+*ᵍ projChartGrading A' n where
  toRingHom := MvPolynomial.map φ
  map_mem := by
    intro i x hx
    rw [projChartGrading, MvPolynomial.mem_homogeneousSubmodule] at hx ⊢
    exact hx.map φ

/-- The underlying ring hom of `projChartBaseHom φ` is `MvPolynomial.map φ` —
definitional unfolding used to compute its action on variables and constants. -/
lemma projChartBaseHom_apply (φ : A →+* A') (x : MvPolynomial (Fin (n + 1)) A) :
    projChartBaseHom A A' n φ x = MvPolynomial.map φ x := rfl

/-- The base-change hom satisfies the irrelevant-ideal hypothesis required by
`AlgebraicGeometry.Proj.map`: `𝒜'₊ ≤ 𝒜₊.map (projChartBaseHom φ)`.  Reason: each
variable `tᵢ` maps to `tᵢ` (`MvPolynomial.map_X`), and `tᵢ ∈ 𝒜₊`, so every variable
of the target lies in the mapped ideal; a positive-degree homogeneous polynomial has
every monomial divisible by some variable
(`MvPolynomial.mem_ideal_span_X_image`), hence lies in the ideal generated by the
variables, which is contained in the mapped ideal. -/
lemma projChartBaseHom_irrelevant_le (φ : A →+* A') :
    HomogeneousIdeal.irrelevant (projChartGrading A' n) ≤
      (HomogeneousIdeal.irrelevant (projChartGrading A n)).map (projChartBaseHom A A' n φ) := by
  -- every variable of the target lies in the mapped irrelevant ideal
  have hXmem : ∀ j : Fin (n + 1),
      (X j : MvPolynomial (Fin (n + 1)) A') ∈
        ((HomogeneousIdeal.irrelevant (projChartGrading A n)).map
          (projChartBaseHom A A' n φ)).toIdeal := by
    intro j
    rw [HomogeneousIdeal.toIdeal_map]
    have hXA : (X j : MvPolynomial (Fin (n + 1)) A) ∈
        HomogeneousIdeal.irrelevant (projChartGrading A n) := by
      refine HomogeneousIdeal.mem_irrelevant_of_mem (projChartGrading A n) (i := 1) one_pos ?_
      rw [projChartGrading, MvPolynomial.mem_homogeneousSubmodule]
      exact isHomogeneous_X A j
    have hmap : projChartBaseHom A A' n φ (X j) = X j := by
      rw [projChartBaseHom_apply, MvPolynomial.map_X]
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hXA
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi a ha
  have haH : (a : MvPolynomial (Fin (n + 1)) A').IsHomogeneous i := by
    have ha' : a ∈ projChartGrading A' n i := ha
    rwa [projChartGrading, MvPolynomial.mem_homogeneousSubmodule] at ha'
  -- `a` lies in the ideal generated by the variables
  have hspan : a ∈ Ideal.span (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A')) := by
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    rw [MvPolynomial.mem_support_iff] at hm
    have hdeg : Finsupp.degree m = i := by
      by_contra hne
      exact hm (haH.coeff_eq_zero hne)
    have hne0 : ∃ j, m j ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_not] at hcon
      have hm0 : m = 0 := by ext j; exact hcon j
      rw [hm0, map_zero] at hdeg
      omega
    obtain ⟨j, hj⟩ := hne0
    exact ⟨j, Set.mem_univ j, hj⟩
  -- the variable-ideal is contained in the mapped irrelevant ideal
  have hle : Ideal.span (Set.range (X : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A')) ≤
      ((HomogeneousIdeal.irrelevant (projChartGrading A n)).map
        (projChartBaseHom A A' n φ)).toIdeal := by
    rw [Ideal.span_le]
    rintro x ⟨j, rfl⟩
    exact hXmem j
  exact hle hspan

/-- The **base-change transition morphism** `Proj A'[t•] ⟶ Proj A[t•]` attached to a
ring hom `φ : A →+* A'`: the `AlgebraicGeometry.Proj.map` functoriality applied to the
graded ring hom `projChartBaseHom φ` (contravariant in `φ`).  Composed with the
frame-change `projChartFrameMap` over the overlap ring, it is the full chart transition
of the cross-`S` GlueData (`def:relative-proj` step 4). -/
noncomputable def projChartBaseMap (φ : A →+* A') :
    projChart A' n ⟶ projChart A n :=
  Proj.map (projChartBaseHom A A' n φ) (projChartBaseHom_irrelevant_le A A' n φ)

/-- `Proj.map` is congruent in its graded-hom argument (base-change variant, between
the two distinct chart gradings of `A` and `A'`): equal homs give equal morphisms, the
irrelevant-ideal proof being proof-irrelevant.  Used to collapse the base-change
functoriality identity to the scheme level. -/
lemma projChartBaseMap_congr
    {f₁ f₂ : projChartGrading A n →+*ᵍ projChartGrading A' n}
    (h₁ : HomogeneousIdeal.irrelevant (projChartGrading A' n) ≤
      (HomogeneousIdeal.irrelevant (projChartGrading A n)).map f₁)
    (h₂ : HomogeneousIdeal.irrelevant (projChartGrading A' n) ≤
      (HomogeneousIdeal.irrelevant (projChartGrading A n)).map f₂)
    (he : f₁ = f₂) :
    Proj.map f₁ h₁ = Proj.map f₂ h₂ := by
  subst he; rfl

/-- The identity ring map induces the identity base-change hom: `projChartBaseHom (id) =
GradedRingHom.id`, since `MvPolynomial.map (RingHom.id) = id` (`MvPolynomial.map_id`).
The unit of the base-change functoriality. -/
lemma projChartBaseHom_id :
    projChartBaseHom A A n (RingHom.id A) = GradedRingHom.id (projChartGrading A n) := by
  refine GradedRingHom.ext fun x => ?_
  rw [projChartBaseHom_apply, GradedRingHom.id_apply, MvPolynomial.map_id]

/-- The identity ring map induces the identity chart transition:
`projChartBaseMap (id) = 𝟙`, collapsing via `projChartBaseHom_id` and `Proj.map_id`.
The unit / diagonal datum of the cross-`S` GlueData. -/
lemma projChartBaseMap_id :
    projChartBaseMap A A n (RingHom.id A) = 𝟙 (projChart A n) := by
  rw [projChartBaseMap]
  exact (projChartBaseMap_congr A A n _ HomogeneousIdeal.map_id.ge
    (projChartBaseHom_id A n)).trans Proj.map_id

end ProjChartBase

section ProjChartBaseComp

variable (A A' A'' : Type u) [CommRing A] [CommRing A'] [CommRing A''] (n : ℕ)

/-- **Composition law of the base-change homs** (covariant in the ring map):
`projChartBaseHom ψ ∘ projChartBaseHom φ = projChartBaseHom (ψ ∘ φ)`, since
`MvPolynomial.map` is functorial in the coefficient ring map
(`MvPolynomial.map_map`). -/
lemma projChartBaseHom_comp (φ : A →+* A') (ψ : A' →+* A'') :
    (projChartBaseHom A' A'' n ψ).comp (projChartBaseHom A A' n φ) =
      projChartBaseHom A A'' n (ψ.comp φ) := by
  refine GradedRingHom.ext fun x => ?_
  rw [GradedRingHom.comp_apply, projChartBaseHom_apply, projChartBaseHom_apply,
    projChartBaseHom_apply]
  exact MvPolynomial.map_map φ ψ x

/-- **Scheme-level functoriality / cocycle of the base-change transitions**
(contravariant in the ring map): `projChartBaseMap (ψ ∘ φ) =
projChartBaseMap ψ ≫ projChartBaseMap φ`, descended from `projChartBaseHom_comp` via
`AlgebraicGeometry.Proj.map_comp`.  This is the base-change half of the cross-`S`
GlueData cocycle. -/
lemma projChartBaseMap_comp (φ : A →+* A') (ψ : A' →+* A'') :
    projChartBaseMap A A'' n (ψ.comp φ) =
      projChartBaseMap A' A'' n ψ ≫ projChartBaseMap A A' n φ := by
  refine Eq.trans ?_ (Proj.map_comp (projChartBaseHom A A' n φ) (projChartBaseHom A' A'' n ψ)
    (projChartBaseHom_irrelevant_le A A' n φ) (projChartBaseHom_irrelevant_le A' A'' n ψ))
  rw [projChartBaseMap]
  exact projChartBaseMap_congr A A'' n (projChartBaseHom_irrelevant_le A A'' n (ψ.comp φ)) _
    (projChartBaseHom_comp A A' A'' n φ ψ).symm

end ProjChartBaseComp

/-! ## Project-local Mathlib supplement — naturality of `Proj.toSpecZero` along `Proj.map` (step 5)

For the affine charts of the relative `Proj` to glue to a scheme *over* `S`
(`def:relative-proj` step 5), the chart structure morphisms `projChartToSpecBase`
(built from `Proj.toSpecZero` by identifying `A[t•]₀ = A`) must be compatible with the
two halves of the chart transition.  Both are instances of the **naturality of
`Proj.toSpecZero` along `Proj.map`**, a square that is *absent* from Mathlib (only the
affine-chart versions `awayι_toSpecZero`, `awayι_comp_map` exist).  We build it here as
a project-local supplement, checking the equality on the affine open cover
`mapAffineOpenCover` of `Proj ℬ` and reducing to the ring identity
`Away.map f s ∘ fromZeroRingHom 𝒜 = fromZeroRingHom ℬ ∘ f₀` (`f₀ = degree-0 restriction). -/

section ProjMapToSpecZero

variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]

/-- The away-localization functoriality `HomogeneousLocalization.Away.map f s` commutes
with the degree-zero inclusion `fromZeroRingHom`: on the constant `a/1` it is `f a / 1`,
i.e. `Away.map f s ∘ fromZeroRingHom 𝒜 = fromZeroRingHom ℬ ∘ f₀` where
`f₀ = GradedRingHom.gradedZeroRingHom f` is the degree-zero restriction of `f`.  This is
the ring identity that powers the naturality of `Proj.toSpecZero` along `Proj.map`. -/
private lemma awayMap_comp_fromZeroRingHom (f : 𝒜 →+*ᵍ ℬ) (s : A) :
    (HomogeneousLocalization.Away.map f s).comp
        (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers s)) =
      (HomogeneousLocalization.fromZeroRingHom ℬ (Submonoid.powers (f s))).comp
        (GradedRingHom.gradedZeroRingHom f) := by
  ext a
  simp [HomogeneousLocalization.fromZeroRingHom, HomogeneousLocalization.Away.map,
    HomogeneousLocalization.map_mk]

/-- **Naturality of `Proj.toSpecZero` along `Proj.map`** (project-local; absent from
Mathlib).  For a graded ring hom `f : 𝒜 →+*ᵍ ℬ` satisfying the irrelevant-ideal
hypothesis `hf`, the square

```
Proj ℬ ----Proj.map f hf----> Proj 𝒜
  |                              |
toSpecZero ℬ                toSpecZero 𝒜
  v                              v
Spec ℬ₀ ---Spec.map f₀-------> Spec 𝒜₀
```

commutes, where `f₀ = GradedRingHom.gradedZeroRingHom f : 𝒜₀ →+* ℬ₀` is the degree-zero
restriction of `f` (note `Spec.map` and `Proj.map` are both contravariant).  Proved by
checking on the affine open cover `mapAffineOpenCover f hf` of `Proj ℬ`: on each chart
`awayι ℬ (f s)` the square reduces, via `awayι_comp_map` and `awayι_toSpecZero`, to the
ring identity `awayMap_comp_fromZeroRingHom`. -/
lemma projMap_toSpecZero (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (GradedRingHom.gradedZeroRingHom f)) := by
  refine (Proj.mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s => ?_
  simp only [Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f,
    Proj.mapAffineOpenCover_f]
  -- `erw` is needed where the cover's `awayι` carries proof-term arguments (`f_deg`, `hm`)
  -- that are only defeq — not syntactically equal — to those produced by `awayι_comp_map`.
  erw [Proj.awayι_comp_map_assoc f hf s.1.2 _ s.2.2]
  rw [Proj.awayι_toSpecZero]
  erw [Proj.awayι_toSpecZero_assoc]
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, awayMap_comp_fromZeroRingHom]

end ProjMapToSpecZero

/-! ## Project-local Mathlib supplement — chart structure-morphism compatibility (step 5)

The two halves of the chart transition must be compatible with the chart structure
morphism `projChartToSpecBase` for the charts to glue to a scheme *over* `S`
(`def:relative-proj` step 5).  Both follow from the naturality lemma `projMap_toSpecZero`,
transported through the identification `A[t•]₀ = A` (`specGradeZeroIsoSpecBase`) used to
define `projChartToSpecBase`. -/

section ProjChartToSpecBaseCompat

variable (A A' : Type u) [CommRing A] [CommRing A'] (n : ℕ)

/-- The frame-change graded hom is the **identity on the degree-zero part**: the substitution
`tᵢ ↦ Σⱼ gᵢⱼ tⱼ` fixes the constants `A[t•]₀ = A` pointwise, so
`(projChartFrameHom g)₀ = id`.  This is what makes the frame change leave the base projection
`projChartToSpecBase` unchanged. -/
lemma gradedZeroRingHom_projChartFrameHom
    (g : Matrix (Fin (n + 1)) (Fin (n + 1)) A) :
    GradedRingHom.gradedZeroRingHom (projChartFrameHom A n g) =
      RingHom.id (projChartGrading A n 0) := by
  refine RingHom.ext fun a => Subtype.ext ?_
  change projChartFrameHom A n g (a : MvPolynomial (Fin (n + 1)) A)
    = (a : MvPolynomial (Fin (n + 1)) A)
  obtain ⟨c, hc⟩ : ∃ c, (a : MvPolynomial (Fin (n + 1)) A) = C c := by
    have ha : (a : MvPolynomial (Fin (n + 1)) A) ∈ homogeneousSubmodule (Fin (n + 1)) A 0 := a.2
    rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.one_eq_range] at ha
    obtain ⟨c, hc⟩ := ha
    exact ⟨c, by rw [← hc]; rfl⟩
  rw [hc, projChartFrameHom_apply, aeval_C, MvPolynomial.algebraMap_eq]

/-- **Frame change fixes the base projection** (`lem:projchart-frame-map-tospecbase`).
`projChartFrameMap g ≫ projChartToSpecBase = projChartToSpecBase`.  The frame substitution
fixes the degree-zero part `A[t•]₀ = A` pointwise (`gradedZeroRingHom_projChartFrameHom`), so the
`Proj.map`–`toSpecZero` square (`projMap_toSpecZero`) collapses to `Spec.map (𝟙) = 𝟙`. -/
lemma projChartFrameMap_toSpecBase
    (g h : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (hgh : h * g = 1) :
    projChartFrameMap A n g h hgh ≫ projChartToSpecBase A n = projChartToSpecBase A n := by
  rw [projChartFrameMap, projChartToSpecBase, projChartToSpecZero, ← Category.assoc]
  -- `erw`: the `Proj.map` proof argument from `projChartFrameMap`'s definition is only defeq
  -- to the one in `projMap_toSpecZero`.
  erw [projMap_toSpecZero (projChartFrameHom A n g) (projChartFrameHom_irrelevant_le A n g h hgh)]
  rw [gradedZeroRingHom_projChartFrameHom, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]

/-- The base-change graded hom restricts on the degree-zero part to `φ` itself, transported
through `A[t•]₀ = A`, `A'[t•]₀ = A'`:
`(projChartBaseHom φ)₀ ∘ (A ≅ A[t•]₀) = (A' ≅ A'[t•]₀) ∘ φ`.  This is the ring identity behind
`projChartBaseMap_toSpecBase`; it holds because `MvPolynomial.map φ (C c) = C (φ c)`. -/
lemma gradedZeroRingHom_projChartBaseHom_comp (φ : A →+* A') :
    (GradedRingHom.gradedZeroRingHom (projChartBaseHom A A' n φ)).comp
        (projChartGradeZeroEquiv A n) =
      (projChartGradeZeroEquiv A' n : A' →+* projChartGrading A' n 0).comp φ := by
  refine RingHom.ext fun c => Subtype.ext ?_
  change projChartBaseHom A A' n φ (projChartGradeZeroEquiv A n c : MvPolynomial (Fin (n + 1)) A) =
    ((projChartGradeZeroEquiv A' n (φ c)) : MvPolynomial (Fin (n + 1)) A')
  have hA : (projChartGradeZeroEquiv A n c : MvPolynomial (Fin (n + 1)) A) = C c := by
    rw [projChartGradeZeroEquiv, RingEquiv.coe_ofBijective, SetLike.GradeZero.coe_algebraMap,
      MvPolynomial.algebraMap_eq]
  have hA' : (projChartGradeZeroEquiv A' n (φ c) : MvPolynomial (Fin (n + 1)) A') = C (φ c) := by
    rw [projChartGradeZeroEquiv, RingEquiv.coe_ofBijective, SetLike.GradeZero.coe_algebraMap,
      MvPolynomial.algebraMap_eq]
  rw [hA, hA', projChartBaseHom_apply, MvPolynomial.map_C]

/-- The `Spec`-level half of `projChartBaseMap_toSpecBase`: the degree-zero hom of the base
change, post-composed with the `A[t•]₀ = A` identification, equals the `A'[t•]₀ = A'`
identification followed by `Spec φ`.  Pure `Spec`-functoriality of
`gradedZeroRingHom_projChartBaseHom_comp`. -/
private lemma specMap_gradedZeroRingHom_projChartBaseHom (φ : A →+* A') :
    Spec.map (CommRingCat.ofHom (GradedRingHom.gradedZeroRingHom (projChartBaseHom A A' n φ))) ≫
        (specGradeZeroIsoSpecBase A n).hom =
      (specGradeZeroIsoSpecBase A' n).hom ≫ Spec.map (CommRingCat.ofHom φ) := by
  simp only [specGradeZeroIsoSpecBase, asIso_hom]
  rw [← Spec.map_comp, ← Spec.map_comp,
    RingEquiv.toCommRingCatIso_hom, RingEquiv.toCommRingCatIso_hom,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
    gradedZeroRingHom_projChartBaseHom_comp]

/-- **Base change covers `Spec φ`** (`lem:projchart-base-map-tospecbase`).
`projChartBaseMap φ ≫ projChartToSpecBase_A = projChartToSpecBase_{A'} ≫ Spec.map (ofHom φ)`.
The base-change hom `MvPolynomial.map φ` restricts on the degree-zero part to `φ`
(`gradedZeroRingHom_projChartBaseHom_comp`); the `Proj.map`–`toSpecZero` naturality square
(`projMap_toSpecZero`) then gives the result after transporting through `A[t•]₀ = A`. -/
lemma projChartBaseMap_toSpecBase (φ : A →+* A') :
    projChartBaseMap A A' n φ ≫ projChartToSpecBase A n =
      projChartToSpecBase A' n ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [projChartBaseMap, projChartToSpecBase, projChartToSpecBase, projChartToSpecZero,
    projChartToSpecZero, ← Category.assoc]
  -- `erw`: the `Proj.map` proof argument from `projChartBaseMap`'s definition is only defeq
  -- to the one in `projMap_toSpecZero`.
  erw [projMap_toSpecZero (projChartBaseHom A A' n φ) (projChartBaseHom_irrelevant_le A A' n φ)]
  -- reassociate via term-mode `Category.assoc` (the bundled `IsIso` instance arguments of the
  -- chart isomorphisms defeat `rw [Category.assoc]`'s keyed matching, but unify fine in term mode).
  refine (Category.assoc _ _ _).trans ?_
  rw [specMap_gradedZeroRingHom_projChartBaseHom]
  exact (Category.assoc _ _ _).symm

end ProjChartToSpecBaseCompat

end MR2223407ConstructionHilbertQuot
