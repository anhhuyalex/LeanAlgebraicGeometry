/-
Copyright (c) 2024 Archon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Archon
-/
import MR2223407ConstructionHilbertQuot.Basic

/-!
# MR2223407: The Hilbert and Quot Functors, and the Grassmannian

This file scaffolds Chapter `chapters/Functors.tex` (Nitsure §1).  It defines the
goal objects of the project — the Hilbert and Quot functors in their projective
and relative forms — records the stratification by Hilbert polynomials and the
fppf-descent property, and constructs the Grassmannian scheme over `ℤ` together
with its tautological quotient.

Each declaration corresponds to a `\lean{...}`-tagged block in the blueprint:

* `hilbertFunctorPn`               — `def:hilbert-functor-pn`
* `quotFunctorPn`                  — `def:quot-functor-pn`
* `quotFunctor`                    — `def:quot-functor`
* `hilbertFunctor`                 — `def:hilbert-functor`
* `hilbertPolynomial`              — `def:hilbert-polynomial`
* `quotFunctorPhi`                 — `def:quot-functor-phi`
* `quot_hilbert_decomposition`     — `lem:quot-hilbert-decomposition`
* `quot_ffdescent`                 — `lem:quot-ffdescent`
* `grassmannianScheme`             — `def:grassmannian-scheme`
* `grassmannian_cocycle`           — `lem:grassmannian-cocycle`
* `grassmannian_separated`         — `lem:grassmannian-separated`
* `grassmannian_proper`            — `lem:grassmannian-proper`
* `grassmannianUniversalQuotient`  — `def:grassmannian-universal-quotient`
* `grassmannian_very_ample`        — `lem:grassmannian-very-ample`
* `grassmannian_represents`        — `thm:grassmannian-represents`

Several of the moduli conditions (a *coherent* sheaf being *flat over the base*,
a sheaf being *locally free of fixed rank*, the *fibrewise Hilbert polynomial*,
and the full fppf *sheaf* condition) rest on Mathlib gaps already recorded in
`Basic.lean` (coherent cohomology, Euler characteristics, fppf descent
equivalence).  As in `Basic.lean` we state the closest honest approximation with
a `sorry` body and record the precise stating-gap in a doc comment.  No `axiom`
is introduced.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace MR2223407ConstructionHilbertQuot

/-! ## Auxiliary predicates (Mathlib gaps, stated abstractly) -/

/-- The free `O_X`-module `⊕^r O_X = O_X^{⊕ r}` of rank `r` on a scheme `X`, as a
sheaf of modules.  This is the source of the surjections defining the Quot and
Grassmannian functors; the same `SheafOfModules.free` shape is used in
`Basic.serre_vanishing`. -/
noncomputable def freeModule (X : Scheme.{u}) (r : ℕ) : X.Modules :=
  SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))

/-- **(Gap.)** A sheaf of modules `F` on `X` is *flat over the base* `S` along
`f : X ⟶ S`.  Relative flatness of a sheaf over a base scheme is not packaged in
Mathlib (flatness exists only for *morphisms*, `AlgebraicGeometry.Flat`).  Stated
abstractly here; tracked for discharge once sheaf-relative flatness lands. -/
def SheafFlatOver {X S : Scheme.{u}} (_f : X ⟶ S) (_F : X.Modules) : Prop := sorry

/-- **(Gap.)** A sheaf of modules `F` on `X` is *locally free of rank `d`*.  A
locally-free-of-fixed-rank predicate for `SheafOfModules` is not yet in Mathlib;
on affine pieces it corresponds to projectivity of rank `d` (cf.
`Module.Grassmannian`).  Stated abstractly; tracked for discharge. -/
def IsLocallyFreeOfRank (_d : ℕ) {X : Scheme.{u}} (_F : X.Modules) : Prop := sorry

/-! ## The Hilbert and Quot functors of `ℙⁿ` -/

/-- A *family of subschemes of `ℙⁿ` parametrised by `S`*: a closed subscheme
`Y ⊂ ℙⁿ_S` that is flat over `S` (`def:hilbert-functor-pn`).  We record the closed
subscheme as a closed immersion `Y ↪ ℙⁿ_S` together with flatness of the composite
`Y ⟶ S`. -/
structure HilbertFamilyPn (n : ℕ) (S : Scheme.{u}) where
  /-- The total space of the family. -/
  Y : Scheme.{u}
  /-- The closed immersion `Y ↪ ℙⁿ_S`. -/
  incl : Y ⟶ projectiveSpace n S
  /-- `incl` is a closed immersion, so `Y` is a closed subscheme. -/
  isClosed : IsClosedImmersion incl
  /-- `Y` is flat over the base `S`. -/
  flat : Flat (incl ≫ projectiveSpace.structureMorphism n S)

/-- **The Hilbert functor of projective space** (`def:hilbert-functor-pn`).

The contravariant set-valued functor `S ↦ {Y ⊂ ℙⁿ_S | Y flat over S}`.  Pullback
gives the functorial action; the pullback maps require the relative-`Proj`/base-change
machinery stubbed in `Basic.lean`, so the action `map` is left as `sorry`.

STATING-GAP: the category of *locally noetherian* schemes is approximated by all
of `Scheme.{u}`; the noetherian hypothesis is not carried. -/
noncomputable def hilbertFunctorPn (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj S := HilbertFamilyPn n S.unop
  map _ := sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- A *family of quotients of `⊕^r O_{ℙⁿ}` parametrised by `S`* (`def:quot-functor-pn`):
a coherent sheaf `F` on `ℙⁿ_S`, flat over `S`, together with a surjection
`q : ⊕^r O_{ℙⁿ_S} → F`.

STATING-GAP: *coherence* is approximated by *quasi-coherence* (`F.IsQuasicoherent`),
and *flatness over `S`* by the abstract `SheafFlatOver` (Mathlib gaps, see
`Basic.lean`).  The structure records a representative `(F, q)`; the equivalence
`⟨F, q⟩ ~ ⟨F', q'⟩ ⟺ ker q = ker q'` is deferred (it requires kernels of sheaf
maps), so the functor value is the type of representatives rather than its
quotient. -/
structure QuotFamilyPn (r n : ℕ) (S : Scheme.{u}) where
  /-- The quotient sheaf `F` on `ℙⁿ_S`. -/
  F : (projectiveSpace n S).Modules
  /-- `F` is (quasi-)coherent. -/
  coherent : F.IsQuasicoherent
  /-- `F` is flat over the base `S`. -/
  flat : SheafFlatOver (projectiveSpace.structureMorphism n S) F
  /-- The defining surjection `⊕^r O_{ℙⁿ_S} → F`. -/
  q : freeModule (projectiveSpace n S) r ⟶ F
  /-- `q` is surjective. -/
  surj : Epi q

/-- **The Quot functor of `⊕^r O_{ℙⁿ}`** (`def:quot-functor-pn`).

`S ↦ {⟨F, q⟩}` with `q : ⊕^r O_{ℙⁿ_S} ↠ F`, `F` coherent and flat over `S`.  As
for `hilbertFunctorPn`, the pullback action is stubbed. -/
noncomputable def quotFunctorPn (r n : ℕ) : Scheme.{u}ᵒᵖ ⥤ Type (u + 1) where
  obj S := QuotFamilyPn r n S.unop
  map _ := sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-! ## The relative Hilbert and Quot functors -/

/-- A *family of quotients of `E` parametrised by an `S`-scheme `T`*
(`def:quot-functor`): with `π : X ⟶ S` and `E` a sheaf on `X`, a coherent sheaf
`F` on `X_T = X ×_S T`, flat over `T` and with support proper over `T`, together
with a surjection `q : E_T → F`, where `E_T` is the pullback of `E` along the
projection `X_T ⟶ X`.

STATING-GAP: coherence ↦ quasi-coherence; flatness over `T` ↦ `SheafFlatOver`; the
*proper support* condition is omitted (it needs the schematic support of a sheaf,
a Mathlib gap), and the `ker`-equivalence is deferred. -/
structure QuotFamily {S X : Scheme.{u}} (π : X ⟶ S) (E : X.Modules) (T : Over S) where
  /-- The quotient sheaf `F` on `X_T = X ×_S T`. -/
  F : (pullback π T.hom).Modules
  /-- `F` is (quasi-)coherent. -/
  coherent : F.IsQuasicoherent
  /-- `F` is flat over `T` (via the second projection `X_T ⟶ T`). -/
  flat : SheafFlatOver (pullback.snd π T.hom) F
  /-- The defining surjection `E_T → F`, where `E_T` is the pullback of `E`. -/
  q : (Scheme.Modules.pullback (pullback.fst π T.hom)).obj E ⟶ F
  /-- `q` is surjective. -/
  surj : Epi q

/-- **The Quot functor `Quot_{E/X/S}`** (`def:quot-functor`).

The contravariant functor `Sch_S → Set`, `T ↦ {⟨F, q⟩}`.  The base category of
locally noetherian `S`-schemes is approximated by the slice `Over S`; the pullback
action is stubbed. -/
noncomputable def quotFunctor {S X : Scheme.{u}} (π : X ⟶ S) (E : X.Modules) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := QuotFamily π E T.unop
  map _ := sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- **The Hilbert functor `Hilb_{X/S}`** (`def:hilbert-functor`).

The special case `E = O_X` of `Quot_{E/X/S}`.  We take `O_X` to be the rank-one
free module `freeModule X 1 ≅ O_X`; a class `⟨F, q⟩` with `q : O_{X_T} ↠ F`
records a closed subscheme `Y ⊂ X_T` proper and flat over `T`. -/
noncomputable def hilbertFunctor {S X : Scheme.{u}} (π : X ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type (u + 1) :=
  quotFunctor π (freeModule X 1)

/-! ## Stratification by Hilbert polynomials -/

/-- **The Hilbert polynomial of a coherent sheaf** (`def:hilbert-polynomial`).

For `X` of finite type over a field `k` with a line bundle `L`, and `F` a coherent
sheaf with proper support, the Hilbert polynomial `Φ ∈ ℚ[λ]` is the polynomial
agreeing for all integers `m` with `χ(F ⊗ L^{⊗ m}) = Σ (-1)ⁱ dimₖ Hⁱ(X, F ⊗ L^{⊗ m})`.

MATHLIB GAP: coherent cohomology `Hⁱ`, the Euler characteristic `χ`, and Snapper's
lemma (that `m ↦ χ(F(m))` is polynomial) are all absent (cf. `Basic.serre_vanishing`,
`Basic.coherent_higher_direct_image`).  We give the signature returning the
polynomial in `ℚ[λ]`; the value is `sorry` until the cohomology API lands. -/
noncomputable def hilbertPolynomial {k : Type u} [Field k] (X : Scheme.{u})
    (_f : X ⟶ Spec (CommRingCat.of k)) (_L : X.Modules) (_F : X.Modules) :
    Polynomial ℚ :=
  sorry

/-- **(Gap.)** The fibrewise Hilbert polynomial `t ↦ Φ_t` of a family `⟨F, q⟩` at a
point `t` of the base, computed with the pullback of a chosen line bundle `L`.  The
restriction `F_t` to the fibre and its Hilbert polynomial need the cohomology API
absent from Mathlib; stated abstractly via `hilbertPolynomial`, deferred. -/
noncomputable def fibreHilbertPolynomial {S X : Scheme.{u}} (_π : X ⟶ S)
    (_E _L : X.Modules) {T : Over S} (_fam : QuotFamily _π _E T) (_t : T.left) :
    Polynomial ℚ :=
  sorry

/-- A family `⟨F, q⟩` together with the constraint that its fibrewise Hilbert
polynomial is constant `= Φ` (`def:quot-functor-phi`). -/
structure QuotFamilyPhi {S X : Scheme.{u}} (π : X ⟶ S) (E L : X.Modules)
    (Φ : Polynomial ℚ) (T : Over S) where
  /-- The underlying family of quotients. -/
  fam : QuotFamily π E T
  /-- At every point `t` of `T`, the Hilbert polynomial of the fibre `F_t` is `Φ`. -/
  hΦ : ∀ t : T.left, fibreHilbertPolynomial π E L fam t = Φ

/-- **The fixed-polynomial Quot subfunctor `Quot^{Φ,L}_{E/X/S}`** (`def:quot-functor-phi`).

The subfunctor of `Quot_{E/X/S}` of classes whose fibrewise Hilbert polynomial
(computed with the pullback of `L`) is everywhere `Φ`. -/
noncomputable def quotFunctorPhi {S X : Scheme.{u}} (π : X ⟶ S) (E L : X.Modules)
    (Φ : Polynomial ℚ) : (Over S)ᵒᵖ ⥤ Type (u + 1) where
  obj T := QuotFamilyPhi π E L Φ T.unop
  map _ := sorry
  map_id _ := sorry
  map_comp _ _ := sorry

/-- **Decomposition by Hilbert polynomial** (`lem:quot-hilbert-decomposition`).

`Quot_{E/X/S}` is the coproduct `∐_Φ Quot^{Φ,L}_{E/X/S}` over `Φ ∈ ℚ[λ]`.  Since
`t ↦ Φ_t` is locally constant in a flat family, the value at each `T` is the
disjoint union (`Σ`-type) of the fixed-polynomial subfunctor values; we state this
pointwise natural bijection (the categorical coproduct in `(Over S)ᵒᵖ ⥤ Type` is
computed pointwise as this `Σ`-type). -/
theorem quot_hilbert_decomposition {S X : Scheme.{u}} (π : X ⟶ S) (E L : X.Modules)
    (T : (Over S)ᵒᵖ) :
    Nonempty ((quotFunctor π E).obj T ≃
      Σ Φ : Polynomial ℚ, (quotFunctorPhi π E L Φ).obj T) :=
  sorry

/-! ## Faithfully flat descent -/

/-- **The Hilbert and Quot functors are fppf sheaves** (`lem:quot-ffdescent`).

MATHLIB GAP: there is no Grothendieck-topology `IsSheaf` statement available for
these functors (the fppf topology on schemes and the descent equivalence are absent
— cf. `Basic.faithfullyFlatDescent`).  The expressible qualitative shadow, matching
`Basic.faithfullyFlatDescent`, is *separatedness of the presheaf*: pulling a family
back along a faithfully flat quasi-compact `S`-morphism `g : T' ⟶ T` is injective on
families, so a family is determined by its restriction to an fppf cover.  The full
glueing (effectivity) half of descent is deferred. -/
theorem quot_ffdescent {S X : Scheme.{u}} (π : X ⟶ S) (E : X.Modules)
    {T' T : Over S} (g : T' ⟶ T) [Flat g.left] [QuasiCompact g.left]
    (_hg : Function.Surjective g.left.base) :
    Function.Injective ((quotFunctor π E).map g.op) :=
  sorry

/-! ## Construction of the Grassmannian -/

/-! ### Chart data for the Grassmannian (project-bespoke BUILD helpers)

The construction of `grassmannianScheme` follows the 6-step `Scheme.GlueData`
recipe of `def:grassmannian-scheme`.  This block builds the bottom layer — the
charts, frame matrices, minors, localisations and transition ring maps — as
genuine, axiom-free definitions; the `GlueData` assembly that consumes them is
staged on top (see `grassmannianScheme`). -/

/-- Index of a chart of `Grass(r, d)`: a `d`-element subset of `Fin r`, encoded
as an embedding `I : Fin d ↪ Fin r` (the columns `I 0, …, I (d-1)` carry the
identity minor `X^I_I = 1`).  There are `binom r d` such charts. -/
abbrev GrassChart (r d : ℕ) : Type := Fin d ↪ Fin r

/-- Free variables of the chart `U^I = Spec ℤ[x^I_{p,q}]`: the matrix positions
`(p, q)` with row `p : Fin d` and column `q` **not** in the range of `I` (the
columns in `range I` carry the identity, so they are not free).  This is the
index set `𝒱 = {(p,q) : q ∉ range I}` of `def:grassmannian-scheme` (step 2). -/
def GrassVars (r d : ℕ) (I : GrassChart r d) : Type :=
  Fin d × { q : Fin r // q ∉ Set.range (⇑I) }

/-- The coordinate ring `ℤ[X^I]` of the chart `U^I`, a polynomial ring over `ℤ`
in the free variables `GrassVars r d I`.  `ULift` lands the variable index in
universe `u` so that `Spec` of this ring is a `Scheme.{u}` (step 3). -/
noncomputable def grassChartRing (r d : ℕ) (I : GrassChart r d) : CommRingCat.{u} :=
  CommRingCat.of (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)

/-- The affine chart `U^I = Spec ℤ[X^I]` (step 3). -/
noncomputable def grassChart (r d : ℕ) (I : GrassChart r d) : Scheme.{u} :=
  Spec (grassChartRing.{u} r d I)

/-- The `d × r` frame matrix `X^I` over `ℤ[X^I]` (step 2): in the columns `q = I s`
indexed by `I` it is the identity (`entry (p, I s) = δ_{p,s}`), and in every other
column `q ∉ range I` its `(p,q)` entry is the free variable `x^I_{p,q}`.  This is
exactly the matrix that `grassmannian_cocycle` operates on. -/
noncomputable def grassFrame (r d : ℕ) (I : GrassChart r d) :
    Matrix (Fin d) (Fin r) (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ) :=
  fun p q =>
    if h : ∃ s, I s = q then
      if p = h.choose then 1 else 0
    else
      MvPolynomial.X (ULift.up (p, ⟨q, fun hq => h (Set.mem_range.mp hq)⟩))

/-- The minor polynomial `P^I_J = det(X^I_J)`, the determinant of the `d × d`
submatrix of `X^I` on the columns selected by `J` (step 4).  The basic open
`U^I_J = D(P^I_J) ⊂ U^I` is the overlap of the charts `I` and `J`. -/
noncomputable def grassMinor (r d : ℕ) (I J : GrassChart r d) :
    MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ :=
  ((grassFrame.{u} r d I).submatrix _root_.id (⇑J)).det

/-- The `I`-minor of the frame matrix `X^I` is the identity: `X^I_I = 1_{d×d}`.
This is the normalisation built into `grassFrame` (the columns indexed by `I`
carry the identity).  It is the key fact behind `θ_{I,I} = id` (`t_id`/`f_id`)
and the cancellation in the cocycle proof. -/
lemma grassFrame_minor_self (r d : ℕ) (I : GrassChart r d) :
    (grassFrame.{u} r d I).submatrix _root_.id (⇑I) = 1 := by
  refine Matrix.ext fun p s => ?_
  rw [Matrix.submatrix_apply, Matrix.one_apply]
  change grassFrame r d I p (I s) = _
  unfold grassFrame
  have h : ∃ s', I s' = I s := ⟨s, rfl⟩
  rw [dif_pos h]
  have hcs : h.choose = s := I.injective h.choose_spec
  rw [hcs]

/-- `P^I_I = det(X^I_I) = det 1 = 1`: the minor along the chart's own index set
is a unit, so the overlap `U^I_I = D(P^I_I) = U^I` and `f I I` is an iso. -/
lemma grassMinor_self (r d : ℕ) (I : GrassChart r d) :
    grassMinor.{u} r d I I = 1 := by
  rw [grassMinor, grassFrame_minor_self, Matrix.det_one]

/-- The overlap ring `ℤ[X^I, 1/P^I_J]`: the localisation of `ℤ[X^I]` away from the
minor `P^I_J`.  `Spec` of this ring is the open subscheme `U^I_J = D(P^I_J)` (step 4). -/
noncomputable abbrev grassOverlapRing (r d : ℕ) (I J : GrassChart r d) : Type u :=
  Localization.Away (grassMinor.{u} r d I J)

/-- The frame matrix `X^I` pushed into the overlap ring `ℤ[X^I, 1/P^I_J]`. -/
noncomputable def grassFrameLoc (r d : ℕ) (I J : GrassChart r d) :
    Matrix (Fin d) (Fin r) (grassOverlapRing.{u} r d I J) :=
  (grassFrame.{u} r d I).map (algebraMap _ _)

/-- The `J`-minor matrix `X^I_J` over the overlap ring; its determinant is the
image of `P^I_J`, a unit in `ℤ[X^I, 1/P^I_J]`, so `X^I_J ∈ GL_d`. -/
noncomputable def grassMinorMatrixLoc (r d : ℕ) (I J : GrassChart r d) :
    Matrix (Fin d) (Fin d) (grassOverlapRing.{u} r d I J) :=
  (grassFrameLoc.{u} r d I J).submatrix _root_.id (⇑J)

/-- `det(X^I_J) = P^I_J` over the overlap ring: the determinant of the minor
matrix is the image of the minor polynomial under the localisation map. -/
lemma grassMinorMatrixLoc_det (r d : ℕ) (I J : GrassChart r d) :
    (grassMinorMatrixLoc.{u} r d I J).det
      = algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
          (grassOverlapRing.{u} r d I J) (grassMinor.{u} r d I J) := by
  unfold grassMinorMatrixLoc grassFrameLoc grassMinor
  rw [Matrix.submatrix_map]
  exact (RingHom.map_det _ _).symm

/-- The minor matrix `X^I_J` is invertible over `ℤ[X^I, 1/P^I_J]`: its determinant
`P^I_J` is a unit there.  This is what makes `(X^I_J)⁻¹` a genuine inverse and
powers the transition map `θ_{I,J}`. -/
lemma grassMinorMatrixLoc_isUnit_det (r d : ℕ) (I J : GrassChart r d) :
    IsUnit (grassMinorMatrixLoc.{u} r d I J).det := by
  rw [grassMinorMatrixLoc_det]
  exact IsLocalization.Away.algebraMap_isUnit (grassMinor.{u} r d I J)

/-- The transition matrix `θ_{I,J}(X^J) = (X^I_J)⁻¹ · X^I` over the overlap ring
`ℤ[X^I, 1/P^I_J]` (step 5).  Its `(p,q)` entry is the image of the chart-`J`
variable `x^J_{p,q}` under the transition map. -/
noncomputable def grassTransMatrix (r d : ℕ) (I J : GrassChart r d) :
    Matrix (Fin d) (Fin r) (grassOverlapRing.{u} r d I J) :=
  (grassMinorMatrixLoc.{u} r d I J)⁻¹ * grassFrameLoc.{u} r d I J

/-- The `J`-minor of the transition matrix is the identity:
`((X^I_J)⁻¹ X^I)_J = (X^I_J)⁻¹ X^I_J = 1`.  This is the geometric content of
`θ_{I,J}(X^J_J) = 1` and a key ingredient of `t_id` and the cocycle. -/
lemma grassTransMatrix_submatrix_self (r d : ℕ) (I J : GrassChart r d) :
    (grassTransMatrix.{u} r d I J).submatrix _root_.id (⇑J) = 1 := by
  have hmul : (grassTransMatrix.{u} r d I J).submatrix _root_.id (⇑J)
      = (grassMinorMatrixLoc.{u} r d I J)⁻¹ * grassMinorMatrixLoc.{u} r d I J := by
    refine Matrix.ext fun p s => ?_
    simp only [grassTransMatrix, grassMinorMatrixLoc, Matrix.submatrix_apply,
      Matrix.mul_apply, _root_.id]
  rw [hmul]
  exact Matrix.nonsing_inv_mul _ (grassMinorMatrixLoc_isUnit_det r d I J)

/-- The transition ring map `θ_{I,J} : ℤ[X^J] → ℤ[X^I, 1/P^I_J]` at the
polynomial level (step 5): it sends each free chart-`J` variable `x^J_{p,q}`
(`q ∉ range J`) to the `(p,q)` entry of `(X^I_J)⁻¹ X^I`.  Composed with the
localisation `ℤ[X^J] → ℤ[X^J, 1/P^J_I]` this factors through `grassOverlapRing J I`
(since `θ_{I,J}(P^J_I) = 1/P^I_J` is a unit), realising the geometric transition
`t i j : U^I_J ⟶ U^J_I`.  The factorisation through the localisation, and the
cocycle identity powering `Scheme.GlueData.cocycle`, are `grassmannian_cocycle`
applied entrywise — staged on top of this map. -/
noncomputable def grassTransAux (r d : ℕ) (I J : GrassChart r d) :
    MvPolynomial (ULift.{u} (GrassVars r d J)) ℤ →+* grassOverlapRing.{u} r d I J :=
  MvPolynomial.eval₂Hom
    ((algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
        (grassOverlapRing.{u} r d I J)).comp (Int.castRingHom _))
    (fun v => grassTransMatrix.{u} r d I J v.down.1 v.down.2)

/-- `θ_{I,J}` applied entrywise to the frame `X^J` is the transition matrix
`(X^I_J)⁻¹ X^I`.  On the free columns `q ∉ range J` this is the definition of
`grassTransAux`; on the identity columns `q = J s` both sides are `δ_{p,s}`
(`grassTransMatrix_submatrix_self`).  This is the matrix form of
`θ_{I,J}(X^J) = (X^I_J)⁻¹ X^I`. -/
lemma grassTransAux_map_frame (r d : ℕ) (I J : GrassChart r d) :
    (grassFrame.{u} r d J).map (grassTransAux.{u} r d I J)
      = grassTransMatrix.{u} r d I J := by
  refine Matrix.ext fun p q => ?_
  rw [Matrix.map_apply]
  by_cases hq : ∃ s, J s = q
  · -- identity column `q = J (hq.choose)`
    have hval : grassFrame.{u} r d J p q = if p = hq.choose then 1 else 0 := by
      simp only [grassFrame, dif_pos hq]
    have hcol : grassTransMatrix.{u} r d I J p q
        = (grassTransMatrix.{u} r d I J).submatrix _root_.id (⇑J) p hq.choose := by
      rw [Matrix.submatrix_apply, id_eq, hq.choose_spec]
    rw [hval, hcol, grassTransMatrix_submatrix_self, Matrix.one_apply]
    split_ifs <;> simp
  · -- free column `q ∉ range J`: `θ(x^J_{p,q}) = grassTransMatrix p q` by definition
    unfold grassTransAux grassFrame
    rw [dif_neg hq, MvPolynomial.eval₂Hom_X']

/-- **Transition-map gate.** `θ_{I,J}(P^J_I) = 1/P^I_J` is a unit in
`ℤ[X^I, 1/P^I_J]`: indeed `θ_{I,J}(X^J_I) = (X^I_J)⁻¹ X^I_I = (X^I_J)⁻¹`
(`grassFrame_minor_self`, `grassTransAux_map_frame`), so its determinant
`θ_{I,J}(P^J_I)` is `det((X^I_J)⁻¹)`, a unit.  This is the hypothesis needed to
lift `grassTransAux` to a ring map `ℤ[X^J, 1/P^J_I] → ℤ[X^I, 1/P^I_J]` via
`IsLocalization.Away.lift`, i.e. to build the geometric transition `t i j`
(GlueData `t` field). -/
lemma grassTransAux_minor_isUnit (r d : ℕ) (I J : GrassChart r d) :
    IsUnit (grassTransAux.{u} r d I J (grassMinor.{u} r d J I)) := by
  have hframeI : (grassFrameLoc.{u} r d I J).submatrix _root_.id (⇑I) = 1 := by
    rw [grassFrameLoc, Matrix.submatrix_map, grassFrame_minor_self]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  -- `θ(P^J_I) = det( (θ·X^J)_I ) = det( (grassTransMatrix)_I ) = det((X^I_J)⁻¹)`.
  have hdet : grassTransAux.{u} r d I J (grassMinor.{u} r d J I)
      = ((grassTransMatrix.{u} r d I J).submatrix _root_.id (⇑I)).det := by
    rw [show grassMinor.{u} r d J I
          = ((grassFrame.{u} r d J).submatrix _root_.id (⇑I)).det from rfl,
      RingHom.map_det (grassTransAux.{u} r d I J)]
    congr 1
    rw [RingHom.mapMatrix_apply, ← Matrix.submatrix_map, grassTransAux_map_frame]
  -- `(grassTransMatrix)_I = (X^I_J)⁻¹ * X^I_I = (X^I_J)⁻¹`.
  have hcol : (grassTransMatrix.{u} r d I J).submatrix _root_.id (⇑I)
      = (grassMinorMatrixLoc.{u} r d I J)⁻¹ := by
    have hmul : (grassTransMatrix.{u} r d I J).submatrix _root_.id (⇑I)
        = (grassMinorMatrixLoc.{u} r d I J)⁻¹
            * (grassFrameLoc.{u} r d I J).submatrix _root_.id (⇑I) := by
      refine Matrix.ext fun p s => ?_
      simp only [grassTransMatrix, Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
    rw [hmul, hframeI, Matrix.mul_one]
  rw [hdet, hcol, Matrix.det_nonsing_inv]
  exact (grassMinorMatrixLoc_isUnit_det r d I J).ringInverse

/-- The overlap chart `U^I_J = D(P^I_J) = Spec ℤ[X^I, 1/P^I_J]` as a scheme: the
`V (I, J)` data field of the `Scheme.GlueData` (step 4). -/
noncomputable def grassOverlap (r d : ℕ) (I J : GrassChart r d) : Scheme.{u} :=
  Spec (CommRingCat.of (grassOverlapRing.{u} r d I J))

/-- The open immersion `f I J : U^I_J ↪ U^I` of the overlap into the chart `U^I`,
realised as `Spec` of the localisation map `ℤ[X^I] → ℤ[X^I, 1/P^I_J]`.  It is an
open immersion by `instIsOpenImmersionMapOfHomAwayAlgebraMap` (step 4). -/
noncomputable def grassInclusion (r d : ℕ) (I J : GrassChart r d) :
    grassOverlap.{u} r d I J ⟶ grassChart.{u} r d I :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ) (grassOverlapRing.{u} r d I J)))

instance (r d : ℕ) (I J : GrassChart r d) :
    IsOpenImmersion (grassInclusion.{u} r d I J) := by
  unfold grassInclusion grassOverlap grassChart grassChartRing
  infer_instance

/-- The transition ring map `θ_{I,J} : ℤ[X^J, 1/P^J_I] → ℤ[X^I, 1/P^I_J]`, the
lift of `grassTransAux` along the localisation `ℤ[X^J] → ℤ[X^J, 1/P^J_I]`,
well-defined by the gate `grassTransAux_minor_isUnit` (step 5). -/
noncomputable def grassTrans (r d : ℕ) (I J : GrassChart r d) :
    grassOverlapRing.{u} r d J I →+* grassOverlapRing.{u} r d I J :=
  Localization.awayLift (grassTransAux.{u} r d I J) (grassMinor.{u} r d J I)
    (grassTransAux_minor_isUnit r d I J)

/-- The geometric transition `t I J : U^I_J ⟶ U^J_I` (the GlueData `t` data field):
`Spec` of the transition ring map `θ_{I,J}` (step 5). -/
noncomputable def grassTransMorphism (r d : ℕ) (I J : GrassChart r d) :
    grassOverlap.{u} r d I J ⟶ grassOverlap.{u} r d J I :=
  Spec.map (CommRingCat.ofHom (grassTrans.{u} r d I J))

/-! ### Remaining `Scheme.GlueData` fields for the Grassmannian

These close out the `GlueData` of `def:grassmannian-scheme`: the `f_id`
isomorphism, the `t_id` degeneracy, the triple-overlap morphism `t'` and its
two Prop fields `t_fac`/`cocycle`. -/

/-- **`f_id` field.** The self-inclusion `f I I : U^I_I ↪ U^I` is an isomorphism:
`P^I_I = 1` (`grassMinor_self`), so the localisation `ℤ[X^I, 1/P^I_I]` is away
from a unit and `U^I_I = D(1) = U^I`. -/
lemma grassInclusion_self_isIso (r d : ℕ) (I : GrassChart r d) :
    IsIso (grassInclusion.{u} r d I I) := by
  unfold grassInclusion grassOverlap grassChart grassChartRing
  rw [isIso_SpecMap_iff]
  change Function.Bijective ⇑(algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
      (grassOverlapRing.{u} r d I I))
  have hx : IsUnit (grassMinor.{u} r d I I) := grassMinor_self r d I ▸ isUnit_one
  have e := IsLocalization.atUnit (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
      (grassOverlapRing.{u} r d I I) (grassMinor.{u} r d I I) hx
  have h : ⇑(algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
      (grassOverlapRing.{u} r d I I)) = ⇑e := by
    ext r; simp [(e.commutes r).symm]
  rw [h]; exact e.bijective

/-- The `I`-minor matrix over the overlap ring `ℤ[X^I, 1/P^I_I]` is the identity
(the localised form of `grassFrame_minor_self`). -/
lemma grassMinorMatrixLoc_self (r d : ℕ) (I : GrassChart r d) :
    grassMinorMatrixLoc.{u} r d I I = 1 := by
  unfold grassMinorMatrixLoc grassFrameLoc
  rw [Matrix.submatrix_map, grassFrame_minor_self]
  exact Matrix.map_one _ (map_zero _) (map_one _)

/-- The transition matrix `θ_{I,I}(X^I) = (X^I_I)⁻¹ X^I = X^I` is just the frame
pushed into the overlap ring, since `X^I_I = 1`. -/
lemma grassTransMatrix_self (r d : ℕ) (I : GrassChart r d) :
    grassTransMatrix.{u} r d I I = grassFrameLoc.{u} r d I I := by
  unfold grassTransMatrix
  rw [grassMinorMatrixLoc_self, inv_one, Matrix.one_mul]

/-- `θ_{I,I}` is the localisation map: at the polynomial level the transition map
into its own chart sends every variable to its own image, so it agrees with the
algebra map `ℤ[X^I] → ℤ[X^I, 1/P^I_I]`. -/
lemma grassTransAux_self (r d : ℕ) (I : GrassChart r d) :
    grassTransAux.{u} r d I I
      = algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
          (grassOverlapRing.{u} r d I I) := by
  apply MvPolynomial.ringHom_ext
  · intro n
    change (grassTransAux.{u} r d I I) (MvPolynomial.C n) = _
    rw [grassTransAux, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
    simp
  · intro v
    rw [grassTransAux, MvPolynomial.eval₂Hom_X', grassTransMatrix_self,
      grassFrameLoc, Matrix.map_apply]
    have hq : ¬ ∃ s, I s = (↑v.down.2 : Fin r) := fun h => v.down.2.2 (Set.mem_range.mpr h)
    have : grassFrame.{u} r d I v.down.1 (↑v.down.2 : Fin r) = MvPolynomial.X v := by
      unfold grassFrame
      rw [dif_neg hq]
      congr 1
    rw [this]

/-- **`t_id` field (ring level).** `θ_{I,I} = id` on `ℤ[X^I, 1/P^I_I]`: the lift of
the localisation map past the unit `P^I_I = 1` is the identity. -/
lemma grassTrans_self (r d : ℕ) (I : GrassChart r d) :
    grassTrans.{u} r d I I = RingHom.id (grassOverlapRing.{u} r d I I) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (grassMinor.{u} r d I I))
  rw [RingHom.id_comp, grassTrans, IsLocalization.Away.lift_comp, grassTransAux_self]

/-- **`t_id` field.** The self-transition `t I I : U^I_I ⟶ U^I_I` is the identity. -/
lemma grassTransMorphism_self (r d : ℕ) (I : GrassChart r d) :
    grassTransMorphism.{u} r d I I = 𝟙 (grassOverlap.{u} r d I I) := by
  rw [grassTransMorphism, grassTrans_self, CommRingCat.ofHom_id, Spec.map_id]
  rfl

/-- **Cross-minor value of the transition map** (the algebraic core of the `t'`
gate). `θ_{I,J}(P^J_K) = det((X^I_J)⁻¹) · P^I_K` in `ℤ[X^I, 1/P^I_J]`: applying the
transition to the `K`-minor of `X^J` gives `det(((X^I_J)⁻¹ X^I)_K) =
det((X^I_J)⁻¹) det(X^I_K)`.  Specialising `K = I` recovers
`grassTransAux_minor_isUnit` (`P^I_I = 1`); for general `K` it shows `θ_{I,J}(P^J_K)`
becomes a unit once `P^I_K` is inverted — the gate that lifts `θ_{I,J}` to the
double localisation `ℤ[X^I, 1/(P^I_J P^I_K)]` underlying the triple-overlap map
`t'`. -/
lemma grassTransAux_minor (r d : ℕ) (I J K : GrassChart r d) :
    grassTransAux.{u} r d I J (grassMinor.{u} r d J K)
      = (grassMinorMatrixLoc.{u} r d I J)⁻¹.det
          * algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
              (grassOverlapRing.{u} r d I J) (grassMinor.{u} r d I K) := by
  have hdet : grassTransAux.{u} r d I J (grassMinor.{u} r d J K)
      = ((grassTransMatrix.{u} r d I J).submatrix _root_.id (⇑K)).det := by
    rw [show grassMinor.{u} r d J K
          = ((grassFrame.{u} r d J).submatrix _root_.id (⇑K)).det from rfl,
      RingHom.map_det (grassTransAux.{u} r d I J)]
    congr 1
    rw [RingHom.mapMatrix_apply, ← Matrix.submatrix_map, grassTransAux_map_frame]
  rw [hdet]
  have hmul : (grassTransMatrix.{u} r d I J).submatrix _root_.id (⇑K)
      = (grassMinorMatrixLoc.{u} r d I J)⁻¹
          * (grassFrameLoc.{u} r d I J).submatrix _root_.id (⇑K) := by
    refine Matrix.ext fun p s => ?_
    simp only [grassTransMatrix, Matrix.submatrix_apply, Matrix.mul_apply, id_eq]
  rw [hmul, Matrix.det_mul]
  congr 1
  change ((grassFrameLoc.{u} r d I J).submatrix _root_.id (⇑K)).det
    = algebraMap _ _ ((grassFrame.{u} r d I).submatrix _root_.id (⇑K)).det
  rw [grassFrameLoc, Matrix.submatrix_map]
  exact (RingHom.map_det _ _).symm

/-- **Parametric `t'` gate.** In any `ℤ[X^I, 1/P^I_J]`-algebra `S` in which the
image of `P^I_K` is a unit (e.g. the double localisation `ℤ[X^I, 1/(P^I_J P^I_K)]`,
which is the coordinate ring of the triple overlap `pullback (f I J) (f I K)`), the
image of `θ_{I,J}(P^J_K)` is a unit.  By `grassTransAux_minor` it factors as
`det((X^I_J)⁻¹) · P^I_K`; the first factor is a unit already in `ℤ[X^I, 1/P^I_J]`
(`grassMinorMatrixLoc_isUnit_det`).  This is exactly the hypothesis
`Localization.awayLift` needs to lift `θ_{I,J}` over the triple overlap, hence to
build the triple-overlap morphism `t'` of the `Scheme.GlueData`. -/
lemma grassTransAux_minor_isUnit_of (r d : ℕ) (I J K : GrassChart r d)
    {S : Type u} [CommRing S] [Algebra (grassOverlapRing.{u} r d I J) S]
    (hK : IsUnit (algebraMap (grassOverlapRing.{u} r d I J) S
            (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
              (grassOverlapRing.{u} r d I J) (grassMinor.{u} r d I K)))) :
    IsUnit (algebraMap (grassOverlapRing.{u} r d I J) S
      (grassTransAux.{u} r d I J (grassMinor.{u} r d J K))) := by
  rw [grassTransAux_minor, map_mul]
  refine IsUnit.mul ?_ hK
  apply IsUnit.map
  rw [Matrix.det_nonsing_inv]
  exact (grassMinorMatrixLoc_isUnit_det r d I J).ringInverse

/-! ### Triple-overlap transition (the GlueData `t'` field)

The last `Scheme.GlueData` data field is the triple-overlap morphism
`t' I J K : pullback (f I J) (f I K) ⟶ pullback (f J K) (f J I)`.  Since both
`f`'s are `Spec` of localisation maps, each pullback is `Spec` of a localisation
of the chart ring away from a *product* of two minors; we build the ring map
between these double localisations and take `Spec`, transporting along
`pullbackSpecIso`. -/

/-- Coordinate ring of the triple overlap `pullback (f I J) (f I K) = U^I_J ∩ U^I_K`:
the localisation of `ℤ[X^I]` away from the product `P^I_J · P^I_K`.  By
`IsLocalization.Away.mul` it is also the localisation of `ℤ[X^I, 1/P^I_J]` away
from the image of `P^I_K`, i.e. the tensor product handed back by
`pullbackSpecIso`. -/
noncomputable abbrev grassOverlapRing2 (r d : ℕ) (I J K : GrassChart r d) : Type u :=
  Localization.Away (grassMinor.{u} r d I J * grassMinor.{u} r d I K)

/-- The localisation map `ℤ[X^I, 1/P^I_J] → ℤ[X^I, 1/(P^I_J P^I_K)]` from a double
overlap into the triple overlap (inverting `P^I_K` further), via
`IsLocalization.Away.awayToAwayRight`. -/
noncomputable def grassOverlapToTriple (r d : ℕ) (I J K : GrassChart r d) :
    grassOverlapRing.{u} r d I J →+* grassOverlapRing2.{u} r d I J K :=
  IsLocalization.Away.awayToAwayRight (grassMinor.{u} r d I J) (grassMinor.{u} r d I K)

/-- `θ_{I,J}` pushed all the way into the triple-overlap ring `ℤ[X^I, 1/(P^I_J P^I_K)]`. -/
noncomputable def grassTransAuxTriple (r d : ℕ) (I J K : GrassChart r d) :
    MvPolynomial (ULift.{u} (GrassVars r d J)) ℤ →+* grassOverlapRing2.{u} r d I J K :=
  (grassOverlapToTriple.{u} r d I J K).comp (grassTransAux.{u} r d I J)

/-- **Triple-overlap gate.** The image of `P^J_K · P^J_I` under `θ_{I,J}` is a unit in
`ℤ[X^I, 1/(P^I_J P^I_K)]`.  Factor `P^J_K` by `grassTransAux_minor` into
`det((X^I_J)⁻¹) · P^I_K`: the first factor is a unit already over `ℤ[X^I, 1/P^I_J]`,
and `P^I_K` is a unit in the triple overlap since `P^I_J · P^I_K` is inverted there;
`P^J_I` is a unit by `grassTransAux_minor_isUnit`.  This is the `awayLift` hypothesis
for `grassTrans2`. -/
lemma grassTransAuxTriple_isUnit (r d : ℕ) (I J K : GrassChart r d) :
    IsUnit (grassTransAuxTriple.{u} r d I J K
      (grassMinor.{u} r d J K * grassMinor.{u} r d J I)) := by
  rw [grassTransAuxTriple, RingHom.comp_apply, map_mul, map_mul]
  refine IsUnit.mul ?_ (IsUnit.map _ (grassTransAux_minor_isUnit r d I J))
  rw [grassTransAux_minor, map_mul]
  refine IsUnit.mul ?_ ?_
  · apply IsUnit.map
    rw [Matrix.det_nonsing_inv]
    exact (grassMinorMatrixLoc_isUnit_det r d I J).ringInverse
  · rw [grassOverlapToTriple, IsLocalization.Away.awayToAwayRight_eq]
    refine isUnit_of_mul_isUnit_right (x := algebraMap _ _ (grassMinor.{u} r d I J)) ?_
    rw [← map_mul]
    exact IsLocalization.Away.algebraMap_isUnit _

/-- The triple-overlap transition ring map
`θ'_{I,J,K} : ℤ[X^J, 1/(P^J_K P^J_I)] → ℤ[X^I, 1/(P^I_J P^I_K)]`, the lift of
`θ_{I,J}` over the double localisation, valid by `grassTransAuxTriple_isUnit`. -/
noncomputable def grassTrans2 (r d : ℕ) (I J K : GrassChart r d) :
    grassOverlapRing2.{u} r d J K I →+* grassOverlapRing2.{u} r d I J K :=
  Localization.awayLift (grassTransAuxTriple.{u} r d I J K)
    (grassMinor.{u} r d J K * grassMinor.{u} r d J I)
    (grassTransAuxTriple_isUnit r d I J K)

/-- `θ'_{I,J,K}` restricted to the chart ring `ℤ[X^J]` is `grassTransAuxTriple`: the
defining `awayLift` factorisation `grassTrans2 ∘ algebraMap = grassTransAuxTriple`.
This is the comp law that reduces the ring-level `t_fac`/`cocycle` identities (after
collapsing the `grassTripleIso` factors) to `MvPolynomial.ringHom_ext` on the frame
variables. -/
lemma grassTrans2_comp_algebraMap (r d : ℕ) (I J K : GrassChart r d) :
    (grassTrans2.{u} r d I J K).comp
        (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d J)) ℤ)
          (grassOverlapRing2.{u} r d J K I))
      = grassTransAuxTriple.{u} r d I J K := by
  rw [grassTrans2, IsLocalization.Away.lift_comp]

set_option synthInstance.maxHeartbeats 1000000 in
-- The `IsScalarTower`/`IsLocalization.Away` synthesis over the `MvPolynomial` base ring
-- combined with the `grassOverlapRing` abbrev unfolding exceeds the default budget.
/-- The triple overlap as a tensor product is the localisation away from the product
of minors: `ℤ[X^I,1/P^I_J] ⊗_{ℤ[X^I]} ℤ[X^I,1/P^I_K] ≃ ℤ[X^I, 1/(P^I_J P^I_K)]`.
This is the algebraic shadow of `pullbackSpecIso` for the two chart inclusions;
`IsLocalization.Away.mul'` exhibits the tensor product as a localisation at the
product, and both sides are localisations of `ℤ[X^I]` at the same submonoid. -/
noncomputable def grassTripleRingEquiv (r d : ℕ) (I J K : GrassChart r d) :
    (grassOverlapRing.{u} r d I J ⊗[MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ]
        grassOverlapRing.{u} r d I K) ≃ₐ[MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ]
      grassOverlapRing2.{u} r d I J K := by
  haveI : IsLocalization.Away (grassMinor.{u} r d I J * grassMinor.{u} r d I K)
      (grassOverlapRing.{u} r d I J ⊗[MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ]
        grassOverlapRing.{u} r d I K) :=
    IsLocalization.Away.mul' (grassOverlapRing.{u} r d I J) _
      (grassMinor.{u} r d I J) (grassMinor.{u} r d I K)
  exact IsLocalization.algEquiv
    (Submonoid.powers (grassMinor.{u} r d I J * grassMinor.{u} r d I K)) _ _

/-- **Geometric identification of the triple overlap.** The fibre product
`pullback (f I J) (f I K)` of the two chart inclusions is `Spec` of the triple
overlap ring `ℤ[X^I, 1/(P^I_J P^I_K)]`, via `pullbackSpecIso` followed by
`grassTripleRingEquiv`. -/
noncomputable def grassTripleIso (r d : ℕ) (I J K : GrassChart r d) :
    pullback (grassInclusion.{u} r d I J) (grassInclusion.{u} r d I K) ≅
      Spec (CommRingCat.of (grassOverlapRing2.{u} r d I J K)) :=
  pullbackSpecIso (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
      (grassOverlapRing.{u} r d I J) (grassOverlapRing.{u} r d I K) ≪≫
    Scheme.Spec.mapIso (grassTripleRingEquiv.{u} r d I J K).symm.toRingEquiv.toCommRingCatIso.op

/-- **The triple-overlap transition morphism** `t' I J K : pullback (f I J) (f I K) ⟶
pullback (f J K) (f J I)` (the GlueData `t'` data field).  It is `Spec` of the
double-localisation ring map `grassTrans2`, transported along the geometric
identifications `grassTripleIso`. -/
noncomputable def grassTransMorphism2 (r d : ℕ) (I J K : GrassChart r d) :
    pullback (grassInclusion.{u} r d I J) (grassInclusion.{u} r d I K) ⟶
      pullback (grassInclusion.{u} r d J K) (grassInclusion.{u} r d J I) :=
  (grassTripleIso.{u} r d I J K).hom ≫
    Spec.map (CommRingCat.ofHom (grassTrans2.{u} r d I J K)) ≫
      (grassTripleIso.{u} r d J K I).inv

/-- **Cocycle condition for the glueing** (`lem:grassmannian-cocycle`).

The transition maps satisfy `θ_{I,I} = id` and `θ_{I,K} = θ_{I,J} ∘ θ_{J,K}`.  We
state the underlying matrix identity that powers the geometric cocycle: for a
`d × r` matrix `M` (the frame `X^I`) and column-selections `J, K : Fin d → Fin r`
whose square submatrices are invertible, normalising by `J` then by `K` agrees with
normalising directly by `K`:
`(M_K)⁻¹ M = (((M_J)⁻¹ M)_K)⁻¹ ((M_J)⁻¹ M)`,
where `M_J = M.submatrix id J` is the `J`-minor.  This is exactly
`θ_{I,K} = θ_{I,J} θ_{J,K}` written on the matrix entries. -/
theorem grassmannian_cocycle {R : Type u} [CommRing R] {d r : ℕ}
    (M : Matrix (Fin d) (Fin r) R) (J K : Fin d → Fin r)
    [Invertible (M.submatrix _root_.id J)]
    [Invertible ((⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K)] :
    haveI : Invertible (M.submatrix _root_.id K) := by
      -- The `K`-minor of `⅟M_J · M` equals `⅟M_J · M_K`: `submatrix _root_.id K`
      -- only reindexes columns, so it commutes past the left factor `⅟M_J`.
      have hcol : (⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K
          = ⅟(M.submatrix _root_.id J) * M.submatrix _root_.id K := by
        ext i j
        simp [Matrix.mul_apply, Matrix.submatrix_apply]
      -- Hence `M_K = M_J · (⅟M_J · M)_K` is a product of two invertible matrices.
      have hMK : M.submatrix _root_.id K
          = M.submatrix _root_.id J
              * (⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K := by
        rw [hcol, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
      rw [hMK]
      exact invertibleMul _ _
    ⅟(M.submatrix _root_.id K) * M
      = ⅟((⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K)
          * (⅟(M.submatrix _root_.id J) * M) := by
  -- Same column-minor identity as above: `(⅟M_J · M)_K = ⅟M_J · M_K`.
  have hcol : (⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K
      = ⅟(M.submatrix _root_.id J) * M.submatrix _root_.id K := by
    ext i j
    simp [Matrix.mul_apply, Matrix.submatrix_apply]
  -- Re-establish `Invertible M_K` in the local context so the `⅟M_K` written
  -- below elaborate (the statement's instance is baked into the goal type).
  haveI : Invertible (M.submatrix _root_.id K) := by
    have hMK : M.submatrix _root_.id K
        = M.submatrix _root_.id J
            * (⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K := by
      rw [hcol, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul]
    rw [hMK]; exact invertibleMul _ _
  -- Key cancellation: `(⅟M_J · M)_K · (⅟M_K · M) = ⅟M_J · M`, since
  -- `(⅟M_J · M_K) · (⅟M_K · M) = ⅟M_J · (M_K · ⅟M_K) · M = ⅟M_J · M`.
  have key : (⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K
        * (⅟(M.submatrix _root_.id K) * M)
      = ⅟(M.submatrix _root_.id J) * M := by
    rw [hcol, Matrix.mul_assoc, ← Matrix.mul_assoc (M.submatrix _root_.id K),
      mul_invOf_self, Matrix.one_mul]
  -- Now `⅟M_K · M = ⅟(⅟M_J · M)_K · ((⅟M_J · M)_K · (⅟M_K · M)) = ⅟(⅟M_J · M)_K · (⅟M_J · M)`.
  have h : ⅟(M.submatrix _root_.id K) * M
      = ⅟((⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K)
          * (⅟(M.submatrix _root_.id J) * M) := by
    calc ⅟(M.submatrix _root_.id K) * M
        = ⅟((⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K)
            * ((⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K
                * (⅟(M.submatrix _root_.id K) * M)) := by
          rw [← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul]
      _ = ⅟((⅟(M.submatrix _root_.id J) * M).submatrix _root_.id K)
            * (⅟(M.submatrix _root_.id J) * M) := by rw [key]
  -- Reconcile the locally-built `Invertible M_K` with the one baked into the
  -- statement: `Invertible` is a subsingleton, so `convert` discharges the
  -- instance mismatch in the two `⅟M_K`.
  convert h using 3

/-! ## Project-local Mathlib supplement — Grassmannian GlueData cocycle & assembly

The two `Scheme.GlueData` Prop fields `t_fac`/`cocycle` for the Grassmannian, plus
the final assembly `grassGlueData`/`grassmannianScheme := D.glued`.  Both Prop
fields reduce (after cancelling the `grassTripleIso` factors) to ring-level
identities about `grassTrans2`, which in turn bottom out at the proven matrix
cocycle `grassmannian_cocycle`.  The supporting lemmas below are project-local
matrix/localisation bookkeeping with no Mathlib analogue in this revision. -/

/-- A ring hom commutes with `Ring.inverse` on units. -/
private theorem ringHom_ringInverse {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {a : R} (ha : IsUnit a) : f (Ring.inverse a) = Ring.inverse (f a) := by
  obtain ⟨u, rfl⟩ := ha
  rw [Ring.inverse_unit, show f ↑u = ↑(Units.map (f : R →* S) u) from rfl, Ring.inverse_unit]; simp

/-- A ring hom commutes with the nonsingular inverse of a square matrix with unit
determinant (`mapMatrix` form, square only). -/
private theorem RingHom.mapMatrix_nonsing_inv {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n R) (hM : IsUnit M.det) :
    f.mapMatrix M⁻¹ = (f.mapMatrix M)⁻¹ := by
  ext i j
  rw [Matrix.inv_def, Matrix.inv_def]
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [ringHom_ringInverse f hM]
  have hdet : (M.map ⇑f).det = f M.det := by rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hadj : (M.map ⇑f).adjugate i j = f (M.adjugate i j) := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]; rfl
  rw [hdet, hadj]

/-- A ring hom commutes with the nonsingular inverse of a square matrix with unit
determinant (`Matrix.map` form). -/
private theorem map_nonsing_inv {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {n : Type*} [DecidableEq n] [Fintype n] (M : Matrix n n R) (hM : IsUnit M.det) :
    M⁻¹.map ⇑f = (M.map ⇑f)⁻¹ := by
  rw [← RingHom.mapMatrix_apply f M⁻¹, ← RingHom.mapMatrix_apply f M,
    RingHom.mapMatrix_nonsing_inv f M hM]

/-- The localisation map `ℤ[X^I,1/P^I_J] → ℤ[X^I,1/(P^I_J P^I_K)]` composed with the
chart structural map is the chart structural map into the triple overlap (scalar tower). -/
private lemma grassOverlapToTriple_comp_algebraMap (r d : ℕ) (I J K : GrassChart r d) :
    (grassOverlapToTriple.{u} r d I J K).comp
        (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ) (grassOverlapRing.{u} r d I J))
      = algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
          (grassOverlapRing2.{u} r d I J K) := by
  rw [grassOverlapToTriple]
  refine RingHom.ext fun a => ?_
  rw [RingHom.comp_apply]
  exact IsLocalization.Away.awayToAwayRight_eq _ _ a

/-- The localised frame `X^I` pushed into the triple overlap ring is the chart frame
mapped by the structural algebra map. -/
private lemma grassFrameLoc_map_overlapToTriple (r d : ℕ) (I J K : GrassChart r d) :
    (grassFrameLoc.{u} r d I J).map (grassOverlapToTriple.{u} r d I J K)
      = (grassFrame.{u} r d I).map (algebraMap _ (grassOverlapRing2.{u} r d I J K)) := by
  rw [grassFrameLoc, Matrix.map_map, ← RingHom.coe_comp, grassOverlapToTriple_comp_algebraMap]

/-- `θ'_{I,J,K}` applied entrywise to the chart-`J` frame is `(X^I_J)⁻¹ X^I` pushed. -/
private lemma grassTransAuxTriple_map_frame (r d : ℕ) (I J K : GrassChart r d) :
    (grassFrame.{u} r d J).map (grassTransAuxTriple.{u} r d I J K)
      = (grassTransMatrix.{u} r d I J).map (grassOverlapToTriple.{u} r d I J K) := by
  rw [grassTransAuxTriple, RingHom.coe_comp, ← Matrix.map_map, grassTransAux_map_frame]

/-- `θ'_{I,J,K}` applied entrywise to the chart-`J` frame (pushed into the triple
overlap) is the transition matrix `(X^I_J)⁻¹ X^I` pushed into the triple overlap. -/
private lemma grassTrans2_map_frame (r d : ℕ) (I J K : GrassChart r d) :
    ((grassFrame.{u} r d J).map (algebraMap _ (grassOverlapRing2.{u} r d J K I))).map
        ⇑(grassTrans2.{u} r d I J K)
      = (grassTransMatrix.{u} r d I J).map (grassOverlapToTriple.{u} r d I J K) := by
  rw [Matrix.map_map, ← RingHom.coe_comp, grassTrans2_comp_algebraMap]
  exact grassTransAuxTriple_map_frame r d I J K

/-- The pushed transition matrix `θ'(X^J)` expressed as `(PF^I_J)⁻¹ PF^I` where `PF^I`
is the chart-`I` frame pushed into the triple overlap. -/
private lemma grassTransMatrix_map_overlapToTriple (r d : ℕ) (I J K : GrassChart r d) :
    (grassTransMatrix.{u} r d I J).map (grassOverlapToTriple.{u} r d I J K)
      = (((grassFrame.{u} r d I).map (algebraMap _ (grassOverlapRing2.{u} r d I J K))).submatrix
            _root_.id (⇑J))⁻¹
          * ((grassFrame.{u} r d I).map (algebraMap _ (grassOverlapRing2.{u} r d I J K))) := by
  rw [grassTransMatrix, Matrix.map_mul,
    map_nonsing_inv _ _ (grassMinorMatrixLoc_isUnit_det r d I J), grassFrameLoc_map_overlapToTriple]
  congr 2
  rw [grassMinorMatrixLoc, ← Matrix.submatrix_map, grassFrameLoc_map_overlapToTriple]

/-- The determinant of the `Y`-minor of the chart-`X` frame pushed into a ring `R` is
the image of the minor polynomial `P^X_Y`. -/
private lemma pushedMinor_det (r d : ℕ) (X Y : GrassChart r d) (R : Type u) [CommRing R]
    [Algebra (MvPolynomial (ULift.{u} (GrassVars r d X)) ℤ) R] :
    (((grassFrame.{u} r d X).map (algebraMap _ R)).submatrix _root_.id (⇑Y)).det
      = algebraMap (MvPolynomial (ULift.{u} (GrassVars r d X)) ℤ) R (grassMinor.{u} r d X Y) := by
  rw [grassMinor, Matrix.submatrix_map, ← RingHom.mapMatrix_apply, RingHom.map_det]

/-- The matrix cocycle `grassmannian_cocycle` repackaged with `⁻¹`/`IsUnit` in place of
`⅟`/`Invertible`: normalising by `B` directly equals normalising by `C` then by `B`. -/
private lemma cocycle_nonsing_inv {R : Type u} [CommRing R] {d r : ℕ}
    (M : Matrix (Fin d) (Fin r) R) (B C : Fin d → Fin r)
    (h1 : IsUnit (M.submatrix _root_.id C).det)
    (h2 : IsUnit (((M.submatrix _root_.id C)⁻¹ * M).submatrix _root_.id B).det) :
    (((M.submatrix _root_.id C)⁻¹ * M).submatrix _root_.id B)⁻¹ * ((M.submatrix _root_.id C)⁻¹ * M)
      = (M.submatrix _root_.id B)⁻¹ * M := by
  haveI iC : Invertible (M.submatrix _root_.id C) :=
    (M.submatrix _root_.id C).invertibleOfIsUnitDet h1
  haveI iCB : Invertible ((⅟(M.submatrix _root_.id C) * M).submatrix _root_.id B) := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact (((M.submatrix _root_.id C)⁻¹ * M).submatrix _root_.id B).invertibleOfIsUnitDet h2
  have hcoc := grassmannian_cocycle M C B
  simp only [Matrix.invOf_eq_nonsing_inv] at hcoc
  exact hcoc.symm

/-- **The single cocycle step.** Applying `θ'_{I,J,K}` to the pushed transition matrix
`(PF^J_B)⁻¹ PF^J` produces `(PF^I_B)⁻¹ PF^I`; this is `θ_{I,J}∘θ_{J,B} = θ_{I,B}` at the
matrix level over the triple overlap, valid when the relevant minors are units there. -/
private lemma grassTransStep (r d : ℕ) (I J K B : GrassChart r d)
    (hBJ : IsUnit (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d J)) ℤ)
        (grassOverlapRing2.{u} r d J K I) (grassMinor.{u} r d J B)))
    (h1 : IsUnit (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
        (grassOverlapRing2.{u} r d I J K) (grassMinor.{u} r d I J)))
    (hBI : IsUnit (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
        (grassOverlapRing2.{u} r d I J K) (grassMinor.{u} r d I B))) :
    ((((grassFrame.{u} r d J).map (algebraMap _ (grassOverlapRing2.{u} r d J K I))).submatrix
          _root_.id (⇑B))⁻¹
        * ((grassFrame.{u} r d J).map (algebraMap _ (grassOverlapRing2.{u} r d J K I)))).map
        ⇑(grassTrans2.{u} r d I J K)
      = (((grassFrame.{u} r d I).map (algebraMap _ (grassOverlapRing2.{u} r d I J K))).submatrix
            _root_.id (⇑B))⁻¹
          * ((grassFrame.{u} r d I).map (algebraMap _ (grassOverlapRing2.{u} r d I J K))) := by
  set PFJ := (grassFrame.{u} r d J).map (algebraMap _ (grassOverlapRing2.{u} r d J K I)) with hPFJ
  set PFI := (grassFrame.{u} r d I).map (algebraMap _ (grassOverlapRing2.{u} r d I J K)) with hPFI
  set g := grassTrans2.{u} r d I J K with hg
  have hBJm : IsUnit (PFJ.submatrix _root_.id (⇑B)).det := by rw [hPFJ, pushedMinor_det]; exact hBJ
  have hgPFJ : PFJ.map ⇑g = (PFI.submatrix _root_.id (⇑J))⁻¹ * PFI := by
    rw [hPFJ, hg, grassTrans2_map_frame, grassTransMatrix_map_overlapToTriple, ← hPFI]
  have h1m : IsUnit (PFI.submatrix _root_.id (⇑J)).det := by rw [hPFI, pushedMinor_det]; exact h1
  have h2m : IsUnit (((PFI.submatrix _root_.id (⇑J))⁻¹ * PFI).submatrix _root_.id (⇑B)).det := by
    have hsm : ((PFI.submatrix _root_.id (⇑J))⁻¹ * PFI).submatrix _root_.id (⇑B)
        = (PFI.submatrix _root_.id (⇑J))⁻¹ * (PFI.submatrix _root_.id (⇑B)) := by
      ext i j; simp [Matrix.mul_apply, Matrix.submatrix_apply]
    rw [hsm, Matrix.det_mul, Matrix.det_nonsing_inv, hPFI, pushedMinor_det, pushedMinor_det]
    exact (h1.ringInverse).mul hBI
  rw [Matrix.map_mul, map_nonsing_inv g _ hBJm, ← Matrix.submatrix_map, hgPFJ]
  exact cocycle_nonsing_inv PFI (⇑B) (⇑J) h1m h2m

/-- The image of the left minor factor `P^X_Y` of the triple overlap ring is a unit. -/
private lemma grassMinor_algebraMap_isUnit_left (r d : ℕ) (X Y Z : GrassChart r d) :
    IsUnit (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d X)) ℤ)
      (grassOverlapRing2.{u} r d X Y Z) (grassMinor.{u} r d X Y)) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (R := MvPolynomial (ULift.{u} (GrassVars r d X)) ℤ) (S := grassOverlapRing2.{u} r d X Y Z)
    (grassMinor.{u} r d X Y * grassMinor.{u} r d X Z)
  rw [map_mul] at h; exact isUnit_of_mul_isUnit_left h

/-- The image of the right minor factor `P^X_Z` of the triple overlap ring is a unit. -/
private lemma grassMinor_algebraMap_isUnit_right (r d : ℕ) (X Y Z : GrassChart r d) :
    IsUnit (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d X)) ℤ)
      (grassOverlapRing2.{u} r d X Y Z) (grassMinor.{u} r d X Z)) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (R := MvPolynomial (ULift.{u} (GrassVars r d X)) ℤ) (S := grassOverlapRing2.{u} r d X Y Z)
    (grassMinor.{u} r d X Y * grassMinor.{u} r d X Z)
  rw [map_mul] at h; exact isUnit_of_mul_isUnit_right h

/-- **Ring-level cocycle.** The triple composite of the double-localisation
transition maps is the identity:
`θ'_{I,J,K} ∘ θ'_{J,K,I} ∘ θ'_{K,I,J} = id` on `ℤ[X^I, 1/(P^I_J P^I_K)]`.  This is
the algebraic heart of the GlueData `cocycle` field: composing the three matrix
transitions `θ_{I,J}θ_{J,K}θ_{K,I} = θ_{I,I} = id` via `grassmannian_cocycle`. -/
lemma grassTrans2_cocycle (r d : ℕ) (I J K : GrassChart r d) :
    (grassTrans2.{u} r d I J K).comp
        ((grassTrans2.{u} r d J K I).comp (grassTrans2.{u} r d K I J))
      = RingHom.id (grassOverlapRing2.{u} r d I J K) := by
  apply IsLocalization.ringHom_ext
    (Submonoid.powers (grassMinor.{u} r d I J * grassMinor.{u} r d I K))
  rw [RingHom.id_comp, RingHom.comp_assoc, RingHom.comp_assoc, grassTrans2_comp_algebraMap]
  have hmat : (grassFrame.{u} r d I).map
        ⇑((grassTrans2.{u} r d I J K).comp ((grassTrans2.{u} r d J K I).comp
          (grassTransAuxTriple.{u} r d K I J)))
      = (grassFrame.{u} r d I).map (algebraMap _ (grassOverlapRing2.{u} r d I J K)) := by
    rw [RingHom.coe_comp, ← Matrix.map_map, RingHom.coe_comp, ← Matrix.map_map,
      grassTransAuxTriple_map_frame, grassTransMatrix_map_overlapToTriple,
      grassTransStep r d J K I I (grassMinor_algebraMap_isUnit_left r d K I J)
        (grassMinor_algebraMap_isUnit_left r d J K I)
        (grassMinor_algebraMap_isUnit_right r d J K I),
      grassTransStep r d I J K I (grassMinor_algebraMap_isUnit_right r d J K I)
        (grassMinor_algebraMap_isUnit_left r d I J K)
        (by rw [grassMinor_self, map_one]; exact isUnit_one)]
    rw [show ((grassFrame.{u} r d I).map (algebraMap _ (grassOverlapRing2.{u} r d I J K))).submatrix
          _root_.id (⇑I) = 1 by
      rw [Matrix.submatrix_map, grassFrame_minor_self]
      exact Matrix.map_one _ (map_zero _) (map_one _),
      inv_one, Matrix.one_mul]
  apply MvPolynomial.ringHom_ext
  · intro n
    rw [eq_intCast (MvPolynomial.C) n, map_intCast, map_intCast]
  · intro v
    have hfr : grassFrame.{u} r d I v.down.1 (↑v.down.2 : Fin r) = MvPolynomial.X v := by
      unfold grassFrame
      rw [dif_neg (fun h => v.down.2.2 (Set.mem_range.mpr h))]; congr 1
    have hentry := congrFun (congrFun hmat v.down.1) (↑v.down.2 : Fin r)
    simp only [Matrix.map_apply] at hentry
    rw [← hfr]; exact hentry

/-- **Geometric cocycle** (`Scheme.GlueData.cocycle` field). The triple-overlap
transitions compose to the identity, by cancelling the `grassTripleIso` factors and
reducing the three `Spec.map`s to `Spec.map` of `grassTrans2_cocycle = id`. -/
lemma grassTransMorphism2_cocycle (r d : ℕ) (I J K : GrassChart r d) :
    grassTransMorphism2.{u} r d I J K ≫ grassTransMorphism2.{u} r d J K I
        ≫ grassTransMorphism2.{u} r d K I J
      = 𝟙 (pullback (grassInclusion.{u} r d I J) (grassInclusion.{u} r d I K)) := by
  simp only [grassTransMorphism2, Category.assoc, Iso.inv_hom_id_assoc]
  slice_lhs 2 4 => rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, grassTrans2_cocycle, CommRingCat.ofHom_id, Spec.map_id]
  simp

/-! ## Project-local Mathlib supplement — Grassmannian GlueData `t_fac` & final assembly

The remaining `Scheme.GlueData` data assembly: the Prop field `t_fac` and the
`grassGlueData`/`grassmannianScheme := D.glued` construction.  `t_fac` is transported
through the geometric identifications `grassTripleIso` (whose two projection halves are
`grassTripleIso_inv_fst`/`_snd`) to a ring identity `grassTrans2_proj_snd_eq` that bottoms
out at the defining `awayLift` factorisations (`grassTrans2_comp_algebraMap`,
`IsLocalization.Away.lift_comp`) and the proven `grassOverlapToTriple_comp_algebraMap`. -/

/-- The ring map underlying the first projection `pullback (f I J) (f I K) ⟶ U^I_J`
under the affine identification `grassTripleIso`: the left tensor inclusion
`s ↦ s ⊗ₜ 1` transported by `grassTripleRingEquiv`. -/
noncomputable def grassTripleProjFst (r d : ℕ) (I J K : GrassChart r d) :
    grassOverlapRing.{u} r d I J →+* grassOverlapRing2.{u} r d I J K :=
  (grassTripleRingEquiv.{u} r d I J K).toRingHom.comp Algebra.TensorProduct.includeLeftRingHom

/-- The ring map underlying the second projection `pullback (f I J) (f I K) ⟶ U^I_K`
under the affine identification `grassTripleIso`: the right tensor inclusion
`t ↦ 1 ⊗ₜ t` transported by `grassTripleRingEquiv`. -/
noncomputable def grassTripleProjSnd (r d : ℕ) (I J K : GrassChart r d) :
    grassOverlapRing.{u} r d I K →+* grassOverlapRing2.{u} r d I J K :=
  (grassTripleRingEquiv.{u} r d I J K).toRingHom.comp
    (Algebra.TensorProduct.includeRight).toRingHom

/-- `grassTripleProjFst` restricts to the chart structural map on `ℤ[X^I]`: it is an
`ℤ[X^I]`-algebra map (tensor inclusion ∘ equivalence). -/
lemma grassTripleProjFst_comp_algebraMap (r d : ℕ) (I J K : GrassChart r d) :
    (grassTripleProjFst.{u} r d I J K).comp
        (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ) (grassOverlapRing.{u} r d I J))
      = algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
          (grassOverlapRing2.{u} r d I J K) := by
  refine RingHom.ext fun x => ?_
  change (grassTripleRingEquiv.{u} r d I J K)
      (Algebra.TensorProduct.includeLeftRingHom
        (algebraMap _ (grassOverlapRing.{u} r d I J) x)) = _
  rw [show Algebra.TensorProduct.includeLeftRingHom
          (algebraMap _ (grassOverlapRing.{u} r d I J) x)
        = algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
            (grassOverlapRing.{u} r d I J ⊗[MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ]
              grassOverlapRing.{u} r d I K) x by simp]
  exact (grassTripleRingEquiv.{u} r d I J K).commutes x

/-- `grassTripleProjSnd` restricts to the chart structural map on `ℤ[X^I]`. -/
lemma grassTripleProjSnd_comp_algebraMap (r d : ℕ) (I J K : GrassChart r d) :
    (grassTripleProjSnd.{u} r d I J K).comp
        (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ) (grassOverlapRing.{u} r d I K))
      = algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
          (grassOverlapRing2.{u} r d I J K) := by
  refine RingHom.ext fun x => ?_
  change (grassTripleRingEquiv.{u} r d I J K)
      (Algebra.TensorProduct.includeRight
        (algebraMap _ (grassOverlapRing.{u} r d I K) x)) = _
  rw [show Algebra.TensorProduct.includeRight
          (algebraMap _ (grassOverlapRing.{u} r d I K) x)
        = algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
            (grassOverlapRing.{u} r d I J ⊗[MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ]
              grassOverlapRing.{u} r d I K) x by simp]
  exact (grassTripleRingEquiv.{u} r d I J K).commutes x

/-- **First projection of `grassTripleIso`.** Under the affine identification of the
triple overlap `pullback (f I J) (f I K) ≅ Spec ℤ[X^I,1/(P^I_J P^I_K)]`, the first
pullback projection is `Spec` of the localisation map `grassTripleProjFst`. -/
lemma grassTripleIso_inv_fst (r d : ℕ) (I J K : GrassChart r d) :
    (grassTripleIso.{u} r d I J K).inv ≫
        pullback.fst (grassInclusion.{u} r d I J) (grassInclusion.{u} r d I K)
      = Spec.map (CommRingCat.ofHom (grassTripleProjFst.{u} r d I J K)) := by
  rw [grassTripleIso, Iso.trans_inv, Category.assoc,
    show (Scheme.Spec.mapIso
            (grassTripleRingEquiv.{u} r d I J K).symm.toRingEquiv.toCommRingCatIso.op).inv
          = Spec.map (CommRingCat.ofHom (grassTripleRingEquiv.{u} r d I J K).toRingHom) from rfl]
  erw [pullbackSpecIso_inv_fst']
  erw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- **Second projection of `grassTripleIso`.** The second pullback projection is `Spec`
of the localisation map `grassTripleProjSnd`. -/
lemma grassTripleIso_inv_snd (r d : ℕ) (I J K : GrassChart r d) :
    (grassTripleIso.{u} r d I J K).inv ≫
        pullback.snd (grassInclusion.{u} r d I J) (grassInclusion.{u} r d I K)
      = Spec.map (CommRingCat.ofHom (grassTripleProjSnd.{u} r d I J K)) := by
  rw [grassTripleIso, Iso.trans_inv, Category.assoc,
    show (Scheme.Spec.mapIso
            (grassTripleRingEquiv.{u} r d I J K).symm.toRingEquiv.toCommRingCatIso.op).inv
          = Spec.map (CommRingCat.ofHom (grassTripleRingEquiv.{u} r d I J K).toRingHom) from rfl]
  erw [pullbackSpecIso_inv_snd]
  erw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- `θ_{I,J}` lifted past the localisation map restricts to `grassTransAux` on `ℤ[X^J]`. -/
private lemma grassTrans_comp_algebraMap (r d : ℕ) (I J : GrassChart r d) :
    (grassTrans.{u} r d I J).comp
        (algebraMap (MvPolynomial (ULift.{u} (GrassVars r d J)) ℤ) (grassOverlapRing.{u} r d J I))
      = grassTransAux.{u} r d I J := by
  rw [grassTrans, IsLocalization.Away.lift_comp]

/-- The first-projection ring map agrees with `grassOverlapToTriple`: both are the unique
`ℤ[X^I]`-algebra localisation map `ℤ[X^I,1/P^I_J] → ℤ[X^I,1/(P^I_J P^I_K)]`. -/
lemma grassTripleProjFst_eq_overlapToTriple (r d : ℕ) (I J K : GrassChart r d) :
    grassTripleProjFst.{u} r d I J K = grassOverlapToTriple.{u} r d I J K := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (grassMinor.{u} r d I J))
  rw [grassTripleProjFst_comp_algebraMap, grassOverlapToTriple_comp_algebraMap]

/-- **Ring-level `t_fac`.** The triple-overlap transition `θ'_{I,J,K}` followed by the
second projection equals the first projection followed by `θ_{I,J}`; both restrict on
`ℤ[X^J]` to `grassTransAuxTriple`. -/
lemma grassTrans2_proj_snd_eq (r d : ℕ) (I J K : GrassChart r d) :
    (grassTrans2.{u} r d I J K).comp (grassTripleProjSnd.{u} r d J K I)
      = (grassTripleProjFst.{u} r d I J K).comp (grassTrans.{u} r d I J) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (grassMinor.{u} r d J I))
  rw [RingHom.comp_assoc, grassTripleProjSnd_comp_algebraMap, grassTrans2_comp_algebraMap,
    RingHom.comp_assoc, grassTrans_comp_algebraMap, grassTripleProjFst_eq_overlapToTriple,
    grassTransAuxTriple]

/-- **`t_fac` field of the Grassmannian `GlueData`.** The triple-overlap morphism `t'`
followed by the second projection equals the first projection followed by `t`, by
transporting the ring identity `grassTrans2_proj_snd_eq` through `grassTripleIso`. -/
lemma grassTransMorphism2_tfac (r d : ℕ) (I J K : GrassChart r d) :
    grassTransMorphism2.{u} r d I J K ≫
        pullback.snd (grassInclusion.{u} r d J K) (grassInclusion.{u} r d J I)
      = pullback.fst (grassInclusion.{u} r d I J) (grassInclusion.{u} r d I K) ≫
          grassTransMorphism.{u} r d I J := by
  rw [← cancel_epi (grassTripleIso.{u} r d I J K).inv]
  rw [grassTransMorphism2]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [grassTripleIso_inv_snd, ← Category.assoc, grassTripleIso_inv_fst, grassTransMorphism]
  erw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rw [grassTrans2_proj_snd_eq]

/-- **The Grassmannian `Scheme.GlueData`** (`def:grassmannian-scheme`).  All data fields
are realised by the chart constructions above; both Prop fields `t_fac`/`cocycle` are
proven (`grassTransMorphism2_tfac`/`grassTransMorphism2_cocycle`). -/
noncomputable def grassGlueData (r d : ℕ) : Scheme.GlueData.{u} where
  J := ULift.{u} (GrassChart r d)
  U i := grassChart.{u} r d i.down
  V p := grassOverlap.{u} r d p.1.down p.2.down
  f i j := grassInclusion.{u} r d i.down j.down
  f_id i := grassInclusion_self_isIso.{u} r d i.down
  t i j := grassTransMorphism.{u} r d i.down j.down
  t_id i := grassTransMorphism_self.{u} r d i.down
  t' i j k := grassTransMorphism2.{u} r d i.down j.down k.down
  t_fac i j k := grassTransMorphism2_tfac.{u} r d i.down j.down k.down
  cocycle i j k := grassTransMorphism2_cocycle.{u} r d i.down j.down k.down
  f_open i j := inferInstance

/-- **The Grassmannian scheme `Grass(r, d)` over `ℤ`** (`def:grassmannian-scheme`).

The finite-type, smooth scheme over `ℤ` obtained by glueing the `binom r d` affine
charts `U^I = Spec ℤ[X^I]` along the transition maps `θ_{I,J}(X^J) = (X^I_J)⁻¹ X^I`.

BUILD STATUS (bottom-up `Scheme.GlueData` assembly, see the chart-data block above).
The bottom data layer is now in place as genuine axiom-free definitions:
* index `GrassChart`, free vars `GrassVars`, chart ring `grassChartRing`,
  chart `grassChart` (GlueData `U`);
* frame `grassFrame`, minor `grassMinor`, with `grassFrame_minor_self`
  (`X^I_I = 1`) and `grassMinor_self` (`P^I_I = 1`);
* overlap scheme `grassOverlap` (GlueData `V`) and inclusion `grassInclusion`
  (GlueData `f`), with the proven `IsOpenImmersion` instance (the `f_open` field);
* overlap ring `grassOverlapRing`, frame/minor over it (`grassFrameLoc`,
  `grassMinorMatrixLoc`) with `grassMinorMatrixLoc_det`/`_isUnit_det`
  (`X^I_J ∈ GL_d`), transition matrix `grassTransMatrix`, polynomial-level
  transition `grassTransAux : ℤ[X^J] → ℤ[X^I, 1/P^I_J]`, the matrix identity
  `grassTransAux_map_frame` (`θ(X^J) = (X^I_J)⁻¹ X^I`) and the **transition-map
  gate** `grassTransAux_minor_isUnit` (`θ_{I,J}(P^J_I) = 1/P^I_J` is a unit);
* transition ring map `grassTrans : ℤ[X^J,1/P^J_I] → ℤ[X^I,1/P^I_J]` (lift of
  `grassTransAux` past the gate) and geometric `grassTransMorphism`
  (`t I J : U^I_J ⟶ U^J_I`, the GlueData `t` data field).

All FOUR GlueData data fields are now real: `U = grassChart`, `V = grassOverlap`,
`f = grassInclusion` (`f_open` proven), `t = grassTransMorphism`.

REMAINING to assemble `D : Scheme.GlueData` (`grassmannianScheme := D.glued`):
1. `f_id` (`IsIso (f i i)`): from `grassMinor_self` (`P^I_I = 1`), the localisation
   away from the unit `1` is iso (`IsLocalization.atUnits`/`Away` of a unit).
2. `t_id` (`t i i = 𝟙`): `θ_{I,I} = id` since `grassTransMatrix I I = X^I`
   (`grassMinorMatrixLoc I I = 1` by `grassFrame_minor_self`, so `(1)⁻¹ X^I = X^I`),
   hence `grassTrans I I = RingHom.id` and `Spec.map (𝟙) = 𝟙`.
3. `t'` (data) on triple overlaps `pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)`:
   `f_hasPullback` is automatic (open immersions); build `t'` as the induced map and
   discharge `t_fac` + `cocycle` entrywise from `grassmannian_cocycle` (already
   proven, line ~545) applied to the frame matrices.  This is the last algebraic
   step — the hard well-definedness was the gate, now closed.
All data fields are now real morphisms with both Prop fields proven, so the scheme is
the genuine glued scheme `(grassGlueData r d).glued`. -/
noncomputable def grassmannianScheme (r d : ℕ) : Scheme.{u} :=
  (grassGlueData.{u} r d).glued

/-- The structure morphism `Grass(r, d) ⟶ Spec ℤ`, realised as the unique morphism
to the terminal scheme. -/
noncomputable def grassmannianScheme.structureMorphism (r d : ℕ) :
    grassmannianScheme.{u} r d ⟶ ⊤_ Scheme.{u} :=
  terminal.from _

/-! ### Separatedness: the algebraic core

On the chart product `U^I ×_ℤ U^J = Spec(ℤ[X^I] ⊗_ℤ ℤ[X^J])` the diagonal restricts to the
overlap `U^I_J = Spec ℤ[X^I, 1/P^I_J]`, classified by the ring map `ℤ[X^I] ⊗_ℤ ℤ[X^J] →
ℤ[X^I,1/P^I_J]` (`algebraMap` on the first factor, the polynomial transition `θ_{I,J}` on the
second). This map is **surjective**: its image already contains all of `ℤ[X^I]` and the unit
`θ_{I,J}(P^J_I) = (P^I_J)⁻¹`, hence all of the localisation `ℤ[X^I, 1/P^I_J]`. Surjectivity makes
the diagonal a closed immersion on each chart product, which is the content of
`lem:grassmannian-separated`.

The algebraic identity `θ_{I,J}(P^J_I) = (P^I_J)⁻¹` (`grassTransAux_minor_self_mul`) is the heart
of that surjectivity and is proven below. The full surjectivity statement of the diagonal ring map
`ℤ[X^I] ⊗_ℤ ℤ[X^J] → ℤ[X^I,1/P^I_J]` is stated as `grassDiagRing_surjective`; see the proof note
there for the `⊗[ℤ]`-module-diamond obstruction that currently blocks naming the tensor map. -/

/-- `θ_{I,J}(P^J_I) = (P^I_J)⁻¹`: the polynomial transition sends the cross-minor `P^J_I` to the
ring inverse of the image of `P^I_J`, so `algebraMap(P^I_J) · θ_{I,J}(P^J_I) = 1`.  This is the
`K = I` specialisation of `grassTransAux_minor` (using `P^I_I = 1`), the algebraic heart of
separatedness on the chart overlap `U^I_J`. -/
lemma grassTransAux_minor_self_mul (r d : ℕ) (I J : GrassChart r d) :
    algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ) (grassOverlapRing.{u} r d I J)
        (grassMinor.{u} r d I J)
      * grassTransAux.{u} r d I J (grassMinor.{u} r d J I) = 1 := by
  rw [grassTransAux_minor, Matrix.det_nonsing_inv, grassMinor_self, map_one, mul_one,
    ← grassMinorMatrixLoc_det]
  exact Ring.mul_inverse_cancel _ (grassMinorMatrixLoc_isUnit_det r d I J)

/-- **Generation lemma for separatedness.** Every element `z` of the overlap ring
`ℤ[X^I, 1/P^I_J]` is `algebraMap(a) · θ_{I,J}(P^J_I)ⁿ` for some `a ∈ ℤ[X^I]` and `n`.  Equivalently
the overlap ring is generated, as a ring, by the image of `ℤ[X^I]` together with `θ_{I,J}(P^J_I)`
— precisely the two images of the diagonal ring map `ℤ[X^I] ⊗_ℤ ℤ[X^J] → ℤ[X^I,1/P^I_J]`.  This is
the surjectivity content of `lem:grassmannian-separated` stated without naming the `⊗[ℤ]` map (see
note). Proof: `IsLocalization.Away.surj` gives `z · algebraMap(P^I_J)ⁿ = algebraMap(a)`; multiply
by `θ_{I,J}(P^J_I)ⁿ` and cancel using `grassTransAux_minor_self_mul`. -/
lemma grassDiagRing_surjective (r d : ℕ) (I J : GrassChart r d)
    (z : grassOverlapRing.{u} r d I J) :
    ∃ (a : MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ) (n : ℕ),
      z = algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
            (grassOverlapRing.{u} r d I J) a
          * grassTransAux.{u} r d I J (grassMinor.{u} r d J I) ^ n := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj (grassMinor.{u} r d I J) z
  refine ⟨a, n, ?_⟩
  set u := algebraMap (MvPolynomial (ULift.{u} (GrassVars r d I)) ℤ)
    (grassOverlapRing.{u} r d I J) (grassMinor.{u} r d I J) with hu
  set w := grassTransAux.{u} r d I J (grassMinor.{u} r d J I) with hw
  have huw : u * w = 1 := grassTransAux_minor_self_mul r d I J
  have h : z * (u * w) ^ n = algebraMap _ _ a * w ^ n := by
    rw [mul_pow, ← mul_assoc, ha]
  rwa [huw, one_pow, mul_one] at h

/-- **Absolute separatedness of the Grassmannian glued scheme** (the substance of
`lem:grassmannian-separated`).

ROUTE (Nitsure §1): the diagonal `Δ : X ⟶ X ×_⊤ X` of the glued scheme `X = grassmannianScheme`
is a closed immersion. Covering `X ×_⊤ X` by the chart products `U^I ×_⊤ U^J`, the preimage
`Δ⁻¹(U^I ×_⊤ U^J) = U^I_J` is the affine overlap, and the restricted diagonal
`U^I_J ⟶ U^I ×_⊤ U^J` is `Spec` of the ring map `ℤ[X^I] ⊗_ℤ ℤ[X^J] → ℤ[X^I,1/P^I_J]` whose
surjectivity is the algebraic core `grassDiagRing_surjective` (its image contains `ℤ[X^I]` and the
unit `θ_{I,J}(P^J_I) = (P^I_J)⁻¹`). `Spec` of a surjection is a closed immersion
(`IsClosedImmersion.spec_of_surjective`).

PROGRESS: the reduction to `IsClosedImmersion (pullback.diagonal (terminal.from X))` is performed
below. The remaining diagonal-is-closed-immersion step is the documented blocker:
* Mathlib has **no** `Scheme.GlueData → IsSeparated` (verified absent);
* the cover-based criterion `isClosedImmersion_diagonal_restrict_diagonalCoverDiagonalRange` only
  covers the diagonal *blocks* `U^I ×_⊤ U^I`, so the off-diagonal `U^I ×_⊤ U^J` (`I ≠ J`) closed
  immersions must be assembled by hand via `IsZariskiLocalAtTarget` over the product cover;
* naming the chart-product ring `ℤ[X^I] ⊗_ℤ ℤ[X^J]` triggers the `⊗[ℤ]` module diamond
  (`Algebra ℤ`'s module vs `AddCommGroup.intModule`): the tensor `Semiring` instance fails to
  synthesise, so the geometric identification of the restricted diagonal with `Spec` of the
  surjection cannot yet be stated. The *algebraic* content is fully proved
  (`grassDiagRing_surjective`); what remains is the diamond-safe geometric assembly. -/
lemma grassmannianScheme_isSeparated (r d : ℕ) :
    (grassmannianScheme.{u} r d).IsSeparated := by
  rw [Scheme.isSeparated_iff, AlgebraicGeometry.isSeparated_iff]
  -- Goal: `IsClosedImmersion (pullback.diagonal (terminal.from (grassmannianScheme r d)))`.
  -- See the docstring: assemble over the product cover `U^I ×_⊤ U^J`; each off-diagonal block is
  -- `Spec` of the surjection `grassDiagRing_surjective`. Blocked on the `⊗[ℤ]` module diamond.
  sorry

/-- **Separatedness of the Grassmannian** (`lem:grassmannian-separated`).

`Grass(r, d)` is separated over `ℤ`: on each chart product `U^I × U^J` the diagonal
is the closed subscheme cut out by `X^J_I X^I - X^J = 0`.

Reduces (via the structure morphism being `terminal.from`) to absolute separatedness of the glued
scheme, `(grassmannianScheme r d).IsSeparated`; see `grassmannianScheme_isSeparated`. -/
theorem grassmannian_separated (r d : ℕ) :
    IsSeparated (grassmannianScheme.structureMorphism.{u} r d) := by
  haveI : (grassmannianScheme.{u} r d).IsSeparated := grassmannianScheme_isSeparated r d
  unfold grassmannianScheme.structureMorphism
  exact Scheme.IsSeparated.isSeparated_terminal_from

/-! ### Properness: finiteness instances on the structure morphism

`valuativeCriterion_proper` requires `QuasiCompact`, `QuasiSeparated`, `LocallyOfFiniteType` on the
structure morphism, plus a `ValuativeCriterion`. The three finiteness instances are landed here
(they do not depend on the deep DVR criterion); `QuasiSeparated` is free from
`grassmannian_separated` via `IsSeparated.instQuasiSeparated`. -/

/-- The Grassmannian glued scheme is quasi-compact: it is covered by the `binom r d` (finitely many)
affine charts `U^I`, each compact. -/
instance grassmannianScheme_compactSpace (r d : ℕ) :
    CompactSpace (grassmannianScheme.{u} r d) := by
  haveI : Finite (grassGlueData.{u} r d).openCover.I₀ := by
    change Finite (ULift.{u} (GrassChart r d)); infer_instance
  haveI : ∀ i, CompactSpace ((grassGlueData.{u} r d).openCover.X i) := fun i => by
    change CompactSpace (grassChart.{u} r d i.down)
    unfold grassChart; infer_instance
  exact (grassGlueData.{u} r d).openCover.compactSpace

/-- **`QuasiCompact` for properness.** The structure morphism `Grass(r,d) ⟶ Spec ℤ` is
quasi-compact, since `Grass(r,d)` is compact and `Spec ℤ` is the terminal (affine) scheme. -/
instance grassmannian_structureMorphism_quasiCompact (r d : ℕ) :
    QuasiCompact (grassmannianScheme.structureMorphism.{u} r d) := by
  unfold grassmannianScheme.structureMorphism
  rw [← compactSpace_iff_quasiCompact]
  infer_instance

/-- **`QuasiSeparated` for properness.** Free from separatedness of the structure morphism
(`grassmannian_separated`) via `IsSeparated.instQuasiSeparated`. -/
instance grassmannian_structureMorphism_quasiSeparated (r d : ℕ) :
    QuasiSeparated (grassmannianScheme.structureMorphism.{u} r d) := by
  haveI := grassmannian_separated.{u} r d
  infer_instance

/-- **Properness of the Grassmannian** (`lem:grassmannian-proper`).

`π : Grass(r, d) ⟶ Spec ℤ` is proper, via the valuative criterion for DVRs
(`Basic.valuativeCriterion_proper`, i.e. `IsProper.of_valuativeCriterion`).

PROGRESS: the proof is reduced to `valuativeCriterion_proper`, whose `QuasiCompact` /
`QuasiSeparated` instances are now landed (`grassmannian_structureMorphism_quasiCompact` /
`_quasiSeparated`). Two obligations remain, documented as the blocker:
* `LocallyOfFiniteType`: each chart `U^I = Spec ℤ[X^I]` is finitely generated over `ℤ` (finitely
  many variables), so the structure morphism is locally of finite type; needs the source-local
  criterion on `(grassGlueData r d).openCover` plus `Algebra.FiniteType ℤ` of the chart rings.
* `ValuativeCriterion`: the deep Nitsure DVR argument (`lem:grassmannian-proper` source quote) — a
  `Spec K → Grass` factors through a chart `f : ℤ[X^I] → K`; choosing `J` minimising `ν(f(P^I_J))`,
  the composite `g(X^J) = f((X^I_J)⁻¹ X^I)` has all minors of non-negative valuation, so `g` factors
  through the DVR `R ⊂ K`, giving the unique lift `Spec R → Grass`. This is the substantial part. -/
theorem grassmannian_proper (r d : ℕ) :
    IsProper (grassmannianScheme.structureMorphism.{u} r d) := by
  haveI : LocallyOfFiniteType (grassmannianScheme.structureMorphism.{u} r d) := by
    sorry
  refine valuativeCriterion_proper _ ?_
  -- The valuative criterion for DVRs: the Nitsure DVR-valuation lifting argument (see docstring).
  sorry

/-- **The tautological quotient on the Grassmannian** (`def:grassmannian-universal-quotient`).

A rank-`d` locally free sheaf `U` on `Grass(r, d)` with a surjection
`u : ⊕^r O_{Grass(r,d)} → U`, glued from the chart-wise surjections `u^I` given by
the matrix `X^I` via the transition matrices `g_{I,J} = (X^I_J)⁻¹`. -/
structure GrassmannianTautological (r d : ℕ) where
  /-- The tautological rank-`d` sheaf `U`. -/
  U : (grassmannianScheme r d).Modules
  /-- `U` is locally free of rank `d`. -/
  locallyFree : IsLocallyFreeOfRank d U
  /-- The universal surjection `u : ⊕^r O → U`. -/
  u : freeModule (grassmannianScheme r d) r ⟶ U
  /-- `u` is surjective. -/
  surj : Epi u

/-- **The tautological quotient on the Grassmannian** (`def:grassmannian-universal-quotient`). -/
noncomputable def grassmannianUniversalQuotient (r d : ℕ) :
    GrassmannianTautological r d :=
  sorry

/-- **`det U` is very ample; the Plücker embedding** (`lem:grassmannian-very-ample`).

The determinant line bundle `det U` is relatively very ample over `ℤ`; its Plücker
sections `σ_I|_{U^J} = P^J_I` give a closed embedding
`Grass(r, d) ↪ ℙ^m_ℤ`, `m = binom r d - 1`.

STATING-GAP: the determinant `det U = ⋀^d U` of a locally free sheaf is a Mathlib
gap, so we cannot name `det U` directly.  We state the expressible consequence —
the *existence* of a relatively very ample line bundle on `Grass(r, d)` over `ℤ`
(namely `det U`), in the sense of `Basic.RelativelyVeryAmple`. -/
theorem grassmannian_very_ample (r d : ℕ) :
    ∃ L : (grassmannianScheme r d).Modules,
      RelativelyVeryAmple (grassmannianScheme.structureMorphism r d) L :=
  sorry

/-- **The Grassmannian represents the quotient functor** (`thm:grassmannian-represents`).

`Grass(r, d)` together with its tautological quotient represents the functor sending
`T` to the set of rank-`d` locally free quotients `q : ⊕^r O_T ↠ F`.  By the
functor-of-points principle it suffices to give, naturally in a commutative ring
`R`, a bijection between `R`-points `Spec R ⟶ Grass(r, d)` and rank-`d` locally free
quotients of `R^r`.  The latter set is Mathlib's `Module.Grassmannian R (Fin r → R) d`
(submodules `N ⊂ R^r` — the kernels `ker q` — with `R^r / N` finite projective of
rank `d`), which matches the blueprint's `⟨F, q⟩ ↦ ker q` description of the moduli
set exactly.

STATING-GAP: the all-schemes representability `Mor(T, Grass) ≅ Grass(r,d)(T)` is
approximated by its restriction to affine test schemes `T = Spec R`, which (by the
functor-of-points principle) determines the scheme; naturality in `R` is recorded
informally. -/
theorem grassmannian_represents (r d : ℕ) (R : Type u) [CommRing R] :
    Nonempty ((Spec (CommRingCat.of R) ⟶ grassmannianScheme r d) ≃
      Module.Grassmannian R (Fin r → R) d) :=
  sorry

end MR2223407ConstructionHilbertQuot
