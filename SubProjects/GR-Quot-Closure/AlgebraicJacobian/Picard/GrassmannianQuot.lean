import AlgebraicJacobian.Picard.GrassmannianCells
import AlgebraicJacobian.Picard.QuotScheme
import AlgebraicJacobian.Picard.GlueDescent

/-!
# The tautological quotient and the universal property of `Gr(r,d)`

This file adds, on top of the Grassmannian scheme `Gr(d,r)` built in
`GrassmannianCells.lean`, the tautological rank-`d` quotient
`u : O^r ↠ U` and the universal property making `Gr(d,r)` the fine moduli
space of rank-`d` locally free quotients of `O^r`.

Blueprint: `blueprint/src/chapters/Picard_GrassmannianQuot.tex` (Nitsure §1).
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Grassmannian

/-! ## Project-local Mathlib supplement — scalar endomorphisms of the structure sheaf

To realise a matrix of regular functions as a morphism of free sheaves of modules we
need to turn a global section `a ∈ Γ(X, ⊤)` of the structure sheaf into a scalar
endomorphism of `O_X` (= `SheafOfModules.unit X.ringCatSheaf`). On the affine chart
`U^I = Spec R^I` the matrix entries of the universal matrix `X^I` live in `R^I`, and we
inject them into the global sections via `Scheme.ΓSpecIso`.

These helpers are project-local: Mathlib has no ready-made "matrix ↦ morphism of free
sheaves" primitive. -/

variable {X : Scheme.{u}}

/-- The global section of the structure sheaf `O_X` (as a sheaf of modules over itself)
determined by a section `a ∈ Γ(X, ⊤)` over the whole space, by restriction to every open.
Project-local helper for building scalar endomorphisms. -/
noncomputable def globalUnitSection (a : Γ(X, ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk
    (fun Y => (X.ringCatSheaf.obj.map (homOfLE le_top).op a : X.ringCatSheaf.obj.obj Y))
    (by
      intro Y Z f
      change (X.ringCatSheaf.obj.map f) (X.ringCatSheaf.obj.map (homOfLE le_top).op a)
        = X.ringCatSheaf.obj.map (homOfLE le_top).op a
      rw [← CategoryTheory.comp_apply, ← X.ringCatSheaf.obj.map_comp]
      congr 1)

/-- The scalar endomorphism of `O_X` given by a global section `a ∈ Γ(X, ⊤)`:
multiplication by `a`. Project-local helper. -/
noncomputable def scalarEnd (a : Γ(X, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.symm (globalUnitSection a)

/-- `scalarEnd 1` is the identity endomorphism of `O_X`. Project-local helper for
identifying the diagonal entries of the chart quotient. -/
lemma scalarEnd_one : scalarEnd (1 : Γ(X, ⊤)) = 𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
  rw [scalarEnd, Equiv.symm_apply_eq]
  ext Y
  change X.ringCatSheaf.obj.map (homOfLE le_top).op (1 : Γ(X, ⊤))
      = (SheafOfModules.Hom.val (𝟙 (SheafOfModules.unit X.ringCatSheaf))).app Y
          (1 : X.ringCatSheaf.obj.obj Y)
  rw [SheafOfModules.id_val, PresheafOfModules.id_app]
  exact map_one _

/-- `scalarEnd 0` is the zero endomorphism of `O_X`. Project-local helper for identifying
the off-diagonal entries of the chart quotient. -/
lemma scalarEnd_zero : scalarEnd (0 : Γ(X, ⊤)) = 0 := by
  rw [scalarEnd, Equiv.symm_apply_eq]
  ext Y
  change X.ringCatSheaf.obj.map (homOfLE le_top).op (0 : Γ(X, ⊤))
      = (SheafOfModules.Hom.val
          (0 : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)).app Y
          (1 : X.ringCatSheaf.obj.obj Y)
  refine (map_zero _).trans ?_
  rfl

/-- The value of the scalar endomorphism `scalarEnd a` on a section `x` over `Y` is
multiplication by the restriction of `a`: `(scalarEnd a)(x) = x · a|_Y`. Project-local
helper, the computational heart of the `scalarEnd` ring-hom identities below. -/
lemma scalarEnd_val_app (a : Γ(X, ⊤)) (Y : (TopologicalSpace.Opens (X : TopCat))ᵒᵖ)
    (x : X.ringCatSheaf.obj.obj Y) :
    (scalarEnd a).val.app Y x = x * X.ringCatSheaf.obj.map (homOfLE le_top).op a := by
  rfl

/-- `scalarEnd c` corresponds to the global section `c` under `unitHomEquiv`. -/
lemma unitHomEquiv_scalarEnd (c : Γ(X, ⊤)) :
    (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (scalarEnd c) = globalUnitSection c := by
  rw [scalarEnd, Equiv.apply_symm_apply]

/-- The scalar endomorphism `scalarEnd a` sends the unit section `1` to `a|_Y`. -/
lemma scalarEnd_val_app_one (a : Γ(X, ⊤)) (Y : (TopologicalSpace.Opens (X : TopCat))ᵒᵖ) :
    (scalarEnd a).val.app Y (1 : X.ringCatSheaf.obj.obj Y)
      = X.ringCatSheaf.obj.map (homOfLE le_top).op a := by
  exact one_smul _ _

/-- Composition of scalar endomorphisms is multiplication: `scalarEnd a ≫ scalarEnd b =
scalarEnd (a * b)`. Project-local; underlies `matrixEnd` multiplicativity. -/
lemma scalarEnd_comp (a b : Γ(X, ⊤)) :
    scalarEnd a ≫ scalarEnd b = scalarEnd (a * b) := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  change SheafOfModules.sectionsMap (scalarEnd b)
        ((SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (scalarEnd a))
      = (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv (scalarEnd (a * b))
  rw [unitHomEquiv_scalarEnd, unitHomEquiv_scalarEnd]
  refine PresheafOfModules.sections_ext _ _ (fun Y => ?_)
  change (scalarEnd b).val.app Y (X.ringCatSheaf.obj.map (homOfLE le_top).op a)
      = X.ringCatSheaf.obj.map (homOfLE le_top).op (a * b)
  exact (RingHom.map_mul (X.ringCatSheaf.obj.map (homOfLE le_top).op).hom a b).symm

/-- `scalarEnd` is additive: `scalarEnd (a + b) = scalarEnd a + scalarEnd b`.
Project-local; underlies `matrixEnd` matrix-multiplication identity. -/
lemma scalarEnd_add (a b : Γ(X, ⊤)) :
    scalarEnd (a + b) = scalarEnd a + scalarEnd b := by
  conv_lhs => rw [scalarEnd]
  rw [Equiv.symm_apply_eq]
  refine PresheafOfModules.sections_ext _ _ (fun Y => ?_)
  change X.ringCatSheaf.obj.map (homOfLE le_top).op (a + b)
      = (scalarEnd a).val.app Y (1 : X.ringCatSheaf.obj.obj Y)
        + (scalarEnd b).val.app Y (1 : X.ringCatSheaf.obj.obj Y)
  rw [scalarEnd_val_app_one, scalarEnd_val_app_one]
  exact RingHom.map_add (X.ringCatSheaf.obj.map (homOfLE le_top).op).hom a b

/-- `scalarEnd` of a finite sum is the sum of the `scalarEnd`s. Project-local. -/
lemma scalarEnd_sum {ι : Type*} (s : Finset ι) (f : ι → Γ(X, ⊤)) :
    scalarEnd (∑ i ∈ s, f i) = ∑ i ∈ s, scalarEnd (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [scalarEnd_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, scalarEnd_add, ih]

/-! ## Matrix automorphisms of the free sheaf

To realise the `GL_d` bundle transitions we promote an (invertible) `d × d` matrix of
global sections to an automorphism of the free rank-`d` sheaf `O_S^d`, exactly as
`chartQuotientMap` realises the universal matrix. The two key algebraic facts — that
`matrixEnd` turns matrix multiplication into composition and the identity matrix into the
identity — follow from the `scalarEnd` ring-hom identities above. -/

/-- `SheafOfModules` over `O_S` has finite biproducts (it has finite products). -/
instance hasFiniteBiproducts_modules (S : Scheme.{0}) :
    HasFiniteBiproducts (SheafOfModules S.ringCatSheaf) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- A `d × d` matrix of global sections of `O_S` realised as an endomorphism of the free
rank-`d` sheaf `O_S^d`: the `(p,q)`-entry acts as `scalarEnd`, assembled over the rank-`d`
biproduct (mirrors `chartQuotientMap`). Project-local. -/
noncomputable def matrixEnd {S : Scheme.{0}} {d : ℕ} (M : Matrix (Fin d) (Fin d) Γ(S, ⊤)) :
    SheafOfModules.free (R := S.ringCatSheaf) (Fin d) ⟶
      SheafOfModules.free (R := S.ringCatSheaf) (Fin d) :=
  (biproduct.isoCoproduct (fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf)).symm.hom ≫
    biproduct.matrix (fun i p => scalarEnd (M p i)) ≫
    (biproduct.isoCoproduct (fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf)).hom

/-- Composition of two `biproduct.matrix` morphisms is the matrix of pointwise sums of
composites — the categorical matrix product. Project-local helper for `matrixEnd_comp`. -/
private lemma biproduct_matrix_comp {S : Scheme.{0}} {d : ℕ}
    (mM mN : Fin d → Fin d →
      (SheafOfModules.unit S.ringCatSheaf ⟶ SheafOfModules.unit S.ringCatSheaf)) :
    biproduct.matrix (f := fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf)
        (g := fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf) mM ≫ biproduct.matrix mN
      = biproduct.matrix (fun i q => ∑ p, mM i p ≫ mN p q) := by
  refine biproduct.hom_ext' _ _ (fun i => biproduct.hom_ext _ _ (fun q => ?_))
  simp only [Category.assoc, biproduct.ι_matrix_assoc, biproduct.matrix_π, biproduct.lift_desc,
    biproduct.ι_matrix, biproduct.lift_π]

/-- `matrixEnd` turns matrix multiplication into composition (with the order reversed by
the contravariance of the column/component indexing): `matrixEnd M ≫ matrixEnd N =
matrixEnd (N * M)`. Project-local. -/
lemma matrixEnd_comp {S : Scheme.{0}} {d : ℕ} (M N : Matrix (Fin d) (Fin d) Γ(S, ⊤)) :
    matrixEnd M ≫ matrixEnd N = matrixEnd (N * M) := by
  rw [matrixEnd, matrixEnd, matrixEnd]
  have hcomp : biproduct.matrix (fun i p => scalarEnd (M p i))
        ≫ biproduct.matrix (fun i p => scalarEnd (N p i))
      = biproduct.matrix (fun i p => scalarEnd ((N * M) p i)) := by
    rw [biproduct_matrix_comp]
    congr 1
    funext i q
    simp_rw [scalarEnd_comp]
    rw [← scalarEnd_sum, Matrix.mul_apply]
    exact congrArg scalarEnd (Finset.sum_congr rfl (fun p _ => mul_comm _ _))
  simp only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (biproduct.matrix (fun i p => scalarEnd (M p i))), hcomp]

/-- `matrixEnd` of the identity matrix is the identity. Project-local. -/
lemma matrixEnd_one {S : Scheme.{0}} {d : ℕ} :
    matrixEnd (1 : Matrix (Fin d) (Fin d) Γ(S, ⊤)) = 𝟙 _ := by
  rw [matrixEnd]
  have hmat : biproduct.matrix
        (fun i p => scalarEnd ((1 : Matrix (Fin d) (Fin d) Γ(S, ⊤)) p i))
      = 𝟙 (⨁ fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf) := by
    refine biproduct.hom_ext' _ _ (fun i => biproduct.hom_ext _ _ (fun p => ?_))
    simp only [Category.assoc, Category.id_comp, biproduct.ι_matrix_assoc, biproduct.lift_π]
    rw [Matrix.one_apply]
    by_cases h : p = i
    · subst h; rw [if_pos rfl, scalarEnd_one, biproduct.ι_π_self]
    · rw [if_neg h, scalarEnd_zero, biproduct.ι_π_ne _ (Ne.symm h)]
  rw [hmat, Category.id_comp, Iso.symm_hom, Iso.inv_hom_id]

/-- An invertible `d × d` matrix of global sections induces an automorphism of the free
rank-`d` sheaf `O_S^d`. Project-local — the `GL_d` data underlying the bundle transitions. -/
noncomputable def matrixToFreeIso {S : Scheme.{0}} {d : ℕ}
    (M N : Matrix (Fin d) (Fin d) Γ(S, ⊤)) (hMN : M * N = 1) (hNM : N * M = 1) :
    SheafOfModules.free (R := S.ringCatSheaf) (Fin d) ≅
      SheafOfModules.free (R := S.ringCatSheaf) (Fin d) where
  hom := matrixEnd M
  inv := matrixEnd N
  hom_inv_id := by rw [matrixEnd_comp, hNM, matrixEnd_one]
  inv_hom_id := by rw [matrixEnd_comp, hMN, matrixEnd_one]

@[simp] lemma matrixToFreeIso_hom {S : Scheme.{0}} {d : ℕ}
    (M N : Matrix (Fin d) (Fin d) Γ(S, ⊤)) (hMN : M * N = 1) (hNM : N * M = 1) :
    (matrixToFreeIso M N hMN hNM).hom = matrixEnd M := rfl

/-- **Matrix automorphisms compose multiplicatively** (`lem:gr_matrixToFreeIso_mul`): the
forward maps of two matrix automorphisms compose to `matrixEnd` of the matrix product (with
the order reversed by the column/component contravariance). This is the linkage that turns
the matrix-level Cramer-inverse cocycle into a composition identity of sheaf-of-module
isomorphisms. Project-local. -/
lemma matrixToFreeIso_mul {S : Scheme.{0}} {d : ℕ}
    (A A' B B' : Matrix (Fin d) (Fin d) Γ(S, ⊤))
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) (hBB' : B * B' = 1) (hB'B : B' * B = 1) :
    (matrixToFreeIso A A' hAA' hA'A).hom ≫ (matrixToFreeIso B B' hBB' hB'B).hom
      = matrixEnd (B * A) := by
  rw [matrixToFreeIso_hom, matrixToFreeIso_hom, matrixEnd_comp]

@[simp] lemma matrixToFreeIso_inv {S : Scheme.{0}} {d : ℕ}
    (M N : Matrix (Fin d) (Fin d) Γ(S, ⊤)) (hMN : M * N = 1) (hNM : N * M = 1) :
    (matrixToFreeIso M N hMN hNM).inv = matrixEnd N := rfl

/-! ## The rectangular matrix homomorphism of free sheaves

The chart quotient `u^I` is "left multiplication by the `d × r` universal matrix `X^I`";
to manipulate it under pullback and against the square `GL_d` transitions we generalise
the square `matrixEnd` API to rectangular matrices (`def:gr_matrixEndRect`,
`lem:gr_matrixEndRect_comp`; the pullback naturality `lem:gr_matrixEndRect_pullback` comes
after the scalar atom below). -/

/-- A `d × r` matrix of global sections of `O_S` realised as a morphism of free sheaves
`O_S^r ⟶ O_S^d` (`def:gr_matrixEndRect`): the `(p,q)`-entry acts as `scalarEnd`, assembled
over the two biproducts exactly as the square `matrixEnd` and the chart quotient
`chartQuotientMap` (which is by construction `matrixEndRect` of the injected universal
matrix). Project-local. -/
noncomputable def matrixEndRect {S : Scheme.{0}} {d r : ℕ}
    (M : Matrix (Fin d) (Fin r) Γ(S, ⊤)) :
    SheafOfModules.free (R := S.ringCatSheaf) (Fin r) ⟶
      SheafOfModules.free (R := S.ringCatSheaf) (Fin d) :=
  (biproduct.isoCoproduct (fun _ : Fin r => SheafOfModules.unit S.ringCatSheaf)).symm.hom ≫
    biproduct.matrix (fun i p => scalarEnd (M p i)) ≫
    (biproduct.isoCoproduct (fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf)).hom

/-- Composition of two `biproduct.matrix` morphisms with a rectangular first factor —
the categorical matrix product. Project-local helper for `matrixEndRect_comp`. -/
private lemma biproduct_matrix_comp_rect {S : Scheme.{0}} {d r : ℕ}
    (mM : Fin r → Fin d →
      (SheafOfModules.unit S.ringCatSheaf ⟶ SheafOfModules.unit S.ringCatSheaf))
    (mN : Fin d → Fin d →
      (SheafOfModules.unit S.ringCatSheaf ⟶ SheafOfModules.unit S.ringCatSheaf)) :
    biproduct.matrix (f := fun _ : Fin r => SheafOfModules.unit S.ringCatSheaf)
        (g := fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf) mM ≫ biproduct.matrix mN
      = biproduct.matrix (fun i q => ∑ p, mM i p ≫ mN p q) := by
  refine biproduct.hom_ext' _ _ (fun i => biproduct.hom_ext _ _ (fun q => ?_))
  simp only [Category.assoc, biproduct.ι_matrix_assoc, biproduct.matrix_π, biproduct.lift_desc,
    biproduct.ι_matrix, biproduct.lift_π]

/-- **Square-after-rectangular composition law** (`lem:gr_matrixEndRect_comp`):
`matrixEndRect M ≫ matrixEnd N = matrixEndRect (N * M)` for `M : d × r`, `N : d × d` —
the matrix product, with the order reversed by the contravariance of the column/component
indexing exactly as in `matrixEnd_comp`. Project-local. -/
@[reassoc]
lemma matrixEndRect_comp {S : Scheme.{0}} {d r : ℕ}
    (M : Matrix (Fin d) (Fin r) Γ(S, ⊤)) (N : Matrix (Fin d) (Fin d) Γ(S, ⊤)) :
    matrixEndRect M ≫ matrixEnd N = matrixEndRect (N * M) := by
  rw [matrixEndRect, matrixEnd, matrixEndRect]
  have hcomp : biproduct.matrix (fun (i : Fin r) (p : Fin d) => scalarEnd (M p i))
        ≫ biproduct.matrix (fun (i : Fin d) (p : Fin d) => scalarEnd (N p i))
      = biproduct.matrix (fun (i : Fin r) (p : Fin d) => scalarEnd ((N * M) p i)) := by
    rw [biproduct_matrix_comp_rect]
    congr 1
    funext i q
    simp_rw [scalarEnd_comp]
    rw [← scalarEnd_sum, Matrix.mul_apply]
    exact congrArg scalarEnd (Finset.sum_congr rfl (fun p _ => mul_comm _ _))
  simp only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (biproduct.matrix (fun (i : Fin r) (p : Fin d) => scalarEnd (M p i))),
    hcomp]

/-! ## The tautological quotient on the charts -/

/-- The **chart quotient** `u^I : O_{U^I}^r → O_{U^I}^d` (`def:gr_chart_quotient`):
left multiplication by the universal matrix `X^I` (`universalMatrix`). It is realised as
the morphism of free sheaves of modules whose matrix of components, in the standard bases
`(e_{i'})_{i' : Fin r}` and `(e_p)_{p : Fin d}`, is the universal matrix `X^I` injected
into the structure sheaf via `Scheme.ΓSpecIso`. Since the `I`-minor of `X^I` is the
identity, `u^I` is a split surjection onto the free rank-`d` sheaf.

Project-local: Mathlib has no "matrix ↦ morphism of free sheaves" primitive. -/
noncomputable def chartQuotientMap (d r : ℕ) (I : Finset (Fin r)) (hI : I.card = d) :
    SheafOfModules.free (R := (affineChart d r I).ringCatSheaf) (Fin r) ⟶
      SheafOfModules.free (R := (affineChart d r I).ringCatSheaf) (Fin d) :=
  let A := CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ)
  let R := (affineChart d r I).ringCatSheaf
  haveI : HasFiniteBiproducts (SheafOfModules R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let M : ∀ (_ : Fin r) (_ : Fin d), SheafOfModules.unit R ⟶ SheafOfModules.unit R :=
    fun i' p => scalarEnd ((Scheme.ΓSpecIso A).inv.hom ((universalMatrix d r I hI) p i'))
  (biproduct.isoCoproduct (fun _ : Fin r => SheafOfModules.unit R)).symm.hom ≫
    biproduct.matrix M ≫
    (biproduct.isoCoproduct (fun _ : Fin d => SheafOfModules.unit R)).hom

/-- The chart quotient `u^I` sends the `(I.orderIsoOfFin k)`-th basis section of
`O_{U^I}^r` to the `k`-th basis section of `O_{U^I}^d`. Project-local: the column-`I`
restriction of `u^I` is the identity, the matrix-level content of `lem:gr_chartQuotientMap_epi`. -/
private lemma chartQuotientMap_ιFree (d r : ℕ) (I : Finset (Fin r)) (hI : I.card = d)
    (k : Fin d) :
    SheafOfModules.ιFree (R := (affineChart d r I).ringCatSheaf)
        ((I.orderIsoOfFin hI k : Fin r)) ≫ chartQuotientMap d r I hI
      = SheafOfModules.ιFree k := by
  set A := CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ) with hA
  set S := AlgebraicGeometry.Spec A with hS
  haveI : HasFiniteBiproducts (SheafOfModules S.ringCatSheaf) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  change SheafOfModules.ιFree (↑((I.orderIsoOfFin hI) k)) ≫
      ((biproduct.isoCoproduct
            (fun _ : Fin r => SheafOfModules.unit S.ringCatSheaf)).symm.hom ≫
        biproduct.matrix (fun (i' : Fin r) (p : Fin d) => scalarEnd
          ((Scheme.ΓSpecIso A).inv.hom (universalMatrix d r I hI p i'))) ≫
        (biproduct.isoCoproduct
            (fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf)).hom)
      = SheafOfModules.ιFree k
  rw [Iso.symm_hom, SheafOfModules.ιFree, biproduct.isoCoproduct_inv]
  erw [Sigma.ι_desc_assoc]
  rw [biproduct.ι_matrix_assoc, biproduct.isoCoproduct_hom]
  have h1 : (CommRingCat.Hom.hom (Scheme.ΓSpecIso A).inv) (1 : A) = 1 := map_one _
  have h0 : (CommRingCat.Hom.hom (Scheme.ΓSpecIso A).inv) (0 : A) = 0 := map_zero _
  have hsub := universalMatrix_submatrix_self d r I hI
  have lift_eq :
      (biproduct.lift fun p : Fin d => scalarEnd
          ((Scheme.ΓSpecIso A).inv.hom (universalMatrix d r I hI p (↑((I.orderIsoOfFin hI) k)))))
        = biproduct.ι (fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf) k := by
    refine biproduct.hom_ext _ _ (fun p => ?_)
    rw [biproduct.lift_π]
    have hentry : universalMatrix d r I hI p (↑((I.orderIsoOfFin hI) k))
        = (1 : Matrix (Fin d) (Fin d) A) p k :=
      congrFun (congrFun hsub p) k
    rw [hentry, Matrix.one_apply]
    by_cases hpk : p = k
    · rw [if_pos hpk, h1, scalarEnd_one, hpk, biproduct.ι_π_self]
    · rw [if_neg hpk, h0, scalarEnd_zero, biproduct.ι_π_ne _ (Ne.symm hpk)]
  rw [lift_eq, biproduct.ι_desc]
  rfl

/-- **The chart quotient is an epimorphism** (`lem:gr_chartQuotientMap_epi`): `u^I` is split
by the coordinate inclusion `s_I` of the `I`-indexed columns, hence is a (split) epimorphism
of sheaves of modules. -/
lemma chartQuotientMap_epi (d r : ℕ) (I : Finset (Fin r)) (hI : I.card = d) :
    Epi (chartQuotientMap d r I hI) := by
  have hsplit : SheafOfModules.freeMap (R := (affineChart d r I).ringCatSheaf)
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫ chartQuotientMap d r I hI
      = 𝟙 (SheafOfModules.free (R := (affineChart d r I).ringCatSheaf) (Fin d)) := by
    refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (Fin d)) _ _ (fun k => ?_)
    have key : SheafOfModules.ιFree (R := (affineChart d r I).ringCatSheaf) k ≫
          (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
            chartQuotientMap d r I hI)
        = SheafOfModules.ιFree k :=
      (SheafOfModules.ιFree_freeMap_assoc (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) k
        (chartQuotientMap d r I hI)).trans (chartQuotientMap_ιFree d r I hI k)
    exact key.trans (Category.comp_id _).symm
  exact (IsSplitEpi.mk' ⟨_, hsplit⟩).epi

end AlgebraicGeometry.Grassmannian

namespace AlgebraicGeometry.Grassmannian

/-! ## The GL_d bundle transition cocycle

The universal quotient `U` is glued from the per-chart free rank-`d` sheaves `O_{U^I}^d`
along the bundle transitions `g_{I,J} = (X^I_J)⁻¹`, realised as matrix automorphisms via
`matrixToFreeIso` and conjugated to the overlap pullbacks by `pullbackFreeIso`. This section
constructs `bundleTransition` and proves its self-identity (C1); the triple-overlap
multiplicativity (C2) is the matrix cocycle of `lem:gr_cocycle` transported to the common
overlap by `pullbackBaseChangeTransport`/`glueData_bridge_*`. -/

/-- The Cramer inverse of the self-minor `X^I_I` is the identity: since `X^I_I = 1`
(`universalMatrix_submatrix_self`) its inverse is `1`. Project-local; underlies C1. -/
lemma universalMinorInv_self (d r : ℕ) (I : Finset (Fin r)) (hI : I.card = d) :
    universalMinorInv d r I I hI hI = 1 := by
  have hmin : universalMinor d r I I hI hI = 1 := by
    rw [universalMinor, universalMatrix_submatrix_self, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [universalMinorInv, hmin, inv_one]

/-- The injected Cramer inverse and minor matrices over the overlap structure sheaf are
mutually inverse — the `GL_d` invertibility hypotheses for `matrixToFreeIso`. Project-local. -/
private lemma bundleMatrix_cancel (d r : ℕ) (I J : Finset (Fin r)) (hI : I.card = d)
    (hJ : J.card = d) :
    ((Scheme.ΓSpecIso
        (CommRingCat.of (Localization.Away (minorDet d r I J hI hJ)))).inv.hom.mapMatrix
        (universalMinorInv d r I J hI hJ)) *
      ((Scheme.ΓSpecIso
        (CommRingCat.of (Localization.Away (minorDet d r I J hI hJ)))).inv.hom.mapMatrix
        (universalMinor d r I J hI hJ)) = 1 ∧
    ((Scheme.ΓSpecIso
        (CommRingCat.of (Localization.Away (minorDet d r I J hI hJ)))).inv.hom.mapMatrix
        (universalMinor d r I J hI hJ)) *
      ((Scheme.ΓSpecIso
        (CommRingCat.of (Localization.Away (minorDet d r I J hI hJ)))).inv.hom.mapMatrix
        (universalMinorInv d r I J hI hJ)) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [← map_mul, (universalMinorInv_mul_cancel d r I J hI hJ).1, map_one]
  · rw [← map_mul, (universalMinorInv_mul_cancel d r I J hI hJ).2, map_one]

/-- The **bundle transition** `g_{I,J}` (`def:gr_bundleTransition`): the isomorphism of
sheaves of modules on the overlap `U^I_J` induced by the invertible matrix
`(X^I_J)⁻¹ = universalMinorInv d r I J`. It identifies the pullback of `O_{U^I}^d` along
`f_{IJ}` with the pullback of `O_{U^J}^d` along `t_{IJ} ≫ f_{JI}`, by conjugating the
matrix automorphism `matrixToFreeIso (X^I_J)⁻¹` (built like `chartQuotientMap`) by the
free-pullback comparisons `pullbackFreeIso`. -/
noncomputable def bundleTransition (d r : ℕ) (I J : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) :
    (Scheme.Modules.pullback (chartIncl d r I J hI hJ)).obj
        (SheafOfModules.free (R := (affineChart d r I).ringCatSheaf) (Fin d)) ≅
      (Scheme.Modules.pullback (chartTransition d r I J hI hJ ≫ chartIncl d r J I hJ hI)).obj
        (SheafOfModules.free (R := (affineChart d r J).ringCatSheaf) (Fin d)) :=
  Scheme.Modules.pullbackFreeIso (chartIncl d r I J hI hJ) (Fin d) ≪≫
    matrixToFreeIso
      ((Scheme.ΓSpecIso
          (CommRingCat.of (Localization.Away (minorDet d r I J hI hJ)))).inv.hom.mapMatrix
        (universalMinorInv d r I J hI hJ))
      ((Scheme.ΓSpecIso
          (CommRingCat.of (Localization.Away (minorDet d r I J hI hJ)))).inv.hom.mapMatrix
        (universalMinor d r I J hI hJ))
      (bundleMatrix_cancel d r I J hI hJ).1
      (bundleMatrix_cancel d r I J hI hJ).2 ≪≫
    (Scheme.Modules.pullbackFreeIso
      (chartTransition d r I J hI hJ ≫ chartIncl d r J I hJ hI) (Fin d)).symm

/-- **Self-identity of the bundle transition (C1)** (`lem:gr_bundleCocycle_id`): on the
diagonal overlap `U^I_I` (where `t_{II} = 𝟙`) the bundle transition is the identity, in the
form required by the gluing primitive `Scheme.Modules.glue`. The matrix part is the identity
since `(X^I_I)⁻¹ = 1` (`universalMinorInv_self`), so `matrixEnd 1 = 𝟙` (`matrixEnd_one`); the
two free-pullback comparisons then cancel into the `eqToIso` transport.

Resource note (iter-060): the former `set_option maxHeartbeats 1000000 in` override is
removed and the proof rebuilt as a *leaner term* that the kernel checks within the default
budget (the earlier `.hom`-level cast chain hit a `(kernel) deterministic timeout` at default
heartbeats and an OOM ceiling on cold builds at `1000000`). The new term works at the **iso
level**: the matrix automorphism is collapsed to `Iso.refl` in the lightweight single-overlap
context (`hB`, free sheaves only — no pullback), and the two free-pullback comparisons cancel
through the *generic* lemma `pullbackFreeIso_trans_symm_eqToIso` (proved by `subst` on
variable morphisms), so the kernel never whnfs the concrete immersions `chartIncl` /
`chartTransition`. -/
theorem bundleTransition_self (d r : ℕ) (I : Finset (Fin r)) (hI : I.card = d) :
    bundleTransition d r I I hI hI
      = eqToIso (congrArg
          (fun φ => (Scheme.Modules.pullback φ).obj
            (SheafOfModules.free (R := (affineChart d r I).ringCatSheaf) (Fin d)))
          (show chartIncl d r I I hI hI
              = chartTransition d r I I hI hI ≫ chartIncl d r I I hI hI from by
            rw [chartTransition_self, Category.id_comp])) := by
  have hφ : chartIncl d r I I hI hI
      = chartTransition d r I I hI hI ≫ chartIncl d r I I hI hI := by
    rw [chartTransition_self, Category.id_comp]
  -- The matrix automorphism is the identity iso: `(X^I_I)⁻¹` injects to the identity matrix,
  -- so its `matrixEnd` is `𝟙`. Proved here over the single overlap chart (no pullback types).
  have hB : matrixToFreeIso
        ((Scheme.ΓSpecIso
            (CommRingCat.of (Localization.Away (minorDet d r I I hI hI)))).inv.hom.mapMatrix
          (universalMinorInv d r I I hI hI))
        ((Scheme.ΓSpecIso
            (CommRingCat.of (Localization.Away (minorDet d r I I hI hI)))).inv.hom.mapMatrix
          (universalMinor d r I I hI hI))
        (bundleMatrix_cancel d r I I hI hI).1
        (bundleMatrix_cancel d r I I hI hI).2
      = Iso.refl _ := by
    apply Iso.ext
    rw [matrixToFreeIso_hom, Iso.refl_hom, universalMinorInv_self, map_one, matrixEnd_one]
  -- Unfold the transition, collapse the identity matrix factor (`erw` to bridge the
  -- `chartOverlap`/`Spec` defeq on the inferred base scheme), and cancel the comparisons.
  simp only [bundleTransition]
  erw [hB, Iso.refl_trans]
  exact Scheme.Modules.pullbackFreeIso_trans_symm_eqToIso hφ (Fin d)

/-- The bundle transition data packaged over the Grassmannian glue datum, ready to feed the
gluing primitive `Scheme.Modules.glue`. Project-local. -/
noncomputable def bundleTransitionData (d r : ℕ) :
    ∀ (I J : (theGlueData d r).J),
      (Scheme.Modules.pullback ((theGlueData d r).f I J)).obj
          (SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d)) ≅
        (Scheme.Modules.pullback ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).obj
          (SheafOfModules.free (R := ((theGlueData d r).U J).ringCatSheaf) (Fin d)) :=
  fun I J => bundleTransition d r I.1 J.1 I.2 J.2

/-! ### The matrix-level Cramer-inverse cocycle (L1)

The matrix-algebra core of (C2) is the Cramer-inverse cocycle
`(X^J_K)⁻¹ (X^I_J)⁻¹ = (X^I_K)⁻¹` over the triple-overlap ring `S_I = R^I[1/(P^I_J P^I_K)]`.
Its proof reduces to the image-matrix cocycle `cocycle_imageMatrix_eq` of
`GrassmannianCells` by taking the `I`-minor. That lemma and the matrix helpers it depends on
are `private` in `GrassmannianCells.lean`, so they are reproduced here as project-local
helpers (the proofs are verbatim ports of the known-good originals). -/

/-- Port of `GrassmannianCells.mul_submatrix_col` (private there). -/
private lemma mul_submatrix_col' {d r : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin d) (Fin d) R) (B : Matrix (Fin d) (Fin r) R) (g : Fin d → Fin r) :
    (A * B).submatrix id g = A * B.submatrix id g := by
  ext i j; simp [Matrix.mul_apply, Matrix.submatrix_apply]

/-- Port of `GrassmannianCells.map_nonsing_inv` (private there). -/
private lemma map_nonsing_inv' {n : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (h : IsUnit A.det) :
    (A.map f)⁻¹ = A⁻¹.map f := by
  have hmul : (A.map f) * (A⁻¹.map f) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A h, Matrix.map_one f (map_zero f) (map_one f)]
  exact Matrix.inv_eq_right_inv hmul

/-- Port of `GrassmannianCells.map_map_eq_of_comp` (private there). -/
private lemma map_map_eq_of_comp' {m n : ℕ} {R A D : Type*}
    [CommRing R] [CommRing A] [CommRing D]
    (M : Matrix (Fin m) (Fin n) R) (f : R →+* A) (g : A →+* D) (h : R →+* D)
    (hcomp : g.comp f = h) : (M.map f).map g = M.map h := by
  rw [Matrix.map_map, ← RingHom.coe_comp, hcomp]

/-- Port of `GrassmannianCells.isUnit_algebraMap_away_left` (private there). -/
private lemma isUnit_algebraMap_away_left' {R : Type*} [CommRing R] (x y : R) :
    IsUnit (algebraMap R (Localization.Away (x * y)) x) := by
  have h : IsUnit (algebraMap R (Localization.Away (x * y)) (x * y)) :=
    IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_left h

/-- Port of `GrassmannianCells.inv_mul_inv_mul_cancel` (private there). -/
private lemma inv_mul_inv_mul_cancel' {d e : ℕ} {R : Type*} [CommRing R]
    (A B : Matrix (Fin d) (Fin d) R) (M : Matrix (Fin d) (Fin e) R) (hA : IsUnit A.det) :
    (B⁻¹ * A) * (A⁻¹ * M) = B⁻¹ * M := by
  rw [Matrix.mul_assoc B⁻¹ A (A⁻¹ * M), ← Matrix.mul_assoc A A⁻¹ M,
    Matrix.mul_nonsing_inv A hA, Matrix.one_mul]

/-- Port of `GrassmannianCells.imageMatrix_map_eq` (private there). -/
private lemma imageMatrix_map_eq' (d r : ℕ) (I X : Finset (Fin r)) (hI : I.card = d)
    (hX : X.card = d) {D : Type*} [CommRing D]
    [Algebra (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ) D]
    (incl : Localization.Away (minorDet d r I X hI hX) →+* D)
    (hincl : incl.comp (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ)
        (Localization.Away (minorDet d r I X hI hX)))
        = algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ) D) :
    (imageMatrix d r I X hI hX).map incl
      = (((universalMatrix d r I hI).map
            (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ) D)).submatrix id
          (fun j : Fin d => (X.orderIsoOfFin hX j : Fin r)))⁻¹ *
        (universalMatrix d r I hI).map
          (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ) D) := by
  have hmm : (imageMatrix d r I X hI hX).map incl
      = (universalMinorInv d r I X hI hX).map incl
        * ((universalMatrix d r I hI).map
            (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ)
              (Localization.Away (minorDet d r I X hI hX)))).map incl := by
    rw [imageMatrix]; exact Matrix.map_mul
  rw [hmm, map_map_eq_of_comp' _ _ _ _ hincl, universalMinorInv,
    ← map_nonsing_inv' incl (universalMinor d r I X hI hX)
        (isUnit_det_universalMinor d r I X hI hX)]
  congr 1
  rw [universalMinor, map_map_eq_of_comp' _ _ _ _ hincl, ← Matrix.submatrix_map]

/-- Port of `GrassmannianCells.cocycle_imageMatrix_eq` (private there): over the triple
overlap `S_I`, the image matrix `(X^I_K)⁻¹ X^I` of `θ_{I,K}` equals `θ_{I,J}` applied
entrywise to the image matrix `(X^J_K)⁻¹ X^J` of `θ_{J,K}`. -/
private lemma cocycle_imageMatrix_eq' (d r : ℕ) (I J K : Finset (Fin r)) (hI : I.card = d)
    (hJ : J.card = d) (hK : K.card = d) :
    (imageMatrix d r I K hI hK).map
        (awayInclRight (minorDet d r I J hI hJ) (minorDet d r I K hI hK))
      = (imageMatrix d r J K hJ hK).map
          ((cocycleΘIJ d r I J K hI hJ hK).comp
            (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK))) := by
  have hLHS := imageMatrix_map_eq' d r I K hI hK
    (awayInclRight (minorDet d r I J hI hJ) (minorDet d r I K hI hK))
    (awayInclRight_comp_algebraMap _ _)
  have hMJimg := imageMatrix_map_eq' d r I J hI hJ
    (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK))
    (awayInclLeft_comp_algebraMap _ _)
  set Y := (universalMatrix d r I hI).map
      (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ)
        (Localization.Away (minorDet d r I J hI hJ * minorDet d r I K hI hK))) with hY
  have hYJ : IsUnit (Y.submatrix id (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r))).det := by
    have e : (Y.submatrix id (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r))).det
        = algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ)
            (Localization.Away (minorDet d r I J hI hJ * minorDet d r I K hI hK))
            (minorDet d r I J hI hJ) := by
      rw [hY, Matrix.submatrix_map]
      exact (RingHom.map_det _ _).symm
    rw [e]; exact isUnit_algebraMap_away_left' _ _
  have hχ : ((cocycleΘIJ d r I J K hI hJ hK).comp
        (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK))).comp
          (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ J}) ℤ)
            (Localization.Away (minorDet d r J K hJ hK)))
      = (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).comp
          (transitionPreMap d r I J hI hJ).toRingHom := by
    rw [RingHom.comp_assoc, awayInclRight_comp_algebraMap, cocycleΘIJ]
    exact IsLocalization.Away.lift_comp _ _
  have hMJ : (universalMatrix d r J hJ).map
        ((awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).comp
          (transitionPreMap d r I J hI hJ).toRingHom)
      = (Y.submatrix id (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r)))⁻¹ * Y := by
    have e1 : (universalMatrix d r J hJ).map
          ((awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).comp
            (transitionPreMap d r I J hI hJ).toRingHom)
        = (imageMatrix d r I J hI hJ).map
            (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)) := by
      rw [← map_map_eq_of_comp' (universalMatrix d r J hJ)
          (transitionPreMap d r I J hI hJ).toRingHom
          (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)) _ rfl]
      congr 1
      exact universalMatrix_map_transitionPreMap d r I J hI hJ
    rw [e1, hMJimg]
  have hRHS : (imageMatrix d r J K hJ hK).map
        ((cocycleΘIJ d r I J K hI hJ hK).comp
          (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK)))
      = (Y.submatrix id (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r)))⁻¹ * Y := by
    have hmm : (imageMatrix d r J K hJ hK).map
          ((cocycleΘIJ d r I J K hI hJ hK).comp
            (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK)))
        = (universalMinorInv d r J K hJ hK).map
            ((cocycleΘIJ d r I J K hI hJ hK).comp
              (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK)))
          * ((universalMatrix d r J hJ).map
              (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ J}) ℤ)
                (Localization.Away (minorDet d r J K hJ hK)))).map
                  ((cocycleΘIJ d r I J K hI hJ hK).comp
                    (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK))) := by
      rw [imageMatrix]; exact Matrix.map_mul
    rw [hmm, map_map_eq_of_comp' _ _ _ _ hχ, hMJ, universalMinorInv,
      ← map_nonsing_inv' _ _ (isUnit_det_universalMinor d r J K hJ hK), universalMinor,
      map_map_eq_of_comp' _ _ _ _ hχ, ← Matrix.submatrix_map, hMJ,
      mul_submatrix_col' (Y.submatrix id (fun j : Fin d => (J.orderIsoOfFin hJ j : Fin r)))⁻¹ Y
        (fun j : Fin d => (K.orderIsoOfFin hK j : Fin r)),
      Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hYJ,
      inv_mul_inv_mul_cancel' _ _ _ hYJ]
  rw [hLHS, hRHS]

/-- **Cramer-inverse cocycle on the triple overlap (L1)** (`lem:gr_bundleCocycle_matrix`):
over the triple-overlap ring `S_I = R^I[1/(P^I_J P^I_K)]` the base-changed Cramer inverses of
the localised minors satisfy the multiplicative cocycle identity
`(X^J_K)⁻¹ (X^I_J)⁻¹ = (X^I_K)⁻¹`. This is the pure matrix-algebra core of (C2), independent
of any sheaf data. Project-local. -/
theorem bundleTransition_cocycle_matrix (d r : ℕ) (I J K : Finset (Fin r))
    (hI : I.card = d) (hJ : J.card = d) (hK : K.card = d) :
    (universalMinorInv d r J K hJ hK).map
        ((cocycleΘIJ d r I J K hI hJ hK).comp
          (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK)))
      * (universalMinorInv d r I J hI hJ).map
          (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK))
      = (universalMinorInv d r I K hI hK).map
          (awayInclRight (minorDet d r I J hI hJ) (minorDet d r I K hI hK)) := by
  -- Take the `I`-minor (columns indexed by `I`) of the image-matrix cocycle.
  have hcol := congrArg
    (fun M : Matrix (Fin d) (Fin r) (Localization.Away
        (minorDet d r I J hI hJ * minorDet d r I K hI hK)) =>
      M.submatrix id (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)))
    (cocycle_imageMatrix_eq' d r I J K hI hJ hK)
  -- LHS of `hcol` is `(X^I_K)⁻¹` over `S_I`.
  rw [Matrix.submatrix_map, imageMatrix_submatrix_I] at hcol
  -- RHS of `hcol`: push the `I`-minor through the outer map.
  rw [Matrix.submatrix_map] at hcol
  -- `imageMatrix J K = (X^J_K)⁻¹ * X^J`, so its `I`-minor splits off the inverse factor;
  -- the second factor is `X^J` (over `R^J[1/P^J_K]`) restricted to the `I`-columns.
  have hsplit : (imageMatrix d r J K hJ hK).submatrix id
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))
      = universalMinorInv d r J K hJ hK *
        ((universalMatrix d r J hJ).map
          (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ J}) ℤ)
            (Localization.Away (minorDet d r J K hJ hK)))).submatrix id
          (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) := by
    rw [imageMatrix]; exact mul_submatrix_col' _ _ _
  rw [hsplit, Matrix.map_mul] at hcol
  -- The comp identity `θ_{I,J}` realises the cross-localisation map on `R^J`.
  have hχ : ((cocycleΘIJ d r I J K hI hJ hK).comp
        (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK))).comp
          (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ J}) ℤ)
            (Localization.Away (minorDet d r J K hJ hK)))
      = (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).comp
          (transitionPreMap d r I J hI hJ).toRingHom := by
    rw [RingHom.comp_assoc, awayInclRight_comp_algebraMap, cocycleΘIJ]
    exact IsLocalization.Away.lift_comp _ _
  have e1 : (universalMatrix d r J hJ).map
        ((awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).comp
          (transitionPreMap d r I J hI hJ).toRingHom)
      = (imageMatrix d r I J hI hJ).map
          (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)) := by
    rw [← map_map_eq_of_comp' (universalMatrix d r J hJ)
        (transitionPreMap d r I J hI hJ).toRingHom
        (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)) _ rfl]
    congr 1
    exact universalMatrix_map_transitionPreMap d r I J hI hJ
  -- The base change of `X^J|_I` over `θ_{I,J}` is `(X^I_J)⁻¹` over `S_I`.
  have hXJI : (((universalMatrix d r J hJ).map
          (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ J}) ℤ)
            (Localization.Away (minorDet d r J K hJ hK)))).submatrix id
          (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))).map
          ((cocycleΘIJ d r I J K hI hJ hK).comp
            (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK)))
      = (universalMinorInv d r I J hI hJ).map
          (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)) := by
    rw [Matrix.submatrix_map, map_map_eq_of_comp' _ _ _ _ hχ, ← Matrix.submatrix_map, e1,
      Matrix.submatrix_map, imageMatrix_submatrix_I]
  rw [hXJI] at hcol
  exact hcol.symm

/-! ### L3 transport: `scalarEnd`/`matrixEnd` naturality under pullback

The substantive new infrastructure for (C2). The atom is `scalarEnd_pullback`: pulling back a
scalar endomorphism `scalarEnd a` along a scheme morphism `p` is, after the unit-pullback
comparison `pullbackObjUnitToUnit`, the scalar endomorphism of the base-changed function
`p.appTop a`. Its proof transposes the naturality square under the pullback-pushforward
adjunction to a `unit`-level identity, which holds by naturality of the comorphism `p.c`. -/

/-- The reduced (transposed) form of the scalar-naturality atom: on the unit sheaf,
multiplication by `a` followed by the comorphism `unitToPushforwardObjUnit` equals the
comorphism followed by the pushforward of multiplication by `p.appTop a`. Project-local
helper for `scalarEnd_pullback`. -/
lemma unitToPushforward_scalarEnd_comm {T S : Scheme.{0}} (p : T ⟶ S) (a : Γ(S, ⊤)) :
    scalarEnd a ≫ SheafOfModules.unitToPushforwardObjUnit (Scheme.Hom.toRingCatSheafHom p)
      = SheafOfModules.unitToPushforwardObjUnit (Scheme.Hom.toRingCatSheafHom p) ≫
        (Scheme.Modules.pushforward p).map (scalarEnd (p.appTop a)) := by
  apply ((Scheme.Modules.pushforward p).obj
    (SheafOfModules.unit T.ringCatSheaf)).unitHomEquiv.injective
  refine PresheafOfModules.sections_ext _ _ (fun Y => ?_)
  -- Both `.val Y` are nested applications (no morphism composite) up to defeq, since
  -- `unitHomEquiv (f ≫ p) = sectionsMap p (unitHomEquiv f)` and `sectionsMap`/`unitHomEquiv`
  -- are `rfl`/`sectionsMk`-defined; rewrite into that form via `change`.
  change (SheafOfModules.unitToPushforwardObjUnit (Scheme.Hom.toRingCatSheafHom p)).val.app Y
        ((scalarEnd a).val.app Y (1 : S.ringCatSheaf.obj.obj Y))
      = ((Scheme.Modules.pushforward p).map
            (scalarEnd ((Scheme.Hom.appTop p) a))).val.app Y
        ((SheafOfModules.unitToPushforwardObjUnit (Scheme.Hom.toRingCatSheafHom p)).val.app Y
          (1 : S.ringCatSheaf.obj.obj Y))
  rw [scalarEnd_val_app_one, SheafOfModules.unitToPushforwardObjUnit_val_app_apply,
    SheafOfModules.unitToPushforwardObjUnit_val_app_apply, map_one]
  -- Goal: `φ.hom.app Y (a|_Y) = ((pushforward p).map (scalarEnd (p.appTop a))).val.app Y 1`.
  -- RHS reduces (defeq, the pushforward's `map`-application is `rfl` + `scalarEnd_val_app_one`)
  -- to `T.ringCatSheaf.obj.map (homOfLE le_top).op (p.appTop a)`; LHS rewrites to the same by
  -- naturality of the comorphism `(toRingCatSheafHom p).hom` at `(homOfLE le_top).op : op ⊤ ⟶ Y`.
  have hnat := ConcreteCategory.congr_hom
    ((Scheme.Hom.toRingCatSheafHom p).hom.naturality (homOfLE (le_top : Y.unop ≤ ⊤)).op) a
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at hnat
  rw [hnat]
  -- The RHS pushforward (its `map`-application is `rfl` on sections) evaluates the
  -- scalar endomorphism `scalarEnd (p.appTop a)` at `1` over the preimage open; both sides are
  -- then `T.ringCatSheaf.obj.map (homOfLE le_top).op (p.appTop a)` (the `homOfLE`s agree by
  -- proof irrelevance, the comorphism by `forget₂`-on-elements), so `scalarEnd_val_app_one` closes.
  exact (scalarEnd_val_app_one ((Scheme.Hom.appTop p) a)
    (Opposite.op ((TopologicalSpace.Opens.map p.base).obj (Opposite.unop Y)))).symm

/-- **ATOM: scalar endomorphism naturality under pullback** (`lem:gr_scalarEnd_pullback`).
For `p : T ⟶ S` and `a ∈ Γ(S,⊤)`, pulling back the scalar endomorphism `scalarEnd a` is,
after the unit-pullback comparison `q = pullbackObjUnitToUnit`, the scalar endomorphism of the
base-changed function `p.appTop a`:
`(pullback p).map (scalarEnd a) ≫ q = q ≫ scalarEnd (p.appTop a)`.
Proved by transposing under the pullback-pushforward adjunction to
`unitToPushforward_scalarEnd_comm`.
Project-local — the single irreducible new claim underlying `matrixEnd_pullback`. -/
lemma scalarEnd_pullback {T S : Scheme.{0}} (p : T ⟶ S) (a : Γ(S, ⊤)) :
    (Scheme.Modules.pullback p).map (scalarEnd a) ≫
        SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p)
      = SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p) ≫
        scalarEnd (p.appTop a) := by
  apply (Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv
    (SheafOfModules.unit S.ringCatSheaf) (SheafOfModules.unit T.ringCatSheaf) |>.injective
  -- `homEquiv_naturality_left` collapses the LHS transpose; the RHS transpose
  -- (`homEquiv_naturality_right`) is supplied as a term because positional `rw` cannot match
  -- the identical-printing `homEquiv` under the `X.Modules` diamond (memory
  -- `grquot-functor-dropped-termmode`).
  -- `hq` is the lemma `..._homEquiv_pullbackObjUnitToUnit` restated in the `Scheme.Modules`
  -- adjunction form (defeq to the `SheafOfModules` form), so `rw`/`congrArg` match syntactically.
  have hq : (Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv
        (SheafOfModules.unit S.ringCatSheaf) (SheafOfModules.unit T.ringCatSheaf)
        (SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p))
      = SheafOfModules.unitToPushforwardObjUnit (Scheme.Hom.toRingCatSheafHom p) :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  rw [Adjunction.homEquiv_naturality_left, hq]
  refine (unitToPushforward_scalarEnd_comm p a).trans ?_
  exact (((Scheme.Modules.pullbackPushforwardAdjunction p).homEquiv_naturality_right
        (SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p))
        (scalarEnd (p.appTop a))).trans
      (congrArg (· ≫ (Scheme.Modules.pushforward p).map (scalarEnd (p.appTop a))) hq)).symm

/-- The action of `matrixEnd M` on the `j`-th free injection: `ιFree j ≫ matrixEnd M`
expands as the sum over rows `∑ k, scalarEnd (M k j) ≫ ιFree k`. Project-local helper
for `matrixEnd_pullback`. -/
lemma ιFree_matrixEnd {S : Scheme.{0}} {d : ℕ} (M : Matrix (Fin d) (Fin d) Γ(S, ⊤))
    (j : Fin d) :
    SheafOfModules.ιFree (R := S.ringCatSheaf) j ≫ matrixEnd M
      = ∑ k, scalarEnd (M k j) ≫ SheafOfModules.ιFree (R := S.ringCatSheaf) k := by
  rw [matrixEnd, SheafOfModules.ιFree]
  simp only [SheafOfModules.free]
  rw [Iso.symm_hom, biproduct.isoCoproduct_inv, biproduct.isoCoproduct_hom,
    ← Category.assoc, Sigma.ι_desc, biproduct.ι_matrix_assoc, biproduct.lift_desc]
  rfl

/-- **(a) Matrix endomorphism naturality under pullback** (`lem:gr_matrixEnd_pullback`).
For `p : T ⟶ S` and `M : Matrix (Fin d) (Fin d) Γ(S,⊤)`, the pullback of the matrix
endomorphism `matrixEnd M` is, after the free-pullback comparison `Q = pullbackFreeIso p (Fin d)`,
the matrix endomorphism of the base-changed matrix `p.appTop • M` (entrywise comorphism):
`(pullback p).map (matrixEnd M) = Q.hom ≫ matrixEnd (p.appTop.mapMatrix M) ≫ Q.inv`.
Reduces, on each one-element biproduct component, to the scalar atom `scalarEnd_pullback`.
Project-local. -/
lemma matrixEnd_pullback {T S : Scheme.{0}} (p : T ⟶ S) {d : ℕ}
    (M : Matrix (Fin d) (Fin d) Γ(S, ⊤)) :
    (Scheme.Modules.pullback p).map (matrixEnd M)
      = (Scheme.Modules.pullbackFreeIso p (Fin d)).hom ≫
        matrixEnd ((CommRingCat.Hom.hom (Scheme.Hom.appTop p)).mapMatrix M) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin d)).inv := by
  haveI := Scheme.Modules.opensMap_final p
  -- Reduce to the naturality square (cancel the trailing `Q.inv`).
  rw [← Category.assoc, Iso.eq_comp_inv]
  -- Check the two maps out of the coproduct `(pullback p).obj (free (Fin d))` agree on each
  -- free injection `(pullback p).map (ιFree i)` (the cofan of the preserved colimit).
  refine Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback p) _ _
      (SheafOfModules.isColimitFreeCofan (Fin d))) _ _ (fun i => ?_)
  simp only [cofan_mk_inj, Cofan.mk_pt]
  -- `Q.hom` is, by construction of `pullbackFreeIso`, the Mathlib free-pullback comparison.
  have hQhom : (Scheme.Modules.pullbackFreeIso p (Fin d)).hom
      = (SheafOfModules.pullbackObjFreeIso (Scheme.Hom.toRingCatSheafHom p) (Fin d)).hom := rfl
  -- The free injection cancels against `Q.hom` into the unit-pullback comparison
  -- (`pullbackObjUnitToUnit`), which is where `scalarEnd_pullback` lives.
  have key : ∀ k : Fin d,
      (Scheme.Modules.pullback p).map (SheafOfModules.ιFree k)
          ≫ (Scheme.Modules.pullbackFreeIso p (Fin d)).hom
        = SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p)
            ≫ SheafOfModules.ιFree k := by
    intro k
    rw [hQhom]
    exact SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ k
  -- LHS: `map (ιFree i) ≫ map (matrixEnd M)` collapses to `map (ιFree i ≫ matrixEnd M)`,
  -- then `ιFree_matrixEnd` turns it into a row sum, distributed by additivity of the pullback.
  rw [← Functor.map_comp_assoc]
  -- `erw` (defeq matching) is needed to see `ιFree i ≫ matrixEnd M` under `(pullback p).map`.
  erw [ιFree_matrixEnd M i]
  erw [Functor.map_sum]
  rw [Preadditive.sum_comp]
  -- RHS: cancel `map (ιFree i) ≫ Q.hom` into `pullbackObjUnitToUnit ≫ ιFree i`, then expand.
  rw [← Category.assoc ((Scheme.Modules.pullback p).map (SheafOfModules.ιFree i))
        (Scheme.Modules.pullbackFreeIso p (Fin d)).hom,
    key i]
  erw [Category.assoc]
  erw [ιFree_matrixEnd ((CommRingCat.Hom.hom (Scheme.Hom.appTop p)).mapMatrix M) i]
  erw [Preadditive.comp_sum]
  -- Match term by term: each entry reduces to the scalar atom `scalarEnd_pullback`.
  refine Finset.sum_congr rfl (fun k _ => ?_)
  erw [Functor.map_comp]
  rw [Category.assoc, key k]
  erw [reassoc_of% scalarEnd_pullback p (M k i)]
  erw [Category.assoc]

/-- The action of `matrixEndRect M` on the `j`-th free injection: `ιFree j ≫ matrixEndRect M`
expands as the sum over rows `∑ k, scalarEnd (M k j) ≫ ιFree k`. Project-local helper
for `matrixEndRect_pullback` (rectangular analogue of `ιFree_matrixEnd`). -/
lemma ιFree_matrixEndRect {S : Scheme.{0}} {d r : ℕ} (M : Matrix (Fin d) (Fin r) Γ(S, ⊤))
    (j : Fin r) :
    SheafOfModules.ιFree (R := S.ringCatSheaf) j ≫ matrixEndRect M
      = ∑ k, scalarEnd (M k j) ≫ SheafOfModules.ιFree (R := S.ringCatSheaf) k := by
  rw [matrixEndRect, SheafOfModules.ιFree]
  simp only [SheafOfModules.free]
  rw [Iso.symm_hom, biproduct.isoCoproduct_inv, biproduct.isoCoproduct_hom,
    ← Category.assoc, Sigma.ι_desc, biproduct.ι_matrix_assoc, biproduct.lift_desc]
  rfl

/-- **Rectangular matrix homomorphism naturality under pullback**
(`lem:gr_matrixEndRect_pullback`). For `p : T ⟶ S` and a `d × r` matrix `M` of global
sections, the pullback of `matrixEndRect M` is, after the free-pullback comparisons
`Q_r = pullbackFreeIso p (Fin r)` and `Q_d = pullbackFreeIso p (Fin d)`, the rectangular
homomorphism of the base-changed matrix `p^♯ M`:
`(pullback p).map (matrixEndRect M) = Q_r.hom ≫ matrixEndRect (p^♯ M) ≫ Q_d.inv`.
Identical skeleton to the square `matrixEnd_pullback`, reducing on each one-element
biproduct component to the scalar atom `scalarEnd_pullback`. Project-local. -/
lemma matrixEndRect_pullback {T S : Scheme.{0}} (p : T ⟶ S) {d r : ℕ}
    (M : Matrix (Fin d) (Fin r) Γ(S, ⊤)) :
    (Scheme.Modules.pullback p).map (matrixEndRect M)
      = (Scheme.Modules.pullbackFreeIso p (Fin r)).hom ≫
        matrixEndRect (M.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop p))) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin d)).inv := by
  haveI := Scheme.Modules.opensMap_final p
  -- Reduce to the naturality square (cancel the trailing `Q_d.inv`).
  rw [← Category.assoc, Iso.eq_comp_inv]
  -- Check the two maps out of the coproduct `(pullback p).obj (free (Fin r))` agree on each
  -- free injection (the cofan of the preserved colimit).
  refine Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback p) _ _
      (SheafOfModules.isColimitFreeCofan (Fin r))) _ _ (fun i => ?_)
  simp only [cofan_mk_inj, Cofan.mk_pt]
  -- the source/target free-pullback comparisons in their Mathlib form
  have hQr : (Scheme.Modules.pullbackFreeIso p (Fin r)).hom
      = (SheafOfModules.pullbackObjFreeIso (Scheme.Hom.toRingCatSheafHom p) (Fin r)).hom := rfl
  have hQd : (Scheme.Modules.pullbackFreeIso p (Fin d)).hom
      = (SheafOfModules.pullbackObjFreeIso (Scheme.Hom.toRingCatSheafHom p) (Fin d)).hom := rfl
  have key_r : ∀ k : Fin r,
      (Scheme.Modules.pullback p).map (SheafOfModules.ιFree k)
          ≫ (Scheme.Modules.pullbackFreeIso p (Fin r)).hom
        = SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p)
            ≫ SheafOfModules.ιFree k := by
    intro k
    rw [hQr]
    exact SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ k
  have key_d : ∀ k : Fin d,
      (Scheme.Modules.pullback p).map (SheafOfModules.ιFree k)
          ≫ (Scheme.Modules.pullbackFreeIso p (Fin d)).hom
        = SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p)
            ≫ SheafOfModules.ιFree k := by
    intro k
    rw [hQd]
    exact SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ k
  -- LHS: collapse to a row sum via `ιFree_matrixEndRect`, distributed by additivity.
  rw [← Functor.map_comp_assoc]
  erw [ιFree_matrixEndRect M i]
  erw [Functor.map_sum]
  rw [Preadditive.sum_comp]
  -- RHS: cancel `map (ιFree i) ≫ Q_r.hom` into `pullbackObjUnitToUnit ≫ ιFree i`, expand.
  rw [← Category.assoc ((Scheme.Modules.pullback p).map (SheafOfModules.ιFree i))
        (Scheme.Modules.pullbackFreeIso p (Fin r)).hom,
    key_r i]
  erw [Category.assoc]
  erw [ιFree_matrixEndRect (M.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop p))) i]
  erw [Preadditive.comp_sum]
  -- Match term by term: each entry reduces to the scalar atom `scalarEnd_pullback`.
  refine Finset.sum_congr rfl (fun k _ => ?_)
  erw [Functor.map_comp]
  rw [Category.assoc, key_d k]
  erw [reassoc_of% scalarEnd_pullback p (M k i)]
  erw [Category.assoc]

/-- The chart quotient is, definitionally, the rectangular matrix homomorphism of the
injected universal matrix: `u^I = matrixEndRect ((ΓSpecIso R^I).inv X^I)`. Project-local —
the bridge between `chartQuotientMap` and the `matrixEndRect` API. -/
lemma chartQuotientMap_eq_matrixEndRect (d r : ℕ) (I : Finset (Fin r)) (hI : I.card = d) :
    chartQuotientMap d r I hI
      = matrixEndRect ((universalMatrix d r I hI).map
          ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ))).inv)) := rfl

/-! ### Entry extraction and the matrix presentation of free-sheaf morphisms

(The block below was moved up from the chart-transport section so that the chart-loci
covering proof `chartLocus_isOpenCover` — which precedes that section — can use it.) -/

/-- The `p`-th **projection of the free sheaf** `O_X^d ⟶ O_X`, through the
biproduct/coproduct comparison. Companion of `SheafOfModules.ιFree`; project-local. -/
noncomputable def projFree {X : Scheme.{0}} {d : ℕ} (p : Fin d) :
    SheafOfModules.free (R := X.ringCatSheaf) (Fin d) ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (biproduct.isoCoproduct (fun _ : Fin d => SheafOfModules.unit X.ringCatSheaf)).inv ≫
    biproduct.π (fun _ : Fin d => SheafOfModules.unit X.ringCatSheaf) p

/-- The global section of `O_X` carried by an endomorphism of the unit sheaf of modules:
the value of the endomorphism at the unit section `1` over `⊤`. This inverts `scalarEnd`
(`unitEndSection_scalarEnd`); project-local. -/
noncomputable def unitEndSection {X : Scheme.{0}}
    (e : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    Γ(X, ⊤) :=
  e.val.app (Opposite.op ⊤) (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))

/-- `unitEndSection` inverts `scalarEnd`: extracting the section of the scalar
endomorphism of `a` returns `a`. Project-local. -/
lemma unitEndSection_scalarEnd {X : Scheme.{0}} (a : Γ(X, ⊤)) :
    unitEndSection (scalarEnd a) = a := by
  rw [unitEndSection, scalarEnd_val_app_one]
  -- the restriction along `⊤ ≤ ⊤` is the identity (`homOfLE le_top = 𝟙 ⊤` by proof
  -- irrelevance, definitionally)
  change (X.ringCatSheaf.obj.map (𝟙 (Opposite.op (⊤ : X.Opens))) a) = a
  rw [X.ringCatSheaf.obj.map_id]
  rfl

/-- Every endomorphism of the unit sheaf is the scalar endomorphism of its global
section: `scalarEnd (unitEndSection e) = e`. Converse of `unitEndSection_scalarEnd`;
together they make `unitEndSection` a bijection. Project-local. -/
lemma scalarEnd_unitEndSection {X : Scheme.{0}}
    (e : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    scalarEnd (unitEndSection e) = e := by
  apply (SheafOfModules.unit X.ringCatSheaf).unitHomEquiv.injective
  rw [unitHomEquiv_scalarEnd]
  refine PresheafOfModules.sections_ext _ _ (fun Y => ?_)
  -- LHS at `Y` is the restriction of `e`'s value at `⊤`; RHS is `e`'s value at `Y`,
  -- equal by naturality of `e.val` at `Y ≤ ⊤` (and `1|_Y = 1`).
  change X.ringCatSheaf.obj.map (homOfLE le_top).op
      (e.val.app (Opposite.op ⊤) (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤)))
    = e.val.app Y (1 : X.ringCatSheaf.obj.obj Y)
  have hnat := PresheafOfModules.naturality_apply e.val
    (homOfLE (le_top : Y.unop ≤ ⊤)).op (1 : X.ringCatSheaf.obj.obj (Opposite.op ⊤))
  refine hnat.symm.trans (congrArg (fun z => e.val.app Y z) ?_)
  exact PresheafOfModules.unit_map_one X.ringCatSheaf.obj
    (homOfLE (le_top : Y.unop ≤ ⊤)).op

/-- Composing the `k`-th free injection with the `p`-th free projection is the identity
when `k = p` and zero otherwise. Project-local helper for entry extraction. -/
lemma ιFree_projFree {X : Scheme.{0}} {d : ℕ} (k p : Fin d) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) k ≫ projFree p
      = if k = p then 𝟙 (SheafOfModules.unit X.ringCatSheaf) else 0 := by
  rw [projFree, SheafOfModules.ιFree]
  simp only [SheafOfModules.free]
  rw [biproduct.isoCoproduct_inv, ← Category.assoc, Sigma.ι_desc, biproduct.ι_π]
  by_cases h : k = p
  · subst h; rw [dif_pos rfl, if_pos rfl]; rfl
  · rw [dif_neg h, if_neg h]

/-- **Entry extraction for `matrixEndRect`**: the `(p, j)` unit-sheaf component of the
rectangular matrix morphism is the scalar endomorphism of the `(p, j)` entry.
Project-local. -/
lemma ιFree_matrixEndRect_projFree {S : Scheme.{0}} {d r : ℕ}
    (M : Matrix (Fin d) (Fin r) Γ(S, ⊤)) (j : Fin r) (p : Fin d) :
    SheafOfModules.ιFree (R := S.ringCatSheaf) j ≫ matrixEndRect M ≫ projFree p
      = scalarEnd (M p j) := by
  rw [← Category.assoc, ιFree_matrixEndRect, Preadditive.sum_comp]
  refine (Finset.sum_eq_single p (fun k _ hk => ?_)
    (fun hp => absurd (Finset.mem_univ p) hp)).trans ?_
  · rw [Category.assoc, ιFree_projFree, if_neg hk, Limits.comp_zero]
  · rw [Category.assoc, ιFree_projFree, if_pos rfl, Category.comp_id]

set_option maxHeartbeats 800000 in
/-- **Matrix presentation of a morphism of free sheaves**: any `φ : O_S^r ⟶ O_S^d` is
`matrixEndRect` of its matrix of unit-component sections. Project-local — the
extensionality that lets the pullback-naturality of `matrixEndRect` act on arbitrary
free-sheaf morphisms (such as `chartMatrixHom`). -/
lemma matrixEndRect_unitEndSection {S : Scheme.{0}} {d r : ℕ}
    (φ : SheafOfModules.free (R := S.ringCatSheaf) (Fin r) ⟶
      SheafOfModules.free (R := S.ringCatSheaf) (Fin d)) :
    matrixEndRect (Matrix.of fun p j =>
        unitEndSection (SheafOfModules.ιFree j ≫ φ ≫ projFree p)) = φ := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (Fin r)) _ _ (fun j => ?_)
  simp only [SheafOfModules.freeCofan_inj]
  -- compare the two maps `unit ⟶ free (Fin d)` against the biproduct projections
  refine (cancel_mono (biproduct.isoCoproduct
    (fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf)).inv).mp ?_
  refine biproduct.hom_ext _ _ (fun p => ?_)
  simp only [Category.assoc]
  -- fold the trailing comparison-projection pair into `projFree p` (definitional)
  change SheafOfModules.ιFree j ≫ matrixEndRect _ ≫ projFree p
    = SheafOfModules.ιFree j ≫ φ ≫ projFree p
  rw [ιFree_matrixEndRect_projFree]
  -- reduce the `Matrix.of` entry (definitional) so the extensionality lemma applies
  change scalarEnd (unitEndSection (SheafOfModules.ιFree j ≫ φ ≫ projFree p))
    = SheafOfModules.ιFree j ≫ φ ≫ projFree p
  exact scalarEnd_unitEndSection _

/-- The conjugation of the pullback of a rectangular matrix morphism by the free-pullback
comparisons is the matrix morphism of the entrywise base-changed matrix — the
`matrixEndRect_pullback` naturality with the comparisons moved to the other side.
Project-local. -/
lemma pullback_conj_matrixEndRect {W V : Scheme.{0}} (p : W ⟶ V) {d r : ℕ}
    (N : Matrix (Fin d) (Fin r) Γ(V, ⊤)) :
    (Scheme.Modules.pullbackFreeIso p (Fin r)).inv ≫
        (Scheme.Modules.pullback p).map (matrixEndRect N) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin d)).hom
      = matrixEndRect (N.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop p))) := by
  rw [matrixEndRect_pullback]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

set_option maxHeartbeats 800000 in
/-- The free-pullback comparison intertwines index maps:
`p^*(freeMap g) ≫ Q_m = Q_n ≫ freeMap g`. Project-local — naturality of
`pullbackFreeIso` in the index. -/
lemma pullback_map_freeMap_pullbackFreeIso {W V : Scheme.{0}} (p : W ⟶ V) {n m : ℕ}
    (g : Fin n → Fin m) :
    (Scheme.Modules.pullback p).map (SheafOfModules.freeMap (R := V.ringCatSheaf) g) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin m)).hom
      = (Scheme.Modules.pullbackFreeIso p (Fin n)).hom ≫
        SheafOfModules.freeMap (R := W.ringCatSheaf) g := by
  haveI := Scheme.Modules.opensMap_final p
  refine Cofan.IsColimit.hom_ext
    (isColimitCofanMkObjOfIsColimit (Scheme.Modules.pullback p) _ _
      (SheafOfModules.isColimitFreeCofan (Fin n))) _ _ (fun i => ?_)
  simp only [cofan_mk_inj, Cofan.mk_pt]
  have key_n : (Scheme.Modules.pullback p).map (SheafOfModules.ιFree i)
        ≫ (Scheme.Modules.pullbackFreeIso p (Fin n)).hom
      = SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p)
          ≫ SheafOfModules.ιFree i :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ i
  have key_m : (Scheme.Modules.pullback p).map (SheafOfModules.ιFree (g i))
        ≫ (Scheme.Modules.pullbackFreeIso p (Fin m)).hom
      = SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p)
          ≫ SheafOfModules.ιFree (g i) :=
    SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom _ (g i)
  have s1 : (Scheme.Modules.pullback p).map (SheafOfModules.ιFree i) ≫
        (Scheme.Modules.pullback p).map (SheafOfModules.freeMap g) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin m)).hom
      = ((Scheme.Modules.pullback p).map (SheafOfModules.ιFree i) ≫
          (Scheme.Modules.pullback p).map (SheafOfModules.freeMap g)) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin m)).hom := (Category.assoc _ _ _).symm
  have s2 : ((Scheme.Modules.pullback p).map (SheafOfModules.ιFree i) ≫
          (Scheme.Modules.pullback p).map (SheafOfModules.freeMap g)) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin m)).hom
      = (Scheme.Modules.pullback p).map (SheafOfModules.ιFree i ≫
          SheafOfModules.freeMap g) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin m)).hom :=
      congrArg (· ≫ (Scheme.Modules.pullbackFreeIso p (Fin m)).hom)
        ((Scheme.Modules.pullback p).map_comp _ _).symm
  have s3 : (Scheme.Modules.pullback p).map (SheafOfModules.ιFree i ≫
          SheafOfModules.freeMap g) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin m)).hom
      = (Scheme.Modules.pullback p).map (SheafOfModules.ιFree (g i)) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin m)).hom :=
      congrArg (fun z => (Scheme.Modules.pullback p).map z ≫
        (Scheme.Modules.pullbackFreeIso p (Fin m)).hom)
        (SheafOfModules.ιFree_freeMap (R := V.ringCatSheaf) g i)
  have s4 : SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p) ≫
        SheafOfModules.ιFree (g i)
      = SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p) ≫
        SheafOfModules.ιFree i ≫ SheafOfModules.freeMap (R := W.ringCatSheaf) g :=
      congrArg (SheafOfModules.pullbackObjUnitToUnit
        (Scheme.Hom.toRingCatSheafHom p) ≫ ·)
        (SheafOfModules.ιFree_freeMap (R := W.ringCatSheaf) g i).symm
  have s5 : SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p) ≫
        SheafOfModules.ιFree i ≫ SheafOfModules.freeMap (R := W.ringCatSheaf) g
      = (SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p) ≫
          SheafOfModules.ιFree i) ≫ SheafOfModules.freeMap (R := W.ringCatSheaf) g :=
      (Category.assoc _ _ _).symm
  have s6 : (SheafOfModules.pullbackObjUnitToUnit (Scheme.Hom.toRingCatSheafHom p) ≫
          SheafOfModules.ιFree i) ≫ SheafOfModules.freeMap (R := W.ringCatSheaf) g
      = ((Scheme.Modules.pullback p).map (SheafOfModules.ιFree i) ≫
          (Scheme.Modules.pullbackFreeIso p (Fin n)).hom) ≫
        SheafOfModules.freeMap (R := W.ringCatSheaf) g :=
      congrArg (· ≫ SheafOfModules.freeMap (R := W.ringCatSheaf) g) key_n.symm
  have s7 : ((Scheme.Modules.pullback p).map (SheafOfModules.ιFree i) ≫
          (Scheme.Modules.pullbackFreeIso p (Fin n)).hom) ≫
        SheafOfModules.freeMap (R := W.ringCatSheaf) g
      = (Scheme.Modules.pullback p).map (SheafOfModules.ιFree i) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin n)).hom ≫
        SheafOfModules.freeMap (R := W.ringCatSheaf) g := Category.assoc _ _ _
  exact s1.trans (s2.trans (s3.trans (key_m.trans (s4.trans (s5.trans (s6.trans s7))))))

/-! ### The rectangular matrix calculus: composition, identity, injectivity

Support for the covering proof `chartLocus_isOpenCover`: the fully rectangular
composition law (generalising `matrixEndRect_comp`), the identity law, injectivity of the
matrix presentation, and the column-restriction law against `freeMap`. -/

/-- For a square matrix the square and rectangular matrix endomorphisms coincide
(they are definitionally the same biproduct matrix). Project-local bridge. -/
lemma matrixEnd_eq_matrixEndRect {S : Scheme.{0}} {d : ℕ}
    (M : Matrix (Fin d) (Fin d) Γ(S, ⊤)) : matrixEnd M = matrixEndRect M := rfl

/-- `matrixEndRect` of the identity matrix is the identity. Project-local. -/
lemma matrixEndRect_one {S : Scheme.{0}} {d : ℕ} :
    matrixEndRect (1 : Matrix (Fin d) (Fin d) Γ(S, ⊤)) = 𝟙 _ :=
  (matrixEnd_eq_matrixEndRect _).symm.trans matrixEnd_one

/-- Composition of two `biproduct.matrix` morphisms, fully rectangular sizes — the
categorical matrix product. Project-local helper for `matrixEndRect_comp_rect`. -/
private lemma biproduct_matrix_comp_rect₂ {S : Scheme.{0}} {n e d : ℕ}
    (mA : Fin n → Fin e →
      (SheafOfModules.unit S.ringCatSheaf ⟶ SheafOfModules.unit S.ringCatSheaf))
    (mB : Fin e → Fin d →
      (SheafOfModules.unit S.ringCatSheaf ⟶ SheafOfModules.unit S.ringCatSheaf)) :
    biproduct.matrix (f := fun _ : Fin n => SheafOfModules.unit S.ringCatSheaf)
        (g := fun _ : Fin e => SheafOfModules.unit S.ringCatSheaf) mA ≫ biproduct.matrix mB
      = biproduct.matrix (fun i q => ∑ p, mA i p ≫ mB p q) := by
  refine biproduct.hom_ext' _ _ (fun i => biproduct.hom_ext _ _ (fun q => ?_))
  simp only [Category.assoc, biproduct.ι_matrix_assoc, biproduct.matrix_π, biproduct.lift_desc,
    biproduct.ι_matrix, biproduct.lift_π]

/-- **Fully rectangular composition law**: `matrixEndRect A ≫ matrixEndRect B =
matrixEndRect (B * A)` for `A : e × n`, `B : d × e` — the matrix product, with the order
reversed by the contravariance of the column/component indexing exactly as in
`matrixEndRect_comp`. Project-local. -/
lemma matrixEndRect_comp_rect {S : Scheme.{0}} {n e d : ℕ}
    (A : Matrix (Fin e) (Fin n) Γ(S, ⊤)) (B : Matrix (Fin d) (Fin e) Γ(S, ⊤)) :
    matrixEndRect A ≫ matrixEndRect B = matrixEndRect (B * A) := by
  rw [matrixEndRect, matrixEndRect, matrixEndRect]
  have hcomp : biproduct.matrix (fun (i : Fin n) (p : Fin e) => scalarEnd (A p i))
        ≫ biproduct.matrix (fun (i : Fin e) (p : Fin d) => scalarEnd (B p i))
      = biproduct.matrix (fun (i : Fin n) (p : Fin d) => scalarEnd ((B * A) p i)) := by
    rw [biproduct_matrix_comp_rect₂]
    congr 1
    funext i q
    simp_rw [scalarEnd_comp]
    rw [← scalarEnd_sum, Matrix.mul_apply]
    exact congrArg scalarEnd (Finset.sum_congr rfl (fun p _ => mul_comm _ _))
  simp only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id_assoc]
  rw [← Category.assoc (biproduct.matrix (fun (i : Fin n) (p : Fin e) => scalarEnd (A p i))),
    hcomp]

/-- **`matrixEndRect` is injective**: the presenting matrix of a free-sheaf morphism is
unique (entry extraction `ιFree_matrixEndRect_projFree` + `unitEndSection_scalarEnd`).
Project-local. -/
lemma matrixEndRect_injective {S : Scheme.{0}} {d r : ℕ}
    {M N : Matrix (Fin d) (Fin r) Γ(S, ⊤)} (h : matrixEndRect M = matrixEndRect N) :
    M = N := by
  refine Matrix.ext (fun p j => ?_)
  have h1 : SheafOfModules.ιFree (R := S.ringCatSheaf) j ≫ matrixEndRect M ≫ projFree p
      = SheafOfModules.ιFree j ≫ matrixEndRect N ≫ projFree p :=
    congrArg (fun z => SheafOfModules.ιFree j ≫ z ≫ projFree p) h
  have h2 : scalarEnd (M p j) = scalarEnd (N p j) :=
    (ιFree_matrixEndRect_projFree M j p).symm.trans
      (h1.trans (ιFree_matrixEndRect_projFree N j p))
  exact (unitEndSection_scalarEnd (M p j)).symm.trans
    ((congrArg unitEndSection h2).trans (unitEndSection_scalarEnd (N p j)))

/-- **Column restriction against `freeMap`**: precomposing a rectangular matrix morphism
with the index inclusion `freeMap g` is taking the `g`-column submatrix. Project-local. -/
lemma freeMap_matrixEndRect {S : Scheme.{0}} {d r e : ℕ} (g : Fin e → Fin r)
    (M : Matrix (Fin d) (Fin r) Γ(S, ⊤)) :
    SheafOfModules.freeMap (R := S.ringCatSheaf) g ≫ matrixEndRect M
      = matrixEndRect (M.submatrix id g) := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (Fin e)) _ _ (fun j => ?_)
  simp only [SheafOfModules.freeCofan_inj]
  refine (cancel_mono (biproduct.isoCoproduct
    (fun _ : Fin d => SheafOfModules.unit S.ringCatSheaf)).inv).mp ?_
  refine biproduct.hom_ext _ _ (fun p => ?_)
  simp only [Category.assoc]
  change SheafOfModules.ιFree j ≫ (SheafOfModules.freeMap g ≫ matrixEndRect M) ≫ projFree p
    = SheafOfModules.ιFree j ≫ matrixEndRect (M.submatrix id g) ≫ projFree p
  calc SheafOfModules.ιFree j ≫ (SheafOfModules.freeMap g ≫ matrixEndRect M) ≫ projFree p
      = (SheafOfModules.ιFree j ≫ SheafOfModules.freeMap g) ≫
          matrixEndRect M ≫ projFree p := by
        simp only [Category.assoc]
    _ = SheafOfModules.ιFree (g j) ≫ matrixEndRect M ≫ projFree p :=
        congrArg (· ≫ matrixEndRect M ≫ projFree p)
          (SheafOfModules.ιFree_freeMap (R := S.ringCatSheaf) g j)
    _ = scalarEnd (M p (g j)) := ιFree_matrixEndRect_projFree M (g j) p
    _ = SheafOfModules.ιFree j ≫ matrixEndRect (M.submatrix id g) ≫ projFree p :=
        (ιFree_matrixEndRect_projFree (M.submatrix id g) j p).symm

/-! ### Epimorphisms between free sheaves split over affines

The Nakayama/covering step of `chartLocus_isOpenCover` needs pointwise (fibre-level)
surjectivity of an epimorphism of sheaves of modules. Over an affine base this needs no
stalk theory at all: the tilde functor `ModuleCat R ⥤ (Spec R).Modules` is fully
faithful and additive, identifies the free sheaf with the tilde of the free module
(`tildeFinsupp`), epimorphisms of modules are surjections, and free modules are
projective — so any epimorphism between free sheaves on `Spec R` is *split*, and its
presenting matrix admits a right inverse over the global sections. -/

/-- **Epimorphisms between free sheaves of modules on `Spec R` split**: the splitting is
transported through the fully faithful `tilde.functor` from the projectivity of the free
module `Fin d →₀ R`. Project-local. -/
lemma exists_section_of_epi_free_spec {R : CommRingCat.{0}} {d r : ℕ}
    (ψ : SheafOfModules.free (R := (Spec R).ringCatSheaf) (Fin r) ⟶
      SheafOfModules.free (R := (Spec R).ringCatSheaf) (Fin d)) [Epi ψ] :
    ∃ Φ : SheafOfModules.free (R := (Spec R).ringCatSheaf) (Fin d) ⟶
        SheafOfModules.free (R := (Spec R).ringCatSheaf) (Fin r),
      Φ ≫ ψ = 𝟙 (SheafOfModules.free (R := (Spec R).ringCatSheaf) (Fin d)) := by
  -- the tilde-conjugate of `ψ` and its module-level preimage under full faithfulness
  let ψt : tilde (ModuleCat.of ↥R (Fin r →₀ ↥R)) ⟶ tilde (ModuleCat.of ↥R (Fin d →₀ ↥R)) :=
    (tildeFinsupp (Fin r)).hom ≫ ψ ≫ (tildeFinsupp (Fin d)).inv
  let g : ModuleCat.of ↥R (Fin r →₀ ↥R) ⟶ ModuleCat.of ↥R (Fin d →₀ ↥R) :=
    tilde.fullyFaithfulFunctor.preimage ψt
  have hg : tilde.map g = ψt := tilde.fullyFaithfulFunctor.map_preimage ψt
  haveI hiso_r : IsIso (tildeFinsupp (R := R) (Fin r)).hom := inferInstance
  haveI hiso_d : IsIso (tildeFinsupp (R := R) (Fin d)).inv := inferInstance
  haveI hψt : Epi ψt := by
    -- fully explicit: the `(Spec R).Modules` / `(Spec (.of ↥R)).Modules` defeq blocks
    -- automatic instance search across the composite
    haveI h1 : Epi (ψ ≫ (tildeFinsupp (Fin d)).inv) :=
      @epi_comp _ _ _ _ _ ψ ‹Epi ψ› _ (IsIso.epi_of_iso _)
    exact @epi_comp _ _ _ _ _ (tildeFinsupp (Fin r)).hom (IsIso.epi_of_iso _) _ h1
  haveI hge : Epi g := by
    refine (tilde.functor R).epi_of_epi_map ?_
    show Epi (tilde.map g)
    rw [hg]
    exact hψt
  have hsurj : Function.Surjective g.hom := (ModuleCat.epi_iff_surjective g).mp hge
  -- a module-level section of `g` by projectivity of the free module
  obtain ⟨w, hw⟩ := Module.projective_lifting_property g.hom LinearMap.id hsurj
  refine ⟨(tildeFinsupp (Fin d)).inv ≫ tilde.map (ModuleCat.ofHom w) ≫
    (tildeFinsupp (Fin r)).hom, ?_⟩
  have hcomp : ModuleCat.ofHom w ≫ g = 𝟙 (ModuleCat.of ↥R (Fin d →₀ ↥R)) :=
    ModuleCat.hom_ext (by
      rw [ModuleCat.hom_comp, ModuleCat.hom_id, ModuleCat.hom_ofHom]
      exact hw)
  have hstep : (tildeFinsupp (Fin r)).hom ≫ ψ = tilde.map g ≫ (tildeFinsupp (Fin d)).hom := by
    rw [hg]
    simp only [ψt, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  calc ((tildeFinsupp (Fin d)).inv ≫ tilde.map (ModuleCat.ofHom w) ≫
        (tildeFinsupp (Fin r)).hom) ≫ ψ
      = (tildeFinsupp (Fin d)).inv ≫ tilde.map (ModuleCat.ofHom w) ≫
        ((tildeFinsupp (Fin r)).hom ≫ ψ) := by simp only [Category.assoc]
    _ = (tildeFinsupp (Fin d)).inv ≫ tilde.map (ModuleCat.ofHom w) ≫
        tilde.map g ≫ (tildeFinsupp (Fin d)).hom := by rw [hstep]
    _ = (tildeFinsupp (Fin d)).inv ≫ tilde.map (ModuleCat.ofHom w ≫ g) ≫
        (tildeFinsupp (Fin d)).hom := by rw [← tilde.map_comp_assoc]
    _ = (tildeFinsupp (Fin d)).inv ≫ 𝟙 _ ≫ (tildeFinsupp (Fin d)).hom := by
        rw [hcomp, tilde.map_id]
    _ = 𝟙 _ := by rw [Category.id_comp, Iso.inv_hom_id]

/-- **Presenting matrices of epimorphisms admit right inverses over `Spec R`**: combine
the splitting `exists_section_of_epi_free_spec` with the matrix presentation of the
section and the rectangular composition law. Project-local. -/
lemma exists_rightInverse_of_epi_matrixEndRect_spec {R : CommRingCat.{0}} {d r : ℕ}
    (M : Matrix (Fin d) (Fin r) Γ(Spec R, ⊤)) (h : Epi (matrixEndRect M)) :
    ∃ G : Matrix (Fin r) (Fin d) Γ(Spec R, ⊤), M * G = 1 := by
  haveI := h
  obtain ⟨Φ, hΦ⟩ := exists_section_of_epi_free_spec (matrixEndRect M)
  refine ⟨Matrix.of (fun q p => unitEndSection
    (SheafOfModules.ιFree p ≫ Φ ≫ projFree q)), ?_⟩
  have hpres : matrixEndRect (Matrix.of (fun q p => unitEndSection
      (SheafOfModules.ιFree p ≫ Φ ≫ projFree q))) = Φ := matrixEndRect_unitEndSection Φ
  apply matrixEndRect_injective
  rw [← matrixEndRect_comp_rect, hpres, hΦ, matrixEndRect_one]

/-- **Presenting matrices of epimorphisms admit right inverses over any affine scheme** —
the `Spec` case transported along `S.isoSpec` through the free-pullback comparisons
(`pullback_conj_matrixEndRect`). Project-local; the algebraic heart of the Nakayama
covering step. -/
lemma exists_rightInverse_of_epi_matrixEndRect {S : Scheme.{0}} [IsAffine S] {d r : ℕ}
    (M : Matrix (Fin d) (Fin r) Γ(S, ⊤)) (h : Epi (matrixEndRect M)) :
    ∃ G : Matrix (Fin r) (Fin d) Γ(S, ⊤), M * G = 1 := by
  -- transport to `Spec Γ(S, ⊤)` along the inverse of `isoSpec`
  haveI h1 : Epi ((Scheme.Modules.pullback S.isoSpec.inv).map (matrixEndRect M)) :=
    @CategoryTheory.Functor.map_epi _ _ _ _ (Scheme.Modules.pullback S.isoSpec.inv)
      inferInstance _ _ _ h
  haveI h2 : Epi ((Scheme.Modules.pullbackFreeIso S.isoSpec.inv (Fin r)).inv ≫
      (Scheme.Modules.pullback S.isoSpec.inv).map (matrixEndRect M) ≫
      (Scheme.Modules.pullbackFreeIso S.isoSpec.inv (Fin d)).hom) := by
    haveI : Epi ((Scheme.Modules.pullback S.isoSpec.inv).map (matrixEndRect M) ≫
        (Scheme.Modules.pullbackFreeIso S.isoSpec.inv (Fin d)).hom) := epi_comp _ _
    exact epi_comp _ _
  have h3 : Epi (matrixEndRect (M.map
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.inv)))) := by
    rw [← pullback_conj_matrixEndRect S.isoSpec.inv M]
    exact h2
  obtain ⟨G', hG'⟩ := exists_rightInverse_of_epi_matrixEndRect_spec
    (M.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.inv))) h3
  -- pull the right inverse back along the (iso) global-sections comorphism
  have hcancel : Scheme.Hom.appTop S.isoSpec.inv ≫ Scheme.Hom.appTop S.isoSpec.hom
      = 𝟙 (Γ(S, ⊤)) := by
    rw [← Scheme.Hom.comp_appTop, S.isoSpec.hom_inv_id]
    simp
  refine ⟨G'.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.hom)), ?_⟩
  have hM : (M.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.inv))).map
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.hom)) = M := by
    rw [Matrix.map_map]
    refine Matrix.ext (fun p j => ?_)
    have hpt := congrArg (fun (z : Γ(S, ⊤) ⟶ Γ(S, ⊤)) =>
      (CommRingCat.Hom.hom z) (M p j)) hcancel
    simpa using hpt
  calc M * G'.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.hom))
      = (M.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.inv))).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.hom)) *
        G'.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.hom)) := by rw [hM]
    _ = ((M.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.inv))) * G').map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.hom)) :=
        Matrix.map_mul.symm
    _ = (1 : Matrix (Fin d) (Fin d) _).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop S.isoSpec.hom)) := by rw [hG']
    _ = 1 := Matrix.map_one _ (map_zero _) (map_one _)

end AlgebraicGeometry.Grassmannian

namespace AlgebraicGeometry.Grassmannian

/-- **Transport of a matrix automorphism through `pullbackBaseChangeTransport`** — the
reusable (a)→(c) bridge for the bundle cocycle (`lem:gr_matrixToFreeIso_transport`). A
transition isomorphism of the bundle-transition shape
`pullbackFreeIso a ≪≫ matrixToFreeIso M N ≪≫ (pullbackFreeIso b).symm` (a `GL_d` matrix
automorphism conjugated to the overlap pullbacks) transports along `p : W ⟶ V` to the same
shape over `p ≫ a` / `p ≫ b`, with the matrix base-changed entrywise by the comorphism
`p.appTop`. Combines the matrix-naturality atom `matrixEnd_pullback` with the free-pullback
pseudofunctor coherence `Scheme.Modules.pullbackFreeIso_comp`. Project-local — this is the
abstract core of the bundle cocycle transport, independent of the Grassmannian charts. -/
lemma pullbackBaseChangeTransport_matrixToFreeIso {W V : Scheme.{0}} (p : W ⟶ V)
    {Yi Yj : Scheme.{0}} (a : V ⟶ Yi) (b : V ⟶ Yj) {d : ℕ}
    (M N : Matrix (Fin d) (Fin d) Γ(V, ⊤)) (hMN : M * N = 1) (hNM : N * M = 1) :
    (Scheme.Modules.pullbackBaseChangeTransport p a b
        (Scheme.Modules.pullbackFreeIso a (Fin d) ≪≫ matrixToFreeIso M N hMN hNM ≪≫
          (Scheme.Modules.pullbackFreeIso b (Fin d)).symm)).hom
      = (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom ≫
        matrixEnd ((CommRingCat.Hom.hom (Scheme.Hom.appTop p)).mapMatrix M) ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ b) (Fin d)).inv := by
  simp only [Scheme.Modules.pullbackBaseChangeTransport, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, matrixToFreeIso_hom]
  -- Front coherence: the `pullbackComp` cast + the `a`-leg comparison assemble into the
  -- composite free-pullback comparison `Q_{p≫a}` (pseudofunctoriality, `pullbackFreeIso_comp`).
  have hfront : ((Scheme.Modules.pullbackComp p a).symm.app
          (SheafOfModules.free (Fin d))).hom ≫
        (Scheme.Modules.pullback p).map (Scheme.Modules.pullbackFreeIso a (Fin d)).hom ≫
          (Scheme.Modules.pullbackFreeIso p (Fin d)).hom
      = (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom := by
    erw [← Scheme.Modules.pullbackFreeIso_comp a p (Fin d)]
    simp only [Iso.app_hom, Iso.symm_hom]
    rw [Iso.inv_hom_id_app_assoc]
  -- Back coherence: the inverse `b`-leg comparison + the `pullbackComp` cast assemble into the
  -- inverse composite comparison `Q_{p≫b}⁻¹`. Derived by inverting the `b`-leg coherence iso.
  have hback : (Scheme.Modules.pullbackFreeIso p (Fin d)).inv ≫
        (Scheme.Modules.pullback p).map (Scheme.Modules.pullbackFreeIso b (Fin d)).inv ≫
          ((Scheme.Modules.pullbackComp p b).app (SheafOfModules.free (Fin d))).hom
      = (Scheme.Modules.pullbackFreeIso (p ≫ b) (Fin d)).inv := by
    have hiso : (Scheme.Modules.pullbackComp p b).app (SheafOfModules.free (Fin d)) ≪≫
          Scheme.Modules.pullbackFreeIso (p ≫ b) (Fin d)
        = (Scheme.Modules.pullback p).mapIso (Scheme.Modules.pullbackFreeIso b (Fin d)) ≪≫
          Scheme.Modules.pullbackFreeIso p (Fin d) := by
      apply Iso.ext
      simpa using Scheme.Modules.pullbackFreeIso_comp b p (Fin d)
    have hinv := congrArg Iso.inv hiso
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv] at hinv
    -- hinv : Q_{p≫b}.inv ≫ Cpb.inv.app free = Q_p.inv ≫ (pullback p).map Q_b.inv
    rw [← Category.assoc, ← hinv, Iso.app_hom]
    erw [Category.assoc, Iso.inv_hom_id_app]
    rw [Category.comp_id]
  -- Distribute `pullback p` over the conjugated matrix automorphism and apply the matrix atom.
  rw [Functor.map_comp, Functor.map_comp, matrixEnd_pullback]
  -- Expand both comparison legs of the target via the coherences `hfront`/`hback`; the two sides
  -- then coincide up to the (here definitional) associativity of the composite.
  rw [← hfront, ← hback]
  rfl

/-! ### The base-change bridge (b): geometric comorphisms = localised cocycle ring homs

The three scheme-pullback base-change maps `Γ(U^I_J,⊤) ⟶ Γ(V_IJK,⊤)` — induced by the two
pullback projections and the triple transition `t'` — are identified, through the affine
global-sections isomorphism `ΓSpecIso` and the away-pullback identification
`V_IJK ≅ Spec S_I` (`awayPullbackIso`), with the ring homomorphisms `awayInclLeft`,
`awayInclRight` and `cocycleΘIJ ∘ awayInclRight` over which the matrix cocycle L1
(`bundleTransition_cocycle_matrix`) is stated. -/

/-- **Affine global-sections comorphism is the inducing ring homomorphism**
(`lem:gr_baseChange_bridge_gammaSpec`): for a ring homomorphism `φ : A ⟶ B`, the
global-sections comorphism of `Spec.map φ`, conjugated through the counit isomorphisms
`ΓSpecIso`, is `φ` itself. Pure `Γ ⊣ Spec` naturality; project-local packaging. -/
lemma baseChange_bridge_gammaSpec {A B : CommRingCat.{0}} (φ : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ Scheme.Hom.appTop (Spec.map φ)
      = φ ≫ (Scheme.ΓSpecIso B).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, ← Scheme.ΓSpecIso_naturality, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- The global-sections identification of the triple overlap: the ring map from the
triple-overlap coordinate ring `S_I = R^I[1/(P^I_J P^I_K)]` to the global sections of the
scheme-level triple overlap `V_IJK = U^I_J ×_{U^I} U^I_K`, namely the affine identification
`ΓSpecIso` transported through the away-pullback identification `awayPullbackIso`. It is the
common codomain conjugation of the three base-change bridges below. Project-local. -/
noncomputable def tripleOverlapSections (d r : ℕ) (I J K : Finset (Fin r)) (hI : I.card = d)
    (hJ : J.card = d) (hK : K.card = d) :
    CommRingCat.of (Localization.Away (minorDet d r I J hI hJ * minorDet d r I K hI hK)) ⟶
      Γ(Limits.pullback (chartIncl d r I J hI hJ) (chartIncl d r I K hI hK), ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫
    Scheme.Hom.appTop
      (awayPullbackIso (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).hom

/-- **First-projection bridge to `awayInclLeft`** (`lem:gr_baseChange_bridge_left`): the
global-sections base-change map of the first projection `p^{IJ}_{IJK} : V_IJK ⟶ U^I_J`,
transported through the affine identifications, is the ring homomorphism
`awayInclLeft (P^I_J) (P^I_K)`. Project-local. -/
lemma baseChange_bridge_left (d r : ℕ) (I J K : Finset (Fin r)) (hI : I.card = d)
    (hJ : J.card = d) (hK : K.card = d) :
    (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (minorDet d r I J hI hJ)))).inv ≫
        Scheme.Hom.appTop
          (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r I J hI hJ))))
          (Limits.pullback.fst (chartIncl d r I J hI hJ) (chartIncl d r I K hI hK))
      = CommRingCat.ofHom (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)) ≫
        tripleOverlapSections d r I J K hI hJ hK := by
  have hfst : (awayPullbackIso (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).inv ≫
        Limits.pullback.fst (chartIncl d r I J hI hJ) (chartIncl d r I K hI hK)
      = Spec.map (CommRingCat.ofHom
          (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK))) :=
    awayPullbackIso_inv_fst _ _
  have hp : Limits.pullback.fst (chartIncl d r I J hI hJ) (chartIncl d r I K hI hK)
      = (awayPullbackIso (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).hom ≫
        Spec.map (CommRingCat.ofHom
          (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK))) :=
    (Iso.inv_comp_eq _).mp hfst
  rw [hp, Scheme.Hom.comp_appTop]
  -- term-mode reassociation (positional `rw [← Category.assoc]` misses the comp node: the
  -- middle-object representation differs across the `pullback (chartIncl …)` defeq)
  exact (Category.assoc _ _ _).symm.trans ((congrArg
    (· ≫ Scheme.Hom.appTop
      (awayPullbackIso (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).hom)
    (baseChange_bridge_gammaSpec (CommRingCat.ofHom
      (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK))))).trans
    (Category.assoc _ _ _))

/-- **Second-projection bridge to `awayInclRight`** (`lem:gr_baseChange_bridge_right`): the
global-sections base-change map of the second projection `p^{IK}_{IJK} : V_IJK ⟶ U^I_K`,
transported through the affine identifications, is the ring homomorphism
`awayInclRight (P^I_J) (P^I_K)`. Project-local. -/
lemma baseChange_bridge_right (d r : ℕ) (I J K : Finset (Fin r)) (hI : I.card = d)
    (hJ : J.card = d) (hK : K.card = d) :
    (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (minorDet d r I K hI hK)))).inv ≫
        Scheme.Hom.appTop
          (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r I K hI hK))))
          (Limits.pullback.snd (chartIncl d r I J hI hJ) (chartIncl d r I K hI hK))
      = CommRingCat.ofHom (awayInclRight (minorDet d r I J hI hJ) (minorDet d r I K hI hK)) ≫
        tripleOverlapSections d r I J K hI hJ hK := by
  have hsnd : (awayPullbackIso (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).inv ≫
        Limits.pullback.snd (chartIncl d r I J hI hJ) (chartIncl d r I K hI hK)
      = Spec.map (CommRingCat.ofHom
          (awayInclRight (minorDet d r I J hI hJ) (minorDet d r I K hI hK))) :=
    awayPullbackIso_inv_snd _ _
  have hp : Limits.pullback.snd (chartIncl d r I J hI hJ) (chartIncl d r I K hI hK)
      = (awayPullbackIso (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).hom ≫
        Spec.map (CommRingCat.ofHom
          (awayInclRight (minorDet d r I J hI hJ) (minorDet d r I K hI hK))) :=
    (Iso.inv_comp_eq _).mp hsnd
  rw [hp, Scheme.Hom.comp_appTop]
  -- term-mode reassociation (see `baseChange_bridge_left`)
  exact (Category.assoc _ _ _).symm.trans ((congrArg
    (· ≫ Scheme.Hom.appTop
      (awayPullbackIso (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).hom)
    (baseChange_bridge_gammaSpec (CommRingCat.ofHom
      (awayInclRight (minorDet d r I J hI hJ) (minorDet d r I K hI hK))))).trans
    (Category.assoc _ _ _))

/-- **Triple-transition bridge to `Θ_{IJ}`** (`lem:gr_baseChange_bridge_transition`): the
global-sections base-change map of the composite `t'_{IJK} ≫ p^{JK}_{JKI} : V_IJK ⟶ U^J_K`,
transported through the affine identifications, is the localised cocycle homomorphism
`Θ_{IJ} ∘ awayInclRight (P^J_I) (P^J_K)` — exactly the composite over which the matrix
cocycle L1 (`bundleTransition_cocycle_matrix`) takes the `(J,K)`-Cramer inverse. The
order-swap `awayMulCommEquiv` of `chartTransition'` is absorbed by
`awayMulCommEquiv_comp_awayInclLeft`. Project-local. -/
lemma baseChange_bridge_transition (d r : ℕ) (I J K : Finset (Fin r)) (hI : I.card = d)
    (hJ : J.card = d) (hK : K.card = d) :
    (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away (minorDet d r J K hJ hK)))).inv ≫
        Scheme.Hom.appTop
          (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r J K hJ hK))))
          (chartTransition' d r I J K hI hJ hK ≫
            Limits.pullback.fst (chartIncl d r J K hJ hK) (chartIncl d r J I hJ hI))
      = CommRingCat.ofHom ((cocycleΘIJ d r I J K hI hJ hK).comp
          (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK))) ≫
        tripleOverlapSections d r I J K hI hJ hK := by
  have hfst : (awayPullbackIso (minorDet d r J K hJ hK) (minorDet d r J I hJ hI)).inv ≫
        Limits.pullback.fst (chartIncl d r J K hJ hK) (chartIncl d r J I hJ hI)
      = Spec.map (CommRingCat.ofHom
          (awayInclLeft (minorDet d r J K hJ hK) (minorDet d r J I hJ hI))) :=
    awayPullbackIso_inv_fst _ _
  have hp : chartTransition' d r I J K hI hJ hK ≫
        Limits.pullback.fst (chartIncl d r J K hJ hK) (chartIncl d r J I hJ hI)
      = (awayPullbackIso (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).hom ≫
        Spec.map (CommRingCat.ofHom ((cocycleΘIJ d r I J K hI hJ hK).comp
          (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK)))) := by
    rw [chartTransition']
    simp only [Category.assoc]
    -- `erw` (defeq matching) to fire the fst-leg lemma through the `HasPullback` instance
    -- diamond on the heavy localisation objects (the Cells `chartTransition'_fac` precedent)
    erw [hfst]
    -- collapse the three `Spec.map`s in a fresh homogeneous `have` (positional `rw` cannot
    -- see the `Spec.map ≫ Spec.map` nodes after the erw), then transport by `congrArg`
    have htail : Spec.map (CommRingCat.ofHom (cocycleΘIJ d r I J K hI hJ hK)) ≫
          Spec.map (CommRingCat.ofHom
            (awayMulCommEquiv (minorDet d r J K hJ hK) (minorDet d r J I hJ hI)).toRingHom) ≫
          Spec.map (CommRingCat.ofHom
            (awayInclLeft (minorDet d r J K hJ hK) (minorDet d r J I hJ hI)))
        = Spec.map (CommRingCat.ofHom ((cocycleΘIJ d r I J K hI hJ hK).comp
            (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK)))) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp, awayMulCommEquiv_comp_awayInclLeft]
    exact congrArg
      ((awayPullbackIso (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).hom ≫ ·) htail
  -- `rw [hp]` cannot find the composite under `appTop` (comp-node instance mismatch);
  -- transport by `congrArg` instead, then proceed as in `baseChange_bridge_left`.
  refine (congrArg (fun m => (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
    (minorDet d r J K hJ hK)))).inv ≫ Scheme.Hom.appTop m) hp).trans ?_
  rw [Scheme.Hom.comp_appTop]
  -- term-mode reassociation (see `baseChange_bridge_left`)
  exact (Category.assoc _ _ _).symm.trans ((congrArg
    (· ≫ Scheme.Hom.appTop
      (awayPullbackIso (minorDet d r I J hI hJ) (minorDet d r I K hI hK)).hom)
    (baseChange_bridge_gammaSpec (CommRingCat.ofHom ((cocycleΘIJ d r I J K hI hJ hK).comp
      (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK)))))).trans
    (Category.assoc _ _ _))

/-- **Base-change bridge to the localised cocycle, matrix form** (`lem:gr_baseChange_bridge`):
over the triple overlap `V_IJK` the three geometrically base-changed Cramer inverses satisfy
the multiplicative cocycle. The three projection bridges rewrite each base-changed matrix as
the σ-image (`tripleOverlapSections`) of the corresponding L1 matrix, and the matrix-level
cocycle `bundleTransition_cocycle_matrix` transports along the ring homomorphism σ.
Project-local — this is the (b)-step of the bundle cocycle. -/
theorem baseChange_bridge (d r : ℕ) (I J K : Finset (Fin r)) (hI : I.card = d)
    (hJ : J.card = d) (hK : K.card = d) :
    (CommRingCat.Hom.hom (Scheme.Hom.appTop
          (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r J K hJ hK))))
          (chartTransition' d r I J K hI hJ hK ≫
            Limits.pullback.fst (chartIncl d r J K hJ hK) (chartIncl d r J I hJ hI)))).mapMatrix
        ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
            (minorDet d r J K hJ hK)))).inv.hom.mapMatrix (universalMinorInv d r J K hJ hK))
      * (CommRingCat.Hom.hom (Scheme.Hom.appTop
            (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r I J hI hJ))))
            (Limits.pullback.fst (chartIncl d r I J hI hJ)
              (chartIncl d r I K hI hK)))).mapMatrix
          ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
              (minorDet d r I J hI hJ)))).inv.hom.mapMatrix (universalMinorInv d r I J hI hJ))
      = (CommRingCat.Hom.hom (Scheme.Hom.appTop
            (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r I K hI hK))))
            (Limits.pullback.snd (chartIncl d r I J hI hJ)
              (chartIncl d r I K hI hK)))).mapMatrix
          ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
              (minorDet d r I K hI hK)))).inv.hom.mapMatrix
            (universalMinorInv d r I K hI hK)) := by
  have hL := congrArg CommRingCat.Hom.hom (baseChange_bridge_left d r I J K hI hJ hK)
  have hR := congrArg CommRingCat.Hom.hom (baseChange_bridge_right d r I J K hI hJ hK)
  have hT := congrArg CommRingCat.Hom.hom (baseChange_bridge_transition d r I J K hI hJ hK)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at hL hR hT
  -- collapse the iterated `mapMatrix`s into single `Matrix.map`s along composite ring homs,
  -- rewrite the composites through the three bridges, and split off the σ-factor
  simp only [RingHom.mapMatrix_apply, Matrix.map_map, ← RingHom.coe_comp, hL, hR, hT]
  -- split off exactly the outer σ-layer of each factor, recombine the product under σ, and
  -- close by the matrix cocycle L1; a `calc` keeps every sub-goal freshly elaborated (the
  -- carrier representations `↥(of R)` vs `R` block positional `rw` on the simp-produced goal)
  calc (universalMinorInv d r J K hJ hK).map
          ⇑((CommRingCat.Hom.hom (tripleOverlapSections d r I J K hI hJ hK)).comp
            ((cocycleΘIJ d r I J K hI hJ hK).comp
              (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK)))) *
        (universalMinorInv d r I J hI hJ).map
          ⇑((CommRingCat.Hom.hom (tripleOverlapSections d r I J K hI hJ hK)).comp
            (awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK)))
      = ((universalMinorInv d r J K hJ hK).map
            ⇑((cocycleΘIJ d r I J K hI hJ hK).comp
              (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK)))).map
            ⇑(CommRingCat.Hom.hom (tripleOverlapSections d r I J K hI hJ hK)) *
        ((universalMinorInv d r I J hI hJ).map
            ⇑(awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK))).map
            ⇑(CommRingCat.Hom.hom (tripleOverlapSections d r I J K hI hJ hK)) := by
        simp only [RingHom.coe_comp, Matrix.map_map]
    _ = ((universalMinorInv d r J K hJ hK).map
            ⇑((cocycleΘIJ d r I J K hI hJ hK).comp
              (awayInclRight (minorDet d r J I hJ hI) (minorDet d r J K hJ hK))) *
          (universalMinorInv d r I J hI hJ).map
            ⇑(awayInclLeft (minorDet d r I J hI hJ) (minorDet d r I K hI hK))).map
            ⇑(CommRingCat.Hom.hom (tripleOverlapSections d r I J K hI hJ hK)) :=
        Matrix.map_mul.symm
    _ = ((universalMinorInv d r I K hI hK).map
            ⇑(awayInclRight (minorDet d r I J hI hJ) (minorDet d r I K hI hK))).map
            ⇑(CommRingCat.Hom.hom (tripleOverlapSections d r I J K hI hJ hK)) :=
        congrArg (fun N => N.map
            ⇑(CommRingCat.Hom.hom (tripleOverlapSections d r I J K hI hJ hK)))
          (bundleTransition_cocycle_matrix d r I J K hI hJ hK)
    _ = (universalMinorInv d r I K hI hK).map
          ⇑((CommRingCat.Hom.hom (tripleOverlapSections d r I J K hI hJ hK)).comp
            (awayInclRight (minorDet d r I J hI hJ) (minorDet d r I K hI hK))) := by
        simp only [RingHom.coe_comp, Matrix.map_map]

set_option maxHeartbeats 1600000 in
-- The endpoint-cast collapses rewrite under the `X.Modules` diamond on the heavy
-- triple-overlap localisation objects; the raised limit covers the `isDefEq` cost
-- (the Cells `chartTransition'_fac` precedent).
/-- **Transport and endpoint alignment of the bundle transitions (the hom-level C2)**
(`lem:gr_bundleCocycle_transport`): the underlying-morphism form of the triple-overlap
multiplicativity. Each of the three base-change transports expands, via the abstract core
`pullbackBaseChangeTransport_matrixToFreeIso`, into `Q ≫ matrixEnd(base-changed Cramer
inverse) ≫ Q⁻¹`; the `pullbackCongr` endpoint casts collapse against the free-pullback
comparisons (`pullbackFreeIso_inv_congr_hom` etc., all generic-`subst` lemmas), the two
matrix endomorphisms fuse by `matrixEnd_comp`, and the resulting matrix identity is
exactly the base-change bridge `baseChange_bridge` (b), i.e. the σ-image of the matrix
cocycle L1. -/
theorem bundleTransition_cocycle_transport (d r : ℕ) (I J K : (theGlueData d r).J) :
    (Scheme.Modules.pullbackBaseChangeTransport
        (Limits.pullback.fst ((theGlueData d r).f I J) ((theGlueData d r).f I K))
        ((theGlueData d r).f I J) ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)
        (bundleTransitionData d r I J)).hom ≫
      ((Scheme.Modules.pullbackCongr
          (Scheme.Modules.glueData_bridge_mid (theGlueData d r) I J K)).app
        (SheafOfModules.free (R := ((theGlueData d r).U J).ringCatSheaf) (Fin d))).hom ≫
      (Scheme.Modules.pullbackBaseChangeTransport
        ((theGlueData d r).t' I J K ≫
          Limits.pullback.fst ((theGlueData d r).f J K) ((theGlueData d r).f J I))
        ((theGlueData d r).f J K) ((theGlueData d r).t J K ≫ (theGlueData d r).f K J)
        (bundleTransitionData d r J K)).hom ≫
      ((Scheme.Modules.pullbackCongr
          (Scheme.Modules.glueData_bridge_tgt (theGlueData d r) I J K)).app
        (SheafOfModules.free (R := ((theGlueData d r).U K).ringCatSheaf) (Fin d))).hom
    = ((Scheme.Modules.pullbackCongr
          (Scheme.Modules.glueData_bridge_src (theGlueData d r) I J K)).app
        (SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d))).hom ≫
      (Scheme.Modules.pullbackBaseChangeTransport
        (Limits.pullback.snd ((theGlueData d r).f I J) ((theGlueData d r).f I K))
        ((theGlueData d r).f I K) ((theGlueData d r).t I K ≫ (theGlueData d r).f K I)
        (bundleTransitionData d r I K)).hom := by
  -- (1) expand the three transports via the abstract core (term-mode `have`s; the `g`-argument
  -- `bundleTransitionData` is defeq to the `pullbackFreeIso ≪≫ matrixToFreeIso ≪≫ symm` shape)
  have eIJ : (Scheme.Modules.pullbackBaseChangeTransport
        (Limits.pullback.fst ((theGlueData d r).f I J) ((theGlueData d r).f I K))
        ((theGlueData d r).f I J) ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)
        (bundleTransitionData d r I J)).hom
      = (Scheme.Modules.pullbackFreeIso (Limits.pullback.fst ((theGlueData d r).f I J)
            ((theGlueData d r).f I K) ≫ (theGlueData d r).f I J) (Fin d)).hom ≫
        matrixEnd ((CommRingCat.Hom.hom (Scheme.Hom.appTop
            (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
            (Limits.pullback.fst ((theGlueData d r).f I J)
              ((theGlueData d r).f I K)))).mapMatrix
          ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
              (minorDet d r I.1 J.1 I.2 J.2)))).inv.hom.mapMatrix
            (universalMinorInv d r I.1 J.1 I.2 J.2))) ≫
        (Scheme.Modules.pullbackFreeIso (Limits.pullback.fst ((theGlueData d r).f I J)
            ((theGlueData d r).f I K) ≫ ((theGlueData d r).t I J ≫ (theGlueData d r).f J I))
            (Fin d)).inv :=
    pullbackBaseChangeTransport_matrixToFreeIso _ _ _ _ _ _ _
  have eJK : (Scheme.Modules.pullbackBaseChangeTransport
        ((theGlueData d r).t' I J K ≫
          Limits.pullback.fst ((theGlueData d r).f J K) ((theGlueData d r).f J I))
        ((theGlueData d r).f J K) ((theGlueData d r).t J K ≫ (theGlueData d r).f K J)
        (bundleTransitionData d r J K)).hom
      = (Scheme.Modules.pullbackFreeIso (((theGlueData d r).t' I J K ≫
            Limits.pullback.fst ((theGlueData d r).f J K) ((theGlueData d r).f J I)) ≫
            (theGlueData d r).f J K) (Fin d)).hom ≫
        matrixEnd ((CommRingCat.Hom.hom (Scheme.Hom.appTop
            (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r J.1 K.1 J.2 K.2))))
            ((theGlueData d r).t' I J K ≫
              Limits.pullback.fst ((theGlueData d r).f J K)
                ((theGlueData d r).f J I)))).mapMatrix
          ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
              (minorDet d r J.1 K.1 J.2 K.2)))).inv.hom.mapMatrix
            (universalMinorInv d r J.1 K.1 J.2 K.2))) ≫
        (Scheme.Modules.pullbackFreeIso (((theGlueData d r).t' I J K ≫
            Limits.pullback.fst ((theGlueData d r).f J K) ((theGlueData d r).f J I)) ≫
            ((theGlueData d r).t J K ≫ (theGlueData d r).f K J)) (Fin d)).inv :=
    pullbackBaseChangeTransport_matrixToFreeIso _ _ _ _ _ _ _
  have eIK : (Scheme.Modules.pullbackBaseChangeTransport
        (Limits.pullback.snd ((theGlueData d r).f I J) ((theGlueData d r).f I K))
        ((theGlueData d r).f I K) ((theGlueData d r).t I K ≫ (theGlueData d r).f K I)
        (bundleTransitionData d r I K)).hom
      = (Scheme.Modules.pullbackFreeIso (Limits.pullback.snd ((theGlueData d r).f I J)
            ((theGlueData d r).f I K) ≫ (theGlueData d r).f I K) (Fin d)).hom ≫
        matrixEnd ((CommRingCat.Hom.hom (Scheme.Hom.appTop
            (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 K.1 I.2 K.2))))
            (Limits.pullback.snd ((theGlueData d r).f I J)
              ((theGlueData d r).f I K)))).mapMatrix
          ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
              (minorDet d r I.1 K.1 I.2 K.2)))).inv.hom.mapMatrix
            (universalMinorInv d r I.1 K.1 I.2 K.2))) ≫
        (Scheme.Modules.pullbackFreeIso (Limits.pullback.snd ((theGlueData d r).f I J)
            ((theGlueData d r).f I K) ≫ ((theGlueData d r).t I K ≫ (theGlueData d r).f K I))
            (Fin d)).inv :=
    pullbackBaseChangeTransport_matrixToFreeIso _ _ _ _ _ _ _
  -- (2) the base-change bridge (b), restated over the glue-datum phrasing (defeq)
  have hbridge : (CommRingCat.Hom.hom (Scheme.Hom.appTop
          (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r J.1 K.1 J.2 K.2))))
          ((theGlueData d r).t' I J K ≫
            Limits.pullback.fst ((theGlueData d r).f J K)
              ((theGlueData d r).f J I)))).mapMatrix
        ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
            (minorDet d r J.1 K.1 J.2 K.2)))).inv.hom.mapMatrix
          (universalMinorInv d r J.1 K.1 J.2 K.2))
      * (CommRingCat.Hom.hom (Scheme.Hom.appTop
            (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
            (Limits.pullback.fst ((theGlueData d r).f I J)
              ((theGlueData d r).f I K)))).mapMatrix
          ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
              (minorDet d r I.1 J.1 I.2 J.2)))).inv.hom.mapMatrix
            (universalMinorInv d r I.1 J.1 I.2 J.2))
      = (CommRingCat.Hom.hom (Scheme.Hom.appTop
            (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 K.1 I.2 K.2))))
            (Limits.pullback.snd ((theGlueData d r).f I J)
              ((theGlueData d r).f I K)))).mapMatrix
          ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
              (minorDet d r I.1 K.1 I.2 K.2)))).inv.hom.mapMatrix
            (universalMinorInv d r I.1 K.1 I.2 K.2)) :=
    baseChange_bridge d r I.1 J.1 K.1 I.2 J.2 K.2
  -- (3) expand, collapse the endpoint casts, fuse the matrix endomorphisms, apply (b)
  rw [eIJ, eJK, eIK]
  simp only [Category.assoc]
  rw [Scheme.Modules.pullbackFreeIso_inv_congr_hom_assoc
      (Scheme.Modules.glueData_bridge_mid (theGlueData d r) I J K) (Fin d),
    Scheme.Modules.pullbackCongr_hom_app_free_assoc
      (Scheme.Modules.glueData_bridge_src (theGlueData d r) I J K) (Fin d),
    Scheme.Modules.pullbackFreeIso_inv_congr
      (Scheme.Modules.glueData_bridge_tgt (theGlueData d r) I J K) (Fin d)]
  -- (4) fuse the two matrix endomorphisms and apply the bridge, in a fresh `have` (the
  -- mixed-provenance comp nodes block positional `rw` with `matrixEnd_comp` on the main goal)
  have hfuse : matrixEnd ((CommRingCat.Hom.hom (Scheme.Hom.appTop
          (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
          (Limits.pullback.fst ((theGlueData d r).f I J)
            ((theGlueData d r).f I K)))).mapMatrix
        ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
            (minorDet d r I.1 J.1 I.2 J.2)))).inv.hom.mapMatrix
          (universalMinorInv d r I.1 J.1 I.2 J.2))) ≫
      matrixEnd ((CommRingCat.Hom.hom (Scheme.Hom.appTop
          (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r J.1 K.1 J.2 K.2))))
          ((theGlueData d r).t' I J K ≫
            Limits.pullback.fst ((theGlueData d r).f J K)
              ((theGlueData d r).f J I)))).mapMatrix
        ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
            (minorDet d r J.1 K.1 J.2 K.2)))).inv.hom.mapMatrix
          (universalMinorInv d r J.1 K.1 J.2 K.2))) ≫
      (Scheme.Modules.pullbackFreeIso (Limits.pullback.snd ((theGlueData d r).f I J)
          ((theGlueData d r).f I K) ≫ ((theGlueData d r).t I K ≫ (theGlueData d r).f K I))
          (Fin d)).inv
    = matrixEnd ((CommRingCat.Hom.hom (Scheme.Hom.appTop
          (Y := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 K.1 I.2 K.2))))
          (Limits.pullback.snd ((theGlueData d r).f I J)
            ((theGlueData d r).f I K)))).mapMatrix
        ((Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
            (minorDet d r I.1 K.1 I.2 K.2)))).inv.hom.mapMatrix
          (universalMinorInv d r I.1 K.1 I.2 K.2))) ≫
      (Scheme.Modules.pullbackFreeIso (Limits.pullback.snd ((theGlueData d r).f I J)
          ((theGlueData d r).f I K) ≫ ((theGlueData d r).t I K ≫ (theGlueData d r).f K I))
          (Fin d)).inv :=
    -- term-mode: positional `rw [← Category.assoc]` grabs the scheme-level composite inside
    -- `pullbackFreeIso`'s argument instead of the Modules-level chain
    (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ (Scheme.Modules.pullbackFreeIso
          (Limits.pullback.snd ((theGlueData d r).f I J) ((theGlueData d r).f I K) ≫
            ((theGlueData d r).t I K ≫ (theGlueData d r).f K I)) (Fin d)).inv)
        ((matrixEnd_comp _ _).trans (congrArg matrixEnd hbridge)))
  exact congrArg ((Scheme.Modules.pullbackFreeIso (Limits.pullback.fst ((theGlueData d r).f I J)
    ((theGlueData d r).f I K) ≫ (theGlueData d r).f I J) (Fin d)).hom ≫ ·) hfuse

set_option maxHeartbeats 1600000 in
-- the `Iso.ext`-reduction unifies the inferred `.app _` instances with the transport
-- statement across the `X.Modules` diamond; the raised limit covers the `whnf` cost
/-- **Triple-overlap multiplicativity of the bundle transition (C2)**
(`lem:gr_bundleCocycle_mul`): over each triple overlap the base-change transports of the
three bundle transitions satisfy `ĝ_{JK} ∘ ĝ_{IJ} = ĝ_{IK}`, in the form required by
`Scheme.Modules.glue` — the exact `_hC2` hypothesis instantiated at `theGlueData d r` and
`bundleTransitionData`. At the matrix level this is the Cramer-inverse cocycle
`(X^J_K)⁻¹ (X^I_J)⁻¹ = (X^I_K)⁻¹` (`bundleTransition_cocycle_matrix`); the transport to the
common triple overlap and the endpoint alignment are `bundleTransition_cocycle_transport`. -/
theorem bundleTransition_cocycle (d r : ℕ) (I J K : (theGlueData d r).J) :
    Scheme.Modules.pullbackBaseChangeTransport
        (Limits.pullback.fst ((theGlueData d r).f I J) ((theGlueData d r).f I K))
        ((theGlueData d r).f I J) ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)
        (bundleTransitionData d r I J) ≪≫
      (Scheme.Modules.pullbackCongr
          (Scheme.Modules.glueData_bridge_mid (theGlueData d r) I J K)).app _ ≪≫
      Scheme.Modules.pullbackBaseChangeTransport
        ((theGlueData d r).t' I J K ≫
          Limits.pullback.fst ((theGlueData d r).f J K) ((theGlueData d r).f J I))
        ((theGlueData d r).f J K) ((theGlueData d r).t J K ≫ (theGlueData d r).f K J)
        (bundleTransitionData d r J K) ≪≫
      (Scheme.Modules.pullbackCongr
          (Scheme.Modules.glueData_bridge_tgt (theGlueData d r) I J K)).app _
    = (Scheme.Modules.pullbackCongr
          (Scheme.Modules.glueData_bridge_src (theGlueData d r) I J K)).app _ ≪≫
      Scheme.Modules.pullbackBaseChangeTransport
        (Limits.pullback.snd ((theGlueData d r).f I J) ((theGlueData d r).f I K))
        ((theGlueData d r).f I K) ((theGlueData d r).t I K ≫ (theGlueData d r).f K I)
        (bundleTransitionData d r I K) := by
  -- Reduce the iso-level cocycle to the underlying morphism equality of free sheaves over
  -- the triple overlap `V_IJK`; that equality is `bundleTransition_cocycle_transport`.
  apply Iso.ext
  simp only [Iso.trans_hom]
  exact bundleTransition_cocycle_transport d r I J K

/-! ## The universal quotient sheaf and the tautological quotient -/

/-- The **universal quotient sheaf** `U` on `Gr(d,r)` (`def:gr_universal_quotient_sheaf`):
the rank-`d` locally free sheaf obtained by gluing the free rank-`d` chart sheaves
`O_{U^I}^d` along the bundle transition cocycle `g_{I,J} = (X^I_J)⁻¹`, via the descent
equalizer `Scheme.Modules.glue`. The (C1) self-identity is `bundleTransition_self` and the
(C2) triple-overlap multiplicativity is `bundleTransition_cocycle`. -/
noncomputable def universalQuotient (d r : ℕ) : (scheme d r).Modules :=
  Scheme.Modules.glue (theGlueData d r)
    (fun I => SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d))
    (bundleTransitionData d r)
    (fun I => bundleTransition_self d r I.1 I.2)
    (fun I J K => bundleTransition_cocycle d r I J K)

/-- The per-chart component of the tautological quotient: the adjoint transpose, along the
chart immersion `ι_I`, of the chart quotient `u^I` (`chartQuotientMap`) precomposed with
the free-pullback comparison `pullbackFreeIso (ι_I)`. Project-local helper for
`tautologicalQuotient`. -/
noncomputable def tautologicalQuotientComponent (d r : ℕ) (I : (theGlueData d r).J) :
    SheafOfModules.free (R := (scheme d r).ringCatSheaf) (Fin r) ⟶
      (Scheme.Modules.pushforward ((theGlueData d r).ι I)).obj
        (SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d)) :=
  (Scheme.Modules.pullbackPushforwardAdjunction ((theGlueData d r).ι I)).homEquiv _ _
    ((Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).hom ≫
      chartQuotientMap d r I.1 I.2)

set_option maxHeartbeats 1600000 in
-- The `Q`-cancellation rewrites and the final matrix comparison run under the
-- `X.Modules` diamond on the heavy localisation objects; the raised limit covers the
-- `isDefEq` cost (the `bundleTransition_cocycle_transport` precedent).
/-- **Overlap compatibility of the tautological quotient**
(`lem:gr_tautologicalQuotient_overlap`): the pullback-level identity
`g_{I,J} ∘ f_{IJ}^* u^I = (t_{IJ} ≫ f_{JI})^* u^J` on the overlap `U^I_J`, in the exact
transposed form produced by `tautologicalQuotientComponent_transpose`. Both sides reduce,
through the free-pullback comparisons (`pullbackComp_inv_app_free_map`,
`pullbackCongr_inv_app_free`) and the rectangular base-change naturality
(`matrixEndRect_pullback`), to `Q ≫ matrixEndRect(—) ≫ Q⁻¹` normal forms; the
square-after-rectangular fusion `matrixEndRect_comp` and the matrix identity
`X^I_J · ((X^I_J)⁻¹ X^I) = X^I` (`universalMinorInv_mul_cancel`, with
`X^J ↦ (X^I_J)⁻¹ X^I` provided by `universalMatrix_map_transitionPreMap`) close the
comparison. -/
theorem tautologicalQuotient_overlap (d r : ℕ) (I J : (theGlueData d r).J) :
    (Scheme.Modules.pullbackComp ((theGlueData d r).f I J) ((theGlueData d r).ι I)).inv.app
        (SheafOfModules.free (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫
      (Scheme.Modules.pullback ((theGlueData d r).f I J)).map
        ((Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).hom ≫
          chartQuotientMap d r I.1 I.2)
    = (Scheme.Modules.pullbackCongr
          (show ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) ≫ (theGlueData d r).ι J
              = (theGlueData d r).f I J ≫ (theGlueData d r).ι I by
            rw [Category.assoc]; exact (theGlueData d r).glue_condition I J)).inv.app
        (SheafOfModules.free (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫
      (Scheme.Modules.pullbackComp ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)
        ((theGlueData d r).ι J)).inv.app
        (SheafOfModules.free (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫
      (Scheme.Modules.pullback ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).map
        ((Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι J) (Fin r)).hom ≫
          chartQuotientMap d r J.1 J.2) ≫
      (bundleTransitionData d r I J).inv := by
  -- (1) ring-hom collapse of the scheme-level transition composite:
  -- `t_{IJ} ≫ f_{JI} = Spec.map θ̃_{I,J}` (the pre-localisation hom)
  have hcomp_ring : (transitionMap d r I.1 J.1 I.2 J.2).comp
        (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ)
          (Localization.Away (minorDet d r J.1 I.1 J.2 I.2)))
      = (transitionPreMap d r I.1 J.1 I.2 J.2).toRingHom := by
    rw [transitionMap]
    exact IsLocalization.Away.lift_comp _ _
  have heq : (theGlueData d r).t I J ≫ (theGlueData d r).f J I
      = Spec.map (CommRingCat.ofHom (transitionPreMap d r I.1 J.1 I.2 J.2).toRingHom) := by
    -- re-type the composite at the `Spec`-spelled objects so `Spec.map_comp` can match
    -- (the native `chartOverlap` middle object blocks the pattern)
    change Spec.map (CommRingCat.ofHom (transitionMap d r I.1 J.1 I.2 J.2)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ)
            (Localization.Away (minorDet d r J.1 I.1 J.2 I.2)))) = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp_ring]
  -- (2) the two global-sections bridges; the `X :=`/`Y :=` Spec-ascriptions pin the affine
  -- representations (iter-064 load-bearing trick: without them the print-identical defeq
  -- carriers block the `Matrix.map_map` fusions below)
  have hbb : (Scheme.ΓSpecIso (CommRingCat.of
        (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv ≫
        Scheme.Hom.appTop
          (X := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
          (Y := Spec (CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)))
          ((theGlueData d r).f I J)
      = CommRingCat.ofHom (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
          (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))) ≫
        (Scheme.ΓSpecIso (CommRingCat.of
          (Localization.Away (minorDet d r I.1 J.1 I.2 J.2)))).inv :=
    baseChange_bridge_gammaSpec _
  have hbe : (Scheme.ΓSpecIso (CommRingCat.of
        (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ))).inv ≫
        Scheme.Hom.appTop
          (X := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
          (Y := Spec (CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ)))
          ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)
      = CommRingCat.ofHom (transitionPreMap d r I.1 J.1 I.2 J.2).toRingHom ≫
        (Scheme.ΓSpecIso (CommRingCat.of
          (Localization.Away (minorDet d r I.1 J.1 I.2 J.2)))).inv := by
    refine (congrArg (fun m => (Scheme.ΓSpecIso (CommRingCat.of
        (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ))).inv ≫
        Scheme.Hom.appTop
          (X := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
          (Y := Spec (CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ)))
          m) heq).trans ?_
    exact baseChange_bridge_gammaSpec _
  -- (3) matrix forms of the two bridges
  have hBmat : ((universalMatrix d r I.1 I.2).map
        ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv)).map
        ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
          (X := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
          (Y := Spec (CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)))
          ((theGlueData d r).f I J)))
      = ((universalMatrix d r I.1 I.2).map
          (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
            (Localization.Away (minorDet d r I.1 J.1 I.2 J.2)))).map
        ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (Localization.Away (minorDet d r I.1 J.1 I.2 J.2)))).inv) := by
    have h := congrArg CommRingCat.Hom.hom hbb
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h
    rw [Matrix.map_map, Matrix.map_map, ← RingHom.coe_comp, ← RingHom.coe_comp, h]
  have hEmat : ((universalMatrix d r J.1 J.2).map
        ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ))).inv)).map
        ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
          (X := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
          (Y := Spec (CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ)))
          ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)))
      = (imageMatrix d r I.1 J.1 I.2 J.2).map
        ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (Localization.Away (minorDet d r I.1 J.1 I.2 J.2)))).inv) := by
    have h := congrArg CommRingCat.Hom.hom hbe
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at h
    -- the Cells identity, restated with the `RingHom`-coercion of the `AlgHom` (defeq,
    -- absorbed by the `have` check — the `⇑↑f` coercion bridge blocks a positional rw)
    have hXJ : (universalMatrix d r J.1 J.2).map
          ⇑(transitionPreMap d r I.1 J.1 I.2 J.2).toRingHom
        = imageMatrix d r I.1 J.1 I.2 J.2 :=
      universalMatrix_map_transitionPreMap d r I.1 J.1 I.2 J.2
    rw [Matrix.map_map, ← RingHom.coe_comp, h, RingHom.coe_comp, ← Matrix.map_map, hXJ]
  -- (4) the matrix-level overlap identity `X^I_J · ((X^I_J)⁻¹ X^I) = X^I` over `R^I_J`,
  -- σ-transported to the overlap's global sections
  have hmin_img : universalMinor d r I.1 J.1 I.2 J.2 * imageMatrix d r I.1 J.1 I.2 J.2
      = (universalMatrix d r I.1 I.2).map
          (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
            (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))) := by
    rw [imageMatrix]
    -- term-mode reassociation (the heterogeneous rectangular `HMul` blocks a
    -- positional `rw [← Matrix.mul_assoc]`)
    calc universalMinor d r I.1 J.1 I.2 J.2 * (universalMinorInv d r I.1 J.1 I.2 J.2 *
          (universalMatrix d r I.1 I.2).map
            (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
              (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
        = (universalMinor d r I.1 J.1 I.2 J.2 * universalMinorInv d r I.1 J.1 I.2 J.2) *
          (universalMatrix d r I.1 I.2).map
            (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
              (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))) :=
          (Matrix.mul_assoc _ _ _).symm
      _ = (universalMatrix d r I.1 I.2).map
            (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
              (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))) := by
          rw [(universalMinorInv_mul_cancel d r I.1 J.1 I.2 J.2).2, Matrix.one_mul]
  have hmat : (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
        (minorDet d r I.1 J.1 I.2 J.2)))).inv).mapMatrix (universalMinor d r I.1 J.1 I.2 J.2)
      * (imageMatrix d r I.1 J.1 I.2 J.2).map
        ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
          (minorDet d r I.1 J.1 I.2 J.2)))).inv)
      = ((universalMatrix d r I.1 I.2).map
          (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
            (Localization.Away (minorDet d r I.1 J.1 I.2 J.2)))).map
        ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
          (minorDet d r I.1 J.1 I.2 J.2)))).inv) := by
    rw [RingHom.mapMatrix_apply, ← Matrix.map_mul, hmin_img]
  -- (5) per-chart pullback expansions (`matrixEndRect_pullback` in glue-datum phrasing;
  -- the chartIncl↔`(theGlueData).f` defeq is absorbed by the `have` checks)
  have h2 : (Scheme.Modules.pullback ((theGlueData d r).f I J)).map
        (chartQuotientMap d r I.1 I.2)
      = (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin r)).hom ≫
        matrixEndRect (((universalMatrix d r I.1 I.2).map
            ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
              (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv)).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
            (X := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
            (Y := Spec (CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)))
            ((theGlueData d r).f I J)))) ≫
        (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin d)).inv := by
    rw [chartQuotientMap_eq_matrixEndRect]
    exact matrixEndRect_pullback _ _
  have h5 : (Scheme.Modules.pullback ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).map
        (chartQuotientMap d r J.1 J.2)
      = (Scheme.Modules.pullbackFreeIso
          ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) (Fin r)).hom ≫
        matrixEndRect (((universalMatrix d r J.1 J.2).map
            ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
              (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ))).inv)).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
            (X := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
            (Y := Spec (CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ)))
            ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)))) ≫
        (Scheme.Modules.pullbackFreeIso
          ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) (Fin d)).inv := by
    rw [chartQuotientMap_eq_matrixEndRect]
    exact matrixEndRect_pullback _ _
  -- (6) the bundle transition's inverse, in `Q ≫ matrixEnd ≫ Q⁻¹` form
  have h6 : (bundleTransitionData d r I J).inv
      = (Scheme.Modules.pullbackFreeIso
          ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) (Fin d)).hom ≫
        matrixEnd ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
          (minorDet d r I.1 J.1 I.2 J.2)))).inv).mapMatrix
          (universalMinor d r I.1 J.1 I.2 J.2)) ≫
        (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin d)).inv := by
    change (bundleTransition d r I.1 J.1 I.2 J.2).inv = _
    simp only [bundleTransition, Iso.trans_inv, Iso.symm_inv, matrixToFreeIso_inv,
      Category.assoc]
    rfl
  -- (7) collapse each side's `Q⁻¹ ≫ (chart pullback) ≫ …` core to the common
  -- `matrixEndRect(σ X^I-loc) ≫ Q_d⁻¹` normal form (fresh goals — the rewrites fire on
  -- the haves' own spellings, away from the statement's mixed-provenance comp nodes)
  have hLfin : (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin r)).inv ≫
        ((Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin r)).hom ≫
          matrixEndRect (((universalMatrix d r I.1 I.2).map
              ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
                (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv)).map
            ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
              (X := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
              (Y := Spec (CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)))
              ((theGlueData d r).f I J)))) ≫
          (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin d)).inv)
      = matrixEndRect (((universalMatrix d r I.1 I.2).map
            (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
              (Localization.Away (minorDet d r I.1 J.1 I.2 J.2)))).map
          ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
            (minorDet d r I.1 J.1 I.2 J.2)))).inv)) ≫
        (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin d)).inv := by
    -- term-mode: the `Matrix.map` carrier implicit differs between elaboration contexts,
    -- so a positional `rw [hBmat]` cannot match; `congrArg` absorbs it by defeq
    refine (Iso.inv_hom_id_assoc _ _).trans ?_
    exact congrArg (fun m => matrixEndRect m ≫
      (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin d)).inv) hBmat
  have hRfin : (Scheme.Modules.pullbackFreeIso
        ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) (Fin r)).inv ≫
        (((Scheme.Modules.pullbackFreeIso
            ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) (Fin r)).hom ≫
          matrixEndRect (((universalMatrix d r J.1 J.2).map
              ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
                (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ))).inv)).map
            ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop
              (X := Spec (CommRingCat.of (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))))
              (Y := Spec (CommRingCat.of (MvPolynomial (Fin d × {q : Fin r // q ∉ J.1}) ℤ)))
              ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)))) ≫
          (Scheme.Modules.pullbackFreeIso
            ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) (Fin d)).inv) ≫
        ((Scheme.Modules.pullbackFreeIso
            ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) (Fin d)).hom ≫
          matrixEnd ((CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
            (minorDet d r I.1 J.1 I.2 J.2)))).inv).mapMatrix
            (universalMinor d r I.1 J.1 I.2 J.2)) ≫
          (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin d)).inv))
      = matrixEndRect (((universalMatrix d r I.1 I.2).map
            (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
              (Localization.Away (minorDet d r I.1 J.1 I.2 J.2)))).map
          ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of (Localization.Away
            (minorDet d r I.1 J.1 I.2 J.2)))).inv)) ≫
        (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin d)).inv := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    -- term-mode matrix comparison (the `Matrix.map` carrier implicit blocks positional rw)
    refine (matrixEndRect_comp_assoc _ _ _).trans ?_
    exact congrArg (fun m => matrixEndRect m ≫
      (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin d)).inv)
      ((congrArg (fun m => (CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (Localization.Away (minorDet d r I.1 J.1 I.2 J.2)))).inv).mapMatrix
          (universalMinor d r I.1 J.1 I.2 J.2) * m) hEmat).trans hmat)
  -- (8) assemble in pure term-mode (positional `rw`/`simp` cannot reassociate the
  -- statement's mixed-provenance comp nodes under the `X.Modules` diamond)
  have hglue' : ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) ≫ (theGlueData d r).ι J
      = (theGlueData d r).f I J ≫ (theGlueData d r).ι I := by
    rw [Category.assoc]; exact (theGlueData d r).glue_condition I J
  exact ((congrArg ((Scheme.Modules.pullbackComp ((theGlueData d r).f I J)
        ((theGlueData d r).ι I)).inv.app (SheafOfModules.free
          (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫ ·)
        ((Scheme.Modules.pullback ((theGlueData d r).f I J)).map_comp
          (Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).hom
          (chartQuotientMap d r I.1 I.2))).trans <|
    (Scheme.Modules.pullbackComp_inv_app_free_map_assoc
        ((theGlueData d r).f I J) ((theGlueData d r).ι I) (Fin r)
        ((Scheme.Modules.pullback ((theGlueData d r).f I J)).map
          (chartQuotientMap d r I.1 I.2))).trans <|
    (congrArg (fun m => (Scheme.Modules.pullbackFreeIso
        ((theGlueData d r).f I J ≫ (theGlueData d r).ι I) (Fin r)).hom ≫
        (Scheme.Modules.pullbackFreeIso ((theGlueData d r).f I J) (Fin r)).inv ≫ m)
      h2).trans <|
    congrArg ((Scheme.Modules.pullbackFreeIso
        ((theGlueData d r).f I J ≫ (theGlueData d r).ι I) (Fin r)).hom ≫ ·) hLfin).trans
    ((congrArg (fun m => (Scheme.Modules.pullbackCongr hglue').inv.app
          (SheafOfModules.free (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫
          (Scheme.Modules.pullbackComp ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)
            ((theGlueData d r).ι J)).inv.app (SheafOfModules.free
              (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫ m ≫
          (bundleTransitionData d r I J).inv)
        ((Scheme.Modules.pullback ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).map_comp
          (Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι J) (Fin r)).hom
          (chartQuotientMap d r J.1 J.2))).trans <|
      (congrArg (fun m => (Scheme.Modules.pullbackCongr hglue').inv.app
          (SheafOfModules.free (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫
          (Scheme.Modules.pullbackComp ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)
            ((theGlueData d r).ι J)).inv.app (SheafOfModules.free
              (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫ m)
        (Category.assoc
          ((Scheme.Modules.pullback ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).map
            (Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι J) (Fin r)).hom)
          ((Scheme.Modules.pullback ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).map
            (chartQuotientMap d r J.1 J.2))
          (bundleTransitionData d r I J).inv)).trans <|
      (congrArg ((Scheme.Modules.pullbackCongr hglue').inv.app
          (SheafOfModules.free (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫ ·)
        (Scheme.Modules.pullbackComp_inv_app_free_map_assoc
          ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) ((theGlueData d r).ι J) (Fin r)
          ((Scheme.Modules.pullback ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).map
              (chartQuotientMap d r J.1 J.2) ≫
            (bundleTransitionData d r I J).inv))).trans <|
      (Scheme.Modules.pullbackCongr_inv_app_free_assoc hglue' (Fin r)
        ((Scheme.Modules.pullbackFreeIso
            ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) (Fin r)).inv ≫
          (Scheme.Modules.pullback ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).map
            (chartQuotientMap d r J.1 J.2) ≫
          (bundleTransitionData d r I J).inv)).trans <|
      (congrArg (fun m => (Scheme.Modules.pullbackFreeIso
          ((theGlueData d r).f I J ≫ (theGlueData d r).ι I) (Fin r)).hom ≫
          (Scheme.Modules.pullbackFreeIso
            ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) (Fin r)).inv ≫ m)
        (congrArg₂ (· ≫ ·) h5 h6)).trans <|
      congrArg ((Scheme.Modules.pullbackFreeIso
          ((theGlueData d r).f I J ≫ (theGlueData d r).ι I) (Fin r)).hom ≫ ·) hRfin).symm

/-- **Adjunction transpose of the chart-overlap condition**
(`lem:gr_tautologicalQuotientComponent_transpose`): the `(I,J)`-component of the descent
(equalizing) condition consumed by `glueLift` for the family of chart-quotient transposes
`tautologicalQuotientComponent` holds iff the pullback-level identity
`g_{I,J} ∘ f_{IJ}^* u^I = (t_{IJ} ≫ f_{JI})^* u^J` does (all comparisons through the
pseudofunctor casts) — the statement of `tautologicalQuotient_overlap`. Instance of the
generic `Scheme.Modules.glueLift_cond_iff`. -/
theorem tautologicalQuotientComponent_transpose (d r : ℕ) (I J : (theGlueData d r).J) :
    (tautologicalQuotientComponent d r I ≫
        ((Scheme.Modules.pushforward ((theGlueData d r).ι I)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction ((theGlueData d r).f I J)).unit.app
            (SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d))) ≫
        (Scheme.Modules.pushforwardComp ((theGlueData d r).f I J)
          ((theGlueData d r).ι I)).hom.app
          ((Scheme.Modules.pullback ((theGlueData d r).f I J)).obj
            (SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d))))
      = tautologicalQuotientComponent d r J ≫
        ((Scheme.Modules.pushforward ((theGlueData d r).ι J)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).unit.app
            (SheafOfModules.free (R := ((theGlueData d r).U J).ringCatSheaf) (Fin d))) ≫
        (Scheme.Modules.pushforwardComp ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)
          ((theGlueData d r).ι J)).hom.app
          ((Scheme.Modules.pullback ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).obj
            (SheafOfModules.free (R := ((theGlueData d r).U J).ringCatSheaf) (Fin d))) ≫
        (Scheme.Modules.pushforward
          (((theGlueData d r).t I J ≫ (theGlueData d r).f J I) ≫ (theGlueData d r).ι J)).map
          (bundleTransitionData d r I J).inv ≫
        (Scheme.Modules.pushforwardCongr
          (show ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) ≫ (theGlueData d r).ι J
              = (theGlueData d r).f I J ≫ (theGlueData d r).ι I by
            rw [Category.assoc]; exact (theGlueData d r).glue_condition I J)).hom.app
          ((Scheme.Modules.pullback ((theGlueData d r).f I J)).obj
            (SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d)))))
    ↔ ((Scheme.Modules.pullbackComp ((theGlueData d r).f I J) ((theGlueData d r).ι I)).inv.app
          (SheafOfModules.free (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫
        (Scheme.Modules.pullback ((theGlueData d r).f I J)).map
          ((Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).hom ≫
            chartQuotientMap d r I.1 I.2)
      = (Scheme.Modules.pullbackCongr
            (show ((theGlueData d r).t I J ≫ (theGlueData d r).f J I) ≫ (theGlueData d r).ι J
                = (theGlueData d r).f I J ≫ (theGlueData d r).ι I by
              rw [Category.assoc]; exact (theGlueData d r).glue_condition I J)).inv.app
          (SheafOfModules.free (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫
        (Scheme.Modules.pullbackComp ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)
          ((theGlueData d r).ι J)).inv.app
          (SheafOfModules.free (R := ((theGlueData d r).glued).ringCatSheaf) (Fin r)) ≫
        (Scheme.Modules.pullback ((theGlueData d r).t I J ≫ (theGlueData d r).f J I)).map
          ((Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι J) (Fin r)).hom ≫
            chartQuotientMap d r J.1 J.2) ≫
        (bundleTransitionData d r I J).inv) :=
  Scheme.Modules.glueLift_cond_iff (theGlueData d r)
    (fun K => SheafOfModules.free (R := ((theGlueData d r).U K).ringCatSheaf) (Fin d))
    (bundleTransitionData d r)
    (fun K => (Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι K) (Fin r)).hom ≫
      chartQuotientMap d r K.1 K.2) I J

/-- The **tautological quotient** `u : O^r ↠ U` (`def:tautological_quotient`): the global
surjection assembled from the chart quotients `u^I` (`chartQuotientMap`), compatible with
the bundle gluing of `universalQuotient`. Since `universalQuotient` is the descent
equalizer of pushforwards, the morphism is `glueLift` of the per-chart adjoint
transposes (`tautologicalQuotientComponent`); the equalizing condition — the chart
compatibility `g_{IJ} ∘ f_{IJ}^* u^I = (t_{IJ} ≫ f_{JI})^* u^J`, whose matrix content is
`X^J = (X^I_J)⁻¹ X^I` (`universalMatrix_map_transitionPreMap` / `imageMatrix`) — is
`tautologicalQuotient_overlap`, transposed through the adjunction by
`tautologicalQuotientComponent_transpose`. -/
noncomputable def tautologicalQuotient (d r : ℕ) :
    SheafOfModules.free (R := (scheme d r).ringCatSheaf) (Fin r) ⟶ universalQuotient d r :=
  Scheme.Modules.glueLift (theGlueData d r)
    (fun I => SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d))
    (bundleTransitionData d r)
    (fun I => bundleTransition_self d r I.1 I.2)
    (fun I J K => bundleTransition_cocycle d r I J K)
    (fun I => tautologicalQuotientComponent d r I)
    (fun p => (tautologicalQuotientComponent_transpose d r p.1 p.2).mpr
      (tautologicalQuotient_overlap d r p.1 p.2))

/-! ## The functor of points and the universal property

The Grassmannian functor sends a scheme `T` to the set of *equivalence classes* of
rank-`d` quotients `q : O_T^r ↠ F` with `F` locally free of rank `d`. We encode a single
such quotient as the structure `RankQuotient r d T`, the equivalence as `RankQuotient.Rel`
(an isomorphism of the targets commuting with the quotient maps), and the functor's value
at `T` as the quotient `Quotient (rqSetoid r d T)`. The pullback action `rqPullback`
together with `pullbackFreeIso`/`pullback_isLocallyFreeOfRank` (and the fact that the
pullback functor preserves epimorphisms, being a left adjoint) realise functoriality.

Because a sheaf of modules `F : T.Modules` is a large object, this quotient lives in
`Type 1` (not `Type 0` as the original scaffold signature stated); the corrected universe
is the only change to the pinned signature, and it is forced — the substantive content is
unchanged. -/

/-- A **rank-`d` quotient of `O_T^r`** on a scheme `T`: a sheaf of modules `F` on `T`,
locally free of rank `d`, together with an epimorphism `q : O_T^r ↠ F`. This is the
unbundled datum whose equivalence classes form the value of the Grassmannian functor. -/
structure RankQuotient (r d : ℕ) (T : Scheme.{0}) where
  /-- The quotient sheaf. -/
  F : T.Modules
  /-- The quotient map out of the trivial rank-`r` bundle. -/
  q : SheafOfModules.free (R := T.ringCatSheaf) (Fin r) ⟶ F
  /-- The quotient map is an epimorphism (surjective). -/
  epi : Epi q
  /-- The quotient sheaf is locally free of rank `d`. -/
  locFree : SheafOfModules.IsLocallyFreeOfRank F d

/-- Two rank-`d` quotients are **equivalent** when there is an isomorphism of the targets
commuting with the quotient maps (equivalently, when the kernels of the quotient maps
coincide). -/
def RankQuotient.Rel {r d : ℕ} {T : Scheme.{0}} (x y : RankQuotient r d T) : Prop :=
  ∃ f : x.F ≅ y.F, x.q ≫ f.hom = y.q

lemma RankQuotient.rel_refl {r d : ℕ} {T : Scheme.{0}} (x : RankQuotient r d T) : x.Rel x :=
  ⟨Iso.refl _, Category.comp_id _⟩

lemma RankQuotient.rel_symm {r d : ℕ} {T : Scheme.{0}} {x y : RankQuotient r d T}
    (h : x.Rel y) : y.Rel x := by
  obtain ⟨f, hf⟩ := h
  exact ⟨f.symm, by rw [Iso.symm_hom, Iso.comp_inv_eq]; exact hf.symm⟩

lemma RankQuotient.rel_trans {r d : ℕ} {T : Scheme.{0}} {x y z : RankQuotient r d T}
    (h1 : x.Rel y) (h2 : y.Rel z) : x.Rel z := by
  obtain ⟨f, hf⟩ := h1; obtain ⟨g, hg⟩ := h2
  -- term-mode (the `T.Modules` def-diamond blocks positional category `rw`)
  exact ⟨f ≪≫ g,
    (congrArg (x.q ≫ ·) (Iso.trans_hom f g)).trans <|
      (Category.assoc x.q f.hom g.hom).symm.trans <|
        (congrArg (· ≫ g.hom) hf).trans hg⟩

/-- The equivalence-of-quotients setoid on `RankQuotient r d T`. -/
instance rqSetoid (r d : ℕ) (T : Scheme.{0}) : Setoid (RankQuotient r d T) where
  r := RankQuotient.Rel
  iseqv := ⟨RankQuotient.rel_refl, RankQuotient.rel_symm, RankQuotient.rel_trans⟩

/-- The **pullback action** on a rank-`d` quotient: pull the target sheaf and quotient map
back along `ψ`, re-presenting the source as the trivial bundle via `pullbackFreeIso`. The
result is again an epimorphism (pullback preserves epis) onto a rank-`d` locally free sheaf
(`pullback_isLocallyFreeOfRank`). -/
noncomputable def rqPullback {r d : ℕ} {T' T : Scheme.{0}} (ψ : T' ⟶ T)
    (x : RankQuotient r d T) : RankQuotient r d T' where
  F := (Scheme.Modules.pullback ψ).obj x.F
  q := (Scheme.Modules.pullbackFreeIso ψ (Fin r)).inv ≫ (Scheme.Modules.pullback ψ).map x.q
  epi :=
    -- fully explicit: the def-diamond on `T.Modules` blocks `Epi`-instance search, so
    -- `x.epi` is threaded through `map_epi`/`epi_comp` by hand
    @CategoryTheory.epi_comp _ _ _ _ _
      (Scheme.Modules.pullbackFreeIso ψ (Fin r)).inv inferInstance
      ((Scheme.Modules.pullback ψ).map x.q)
      (@CategoryTheory.Functor.map_epi _ _ _ _ (Scheme.Modules.pullback ψ) inferInstance _ _
        x.q x.epi)
  locFree := Scheme.Modules.pullback_isLocallyFreeOfRank ψ x.locFree

/-- The pullback action respects the equivalence relation, hence descends to quotients. -/
lemma rqPullback_rel {r d : ℕ} {T' T : Scheme.{0}} (ψ : T' ⟶ T)
    {x y : RankQuotient r d T} (h : x.Rel y) :
    (rqPullback ψ x).Rel (rqPullback ψ y) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨(Scheme.Modules.pullback ψ).mapIso f, ?_⟩
  change ((Scheme.Modules.pullbackFreeIso ψ (Fin r)).inv ≫ (Scheme.Modules.pullback ψ).map x.q) ≫
      (Scheme.Modules.pullback ψ).map f.hom
    = (Scheme.Modules.pullbackFreeIso ψ (Fin r)).inv ≫ (Scheme.Modules.pullback ψ).map y.q
  rw [Category.assoc, ← (Scheme.Modules.pullback ψ).map_comp]
  exact congrArg
    (fun m => (Scheme.Modules.pullbackFreeIso ψ (Fin r)).inv ≫ (Scheme.Modules.pullback ψ).map m) hf

end AlgebraicGeometry.Grassmannian

namespace AlgebraicGeometry.Grassmannian

/-- The **Grassmannian functor** `Grass(r,d)` (`def:grassmannian_functor`): the
contravariant functor from schemes to sets sending `T` to the set of equivalence classes
of rank-`d` locally free quotients `q : O_T^r ↠ F`, acting on morphisms by pullback.

The object and morphism assignments are complete; the functoriality laws (`map_id`,
`map_comp`) are discharged — via the naturality of the pseudofunctor comparison isomorphisms
`pullbackId`/`pullbackComp` of `Scheme.Modules.pullback` — through the free-sheaf coherences
`pullbackFreeIso_id`/`pullbackFreeIso_comp`, which reduce by coproduct extensionality to the
unit-level coherences `pullbackObjUnitToUnit_id`/`pullbackObjUnitToUnit_comp`. Fully proved. -/
noncomputable def functor (d r : ℕ) : Scheme.{0}ᵒᵖ ⥤ Type 1 where
  obj T := Quotient (rqSetoid r d T.unop)
  map {X Y} g := TypeCat.ofHom (Quotient.map (rqPullback (r := r) (d := d) g.unop)
    (fun _ _ h => rqPullback_rel g.unop h))
  map_id X := by
    -- reduce to the equivalence relation on representatives
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (rqPullback (𝟙 X).unop x) = Quotient.mk _ x
      -- the canonical iso `(𝟙)^* x.F ≅ x.F` is `pullbackId`; the quotient-map equation it
      -- must satisfy reduces, by naturality of `pullbackId.hom`, to the free coherence
      -- `pullbackFreeIso (𝟙) = (pullbackId).app (free _)`, hence to the unit-level identity
      -- `pullbackObjUnitToUnit (𝟙) = (pullbackId).app unit`. That coherence between
      -- `SheafOfModules.pullbackObjFreeIso` and Mathlib's `pullbackId` is the open obstacle.
      refine Quotient.sound ⟨(Scheme.Modules.pullbackId X.unop).app x.F, ?_⟩
      -- unfold `(rqPullback (𝟙) x).q` and `(pullbackId.app x.F).hom` (defeq)
      change ((Scheme.Modules.pullbackFreeIso (𝟙 X.unop) (Fin r)).inv ≫
          (Scheme.Modules.pullback (𝟙 X.unop)).map x.q) ≫
          (Scheme.Modules.pullbackId X.unop).hom.app x.F = x.q
      rw [Category.assoc, (Scheme.Modules.pullbackId X.unop).hom.naturality x.q,
        ← Scheme.Modules.pullbackFreeIso_id]
      -- `(𝟭).map x.q = x.q` is only defeq, so close by term (rw can't see through it)
      exact Iso.inv_hom_id_assoc _ _
  map_comp {X Y Z} f g := by
    ext z
    induction z using Quotient.ind with
    | _ x =>
      change Quotient.mk _ (rqPullback (f ≫ g).unop x)
        = Quotient.mk _ (rqPullback g.unop (rqPullback f.unop x))
      -- the canonical iso `(g.unop ≫ f.unop)^* x.F ≅ g.unop^*(f.unop^* x.F)` is `pullbackComp`;
      -- the quotient-map equation reduces, by naturality, to the composite free coherence
      -- relating `pullbackFreeIso (g.unop ≫ f.unop)` to `pullbackFreeIso g.unop`/`f.unop`
      -- through `pullbackComp` — the composite analogue of the `map_id` obstacle.
      refine Quotient.sound ⟨((Scheme.Modules.pullbackComp g.unop f.unop).app x.F).symm, ?_⟩
      -- unfold `(rqPullback (g∘f) x).q` and `(pullbackComp.app x.F).symm.hom` (defeq), writing
      -- the composite as `g.unop ≫ f.unop` so the `pullbackComp` naturality matches syntactically
      change ((Scheme.Modules.pullbackFreeIso (g.unop ≫ f.unop) (Fin r)).inv ≫
          (Scheme.Modules.pullback (g.unop ≫ f.unop)).map x.q) ≫
          (Scheme.Modules.pullbackComp g.unop f.unop).inv.app x.F
        = (rqPullback g.unop (rqPullback f.unop x)).q
      -- expose the `pullbackComp.inv` naturality square (mirrors the `map_id` reduction)
      rw [Category.assoc, (Scheme.Modules.pullbackComp g.unop f.unop).inv.naturality x.q]
      -- the composite free coherence (`pullbackFreeIso_comp`) in inverse form: invert both
      -- sides of the iso equation `pullbackComp.hom.app free ≫ pfba.hom = (pullback g).map pfa.hom
      -- ≫ pfb.hom`.
      have hstar : (Scheme.Modules.pullbackFreeIso (g.unop ≫ f.unop) (Fin r)).inv ≫
            (Scheme.Modules.pullbackComp g.unop f.unop).inv.app (SheafOfModules.free (Fin r))
          = (Scheme.Modules.pullbackFreeIso g.unop (Fin r)).inv ≫
            (Scheme.Modules.pullback g.unop).map
              (Scheme.Modules.pullbackFreeIso f.unop (Fin r)).inv := by
        have hH := Scheme.Modules.pullbackFreeIso_comp f.unop g.unop (Fin r)
        rw [← cancel_epi ((Scheme.Modules.pullbackComp g.unop f.unop).hom.app
          (SheafOfModules.free (Fin r)) ≫
          (Scheme.Modules.pullbackFreeIso (g.unop ≫ f.unop) (Fin r)).hom)]
        trans (𝟙 _)
        · rw [Category.assoc, Iso.hom_inv_id_assoc]
          exact (Scheme.Modules.pullbackComp g.unop f.unop).hom_inv_id_app _
        · rw [hH]; simp
      -- whisker `hstar` by `≫ (pullback f ⋙ pullback g).map x.q` and refold the RHS via
      -- `map_comp` into `(rqPullback g (rqPullback f x)).q`.
      exact (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (Scheme.Modules.pullback f.unop ⋙
              Scheme.Modules.pullback g.unop).map x.q) hstar).trans
          ((Category.assoc _ _ _).trans
            (congrArg ((Scheme.Modules.pullbackFreeIso g.unop (Fin r)).inv ≫ ·)
              ((Scheme.Modules.pullback g.unop).map_comp
                (Scheme.Modules.pullbackFreeIso f.unop (Fin r)).inv
                ((Scheme.Modules.pullback f.unop).map x.q)).symm)))

/-- **Chart restriction of the universal quotient sheaf**: over the `I`-th chart, the
universal bundle `U` restricts to the free rank-`d` sheaf — the instantiation of the
descent restriction isomorphism `Scheme.Modules.glueRestrictionIso` at the Grassmannian
glue data. (Its underlying morphism is the adjoint transpose of the `I`-th
descent-equalizer projection; iso-ness rides on
`Scheme.Modules.isIso_glueRestrictionHom`.) -/
noncomputable def universalQuotient_restrictionIso (d r : ℕ) (I : (theGlueData d r).J) :
    (Scheme.Modules.pullback ((theGlueData d r).ι I)).obj (universalQuotient d r)
      ≅ SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d) :=
  Scheme.Modules.glueRestrictionIso (theGlueData d r)
    (fun I => SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d))
    (bundleTransitionData d r)
    (fun I => bundleTransition_self d r I.1 I.2)
    (fun I J K => bundleTransition_cocycle d r I J K) I

/-- **The universal quotient sheaf is locally free of rank `d`**
(`thm:grassmannian_universal_property`, first ingredient): the chart images
`{ι_I(U^I)}` cover the glued scheme, and on each member the restriction of
`universalQuotient` is identified with `O^d` by transporting the descent restriction
isomorphism `universalQuotient_restrictionIso` along the factorization
`ι_I = isoOpensRange.hom ≫ opensRange.ι`. -/
theorem universalQuotient_isLocallyFreeOfRank (d r : ℕ) :
    SheafOfModules.IsLocallyFreeOfRank (universalQuotient d r) d := by
  refine ⟨(theGlueData d r).J, fun I => ((theGlueData d r).ι I).opensRange, ?_, fun I => ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨I, y, rfl⟩ := (theGlueData d r).ι_jointly_surjective x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨I, y, rfl⟩
  · -- transport the chart restriction iso along `ι_I = isoOpensRange.hom ≫ opensRange.ι`,
    -- inverting the chart-parametrization iso via the pullback pseudofunctor
    refine ⟨?_⟩
    letI ι := (theGlueData d r).ι I
    letI e := ι.isoOpensRange
    exact (Scheme.Modules.pullbackId _).symm.app _ ≪≫
      (Scheme.Modules.pullbackCongr (Iso.inv_hom_id e).symm).app _ ≪≫
      ((Scheme.Modules.pullbackComp e.inv e.hom).app _).symm ≪≫
      (Scheme.Modules.pullback e.inv).mapIso
        ((Scheme.Modules.pullbackComp e.hom ι.opensRange.ι).app (universalQuotient d r) ≪≫
          (Scheme.Modules.pullbackCongr (ι.isoOpensRange_hom_ι)).app (universalQuotient d r) ≪≫
          universalQuotient_restrictionIso d r I) ≪≫
      Scheme.Modules.pullbackFreeIso e.inv (Fin d) ≪≫
      SheafOfModules.freeFunctor.mapIso (Equiv.ulift.symm.toIso)

/-- **The tautological quotient is an epimorphism**
(`thm:grassmannian_universal_property`, second ingredient).

ROUTE (scoped iter-066, not yet formalized): epi-ness is chart-local. Transposing
`glueLift_glueProj` along the chart immersion shows
`ι_I^* (tautologicalQuotient) ≫ glueRestrictionHom I` equals (up to the free-pullback
comparison `pullbackFreeIso`) the chart quotient `chartQuotientMap d r I.1 I.2`, which
is a (split) epi (`chartQuotientMap_epi`). A family of morphisms out of the glued
sheaf is jointly reflected by the chart restrictions (the separation half of the sheaf
condition of the descent equalizer), so `q ≫ u = q ≫ v → u = v` follows once all chart
restrictions of `q` are epi. The joint-reflection lemma is the missing ingredient —
it shares its proof skeleton with `isIso_glueRestrictionHom` (mono-ness of
`E ⟶ ∏ (ι_I)_* M_I`). -/
theorem tautologicalQuotient_epi (d r : ℕ) : Epi (tautologicalQuotient d r) := by
  -- Chart-local epi-ness: over each chart `I` the restriction of `u` is, up to the
  -- free-pullback comparison and the descent restriction iso, the split-epi chart
  -- quotient `chartQuotientMap` (`pullback_map_tautologicalQuotient`,
  -- `chartQuotientMap_epi`).
  have hchart : ∀ I : (theGlueData d r).J,
      Epi ((Scheme.Modules.pullback ((theGlueData d r).ι I)).map (tautologicalQuotient d r)) := by
    intro I
    -- the chart restriction identity (inlined `pullback_map_tautologicalQuotient`, which is
    -- only stated later in the file): `ι_I^* u ≫ restrictionIso.hom = pullbackFreeIso.hom ≫ u^I`
    have hptq : (Scheme.Modules.pullback ((theGlueData d r).ι I)).map (tautologicalQuotient d r) ≫
          (universalQuotient_restrictionIso d r I).hom
        = (Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).hom ≫
          chartQuotientMap d r I.1 I.2 := by
      have h := Scheme.Modules.pullback_map_glueLift_glueRestrictionHom (theGlueData d r)
        (fun J => SheafOfModules.free (R := ((theGlueData d r).U J).ringCatSheaf) (Fin d))
        (bundleTransitionData d r)
        (fun J => bundleTransition_self d r J.1 J.2)
        (fun J J' K => bundleTransition_cocycle d r J J' K)
        (fun J => tautologicalQuotientComponent d r J)
        (fun p => (tautologicalQuotientComponent_transpose d r p.1 p.2).mpr
          (tautologicalQuotient_overlap d r p.1 p.2)) I
      have h2 : ((Scheme.Modules.pullbackPushforwardAdjunction
            ((theGlueData d r).ι I)).homEquiv _ _).symm
            (tautologicalQuotientComponent d r I)
          = (Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).hom ≫
            chartQuotientMap d r I.1 I.2 := by
        rw [tautologicalQuotientComponent]
        exact Equiv.symm_apply_apply _ _
      exact h.trans h2
    have heq : (Scheme.Modules.pullback ((theGlueData d r).ι I)).map (tautologicalQuotient d r)
        = ((Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).hom ≫
            chartQuotientMap d r I.1 I.2) ≫ (universalQuotient_restrictionIso d r I).inv :=
      (Iso.eq_comp_inv _).mpr hptq
    rw [heq]
    -- `(iso ≫ u^I) ≫ iso` is epi: `u^I` is the split-epi chart quotient, the rest are isos.
    -- Use `epi_comp'` (explicit `Epi` args) to feed `chartQuotientMap_epi` by defeq, avoiding
    -- instance search through the value-`ModuleCat` diamond.
    exact epi_comp' (epi_comp' inferInstance (chartQuotientMap_epi d r I.1 I.2)) inferInstance
  -- Joint reflection: a morphism out of the glued sheaf is determined chart-locally
  -- (`pullback_map_jointly_faithful`), so `u` being epi follows from chart-wise epi-ness.
  constructor
  intro Z a b hab
  apply Scheme.Modules.pullback_map_jointly_faithful (theGlueData d r)
  intro I
  haveI := hchart I
  -- transport `hab` through the pullback functor and cancel the chart-epi on the left
  exact (cancel_epi ((Scheme.Modules.pullback ((theGlueData d r).ι I)).map
      (tautologicalQuotient d r))).mp
    ((Functor.map_comp _ _ _).symm.trans
      ((congrArg (Scheme.Modules.pullback ((theGlueData d r).ι I)).map hab).trans
        (Functor.map_comp _ _ _)))

/-- **The tautological point of the Grassmannian**: the rank-`d` locally free quotient
`u : O^r ↠ U` on `Gr(d,r)` itself, packaged as a `RankQuotient`. Pulling it back along
`ψ : T ⟶ Gr(d,r)` realizes the forward direction of the universal property. -/
noncomputable def tautologicalRankQuotient (d r : ℕ) : RankQuotient r d (scheme d r) where
  F := universalQuotient d r
  q := tautologicalQuotient d r
  epi := tautologicalQuotient_epi d r
  locFree := universalQuotient_isLocallyFreeOfRank d r

/-! ### The Nitsure §1 inverse construction: chart loci, chart matrices, chart morphisms

For a rank-`d` quotient `x = ⟨F, q⟩` on `T` and a size-`d` subset `I ⊆ Fin r`, the
*chart composite* is `s_I ≫ q : O_T^d ⟶ F` (the `I`-indexed coordinate inclusion
followed by the quotient map) and the *chart locus* `T_I ⊆ T` is the largest open on
which it restricts to an isomorphism. The loci are open by construction (a supremum of
opens), cover `T` (Nakayama at each point), and over `T_I` the quotient is presented by
a `d × r` matrix of sections whose `I`-minor is the identity — its complementary
entries determine a ring map `R^I ⟶ Γ(T_I, O)` and hence a morphism `T_I ⟶ U^I` by the
Γ–Spec adjunction. These glue to the inverse `grPointOfRankQuotient` of the universal
property. -/

/-- The **iso-locus** of a morphism of sheaves of modules on a scheme: the supremum
(union) of all opens `U` such that the pullback of `φ` to the open subscheme `U` is an
isomorphism. This is the largest open on which `φ` is invertible. Project-local
(Mathlib has no iso-locus for morphisms of sheaves of modules). -/
def isoLocus {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N) : X.Opens :=
  sSup {U : X.Opens | IsIso ((Scheme.Modules.pullback U.ι).map φ)}

/-- Membership in the iso-locus: `t ∈ isoLocus φ` iff some open neighbourhood of `t`
pulls `φ` back to an isomorphism. Project-local. -/
lemma mem_isoLocus {X : Scheme.{0}} {M N : X.Modules} {φ : M ⟶ N} {t : X} :
    t ∈ isoLocus φ
      ↔ ∃ U : X.Opens, IsIso ((Scheme.Modules.pullback U.ι).map φ) ∧ t ∈ U := by
  simp only [isoLocus, TopologicalSpace.Opens.mem_sSup, Set.mem_setOf_eq]

/-- Restriction stability of pullback-invertibility: if `φ` pulls back to an
isomorphism on `U` and `W ≤ U`, it pulls back to an isomorphism on `W` — transport
along the pseudofunctor comparison `pullback W.ι ≅ pullback U.ι ⋙ pullback (homOfLE)`.
Project-local. -/
lemma isIso_pullback_map_of_le {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    {W U : X.Opens} (e : W ≤ U)
    (hU : IsIso ((Scheme.Modules.pullback U.ι).map φ)) :
    IsIso ((Scheme.Modules.pullback W.ι).map φ) := by
  have h : IsIso ((Scheme.Modules.pullback U.ι ⋙
      Scheme.Modules.pullback (X.homOfLE e)).map φ) := by
    change IsIso ((Scheme.Modules.pullback (X.homOfLE e)).map
      ((Scheme.Modules.pullback U.ι).map φ))
    exact inferInstance
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.pullbackComp (X.homOfLE e) U.ι ≪≫
      Scheme.Modules.pullbackCongr (X.homOfLE_ι e)) φ).mp h

/-- The **chart composite** `s_I ≫ q : O_T^d ⟶ F` (Nitsure §1): the `I`-indexed
coordinate inclusion of free sheaves followed by the quotient map of the rank-`d`
quotient `x`. Project-local. -/
noncomputable def chartComposite {T : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) :
    SheafOfModules.free (R := T.ringCatSheaf) (Fin d) ⟶ x.F :=
  SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫ x.q

/-- The **chart locus** `T_I ⊆ T` of a rank-`d` quotient (Nitsure §1): the largest open
of `T` on which the chart composite `s_I ≫ q` restricts to an isomorphism. Project-local. -/
noncomputable def chartLocus {T : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) : T.Opens :=
  isoLocus (chartComposite x I hI)

/-- **Right-invertible matrices over a field have an invertible column minor**: a
`d × r` matrix with a right inverse has an invertible `d × d` submatrix on the columns
of some size-`d` subset `I`, enumerated by `I.orderIsoOfFin` (the spelling used by
`chartComposite`). Pure linear algebra: the columns span `K^d`, a spanning set contains
a basis, and a square matrix with independent columns is invertible. Project-local
helper for the Nakayama covering step. -/
private lemma exists_isUnit_submatrix {K : Type} [Field K] {d r : ℕ}
    (M : Matrix (Fin d) (Fin r) K) (G : Matrix (Fin r) (Fin d) K) (hMG : M * G = 1) :
    ∃ (I : Finset (Fin r)) (hI : I.card = d),
      IsUnit (M.submatrix id (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) := by
  classical
  -- the columns of `M` span `K^d` (a right inverse makes `mulVec` surjective)
  have hspan : Submodule.span K (Set.range M.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin, LinearMap.range_eq_top]
    intro v
    refine ⟨G.mulVec v, ?_⟩
    show M.mulVec (G.mulVec v) = v
    rw [Matrix.mulVec_mulVec, hMG, Matrix.one_mulVec]
  -- extract a linearly independent spanning subset `b` of the column set
  obtain ⟨b, hbsub, hbspan, hbind⟩ := exists_linearIndependent K (Set.range M.col)
  rw [hspan] at hbspan
  haveI : Fintype b := ((Set.finite_range M.col).subset hbsub).fintype
  -- `b` is a basis, so it has exactly `d` elements
  let B : Module.Basis b K (Fin d → K) :=
    Module.Basis.mk hbind (by rw [Subtype.range_coe, hbspan])
  have hcard : Fintype.card b = d := by
    have h1 := Module.finrank_eq_card_basis B
    rw [Module.finrank_pi K, Fintype.card_fin] at h1
    exact h1.symm
  -- choose a column index for each element of `b`
  have hchoice : ∀ v : b, ∃ j : Fin r, M.col j = (v : Fin d → K) := fun v => hbsub v.2
  choose φ hφ using hchoice
  have hφinj : Function.Injective φ := fun u v huv => by
    apply Subtype.ext
    rw [← hφ u, ← hφ v, huv]
  have hIcard : (Finset.univ.image φ).card = d := by
    rw [Finset.card_image_of_injective _ hφinj, Finset.card_univ, hcard]
  refine ⟨Finset.univ.image φ, hIcard, ?_⟩
  -- each enumerated column lies in `b`
  have hcol : ∀ j : Fin d,
      M.col (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r)) ∈ b := by
    intro j
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp
      ((Finset.univ.image φ).orderIsoOfFin hIcard j).2
    rw [← hv, hφ v]
    exact v.2
  set c : Fin d → b :=
    fun j => ⟨M.col (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r)), hcol j⟩
    with hcdef
  have hcinj : Function.Injective c := by
    intro j j' hjj
    have hcols : M.col (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r))
        = M.col (((Finset.univ.image φ).orderIsoOfFin hIcard j' : Fin r)) :=
      congrArg Subtype.val hjj
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp
      ((Finset.univ.image φ).orderIsoOfFin hIcard j).2
    obtain ⟨v', -, hv'⟩ := Finset.mem_image.mp
      ((Finset.univ.image φ).orderIsoOfFin hIcard j').2
    have hvv' : v = v' := by
      apply Subtype.ext
      calc (v : Fin d → K)
          = M.col (φ v) := (hφ v).symm
        _ = M.col (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r)) := by rw [hv]
        _ = M.col (((Finset.univ.image φ).orderIsoOfFin hIcard j' : Fin r)) := hcols
        _ = M.col (φ v') := by rw [hv']
        _ = (v' : Fin d → K) := hφ v'
    have hee : (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r))
        = (((Finset.univ.image φ).orderIsoOfFin hIcard j' : Fin r)) := by
      rw [← hv, ← hv', hvv']
    exact ((Finset.univ.image φ).orderIsoOfFin hIcard).injective (Subtype.ext hee)
  -- the columns of the submatrix are the inclusion of `b` along the injective `c`
  have hSind : LinearIndependent K
      (M.submatrix id (fun j : Fin d =>
        (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r)))).col := by
    have heq : (M.submatrix id (fun j : Fin d =>
        (((Finset.univ.image φ).orderIsoOfFin hIcard j : Fin r)))).col
        = fun j => ((c j : Fin d → K)) := by
      funext j
      rfl
    rw [heq]
    exact hbind.comp c hcinj
  exact Matrix.linearIndependent_cols_iff_isUnit.mp hSind

/-- **The chart loci cover `T`** (Nitsure §1, the Nakayama step): at each point `t`, the
fibre `F ⊗ κ(t)` is a `d`-dimensional quotient of `κ(t)^r`, so some `d` of the standard
basis vectors map to a basis; for that subset `I` the chart composite is an isomorphism
near `t` (a surjective endomorphism argument / Nakayama), i.e. `t ∈ T_I`.

PROOF ROUTE (scoped iter-067, not yet formalized): work in a trivialisation `V ∋ t`,
`F|_V ≅ O_V^d` (from `x.locFree`); the composite becomes a `d × d` matrix of sections of
`O_V`; epi-ness of `q` gives stalkwise surjectivity at `t`, so over the residue field
some `d`-column minor of the presenting `d × r` matrix has nonzero determinant; shrink
`V` to the basic open of that determinant, on which the matrix is invertible and hence
the composite an isomorphism (`matrixToFreeIso`). -/
theorem chartLocus_isOpenCover {T : Scheme.{0}} (d r : ℕ) (x : RankQuotient r d T) :
    TopologicalSpace.IsOpenCover (fun I : (theGlueData d r).J => chartLocus x I.1 I.2) := by
  refine TopologicalSpace.IsOpenCover.mk ?_
  rw [eq_top_iff]
  intro t _
  -- B1: a trivialising open `U i ∋ t` from local freeness
  obtain ⟨ιT, U, hUcover, hUtriv⟩ := x.locFree
  have ht : t ∈ ⨆ i, U i := by rw [hUcover]; trivial
  obtain ⟨i, hti⟩ := TopologicalSpace.Opens.mem_iSup.mp ht
  -- B2: refine to an affine open `W ≤ U i` containing `t`
  obtain ⟨W, hWaff, htW, hWle⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (AlgebraicGeometry.Scheme.isBasis_affineOpens T) hti
  -- re-type `W` as `T.Opens` so that `Scheme.Opens` dot-notation applies
  obtain ⟨W, hWaff, htW, hWle⟩ : ∃ W : T.Opens, IsAffineOpen W ∧ t ∈ W ∧ W ≤ U i :=
    ⟨W, hWaff, htW, hWle⟩
  haveI : IsAffine W.toScheme := hWaff
  obtain ⟨e0⟩ := hUtriv i
  -- B3: trivialise `x.F` on `W` and present the pulled-back quotient by a matrix
  set eW : (Scheme.Modules.pullback W.ι).obj x.F
      ≅ SheafOfModules.free (R := W.toScheme.ringCatSheaf) (Fin d) :=
    (Scheme.Modules.pullbackCongr (T.homOfLE_ι hWle).symm).app x.F ≪≫
    ((Scheme.Modules.pullbackComp (T.homOfLE hWle) (U i).ι).app x.F).symm ≪≫
    (Scheme.Modules.pullback (T.homOfLE hWle)).mapIso e0 ≪≫
    Scheme.Modules.pullbackFreeIso (T.homOfLE hWle) (ULift.{0} (Fin d)) ≪≫
    (show SheafOfModules.free (R := W.toScheme.ringCatSheaf) (ULift.{0} (Fin d))
        ≅ SheafOfModules.free (R := W.toScheme.ringCatSheaf) (Fin d) from
      SheafOfModules.freeFunctor.mapIso (Equiv.ulift.toIso)) with heWdef
  set ψW : SheafOfModules.free (R := W.toScheme.ringCatSheaf) (Fin r) ⟶
      SheafOfModules.free (R := W.toScheme.ringCatSheaf) (Fin d) :=
    (Scheme.Modules.pullbackFreeIso W.ι (Fin r)).inv ≫
      (Scheme.Modules.pullback W.ι).map x.q ≫ eW.hom with hψWdef
  haveI hψWepi : Epi ψW := by
    haveI hq : Epi ((Scheme.Modules.pullback W.ι).map x.q) :=
      @CategoryTheory.Functor.map_epi _ _ _ _ (Scheme.Modules.pullback W.ι)
        inferInstance _ _ x.q x.epi
    haveI h1 : Epi ((Scheme.Modules.pullback W.ι).map x.q ≫ eW.hom) :=
      @epi_comp _ _ _ _ _ _ hq _ (IsIso.epi_of_iso _)
    exact @epi_comp _ _ _ _ _ _ (IsIso.epi_of_iso _) _ h1
  set MW : Matrix (Fin d) (Fin r) Γ(W.toScheme, ⊤) := Matrix.of fun p j =>
    unitEndSection (SheafOfModules.ιFree j ≫ ψW ≫ projFree p) with hMWdef
  have hMW : matrixEndRect MW = ψW := matrixEndRect_unitEndSection ψW
  -- B4: the presenting matrix admits a right inverse (affine epi-splitting)
  obtain ⟨G, hG⟩ := exists_rightInverse_of_epi_matrixEndRect MW (by rw [hMW]; exact hψWepi)
  -- B5: evaluate at the residue field of the stalk at `t`
  set t' : W.toScheme := ⟨t, htW⟩ with ht'def
  set χ : Γ(W.toScheme, ⊤) →+* IsLocalRing.ResidueField ↥(W.toScheme.presheaf.stalk t') :=
    (IsLocalRing.residue _).comp
      (CommRingCat.Hom.hom (W.toScheme.presheaf.germ ⊤ t' trivial)) with hχdef
  have hGκ : MW.map ⇑χ * G.map ⇑χ = 1 := by
    rw [← Matrix.map_mul, hG, Matrix.map_one _ (map_zero χ) (map_one χ)]
  -- B6: a column subset `I` whose minor is invertible over the residue field
  obtain ⟨I, hI, hunit⟩ := exists_isUnit_submatrix (MW.map ⇑χ) (G.map ⇑χ) hGκ
  -- B7: the corresponding minor determinant has invertible germ, giving a basic open
  set f0 : Γ(W.toScheme, ⊤) :=
    (MW.submatrix id (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))).det with hf0def
  have hχf : IsUnit (χ f0) := by
    have h2 : IsUnit ((MW.map ⇑χ).submatrix id
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hunit
    rw [Matrix.submatrix_map] at h2
    have h3 : χ f0 = ((MW.submatrix id
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))).map ⇑χ).det := by
      rw [hf0def, RingHom.map_det, RingHom.mapMatrix_apply]
    rwa [h3]
  have hgerm : IsUnit ((CommRingCat.Hom.hom (W.toScheme.presheaf.germ ⊤ t' trivial)) f0) := by
    by_contra hnu
    have hmem : (CommRingCat.Hom.hom (W.toScheme.presheaf.germ ⊤ t' trivial)) f0
        ∈ IsLocalRing.maximalIdeal ↥(W.toScheme.presheaf.stalk t') :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnu)
    have hzero : χ f0 = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    exact hχf.ne_zero hzero
  have htb : t' ∈ W.toScheme.basicOpen f0 :=
    (AlgebraicGeometry.Scheme.mem_basicOpen_top W.toScheme f0 t').mpr hgerm
  -- B8: over the basic open the minor matrix becomes invertible
  set Wb : W.toScheme.Opens := W.toScheme.basicOpen f0 with hWbdef
  have hfb : IsUnit ((CommRingCat.Hom.hom (Scheme.Hom.appTop Wb.ι)) f0) := by
    have hle : Wb.ι ''ᵁ ⊤ ≤ W.toScheme.basicOpen f0 := by
      rw [Scheme.Opens.ι_image_top]
    have hcomp2 : (homOfLE (le_top : Wb.ι ''ᵁ ⊤ ≤ ⊤))
        = homOfLE hle ≫ homOfLE (W.toScheme.basicOpen_le f0) := Subsingleton.elim _ _
    rw [Scheme.Opens.ι_appTop, hcomp2, op_comp, Functor.map_comp]
    show IsUnit ((CommRingCat.Hom.hom (W.toScheme.presheaf.map (homOfLE hle).op))
      ((CommRingCat.Hom.hom (W.toScheme.presheaf.map
        (homOfLE (W.toScheme.basicOpen_le f0)).op)) f0))
    exact IsUnit.map (CommRingCat.Hom.hom (W.toScheme.presheaf.map (homOfLE hle).op))
      (AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen
        (X := W.toScheme.toLocallyRingedSpace.toRingedSpace) f0)
  have hdetb : IsUnit ((MW.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop Wb.ι))).submatrix id
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))).det := by
    rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hfb
  have h_inv1 : (MW.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop Wb.ι))).submatrix id
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) *
      ((MW.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop Wb.ι))).submatrix id
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdetb
  have h_inv2 : ((MW.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop Wb.ι))).submatrix id
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)))⁻¹ *
      (MW.map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop Wb.ι))).submatrix id
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) = 1 :=
    Matrix.nonsing_inv_mul _ hdetb
  haveI hIso : IsIso (matrixEnd ((MW.map
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop Wb.ι))).submatrix id
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)))) :=
    inferInstanceAs (IsIso (matrixToFreeIso _ _ h_inv1 h_inv2).hom)
  -- B9: identify the `W`-pullback of the chart composite with the minor matrix morphism
  have hc : (Scheme.Modules.pullback W.ι).map (chartComposite x I hI)
      = (Scheme.Modules.pullback W.ι).map (SheafOfModules.freeMap
          (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫
        (Scheme.Modules.pullback W.ι).map x.q :=
    (Scheme.Modules.pullback W.ι).map_comp _ _
  have hswap : (Scheme.Modules.pullbackFreeIso W.ι (Fin d)).inv ≫
      (Scheme.Modules.pullback W.ι).map (SheafOfModules.freeMap
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)))
      = SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
        (Scheme.Modules.pullbackFreeIso W.ι (Fin r)).inv := by
    rw [← cancel_mono (Scheme.Modules.pullbackFreeIso W.ι (Fin r)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [pullback_map_freeMap_pullbackFreeIso W.ι
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))]
    rw [Iso.inv_hom_id_assoc]
    -- the right-hand side collapses only by hand across the `X.Modules` diamond
    exact ((Category.assoc _ _ _).trans
      ((congrArg (SheafOfModules.freeMap
          (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫ ·)
        (Iso.inv_hom_id _)).trans (Category.comp_id _))).symm
  have hkey0 : (Scheme.Modules.pullbackFreeIso W.ι (Fin d)).inv ≫
      (Scheme.Modules.pullback W.ι).map (chartComposite x I hI) ≫ eW.hom
      = SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫ ψW := by
    rw [hc, hψWdef]
    -- fully term-mode associativity shuffle (`simp [Category.assoc]` is unreliable
    -- across the `X.Modules` diamond)
    exact (congrArg ((Scheme.Modules.pullbackFreeIso W.ι (Fin d)).inv ≫ ·)
        (Category.assoc _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (Scheme.Modules.pullback W.ι).map x.q ≫ eW.hom) hswap).trans
          (Category.assoc _ _ _)))
  have hfree : SheafOfModules.freeMap (R := W.toScheme.ringCatSheaf)
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫ ψW
      = matrixEndRect (MW.submatrix id
          (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) := by
    rw [← hMW]
    exact freeMap_matrixEndRect _ MW
  have hcW : (Scheme.Modules.pullback W.ι).map (chartComposite x I hI)
      = (Scheme.Modules.pullbackFreeIso W.ι (Fin d)).hom ≫
        matrixEndRect (MW.submatrix id
          (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫ eW.inv := by
    rw [← hfree, ← hkey0]
    simp only [Category.assoc, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.comp_id,
      Iso.inv_hom_id_assoc]
  -- B10: the pullback to the basic open is an isomorphism
  have hb1 : (Scheme.Modules.pullbackFreeIso Wb.ι (Fin d)).inv ≫
      (Scheme.Modules.pullback Wb.ι).map (matrixEndRect (MW.submatrix id
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)))) ≫
      (Scheme.Modules.pullbackFreeIso Wb.ι (Fin d)).hom
      = matrixEndRect ((MW.submatrix id
          (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop Wb.ι))) :=
    pullback_conj_matrixEndRect Wb.ι _
  haveI hb2 : IsIso ((Scheme.Modules.pullback Wb.ι).map (matrixEndRect (MW.submatrix id
      (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))))) := by
    have hdec : (Scheme.Modules.pullback Wb.ι).map (matrixEndRect (MW.submatrix id
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))))
        = (Scheme.Modules.pullbackFreeIso Wb.ι (Fin d)).hom ≫
          matrixEndRect ((MW.submatrix id
            (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))).map
            ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop Wb.ι))) ≫
          (Scheme.Modules.pullbackFreeIso Wb.ι (Fin d)).inv := by
      rw [← hb1]
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc,
        Iso.inv_hom_id_assoc, Iso.inv_hom_id]
    rw [hdec]
    -- `matrixEndRect ((MW.submatrix _ _).map τ)` is definitionally
    -- `matrixEnd ((MW.map τ).submatrix _ _)` (`submatrix_map` and the square bridge
    -- are both `rfl`), so the explicit matrix isomorphism applies directly
    exact inferInstanceAs (IsIso ((Scheme.Modules.pullbackFreeIso Wb.ι (Fin d) ≪≫
      matrixToFreeIso _ _ h_inv1 h_inv2 ≪≫
      (Scheme.Modules.pullbackFreeIso Wb.ι (Fin d)).symm).hom))
  haveI hWlevel : IsIso ((Scheme.Modules.pullback Wb.ι).map
      ((Scheme.Modules.pullback W.ι).map (chartComposite x I hI))) := by
    rw [hcW, Functor.map_comp, Functor.map_comp]
    exact inferInstanceAs (IsIso (((Scheme.Modules.pullback Wb.ι).mapIso
      (Scheme.Modules.pullbackFreeIso W.ι (Fin d)) ≪≫
      asIso ((Scheme.Modules.pullback Wb.ι).map (matrixEndRect (MW.submatrix id
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))))) ≪≫
      (Scheme.Modules.pullback Wb.ι).mapIso eW.symm).hom))
  haveI hjIso : IsIso ((Scheme.Modules.pullback (Wb.ι ≫ W.ι)).map
      (chartComposite x I hI)) := by
    rw [← NatIso.isIso_map_iff (Scheme.Modules.pullbackComp Wb.ι W.ι) (chartComposite x I hI)]
    exact hWlevel
  -- B11: transport along the range factorisation and conclude membership
  have hjfact : Wb.ι ≫ W.ι = (Wb.ι ≫ W.ι).isoOpensRange.hom ≫ (Wb.ι ≫ W.ι).opensRange.ι :=
    (Scheme.Hom.isoOpensRange_hom_ι (Wb.ι ≫ W.ι)).symm
  haveI hcomp3 : IsIso ((Scheme.Modules.pullback
      ((Wb.ι ≫ W.ι).isoOpensRange.hom ≫ (Wb.ι ≫ W.ι).opensRange.ι)).map
      (chartComposite x I hI)) := by
    rw [← hjfact]; exact hjIso
  haveI hpull : IsIso ((Scheme.Modules.pullback (Wb.ι ≫ W.ι).isoOpensRange.hom).map
      ((Scheme.Modules.pullback (Wb.ι ≫ W.ι).opensRange.ι).map (chartComposite x I hI))) :=
    (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp
      (Wb.ι ≫ W.ι).isoOpensRange.hom (Wb.ι ≫ W.ι).opensRange.ι)
      (chartComposite x I hI)).mpr hcomp3
  have hUIso : IsIso ((Scheme.Modules.pullback (Wb.ι ≫ W.ι).opensRange.ι).map
      (chartComposite x I hI)) := by
    haveI h7 : IsIso ((Scheme.Modules.pullback (Wb.ι ≫ W.ι).isoOpensRange.inv).map
        ((Scheme.Modules.pullback (Wb.ι ≫ W.ι).isoOpensRange.hom).map
          ((Scheme.Modules.pullback (Wb.ι ≫ W.ι).opensRange.ι).map
            (chartComposite x I hI)))) :=
      Functor.map_isIso _ _
    have h8 : IsIso ((Scheme.Modules.pullback ((Wb.ι ≫ W.ι).isoOpensRange.inv ≫
        (Wb.ι ≫ W.ι).isoOpensRange.hom)).map
        ((Scheme.Modules.pullback (Wb.ι ≫ W.ι).opensRange.ι).map
          (chartComposite x I hI))) := by
      rw [← NatIso.isIso_map_iff (Scheme.Modules.pullbackComp
        (Wb.ι ≫ W.ι).isoOpensRange.inv (Wb.ι ≫ W.ι).isoOpensRange.hom) _]
      exact h7
    rw [Iso.inv_hom_id] at h8
    exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackId _) _).mp h8
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨I, hI⟩, ?_⟩
  refine mem_isoLocus.mpr ⟨(Wb.ι ≫ W.ι).opensRange, hUIso, ?_⟩
  exact Scheme.Hom.mem_opensRange.mpr ⟨⟨t', htb⟩, rfl⟩

/-- **The chart composite is an isomorphism over the whole chart locus** — the local
inverses glue (separation + gluing halves of the sheaf condition).

PROOF (the blueprint's stalk-wise route, `lem:isIso_pullback_isoLocus_map`): being an
isomorphism of sheaves of modules is stalk-local. Each point of the iso-locus has an
open neighbourhood `U` on which `φ` pulls back to an isomorphism; restriction along the
open immersion `U.ι` preserves stalks (`Scheme.Modules.restrictStalkNatIso`), so the
stalk of (the abelian presheaf of) `φ` is invertible at every point of the locus. The
same stalk comparison for the locus inclusion shows the restriction of `φ` to the locus
is stalkwise invertible, hence an isomorphism of abelian sheaves by the stalk criterion
(`TopCat.Presheaf.isIso_of_stalkFunctor_map_iso`); `toPresheaf` reflects it back to
`X.Modules`, and `restrictFunctorIsoPullback` transports it to the pullback functor. -/
theorem isIso_pullback_isoLocus_map {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N) :
    IsIso ((Scheme.Modules.pullback (isoLocus φ).ι).map φ) := by
  -- Step 1: the stalk of `φ` (as a map of abelian presheaves) is invertible at every
  -- point of the iso-locus.
  have hstalk : ∀ (t : X), t ∈ isoLocus φ →
      IsIso ((TopCat.Presheaf.stalkFunctor Ab t).map
        ((Scheme.Modules.toPresheaf X).map φ)) := by
    intro t ht
    obtain ⟨U, hU, htU⟩ := mem_isoLocus.mp ht
    haveI hres : IsIso ((Scheme.Modules.restrictFunctor U.ι).map φ) :=
      (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback U.ι) φ).mpr hU
    have h2 : IsIso ((Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.toPresheaf _ ⋙
        TopCat.Presheaf.stalkFunctor Ab (⟨t, htU⟩ : U)).map φ) := by
      change IsIso ((TopCat.Presheaf.stalkFunctor Ab (⟨t, htU⟩ : U)).map
        ((Scheme.Modules.toPresheaf _).map ((Scheme.Modules.restrictFunctor U.ι).map φ)))
      infer_instance
    -- `U.ι ⟨t, htU⟩ = t` definitionally (`Scheme.Opens.ι_apply`)
    exact (NatIso.isIso_map_iff
      (Scheme.Modules.restrictStalkNatIso U.ι (⟨t, htU⟩ : U)) φ).mp h2
  -- Step 2: hence the restriction of `φ` to the iso-locus is stalkwise invertible.
  have hstalkres : ∀ (t : (isoLocus φ).toScheme),
      IsIso ((TopCat.Presheaf.stalkFunctor Ab t).map ((Scheme.Modules.toPresheaf _).map
        ((Scheme.Modules.restrictFunctor (isoLocus φ).ι).map φ))) := by
    intro t
    have h4 : IsIso ((Scheme.Modules.restrictFunctor (isoLocus φ).ι ⋙
        Scheme.Modules.toPresheaf _ ⋙ TopCat.Presheaf.stalkFunctor Ab t).map φ) :=
      (NatIso.isIso_map_iff
        (Scheme.Modules.restrictStalkNatIso (isoLocus φ).ι t) φ).mpr
        (hstalk t.1 t.2)
    exact h4
  -- Step 3: assemble the abelian-sheaf morphism, apply the stalk criterion, reflect.
  let ψ := (Scheme.Modules.restrictFunctor (isoLocus φ).ι).map φ
  let α : (⟨_, Scheme.Modules.isSheaf
        ((Scheme.Modules.restrictFunctor (isoLocus φ).ι).obj M)⟩ :
        TopCat.Sheaf Ab ((isoLocus φ).toScheme)) ⟶
      ⟨_, Scheme.Modules.isSheaf ((Scheme.Modules.restrictFunctor (isoLocus φ).ι).obj N)⟩ :=
    ⟨(Scheme.Modules.toPresheaf _).map ψ⟩
  haveI : ∀ (t : (isoLocus φ).toScheme),
      IsIso ((TopCat.Presheaf.stalkFunctor Ab t).map α.1) := hstalkres
  haveI hα : IsIso α := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso α
  haveI hα1 : IsIso α.1 := by
    change IsIso ((TopCat.Sheaf.forget Ab _).map α)
    exact Functor.map_isIso _ α
  haveI hψ : IsIso ψ := by
    haveI : IsIso ((Scheme.Modules.toPresheaf _).map ψ) := hα1
    exact isIso_of_reflects_iso ψ (Scheme.Modules.toPresheaf _)
  exact (NatIso.isIso_map_iff
    (Scheme.Modules.restrictFunctorIsoPullback (isoLocus φ).ι) φ).mp hψ

/-- The **presenting morphism of the quotient over the chart locus**: the pullback of
`q : O_T^r ↠ F` to `T_I`, composed with the inverse of the (there invertible) chart
composite — a morphism of free sheaves `O_{T_I}^r ⟶ O_{T_I}^d`, conjugated through the
free-pullback comparisons. Its matrix (`chartMatrix`) has `I`-minor `1`. Project-local. -/
noncomputable def chartMatrixHom {T : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) :
    SheafOfModules.free (R := (chartLocus x I hI).toScheme.ringCatSheaf) (Fin r) ⟶
      SheafOfModules.free (R := (chartLocus x I hI).toScheme.ringCatSheaf) (Fin d) :=
  (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv ≫
    (Scheme.Modules.pullback (chartLocus x I hI).ι).map x.q ≫
    @CategoryTheory.inv _ _ _ _
      ((Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI))
      (isIso_pullback_isoLocus_map (chartComposite x I hI)) ≫
    (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom

/-- The **presenting matrix `M^I` of the quotient over the chart locus** (Nitsure §1):
the `d × r` matrix of sections of `O_{T_I}` whose `(p,i)`-entry is the section carried
by the unit-sheaf component `ιFree i ≫ chartMatrixHom ≫ projFree p`. Its `I`-minor is
the identity, and its complementary entries are the chart coordinates of the morphism
`T_I ⟶ U^I`. Project-local. -/
noncomputable def chartMatrix {T : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) :
    Matrix (Fin d) (Fin r) Γ((chartLocus x I hI).toScheme, ⊤) :=
  Matrix.of fun p i =>
    unitEndSection (SheafOfModules.ιFree i ≫ chartMatrixHom x I hI ≫ projFree p)

/-- The **chart morphism** `φ_I : T_I ⟶ U^I` (Nitsure §1): the morphism into the affine
chart `U^I = Spec ℤ[x^I_{p,q}]` classified, through the Γ–Spec adjunction, by the ring
map sending the variable `x^I_{p,q}` to the `(p,q)`-entry of the presenting matrix
`chartMatrix`. By construction `φ_I^* X^I = M^I`. Project-local. -/
noncomputable def chartMorphism {T : Scheme.{0}} (d r : ℕ) (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) :
    ((chartLocus x I hI).toScheme : Scheme) ⟶ affineChart d r I :=
  (chartLocus x I hI).toScheme.toSpecΓ ≫
    Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval
        (fun pq : Fin d × {q : Fin r // q ∉ I} =>
          chartMatrix x I hI pq.1 pq.2.1)).toRingHom)

/-! ### The presented matrix along an arbitrary morphism, and change of basis

The overlap compatibility of the chart morphisms compares the two presentations of the
quotient on the intersection `T_I ∩ T_J`. The block below isolates the generic matrix
algebra: along any morphism `j : P ⟶ T` where the chart composite `c_I` pulls back to an
isomorphism, the quotient is presented by a matrix `presentedMatrix`; where two chart
composites are simultaneously invertible the two presentations differ by the (invertible)
`J`-minor of the first — Nitsure's `M^I = M^I_J · M^J`. -/

/-- The inverse free-pullback comparison intertwines index maps:
`Q_n⁻¹ ≫ p^*(freeMap g) = freeMap g ≫ Q_m⁻¹`. Inverse form of
`pullback_map_freeMap_pullbackFreeIso`. Project-local. -/
lemma pullbackFreeIso_inv_freeMap {W V : Scheme.{0}} (p : W ⟶ V) {n m : ℕ}
    (g : Fin n → Fin m) :
    (Scheme.Modules.pullbackFreeIso p (Fin n)).inv ≫
      (Scheme.Modules.pullback p).map (SheafOfModules.freeMap (R := V.ringCatSheaf) g)
    = SheafOfModules.freeMap (R := W.ringCatSheaf) g ≫
      (Scheme.Modules.pullbackFreeIso p (Fin m)).inv := by
  rw [← cancel_mono (Scheme.Modules.pullbackFreeIso p (Fin m)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [pullback_map_freeMap_pullbackFreeIso p g]
  rw [Iso.inv_hom_id_assoc]
  exact ((Category.assoc _ _ _).trans
    ((congrArg (SheafOfModules.freeMap (R := W.ringCatSheaf) g ≫ ·)
      (Iso.inv_hom_id _)).trans (Category.comp_id _))).symm

/-- The **presented matrix of a rank quotient along a morphism** `j : P ⟶ T` on which the
`I`-th chart composite pulls back to an isomorphism: the `unitEndSection` matrix of
`Q_r⁻¹ ≫ j^*q ≫ (j^* c_I)⁻¹ ≫ Q_d`. Generalises `chartMatrix` (the case
`j = (chartLocus x I hI).ι`); the vehicle of the overlap comparison. Project-local. -/
noncomputable def presentedMatrix {T P : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (j : P ⟶ T) (I : Finset (Fin r)) (hI : I.card = d)
    [hcI : IsIso ((Scheme.Modules.pullback j).map (chartComposite x I hI))] :
    Matrix (Fin d) (Fin r) Γ(P, ⊤) :=
  Matrix.of fun p i =>
    unitEndSection (SheafOfModules.ιFree i ≫
      ((Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
        (Scheme.Modules.pullback j).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom) ≫ projFree p)

/-- The presented matrix presents: `matrixEndRect (presentedMatrix …)` is the conjugated
pullback of `q` against the inverted chart composite. Project-local. -/
lemma matrixEndRect_presentedMatrix {T P : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (j : P ⟶ T) (I : Finset (Fin r)) (hI : I.card = d)
    [hcI : IsIso ((Scheme.Modules.pullback j).map (chartComposite x I hI))] :
    matrixEndRect (presentedMatrix x j I hI)
      = (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
        (Scheme.Modules.pullback j).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom :=
  matrixEndRect_unitEndSection
    ((Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
      (Scheme.Modules.pullback j).map x.q ≫
      @CategoryTheory.inv _ _ _ _
        ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
      (Scheme.Modules.pullbackFreeIso j (Fin d)).hom)

/-- The **`J`-minor of the `I`-presented matrix** presents the pulled-back `J`-chart
composite against the inverted `I`-chart composite. Project-local. -/
lemma matrixEndRect_presentedMatrix_minor {T P : Scheme.{0}} {r d : ℕ}
    (x : RankQuotient r d T) (j : P ⟶ T)
    (I : Finset (Fin r)) (hI : I.card = d) (J : Finset (Fin r)) (hJ : J.card = d)
    [hcI : IsIso ((Scheme.Modules.pullback j).map (chartComposite x I hI))] :
    matrixEndRect ((presentedMatrix x j I hI).submatrix id
        (fun k : Fin d => (J.orderIsoOfFin hJ k : Fin r)))
      = (Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫
        (Scheme.Modules.pullback j).map (chartComposite x J hJ) ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom := by
  rw [← freeMap_matrixEndRect, matrixEndRect_presentedMatrix]
  -- `(pb j).map (freeMap σ_J) ≫ (pb j).map q = (pb j).map c_J`
  have hcJ : (Scheme.Modules.pullback j).map (SheafOfModules.freeMap
        (fun k : Fin d => (J.orderIsoOfFin hJ k : Fin r))) ≫
        (Scheme.Modules.pullback j).map x.q
      = (Scheme.Modules.pullback j).map (chartComposite x J hJ) :=
    ((Scheme.Modules.pullback j).map_comp _ _).symm
  calc SheafOfModules.freeMap (fun k : Fin d => (J.orderIsoOfFin hJ k : Fin r)) ≫
      (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
      (Scheme.Modules.pullback j).map x.q ≫
      @CategoryTheory.inv _ _ _ _
        ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
      (Scheme.Modules.pullbackFreeIso j (Fin d)).hom
      = (SheafOfModules.freeMap (fun k : Fin d => (J.orderIsoOfFin hJ k : Fin r)) ≫
        (Scheme.Modules.pullbackFreeIso j (Fin r)).inv) ≫
        (Scheme.Modules.pullback j).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom := (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫
        (Scheme.Modules.pullback j).map (SheafOfModules.freeMap
          (fun k : Fin d => (J.orderIsoOfFin hJ k : Fin r)))) ≫
        (Scheme.Modules.pullback j).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom :=
        congrArg (· ≫ (Scheme.Modules.pullback j).map x.q ≫
          @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
          (Scheme.Modules.pullbackFreeIso j (Fin d)).hom)
          (pullbackFreeIso_inv_freeMap j
            (fun k : Fin d => (J.orderIsoOfFin hJ k : Fin r))).symm
    _ = (Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫
        ((Scheme.Modules.pullback j).map (SheafOfModules.freeMap
          (fun k : Fin d => (J.orderIsoOfFin hJ k : Fin r))) ≫
        (Scheme.Modules.pullback j).map x.q) ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom :=
        (Category.assoc _ _ _).trans
          (congrArg ((Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫ ·)
            (Category.assoc _ _ _).symm)
    _ = (Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫
        (Scheme.Modules.pullback j).map (chartComposite x J hJ) ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫ z ≫
          @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
          (Scheme.Modules.pullbackFreeIso j (Fin d)).hom) hcJ

set_option maxHeartbeats 800000 in
-- the eight-factor middle collapse is a long term-mode chain
/-- **Change of basis between two chart presentations** (Nitsure §1, the overlap matrix
identity `M^I = M^I_J · M^J`): along any morphism on which both chart composites become
invertible, the `I`-presented matrix is the product of its own `J`-minor with the
`J`-presented matrix. The matrix heart of `grPointOfRankQuotient`'s overlap
compatibility. Project-local. -/
lemma presentedMatrix_changeOfBasis {T P : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (j : P ⟶ T) (I : Finset (Fin r)) (hI : I.card = d) (J : Finset (Fin r)) (hJ : J.card = d)
    [hcI : IsIso ((Scheme.Modules.pullback j).map (chartComposite x I hI))]
    [hcJ : IsIso ((Scheme.Modules.pullback j).map (chartComposite x J hJ))] :
    presentedMatrix x j I hI
      = (presentedMatrix x j I hI).submatrix id
          (fun k : Fin d => (J.orderIsoOfFin hJ k : Fin r)) * presentedMatrix x j J hJ := by
  apply matrixEndRect_injective
  rw [← matrixEndRect_comp_rect, matrixEndRect_presentedMatrix,
    matrixEndRect_presentedMatrix, matrixEndRect_presentedMatrix_minor]
  exact (calc ((Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
        (Scheme.Modules.pullback j).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x J hJ)) hcJ ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom) ≫
      ((Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫
        (Scheme.Modules.pullback j).map (chartComposite x J hJ) ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom)
      = (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
        ((Scheme.Modules.pullback j).map x.q ≫
          @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x J hJ)) hcJ ≫
          (Scheme.Modules.pullbackFreeIso j (Fin d)).hom) ≫
        ((Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫
          (Scheme.Modules.pullback j).map (chartComposite x J hJ) ≫
          @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
          (Scheme.Modules.pullbackFreeIso j (Fin d)).hom) := Category.assoc _ _ _
    _ = (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
        (Scheme.Modules.pullback j).map x.q ≫
        (inv ((Scheme.Modules.pullback j).map (chartComposite x J hJ)) ≫
          (Scheme.Modules.pullbackFreeIso j (Fin d)).hom) ≫
        ((Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫
          (Scheme.Modules.pullback j).map (chartComposite x J hJ) ≫
          @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
          (Scheme.Modules.pullbackFreeIso j (Fin d)).hom) :=
        congrArg ((Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫ ·)
          (Category.assoc _ _ _)
    _ = (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
        (Scheme.Modules.pullback j).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x J hJ)) hcJ ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫
        (Scheme.Modules.pullback j).map (chartComposite x J hJ) ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
          (Scheme.Modules.pullback j).map x.q ≫ z) (Category.assoc _ _ _)
    _ = (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
        (Scheme.Modules.pullback j).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x J hJ)) hcJ ≫
        (Scheme.Modules.pullback j).map (chartComposite x J hJ) ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
          (Scheme.Modules.pullback j).map x.q ≫
          @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x J hJ)) hcJ ≫ z)
          (Iso.hom_inv_id_assoc _ _)
    _ = (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
        (Scheme.Modules.pullback j).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback j).map (chartComposite x I hI)) hcI ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
          (Scheme.Modules.pullback j).map x.q ≫ z)
          (IsIso.inv_hom_id_assoc _ _)).symm

/-- **A square matrix whose `matrixEndRect` is an isomorphism is a unit**: present the
inverse morphism by its `unitEndSection` matrix and conclude with the composition law and
injectivity. Converse of `matrixToFreeIso`; supplies the `IsUnit (det M^I_J)` input of
the localization step in the overlap compatibility. Project-local. -/
lemma isUnit_of_isIso_matrixEndRect {S : Scheme.{0}} {d : ℕ}
    (N : Matrix (Fin d) (Fin d) Γ(S, ⊤)) (h : IsIso (matrixEndRect N)) :
    IsUnit N := by
  haveI := h
  have hpres : matrixEndRect (Matrix.of fun p k =>
      unitEndSection (SheafOfModules.ιFree k ≫ inv (matrixEndRect N) ≫ projFree p))
      = inv (matrixEndRect N) := matrixEndRect_unitEndSection (inv (matrixEndRect N))
  have h1 : N * Matrix.of (fun p k =>
      unitEndSection (SheafOfModules.ιFree k ≫ inv (matrixEndRect N) ≫ projFree p)) = 1 := by
    apply matrixEndRect_injective
    rw [← matrixEndRect_comp_rect, hpres, matrixEndRect_one]
    exact IsIso.inv_hom_id _
  have h2 : Matrix.of (fun p k =>
      unitEndSection (SheafOfModules.ιFree k ≫ inv (matrixEndRect N) ≫ projFree p)) * N = 1 := by
    apply matrixEndRect_injective
    rw [← matrixEndRect_comp_rect, hpres, matrixEndRect_one]
    exact IsIso.hom_inv_id _
  exact ⟨⟨N, Matrix.of (fun p k =>
    unitEndSection (SheafOfModules.ιFree k ≫ inv (matrixEndRect N) ≫ projFree p)),
    h1, h2⟩, rfl⟩

/-- An equivalence of rank quotients intertwines the chart composites: if `f` witnesses
`x ∼ y` then `(s_I ≫ q_x) ≫ f = s_I ≫ q_y`. Project-local helper for
`grPointOfRankQuotient_rel`. -/
lemma chartComposite_rel {T : Scheme.{0}} {r d : ℕ} {x y : RankQuotient r d T}
    (f : x.F ≅ y.F) (hf : x.q ≫ f.hom = y.q) (I : Finset (Fin r)) (hI : I.card = d) :
    chartComposite x I hI ≫ f.hom = chartComposite y I hI :=
  (Category.assoc _ _ _).trans
    (congrArg
      (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫ ·) hf)

/-- **The chart composite of a pulled-back rank quotient** is the pullback of the chart
composite, conjugated through the free-pullback comparison: the coordinate inclusion
slides through `pullbackFreeIso` (`pullbackFreeIso_inv_freeMap`). The bridge between the
chart data of `rqPullback ψ y` and the `ψ`-pullback of the chart data of `y` — first
ingredient of the `represents` inverse laws. Project-local. -/
lemma chartComposite_rqPullback {T' T : Scheme.{0}} {r d : ℕ} (ψ : T' ⟶ T)
    (y : RankQuotient r d T) (I : Finset (Fin r)) (hI : I.card = d) :
    chartComposite (rqPullback ψ y) I hI
      = (Scheme.Modules.pullbackFreeIso ψ (Fin d)).inv ≫
        (Scheme.Modules.pullback ψ).map (chartComposite y I hI) := by
  change SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
      (Scheme.Modules.pullbackFreeIso ψ (Fin r)).inv ≫
      (Scheme.Modules.pullback ψ).map y.q
    = _
  calc SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
        (Scheme.Modules.pullbackFreeIso ψ (Fin r)).inv ≫
        (Scheme.Modules.pullback ψ).map y.q
      = (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
          (Scheme.Modules.pullbackFreeIso ψ (Fin r)).inv) ≫
        (Scheme.Modules.pullback ψ).map y.q := (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.pullbackFreeIso ψ (Fin d)).inv ≫
          (Scheme.Modules.pullback ψ).map (SheafOfModules.freeMap
            (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)))) ≫
        (Scheme.Modules.pullback ψ).map y.q :=
        congrArg (· ≫ (Scheme.Modules.pullback ψ).map y.q)
          (pullbackFreeIso_inv_freeMap ψ
            (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))).symm
    _ = (Scheme.Modules.pullbackFreeIso ψ (Fin d)).inv ≫
        ((Scheme.Modules.pullback ψ).map (SheafOfModules.freeMap
            (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫
          (Scheme.Modules.pullback ψ).map y.q) := Category.assoc _ _ _
    _ = (Scheme.Modules.pullbackFreeIso ψ (Fin d)).inv ≫
        (Scheme.Modules.pullback ψ).map (chartComposite y I hI) :=
        congrArg ((Scheme.Modules.pullbackFreeIso ψ (Fin d)).inv ≫ ·)
          ((Scheme.Modules.pullback ψ).map_comp _ _).symm

/-- Equivalent rank quotients have **equal chart loci**: post-composition with the
witnessing isomorphism does not change where the chart composite is invertible.
Project-local helper for `grPointOfRankQuotient_rel`. -/
lemma chartLocus_rel {T : Scheme.{0}} {r d : ℕ} {x y : RankQuotient r d T}
    (h : x.Rel y) (I : Finset (Fin r)) (hI : I.card = d) :
    chartLocus x I hI = chartLocus y I hI := by
  obtain ⟨f, hf⟩ := h
  have key : ∀ U : T.Opens,
      IsIso ((Scheme.Modules.pullback U.ι).map (chartComposite x I hI))
        ↔ IsIso ((Scheme.Modules.pullback U.ι).map (chartComposite y I hI)) := by
    intro U
    haveI : IsIso ((Scheme.Modules.pullback U.ι).map f.hom) :=
      inferInstanceAs (IsIso ((Scheme.Modules.pullback U.ι).mapIso f).hom)
    -- term-mode comparison (positional `rw [Functor.map_comp]` misses the comp node
    -- under the `T.Modules` diamond)
    have hcomp : (Scheme.Modules.pullback U.ι).map (chartComposite x I hI) ≫
          (Scheme.Modules.pullback U.ι).map f.hom
        = (Scheme.Modules.pullback U.ι).map (chartComposite y I hI) :=
      ((Scheme.Modules.pullback U.ι).map_comp _ _).symm.trans
        (congrArg ((Scheme.Modules.pullback U.ι).map) (chartComposite_rel f hf I hI))
    rw [← hcomp]
    exact (isIso_comp_right_iff _ _).symm
  exact congrArg sSup (Set.ext fun U => key U)

/-! ### Transport of the chart data along an inclusion of loci

`grPointOfRankQuotient_rel` compares the glued morphisms of two equivalent quotients. The
chart loci agree (`chartLocus_rel`), so the comparison reduces to transporting the
presenting matrix along the inclusion `homOfLE` of the (equal) chart loci and cancelling
the witnessing isomorphism `f`. The block below builds that transport: section-level
extensionality for endomorphisms of the unit sheaf (`scalarEnd_unitEndSection`), entry
extraction for `matrixEndRect` (`ιFree_matrixEndRect_projFree`), the matrix presentation
of an arbitrary morphism of free sheaves (`matrixEndRect_unitEndSection`), the conjugated
pullback of a matrix morphism (`pullback_conj_matrixEndRect`), pseudofunctor coherence
for the conjugated chart data (`conjPullback_comp`), and the chart-level transports
(`chartMatrixHom_rel` / `chartMatrixHom_transport` / `chartMatrix_rel` /
`chartMorphism_rel`). -/

/-- The conjugated-pullback presentation of a quotient-against-inverse pair is invariant
under an equality of the base morphisms. Generic `subst` lemma (the `IsIso` instances are
propositionally irrelevant). Project-local. -/
lemma conjPullback_congr {Wx X : Scheme.{0}} {j j' : Wx ⟶ X} (hjj : j = j') {r d : ℕ}
    {F : X.Modules} (u : SheafOfModules.free (R := X.ringCatSheaf) (Fin r) ⟶ F)
    (c : SheafOfModules.free (R := X.ringCatSheaf) (Fin d) ⟶ F)
    [IsIso ((Scheme.Modules.pullback j).map c)]
    [IsIso ((Scheme.Modules.pullback j').map c)] :
    (Scheme.Modules.pullbackFreeIso j (Fin r)).inv ≫
        (Scheme.Modules.pullback j).map u ≫
        inv ((Scheme.Modules.pullback j).map c) ≫
        (Scheme.Modules.pullbackFreeIso j (Fin d)).hom
      = (Scheme.Modules.pullbackFreeIso j' (Fin r)).inv ≫
        (Scheme.Modules.pullback j').map u ≫
        inv ((Scheme.Modules.pullback j').map c) ≫
        (Scheme.Modules.pullbackFreeIso j' (Fin d)).hom := by
  subst hjj; rfl

/-- Inverse-side composite free coherence: `Q_{p≫a}⁻¹ ≫ (pullbackComp p a).inv.app (free)
= Q_p⁻¹ ≫ p^*(Q_a⁻¹)`. The inverse form of `pullbackFreeIso_comp` (the `hstar` of the
functor `map_comp` proof, extracted generically). Project-local. -/
lemma pullbackFreeIso_inv_pullbackComp {W V X : Scheme.{0}} (p : W ⟶ V) (a : V ⟶ X)
    (n : Type) :
    (Scheme.Modules.pullbackFreeIso (p ≫ a) n).inv ≫
        (Scheme.Modules.pullbackComp p a).inv.app
          (SheafOfModules.free (R := X.ringCatSheaf) n)
      = (Scheme.Modules.pullbackFreeIso p n).inv ≫
        (Scheme.Modules.pullback p).map (Scheme.Modules.pullbackFreeIso a n).inv := by
  have hH := Scheme.Modules.pullbackFreeIso_comp a p n
  rw [← cancel_epi ((Scheme.Modules.pullbackComp p a).hom.app
    (SheafOfModules.free (R := X.ringCatSheaf) n) ≫
    (Scheme.Modules.pullbackFreeIso (p ≫ a) n).hom)]
  trans (𝟙 _)
  · rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact (Scheme.Modules.pullbackComp p a).hom_inv_id_app _
  · rw [hH]; simp

/-- **Pseudofunctor coherence for the conjugated chart data**: presenting
`q`-against-`inv c` after pullback along a composite `p ≫ a` is the same as pulling the
`a`-level presentation back along `p` (all comparisons through `pullbackFreeIso` /
`pullbackComp`). Project-local — the transport engine for `chartMatrixHom`. -/
lemma conjPullback_comp {W V X : Scheme.{0}} (p : W ⟶ V) (a : V ⟶ X) {r d : ℕ}
    {F : X.Modules} (u : SheafOfModules.free (R := X.ringCatSheaf) (Fin r) ⟶ F)
    (c : SheafOfModules.free (R := X.ringCatSheaf) (Fin d) ⟶ F)
    [IsIso ((Scheme.Modules.pullback a).map c)]
    [IsIso ((Scheme.Modules.pullback (p ≫ a)).map c)] :
    (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin r)).inv ≫
        (Scheme.Modules.pullback (p ≫ a)).map u ≫
        inv ((Scheme.Modules.pullback (p ≫ a)).map c) ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom
      = (Scheme.Modules.pullbackFreeIso p (Fin r)).inv ≫
        (Scheme.Modules.pullback p).map
          ((Scheme.Modules.pullbackFreeIso a (Fin r)).inv ≫
            (Scheme.Modules.pullback a).map u ≫
            inv ((Scheme.Modules.pullback a).map c) ≫
            (Scheme.Modules.pullbackFreeIso a (Fin d)).hom) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin d)).hom := by
  -- naturality of `pullbackComp.inv` at `u` and `c`
  have h_u : (Scheme.Modules.pullback (p ≫ a)).map u ≫
        (Scheme.Modules.pullbackComp p a).inv.app F
      = (Scheme.Modules.pullbackComp p a).inv.app
          (SheafOfModules.free (R := X.ringCatSheaf) (Fin r)) ≫
        (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map u) :=
    (Scheme.Modules.pullbackComp p a).inv.naturality u
  have h_c : (Scheme.Modules.pullback (p ≫ a)).map c ≫
        (Scheme.Modules.pullbackComp p a).inv.app F
      = (Scheme.Modules.pullbackComp p a).inv.app
          (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
        (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map c) :=
    (Scheme.Modules.pullbackComp p a).inv.naturality c
  -- conjugate the inverse through the pseudofunctor-composition cast (the middle factor
  -- is spelled `p^*(inv (a^* c))`, NOT `inv (p^*(a^* c))`, so no instance search has to
  -- cross the `X.Modules` diamond)
  have s2 : (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map c) ≫
        (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c))
      = 𝟙 _ :=
    ((Scheme.Modules.pullback p).map_comp _ _).symm.trans
      ((congrArg ((Scheme.Modules.pullback p).map) (IsIso.hom_inv_id _)).trans
        ((Scheme.Modules.pullback p).map_id _))
  have h_invc : inv ((Scheme.Modules.pullback (p ≫ a)).map c)
      = (Scheme.Modules.pullbackComp p a).inv.app F ≫
        (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
        (Scheme.Modules.pullbackComp p a).hom.app
          (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) := by
    refine (IsIso.eq_inv_of_hom_inv_id ?_).symm
    -- fully term-mode (`rw`/`reassoc` matching fails across the `X.Modules` diamond)
    calc (Scheme.Modules.pullback (p ≫ a)).map c ≫
          (Scheme.Modules.pullbackComp p a).inv.app F ≫
          (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
          (Scheme.Modules.pullbackComp p a).hom.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d))
        = ((Scheme.Modules.pullback (p ≫ a)).map c ≫
            (Scheme.Modules.pullbackComp p a).inv.app F) ≫
          (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
          (Scheme.Modules.pullbackComp p a).hom.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) :=
          (Category.assoc _ _ _).symm
      _ = ((Scheme.Modules.pullbackComp p a).inv.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
            (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map c)) ≫
          (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
          (Scheme.Modules.pullbackComp p a).hom.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) :=
          congrArg (· ≫ (Scheme.Modules.pullback p).map
            (inv ((Scheme.Modules.pullback a).map c)) ≫
            (Scheme.Modules.pullbackComp p a).hom.app
              (SheafOfModules.free (R := X.ringCatSheaf) (Fin d))) h_c
      _ = (Scheme.Modules.pullbackComp p a).inv.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
          ((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map c) ≫
            (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c))) ≫
          (Scheme.Modules.pullbackComp p a).hom.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) := by
          simp only [Category.assoc]
      _ = (Scheme.Modules.pullbackComp p a).inv.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
          𝟙 _ ≫
          (Scheme.Modules.pullbackComp p a).hom.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) :=
          congrArg (fun z => (Scheme.Modules.pullbackComp p a).inv.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫ z ≫
            (Scheme.Modules.pullbackComp p a).hom.app
              (SheafOfModules.free (R := X.ringCatSheaf) (Fin d))) s2
      _ = (Scheme.Modules.pullbackComp p a).inv.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
          (Scheme.Modules.pullbackComp p a).hom.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) :=
          congrArg ((Scheme.Modules.pullbackComp p a).inv.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫ ·)
            (Category.id_comp _)
      _ = 𝟙 _ := (Scheme.Modules.pullbackComp p a).inv_hom_id_app _
  -- assemble: replace the inverse, transpose `u` through the cast, fuse the comparisons
  calc (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin r)).inv ≫
        (Scheme.Modules.pullback (p ≫ a)).map u ≫
        inv ((Scheme.Modules.pullback (p ≫ a)).map c) ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom
      = (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin r)).inv ≫
        (Scheme.Modules.pullback (p ≫ a)).map u ≫
        ((Scheme.Modules.pullbackComp p a).inv.app F ≫
          (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
          (Scheme.Modules.pullbackComp p a).hom.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d))) ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin r)).inv ≫
          (Scheme.Modules.pullback (p ≫ a)).map u ≫ z ≫
          (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom) h_invc
    _ = (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin r)).inv ≫
        ((Scheme.Modules.pullback (p ≫ a)).map u ≫
          (Scheme.Modules.pullbackComp p a).inv.app F) ≫
        (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
        (Scheme.Modules.pullbackComp p a).hom.app
          (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom := by
        simp only [Category.assoc]
    _ = (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin r)).inv ≫
        ((Scheme.Modules.pullbackComp p a).inv.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin r)) ≫
          (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map u)) ≫
        (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
        (Scheme.Modules.pullbackComp p a).hom.app
          (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin r)).inv ≫ z ≫
          (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
          (Scheme.Modules.pullbackComp p a).hom.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
          (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom) h_u
    _ = ((Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin r)).inv ≫
        (Scheme.Modules.pullbackComp p a).inv.app
          (SheafOfModules.free (R := X.ringCatSheaf) (Fin r))) ≫
        (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map u) ≫
        (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
        (Scheme.Modules.pullbackComp p a).hom.app
          (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom := by
        simp only [Category.assoc]
    _ = ((Scheme.Modules.pullbackFreeIso p (Fin r)).inv ≫
        (Scheme.Modules.pullback p).map (Scheme.Modules.pullbackFreeIso a (Fin r)).inv) ≫
        (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map u) ≫
        (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
        (Scheme.Modules.pullbackComp p a).hom.app
          (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom :=
        congrArg (· ≫ (Scheme.Modules.pullback p).map
            ((Scheme.Modules.pullback a).map u) ≫
          (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
          (Scheme.Modules.pullbackComp p a).hom.app
            (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
          (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom)
          (pullbackFreeIso_inv_pullbackComp p a (Fin r))
    _ = (Scheme.Modules.pullbackFreeIso p (Fin r)).inv ≫
        (Scheme.Modules.pullback p).map (Scheme.Modules.pullbackFreeIso a (Fin r)).inv ≫
        (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map u) ≫
        (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
        ((Scheme.Modules.pullbackComp p a).hom.app
          (SheafOfModules.free (R := X.ringCatSheaf) (Fin d)) ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom) := by
        simp only [Category.assoc]
    _ = (Scheme.Modules.pullbackFreeIso p (Fin r)).inv ≫
        (Scheme.Modules.pullback p).map (Scheme.Modules.pullbackFreeIso a (Fin r)).inv ≫
        (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map u) ≫
        (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫
        ((Scheme.Modules.pullback p).map (Scheme.Modules.pullbackFreeIso a (Fin d)).hom ≫
          (Scheme.Modules.pullbackFreeIso p (Fin d)).hom) :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso p (Fin r)).inv ≫
          (Scheme.Modules.pullback p).map
            (Scheme.Modules.pullbackFreeIso a (Fin r)).inv ≫
          (Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map u) ≫
          (Scheme.Modules.pullback p).map (inv ((Scheme.Modules.pullback a).map c)) ≫ z)
          (Scheme.Modules.pullbackFreeIso_comp a p (Fin d))
    _ = (Scheme.Modules.pullbackFreeIso p (Fin r)).inv ≫
        (Scheme.Modules.pullback p).map
          ((Scheme.Modules.pullbackFreeIso a (Fin r)).inv ≫
            (Scheme.Modules.pullback a).map u ≫
            inv ((Scheme.Modules.pullback a).map c) ≫
            (Scheme.Modules.pullbackFreeIso a (Fin d)).hom) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin d)).hom := by
        simp only [Functor.map_comp, Category.assoc]

/-- **Cancellation of the witnessing isomorphism in the presenting morphism**: over the
chart locus of `y`, presenting `y` is the same as presenting `x` (the post-composition
isomorphism `f` cancels between the quotient and the inverted chart composite).
Project-local. -/
lemma chartMatrixHom_rel {T : Scheme.{0}} {r d : ℕ} {x y : RankQuotient r d T}
    (f : x.F ≅ y.F) (hf : x.q ≫ f.hom = y.q) (I : Finset (Fin r)) (hI : I.card = d)
    [IsIso ((Scheme.Modules.pullback (chartLocus y I hI).ι).map (chartComposite x I hI))] :
    chartMatrixHom y I hI
      = (Scheme.Modules.pullbackFreeIso (chartLocus y I hI).ι (Fin r)).inv ≫
        (Scheme.Modules.pullback (chartLocus y I hI).ι).map x.q ≫
        inv ((Scheme.Modules.pullback (chartLocus y I hI).ι).map (chartComposite x I hI)) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus y I hI).ι (Fin d)).hom := by
  haveI : IsIso ((Scheme.Modules.pullback (chartLocus y I hI).ι).map
      (chartComposite y I hI)) :=
    isIso_pullback_isoLocus_map _
  haveI : IsIso ((Scheme.Modules.pullback (chartLocus y I hI).ι).map f.hom) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pullback (chartLocus y I hI).ι).mapIso f).hom)
  have hq : (Scheme.Modules.pullback (chartLocus y I hI).ι).map y.q
      = (Scheme.Modules.pullback (chartLocus y I hI).ι).map x.q ≫
        (Scheme.Modules.pullback (chartLocus y I hI).ι).map f.hom := by
    rw [← Functor.map_comp]
    exact congrArg _ hf.symm
  have hc : (Scheme.Modules.pullback (chartLocus y I hI).ι).map (chartComposite y I hI)
      = (Scheme.Modules.pullback (chartLocus y I hI).ι).map (chartComposite x I hI) ≫
        (Scheme.Modules.pullback (chartLocus y I hI).ι).map f.hom := by
    rw [← Functor.map_comp]
    exact congrArg _ (chartComposite_rel f hf I hI).symm
  have hinv : inv ((Scheme.Modules.pullback (chartLocus y I hI).ι).map
        (chartComposite y I hI))
      = inv ((Scheme.Modules.pullback (chartLocus y I hI).ι).map f.hom) ≫
        inv ((Scheme.Modules.pullback (chartLocus y I hI).ι).map (chartComposite x I hI)) := by
    refine (IsIso.eq_inv_of_hom_inv_id ?_).symm
    rw [hc]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc, IsIso.hom_inv_id]
  change (Scheme.Modules.pullbackFreeIso (chartLocus y I hI).ι (Fin r)).inv ≫
      (Scheme.Modules.pullback (chartLocus y I hI).ι).map y.q ≫
      inv ((Scheme.Modules.pullback (chartLocus y I hI).ι).map (chartComposite y I hI)) ≫
      (Scheme.Modules.pullbackFreeIso (chartLocus y I hI).ι (Fin d)).hom = _
  rw [hq, hinv]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]

/-- **Transport of the presenting morphism along an inclusion of chart loci**: for
equivalent quotients, the presenting morphism of `x` over its chart locus is the
conjugated pullback (along the `homOfLE` of the locus inclusion) of the presenting
morphism of `y`. Project-local. -/
lemma chartMatrixHom_transport {T : Scheme.{0}} {r d : ℕ} {x y : RankQuotient r d T}
    (f : x.F ≅ y.F) (hf : x.q ≫ f.hom = y.q) (I : Finset (Fin r)) (hI : I.card = d)
    (e : chartLocus x I hI ≤ chartLocus y I hI) :
    chartMatrixHom x I hI
      = (Scheme.Modules.pullbackFreeIso (T.homOfLE e) (Fin r)).inv ≫
        (Scheme.Modules.pullback (T.homOfLE e)).map (chartMatrixHom y I hI) ≫
        (Scheme.Modules.pullbackFreeIso (T.homOfLE e) (Fin d)).hom := by
  haveI hx : IsIso ((Scheme.Modules.pullback (chartLocus x I hI).ι).map
      (chartComposite x I hI)) :=
    isIso_pullback_isoLocus_map _
  haveI hyx : IsIso ((Scheme.Modules.pullback (chartLocus y I hI).ι).map
      (chartComposite x I hI)) := by
    have hcc : chartComposite x I hI = chartComposite y I hI ≫ f.inv :=
      (Iso.eq_comp_inv f).mpr (chartComposite_rel f hf I hI)
    have hmap : (Scheme.Modules.pullback (chartLocus y I hI).ι).map (chartComposite x I hI)
        = (Scheme.Modules.pullback (chartLocus y I hI).ι).map (chartComposite y I hI) ≫
          (Scheme.Modules.pullback (chartLocus y I hI).ι).map f.inv :=
      (congrArg ((Scheme.Modules.pullback (chartLocus y I hI).ι).map) hcc).trans
        ((Scheme.Modules.pullback (chartLocus y I hI).ι).map_comp _ _)
    rw [hmap]
    haveI : IsIso ((Scheme.Modules.pullback (chartLocus y I hI).ι).map
        (chartComposite y I hI)) :=
      isIso_pullback_isoLocus_map _
    haveI : IsIso ((Scheme.Modules.pullback (chartLocus y I hI).ι).map f.inv) :=
      inferInstanceAs (IsIso ((Scheme.Modules.pullback (chartLocus y I hI).ι).mapIso f).inv)
    exact inferInstance
  haveI hcomp : IsIso ((Scheme.Modules.pullback
      (T.homOfLE e ≫ (chartLocus y I hI).ι)).map (chartComposite x I hI)) := by
    rw [T.homOfLE_ι e]
    exact hx
  have h1 : chartMatrixHom x I hI
      = (Scheme.Modules.pullbackFreeIso (T.homOfLE e ≫ (chartLocus y I hI).ι) (Fin r)).inv ≫
        (Scheme.Modules.pullback (T.homOfLE e ≫ (chartLocus y I hI).ι)).map x.q ≫
        inv ((Scheme.Modules.pullback (T.homOfLE e ≫ (chartLocus y I hI).ι)).map
          (chartComposite x I hI)) ≫
        (Scheme.Modules.pullbackFreeIso (T.homOfLE e ≫ (chartLocus y I hI).ι) (Fin d)).hom :=
    conjPullback_congr (T.homOfLE_ι e).symm x.q (chartComposite x I hI)
  have h2 := conjPullback_comp (T.homOfLE e) (chartLocus y I hI).ι x.q
    (chartComposite x I hI)
  have h3 : chartMatrixHom y I hI
      = (Scheme.Modules.pullbackFreeIso (chartLocus y I hI).ι (Fin r)).inv ≫
        (Scheme.Modules.pullback (chartLocus y I hI).ι).map x.q ≫
        inv ((Scheme.Modules.pullback (chartLocus y I hI).ι).map (chartComposite x I hI)) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus y I hI).ι (Fin d)).hom :=
    chartMatrixHom_rel f hf I hI
  exact h1.trans (h2.trans (congrArg
    (fun m => (Scheme.Modules.pullbackFreeIso (T.homOfLE e) (Fin r)).inv ≫
      (Scheme.Modules.pullback (T.homOfLE e)).map m ≫
      (Scheme.Modules.pullbackFreeIso (T.homOfLE e) (Fin d)).hom) h3.symm))

/-- **Transport of the presenting matrix**: the entries of `chartMatrix x` are the
restrictions (along the inclusion of the equal chart loci) of the entries of
`chartMatrix y`. Project-local. -/
lemma chartMatrix_rel {T : Scheme.{0}} {r d : ℕ} {x y : RankQuotient r d T}
    (f : x.F ≅ y.F) (hf : x.q ≫ f.hom = y.q) (I : Finset (Fin r)) (hI : I.card = d)
    (e : chartLocus x I hI ≤ chartLocus y I hI) (p : Fin d) (i : Fin r) :
    chartMatrix x I hI p i
      = (CommRingCat.Hom.hom (Scheme.Hom.appTop (T.homOfLE e)))
          (chartMatrix y I hI p i) := by
  have h1 : chartMatrixHom x I hI
      = matrixEndRect ((chartMatrix y I hI).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (T.homOfLE e)))) := by
    rw [chartMatrixHom_transport f hf I hI e,
      show chartMatrixHom y I hI = matrixEndRect (chartMatrix y I hI) from
        (matrixEndRect_unitEndSection (chartMatrixHom y I hI)).symm]
    exact pullback_conj_matrixEndRect (T.homOfLE e) (chartMatrix y I hI)
  calc chartMatrix x I hI p i
      = unitEndSection (SheafOfModules.ιFree i ≫ chartMatrixHom x I hI ≫ projFree p) := rfl
    _ = unitEndSection (SheafOfModules.ιFree i ≫
          matrixEndRect ((chartMatrix y I hI).map
            ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (T.homOfLE e)))) ≫ projFree p) := by
        rw [h1]
    _ = unitEndSection (scalarEnd (((chartMatrix y I hI).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (T.homOfLE e)))) p i)) := by
        rw [ιFree_matrixEndRect_projFree]
    _ = ((chartMatrix y I hI).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (T.homOfLE e)))) p i :=
        unitEndSection_scalarEnd _
    _ = (CommRingCat.Hom.hom (Scheme.Hom.appTop (T.homOfLE e)))
          (chartMatrix y I hI p i) := Matrix.map_apply

/-- **Transport of the chart morphism**: for equivalent quotients, the chart morphism of
`x` factors through the chart morphism of `y` via the inclusion of the (equal) chart
loci. Project-local. -/
lemma chartMorphism_rel {T : Scheme.{0}} (d r : ℕ) {x y : RankQuotient r d T}
    (f : x.F ≅ y.F) (hf : x.q ≫ f.hom = y.q) (I : Finset (Fin r)) (hI : I.card = d)
    (e : chartLocus x I hI ≤ chartLocus y I hI) :
    chartMorphism d r x I hI = T.homOfLE e ≫ chartMorphism d r y I hI := by
  -- the classifying ring maps agree after restriction (entrywise: `chartMatrix_rel`)
  have hring : CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
        (fun pq : Fin d × {q : Fin r // q ∉ I} => chartMatrix x I hI pq.1 pq.2.1)).toRingHom
      = CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix y I hI pq.1 pq.2.1)).toRingHom ≫
        Scheme.Hom.appTop (T.homOfLE e) := by
    refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
      (fun pq => ?_))
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
    exact chartMatrix_rel f hf I hI e pq.1 pq.2.1
  have hnat : T.homOfLE e ≫ (chartLocus y I hI).toScheme.toSpecΓ
      = (chartLocus x I hI).toScheme.toSpecΓ ≫
        Spec.map (Scheme.Hom.appTop (T.homOfLE e)) :=
    Scheme.toSpecΓ_naturality (T.homOfLE e)
  have hspec : Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
        (fun pq : Fin d × {q : Fin r // q ∉ I} =>
          chartMatrix x I hI pq.1 pq.2.1)).toRingHom)
      = Spec.map (Scheme.Hom.appTop (T.homOfLE e)) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix y I hI pq.1 pq.2.1)).toRingHom) :=
    (congrArg Spec.map hring).trans (Spec.map_comp _ _)
  -- fully term-mode assembly (`rw` matching fails against the `change`d goal because the
  -- `aeval` instance paths of the def-unfolded term and a fresh elaboration differ)
  have key : (chartLocus x I hI).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom)
      = T.homOfLE e ≫ (chartLocus y I hI).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix y I hI pq.1 pq.2.1)).toRingHom) := calc
    (chartLocus x I hI).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom)
      = (chartLocus x I hI).toScheme.toSpecΓ ≫
        (Spec.map (Scheme.Hom.appTop (T.homOfLE e)) ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
            (fun pq : Fin d × {q : Fin r // q ∉ I} =>
              chartMatrix y I hI pq.1 pq.2.1)).toRingHom)) :=
        congrArg ((chartLocus x I hI).toScheme.toSpecΓ ≫ ·) hspec
    _ = ((chartLocus x I hI).toScheme.toSpecΓ ≫
          Spec.map (Scheme.Hom.appTop (T.homOfLE e))) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix y I hI pq.1 pq.2.1)).toRingHom) :=
        (Category.assoc _ _ _).symm
    _ = (T.homOfLE e ≫ (chartLocus y I hI).toScheme.toSpecΓ) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix y I hI pq.1 pq.2.1)).toRingHom) :=
        congrArg (· ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix y I hI pq.1 pq.2.1)).toRingHom)) hnat.symm
    _ = T.homOfLE e ≫ (chartLocus y I hI).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix y I hI pq.1 pq.2.1)).toRingHom) := Category.assoc _ _ _
  exact key

/-! ### The `I`-minor of the presenting matrix is the identity

The first ingredient of the chart-morphism overlap compatibility (Nitsure §1:
`φ_I^* X^I = M^I` with `M^I_I = 1`): composing the presenting morphism with the
`I`-indexed coordinate inclusion is the identity, because that composite presents the
chart composite against its own inverse. -/

/-- The chart composite pulls back to an isomorphism on the chart locus — the
`isIso_pullback_isoLocus_map` statement keyed on the `chartLocus` spelling, registered
as an instance so that `inv`-sites over the chart locus synthesize directly (term-level
`haveI` copies of this fact are NOT found across the `X.Modules` diamond). -/
instance isIso_pullback_chartLocus_map {T : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) :
    IsIso ((Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI)) :=
  isIso_pullback_isoLocus_map (chartComposite x I hI)

set_option maxHeartbeats 800000 in
/-- **The `I`-minor of the presenting morphism is the identity** (morphism level): the
`I`-indexed coordinate inclusion composed with `chartMatrixHom` presents the (invertible)
chart composite against its own inverse, hence is `𝟙`. Project-local — the
`M^I_I = 1` ingredient of the Nitsure overlap compatibility. -/
lemma freeMap_chartMatrixHom {T : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) :
    SheafOfModules.freeMap (R := (chartLocus x I hI).toScheme.ringCatSheaf)
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫ chartMatrixHom x I hI
      = 𝟙 (SheafOfModules.free (R := (chartLocus x I hI).toScheme.ringCatSheaf) (Fin d)) := by
  have hcomp := pullback_map_freeMap_pullbackFreeIso (chartLocus x I hI).ι
    (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))
  -- the comparison-naturality, inverted (term-mode; `rw` matching fails across the
  -- `X.Modules` diamond)
  have h1 : SheafOfModules.freeMap (R := (chartLocus x I hI).toScheme.ringCatSheaf)
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv
      = (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        (Scheme.Modules.pullback (chartLocus x I hI).ι).map
          (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) := calc
    SheafOfModules.freeMap (R := (chartLocus x I hI).toScheme.ringCatSheaf)
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv
      = 𝟙 _ ≫ SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv :=
        (Category.id_comp _).symm
    _ = ((Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom) ≫
        SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv :=
        congrArg (· ≫ SheafOfModules.freeMap
            (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
          (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv)
          (Iso.inv_hom_id _).symm
    _ = (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        ((Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom ≫
          SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv := by
        simp only [Category.assoc]
    _ = (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        ((Scheme.Modules.pullback (chartLocus x I hI).ι).map
            (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫
          (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).hom) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso
            (chartLocus x I hI).ι (Fin d)).inv ≫ z ≫
          (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv) hcomp.symm
    _ = (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        (Scheme.Modules.pullback (chartLocus x I hI).ι).map
          (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫
        ((Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).hom ≫
          (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv) := by
        simp only [Category.assoc]
    _ = (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        (Scheme.Modules.pullback (chartLocus x I hI).ι).map
          (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫
        𝟙 _ :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso
            (chartLocus x I hI).ι (Fin d)).inv ≫
          (Scheme.Modules.pullback (chartLocus x I hI).ι).map
            (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫ z)
          (Iso.hom_inv_id _)
    _ = (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        (Scheme.Modules.pullback (chartLocus x I hI).ι).map
          (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) :=
        congrArg ((Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫ ·)
          (Category.comp_id _)
  -- the pulled-back inclusion-then-quotient is the pulled-back chart composite
  have h2 : (Scheme.Modules.pullback (chartLocus x I hI).ι).map
        (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫
        (Scheme.Modules.pullback (chartLocus x I hI).ι).map x.q
      = (Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI) :=
    ((Scheme.Modules.pullback (chartLocus x I hI).ι).map_comp _ _).symm
  calc SheafOfModules.freeMap (R := (chartLocus x I hI).toScheme.ringCatSheaf)
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫ chartMatrixHom x I hI
      = (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
          (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin r)).inv) ≫
        (Scheme.Modules.pullback (chartLocus x I hI).ι).map x.q ≫
        (@CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI))
          (isIso_pullback_chartLocus_map x I hI)) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom := by
        simp only [Category.assoc]; rfl
    _ = ((Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
          (Scheme.Modules.pullback (chartLocus x I hI).ι).map
            (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)))) ≫
        (Scheme.Modules.pullback (chartLocus x I hI).ι).map x.q ≫
        (@CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI))
          (isIso_pullback_chartLocus_map x I hI)) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom :=
        congrArg (· ≫ (Scheme.Modules.pullback (chartLocus x I hI).ι).map x.q ≫
          (@CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI))
          (isIso_pullback_chartLocus_map x I hI)) ≫
          (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom) h1
    _ = (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        (((Scheme.Modules.pullback (chartLocus x I hI).ι).map
            (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫
          (Scheme.Modules.pullback (chartLocus x I hI).ι).map x.q) ≫
          (@CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI))
          (isIso_pullback_chartLocus_map x I hI))) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom := by
        simp only [Category.assoc]
    _ = (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        ((Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI) ≫
          (@CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI))
          (isIso_pullback_chartLocus_map x I hI))) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso
            (chartLocus x I hI).ι (Fin d)).inv ≫ z ≫
          (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom)
          (congrArg (· ≫ (@CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI))
          (isIso_pullback_chartLocus_map x I hI))) h2)
    _ = (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        𝟙 _ ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom :=
        congrArg (fun z => (Scheme.Modules.pullbackFreeIso
            (chartLocus x I hI).ι (Fin d)).inv ≫ z ≫
          (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom)
          (@IsIso.hom_inv_id _ _ _ _
            ((Scheme.Modules.pullback (chartLocus x I hI).ι).map (chartComposite x I hI))
            (isIso_pullback_chartLocus_map x I hI))
    _ = (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).hom :=
        congrArg ((Scheme.Modules.pullbackFreeIso (chartLocus x I hI).ι (Fin d)).inv ≫ ·)
          (Category.id_comp _)
    _ = 𝟙 _ := Iso.inv_hom_id _

/-- The section of the identity endomorphism of the unit sheaf is `1`. Project-local. -/
lemma unitEndSection_id {X : Scheme.{0}} :
    unitEndSection (𝟙 (SheafOfModules.unit X.ringCatSheaf)) = 1 := rfl

/-- The section of the zero endomorphism of the unit sheaf is `0`. Project-local. -/
lemma unitEndSection_zero {X : Scheme.{0}} :
    unitEndSection (0 : SheafOfModules.unit X.ringCatSheaf ⟶
      SheafOfModules.unit X.ringCatSheaf) = 0 := rfl

set_option maxHeartbeats 800000 in
/-- **The `I`-minor of the presenting matrix is the identity** (entry level):
`M^I_{p, ι_I(q)} = δ_{q p}`. Project-local — the entrywise form of
`freeMap_chartMatrixHom`, the `M^I_I = 1` ingredient of the overlap compatibility. -/
lemma chartMatrix_minor {T : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) (p q : Fin d) :
    chartMatrix x I hI p (I.orderIsoOfFin hI q : Fin r) = if q = p then 1 else 0 := by
  have h1 : SheafOfModules.ιFree (R := (chartLocus x I hI).toScheme.ringCatSheaf)
        (I.orderIsoOfFin hI q : Fin r) ≫ chartMatrixHom x I hI ≫ projFree p
      = SheafOfModules.ιFree q ≫ projFree p := by
    calc SheafOfModules.ιFree (R := (chartLocus x I hI).toScheme.ringCatSheaf)
          (I.orderIsoOfFin hI q : Fin r) ≫ chartMatrixHom x I hI ≫ projFree p
        = (SheafOfModules.ιFree q ≫
            SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r))) ≫
          chartMatrixHom x I hI ≫ projFree p :=
          congrArg (· ≫ chartMatrixHom x I hI ≫ projFree p)
            (SheafOfModules.ιFree_freeMap
              (R := (chartLocus x I hI).toScheme.ringCatSheaf)
              (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) q).symm
      _ = SheafOfModules.ιFree q ≫
          (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
            chartMatrixHom x I hI) ≫ projFree p := by
          simp only [Category.assoc]
      _ = SheafOfModules.ιFree q ≫ 𝟙 _ ≫ projFree p :=
          congrArg (fun z => SheafOfModules.ιFree q ≫ z ≫ projFree p)
            (freeMap_chartMatrixHom x I hI)
      _ = SheafOfModules.ιFree q ≫ projFree p :=
          congrArg (SheafOfModules.ιFree q ≫ ·) (Category.id_comp _)
  refine (congrArg unitEndSection h1).trans ?_
  rw [ιFree_projFree]
  by_cases h : q = p
  · rw [if_pos h, if_pos h]
    exact unitEndSection_id
  · rw [if_neg h, if_neg h]
    exact unitEndSection_zero

/-! ### Overlap compatibility of the chart morphisms (Nitsure §1 gluing step)

On the intersection `P = T_I ×_T T_J` of two chart loci both chart composites pull back
to isomorphisms, so the pulled-back quotient is presented by both matrices `M^I_P` and
`M^J_P`. The change-of-basis identity `M^I_P = (M^I_P)_J · M^J_P`
(`presentedMatrix_changeOfBasis`) identifies the `J`-classifying ring map with the
localization-transport `lift(aeval M^I_P) ∘ θ̃_{I,J}` of the `I`-classifying map, so the
two chart morphisms agree into the glued scheme by the glue condition (`chart_point_eq`,
the CommRing form of `existence_chart_kpoint_eq`). The block below supplies the
transports: invertibility along a composite (`isIso_pullback_map_comp`), the presented
matrix along a composite (`presentedMatrix_comp`) and along an equality of base
morphisms (`presentedMatrix_congr`), its own minor (`presentedMatrix_submatrix_self`),
the realisation `aeval(M^I)(X^I) = M^I` (`universalMatrix_map_presentedMatrix`), the
image-matrix transport (`imageMatrix_map_ringHom`), and chart-morphism naturality
(`comp_chartMorphism`). -/

/-- Invertibility of a pulled-back morphism of modules persists along precomposition of
the base morphism: if `a^*c` is an isomorphism then so is `(p ≫ a)^*c`, via the
pseudofunctor comparison `pullbackComp`. Project-local. -/
lemma isIso_pullback_map_comp {W V X : Scheme.{0}} (p : W ⟶ V) (a : V ⟶ X)
    {M N : X.Modules} (c : M ⟶ N) [IsIso ((Scheme.Modules.pullback a).map c)] :
    IsIso ((Scheme.Modules.pullback (p ≫ a)).map c) := by
  haveI h1 : IsIso ((Scheme.Modules.pullback p).map ((Scheme.Modules.pullback a).map c)) :=
    Functor.map_isIso _ _
  haveI h2 : IsIso ((Scheme.Modules.pullback a ⋙ Scheme.Modules.pullback p).map c) := h1
  exact (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp p a) c).mp h2

/-- The presented matrix only depends on the base morphism (the `IsIso` instances are
propositionally irrelevant). Generic `subst` lemma. Project-local. -/
lemma presentedMatrix_congr {T P : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    {j j' : P ⟶ T} (h : j = j') (I : Finset (Fin r)) (hI : I.card = d)
    [IsIso ((Scheme.Modules.pullback j).map (chartComposite x I hI))]
    [IsIso ((Scheme.Modules.pullback j').map (chartComposite x I hI))] :
    presentedMatrix x j I hI = presentedMatrix x j' I hI := by
  subst h; rfl

/-- The presenting matrix over the chart locus is the presented matrix along the locus
inclusion (definitional). Project-local. -/
lemma chartMatrix_eq_presentedMatrix {T : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) :
    chartMatrix x I hI = presentedMatrix x (chartLocus x I hI).ι I hI := rfl

set_option maxHeartbeats 800000 in
-- the pseudofunctor-comparison steps traverse the `X.Modules` instance diamond
/-- **Transport of the presented matrix along a composite**: the matrix presenting the
quotient after pulling back along `p ≫ a` is the entrywise `Γ`-restriction (along `p`)
of the matrix presenting it after pulling back along `a` — `conjPullback_comp` followed
by `pullback_conj_matrixEndRect`, compared through `matrixEndRect_injective`.
Project-local. -/
lemma presentedMatrix_comp {T W V : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (p : W ⟶ V) (a : V ⟶ T) (I : Finset (Fin r)) (hI : I.card = d)
    [hca : IsIso ((Scheme.Modules.pullback a).map (chartComposite x I hI))]
    [hcpa : IsIso ((Scheme.Modules.pullback (p ≫ a)).map (chartComposite x I hI))] :
    presentedMatrix x (p ≫ a) I hI
      = (presentedMatrix x a I hI).map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop p)) := by
  apply matrixEndRect_injective
  -- the four comparison steps, each with the `inv`-instances pinned explicitly (bare
  -- `inv` instance synthesis is unreliable under the `X.Modules` diamond)
  have h1 : matrixEndRect (presentedMatrix x (p ≫ a) I hI)
      = (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin r)).inv ≫
        (Scheme.Modules.pullback (p ≫ a)).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback (p ≫ a)).map (chartComposite x I hI)) hcpa ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom :=
    matrixEndRect_presentedMatrix x (p ≫ a) I hI
  have h2 : (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin r)).inv ≫
        (Scheme.Modules.pullback (p ≫ a)).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback (p ≫ a)).map (chartComposite x I hI)) hcpa ≫
        (Scheme.Modules.pullbackFreeIso (p ≫ a) (Fin d)).hom
      = (Scheme.Modules.pullbackFreeIso p (Fin r)).inv ≫
        (Scheme.Modules.pullback p).map
          ((Scheme.Modules.pullbackFreeIso a (Fin r)).inv ≫
            (Scheme.Modules.pullback a).map x.q ≫
            @CategoryTheory.inv _ _ _ _
              ((Scheme.Modules.pullback a).map (chartComposite x I hI)) hca ≫
            (Scheme.Modules.pullbackFreeIso a (Fin d)).hom) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin d)).hom :=
    conjPullback_comp p a x.q (chartComposite x I hI)
  have h3 : (Scheme.Modules.pullbackFreeIso a (Fin r)).inv ≫
        (Scheme.Modules.pullback a).map x.q ≫
        @CategoryTheory.inv _ _ _ _
          ((Scheme.Modules.pullback a).map (chartComposite x I hI)) hca ≫
        (Scheme.Modules.pullbackFreeIso a (Fin d)).hom
      = matrixEndRect (presentedMatrix x a I hI) :=
    (matrixEndRect_presentedMatrix x a I hI).symm
  have h4 : (Scheme.Modules.pullbackFreeIso p (Fin r)).inv ≫
        (Scheme.Modules.pullback p).map (matrixEndRect (presentedMatrix x a I hI)) ≫
        (Scheme.Modules.pullbackFreeIso p (Fin d)).hom
      = matrixEndRect ((presentedMatrix x a I hI).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop p))) :=
    pullback_conj_matrixEndRect p (presentedMatrix x a I hI)
  exact h1.trans (h2.trans ((congrArg (fun z =>
    (Scheme.Modules.pullbackFreeIso p (Fin r)).inv ≫
      (Scheme.Modules.pullback p).map z ≫
      (Scheme.Modules.pullbackFreeIso p (Fin d)).hom) h3).trans h4))

/-- **The own-minor of the presented matrix is the identity**: the `I`-columns of `M^I`
present the inverted chart composite against itself. Project-local — the matrix-level
`M^I_I = 1`. -/
lemma presentedMatrix_submatrix_self {T P : Scheme.{0}} {r d : ℕ} (x : RankQuotient r d T)
    (j : P ⟶ T) (I : Finset (Fin r)) (hI : I.card = d)
    [IsIso ((Scheme.Modules.pullback j).map (chartComposite x I hI))] :
    (presentedMatrix x j I hI).submatrix id
      (fun k : Fin d => (I.orderIsoOfFin hI k : Fin r)) = 1 := by
  apply matrixEndRect_injective
  rw [matrixEndRect_presentedMatrix_minor x j I hI I hI, matrixEndRect_one]
  exact (congrArg ((Scheme.Modules.pullbackFreeIso j (Fin d)).inv ≫ ·)
    (IsIso.hom_inv_id_assoc _ _)).trans (Iso.inv_hom_id _)

set_option maxHeartbeats 800000 in
-- the entrywise comparison elaborates `presentedMatrix` (a conjugated pullback) per entry
/-- **The classifying map realises the universal matrix as the presented matrix**:
applying `aeval(M^I)` entrywise to `X^I` returns `M^I` — on the free entries by
`aeval_X`, on the `I`-columns because both minors are the identity
(`presentedMatrix_submatrix_self`). Analogue of `universalMatrix_map_transitionPreMap`.
Project-local. -/
lemma universalMatrix_map_presentedMatrix {T P : Scheme.{0}} {r d : ℕ}
    (x : RankQuotient r d T) (j : P ⟶ T) (I : Finset (Fin r)) (hI : I.card = d)
    [IsIso ((Scheme.Modules.pullback j).map (chartComposite x I hI))] :
    (universalMatrix d r I hI).map
        ⇑((MvPolynomial.aeval (R := ℤ) (fun pq : Fin d × {q : Fin r // q ∉ I} =>
          presentedMatrix x j I hI pq.1 pq.2.1)).toRingHom)
      = presentedMatrix x j I hI := by
  ext p q
  simp only [Matrix.map_apply, universalMatrix, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  by_cases hq : q ∈ I
  · rw [dif_pos hq]
    set k := (I.orderIsoOfFin hI).symm ⟨q, hq⟩ with hk
    have hqk : (I.orderIsoOfFin hI k : Fin r) = q := by simp [hk]
    have himg : presentedMatrix x j I hI p q = (1 : Matrix (Fin d) (Fin d) _) p k := by
      have e := congrFun (congrFun (presentedMatrix_submatrix_self x j I hI) p) k
      rw [Matrix.submatrix_apply, id_eq] at e
      rw [← hqk]; exact e
    rw [himg, Matrix.one_apply, apply_ite (MvPolynomial.aeval (R := ℤ)
        (fun pq : Fin d × {q : Fin r // q ∉ I} => presentedMatrix x j I hI pq.1 pq.2.1)),
      map_one, map_zero]
    have hcond : ((I.orderIsoOfFin hI p : Fin r) = q) ↔ (p = k) := by
      conv_lhs => rw [← hqk]
      rw [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq]
    by_cases hpk : p = k
    · rw [if_pos (hcond.mpr hpk), if_pos hpk]
    · rw [if_neg (hcond.not.mpr hpk), if_neg hpk]
  · rw [dif_neg hq, MvPolynomial.aeval_X]

/-- A ring homomorphism carries the nonsingular inverse to the nonsingular inverse when
the determinant is a unit. Project-local (copy of the private helper in
`GrassmannianCells.lean`). -/
lemma matrixMap_nonsing_inv {n : ℕ} {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (A : Matrix (Fin n) (Fin n) R) (h : IsUnit A.det) :
    (A.map ⇑f)⁻¹ = A⁻¹.map ⇑f := by
  have hmul : (A.map ⇑f) * (A⁻¹.map ⇑f) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A h,
      Matrix.map_one f (map_zero f) (map_one f)]
  exact Matrix.inv_eq_right_inv hmul

/-- **Transport of the image matrix along a ring hom over the structure map**: pushing
`M = (X^I_J)⁻¹ X^I` forward along any `incl : R^I_J →+* D` with
`incl ∘ (R^I → R^I_J) = g` yields `(Y_J)⁻¹ · Y` for `Y := X^I` base-changed along `g`.
Non-private CommRing form of the helper inside `GrassmannianCells.lean`. Project-local. -/
lemma imageMatrix_map_ringHom (d r : ℕ) (I J : Finset (Fin r)) (hI : I.card = d)
    (hJ : J.card = d) {D : Type*} [CommRing D]
    (incl : Localization.Away (minorDet d r I J hI hJ) →+* D)
    (g : MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ →+* D)
    (hincl : incl.comp (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ)
        (Localization.Away (minorDet d r I J hI hJ))) = g) :
    (imageMatrix d r I J hI hJ).map ⇑incl
      = (((universalMatrix d r I hI).map ⇑g).submatrix id
          (fun k : Fin d => (J.orderIsoOfFin hJ k : Fin r)))⁻¹ *
        (universalMatrix d r I hI).map ⇑g := by
  have hcoe : ⇑incl ∘ ⇑(algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ)
        (Localization.Away (minorDet d r I J hI hJ))) = ⇑g := by
    rw [← RingHom.coe_comp, hincl]
  have hmm : (imageMatrix d r I J hI hJ).map ⇑incl
      = (universalMinorInv d r I J hI hJ).map ⇑incl *
        ((universalMatrix d r I hI).map
          ⇑(algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ)
            (Localization.Away (minorDet d r I J hI hJ)))).map ⇑incl := by
    rw [imageMatrix]; exact Matrix.map_mul
  rw [hmm, Matrix.map_map, hcoe, universalMinorInv,
    ← matrixMap_nonsing_inv incl (universalMinor d r I J hI hJ)
      (isUnit_det_universalMinor d r I J hI hJ)]
  congr 1
  congr 1
  rw [universalMinor, Matrix.map_map, hcoe, Matrix.submatrix_map]

/-- **Chart-point identity over an arbitrary commutative ring** (the glue condition in
classifying-map form): for a ring map `f : R^I →+* K` under which the minor `P^I_J` is a
unit, the transported point `lift(f) ∘ θ̃_{I,J}` presents the same `K`-point through
chart `J` as `f` does through chart `I`. CommRing generalisation of
`existence_chart_kpoint_eq` (whose `Field` hypothesis is unused); proof copied verbatim.
Project-local. -/
theorem chart_point_eq (d r : ℕ) {K : Type} [CommRing K] (I J : (theGlueData d r).J)
    (f : MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ →+* K)
    (hf : IsUnit (f (minorDet d r I.1 J.1 I.2 J.2))) :
    Spec.map (CommRingCat.ofHom
        ((IsLocalization.Away.lift (minorDet d r I.1 J.1 I.2 J.2) hf).comp
          (transitionPreMap d r I.1 J.1 I.2 J.2).toRingHom)) ≫ (theGlueData d r).ι J
      = Spec.map (CommRingCat.ofHom f) ≫ (theGlueData d r).ι I := by
  set f' : Localization.Away (minorDet d r I.1 J.1 I.2 J.2) →+* K :=
    IsLocalization.Away.lift (minorDet d r I.1 J.1 I.2 J.2) hf with hf'def
  rw [show CommRingCat.ofHom (f'.comp (transitionPreMap d r I.1 J.1 I.2 J.2).toRingHom)
        = CommRingCat.ofHom (transitionPreMap d r I.1 J.1 I.2 J.2).toRingHom ≫
          CommRingCat.ofHom f'
      from by rw [← CommRingCat.ofHom_comp], Spec.map_comp, Category.assoc,
    ← chartTransition_comp_chartIncl d r I.1 J.1 I.2 J.2]
  have hglue : (chartTransition d r I.1 J.1 I.2 J.2 ≫ chartIncl d r J.1 I.1 J.2 I.2)
        ≫ (theGlueData d r).ι J
      = chartIncl d r I.1 J.1 I.2 J.2 ≫ (theGlueData d r).ι I := by
    rw [Category.assoc]; exact (theGlueData d r).glue_condition I J
  refine (congrArg (Spec.map (CommRingCat.ofHom f') ≫ ·) hglue).trans ?_
  have hfI : Spec.map (CommRingCat.ofHom f') ≫ chartIncl d r I.1 J.1 I.2 J.2
      = Spec.map (CommRingCat.ofHom f) := by
    have e1 : CommRingCat.ofHom (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
          (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))) ≫ CommRingCat.ofHom f'
        = CommRingCat.ofHom f := by
      rw [← CommRingCat.ofHom_comp]
      exact congrArg CommRingCat.ofHom (IsLocalization.Away.lift_comp _ hf)
    calc Spec.map (CommRingCat.ofHom f') ≫ chartIncl d r I.1 J.1 I.2 J.2
        = Spec.map (CommRingCat.ofHom
              (algebraMap (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ)
                (Localization.Away (minorDet d r I.1 J.1 I.2 J.2))) ≫
            CommRingCat.ofHom f') :=
          (Spec.map_comp _ _).symm
      _ = Spec.map (CommRingCat.ofHom f) := congrArg Spec.map e1
  calc Spec.map (CommRingCat.ofHom f') ≫ chartIncl d r I.1 J.1 I.2 J.2 ≫
        (theGlueData d r).ι I
      = (Spec.map (CommRingCat.ofHom f') ≫ chartIncl d r I.1 J.1 I.2 J.2)
          ≫ (theGlueData d r).ι I := (Category.assoc _ _ _).symm
    _ = Spec.map (CommRingCat.ofHom f) ≫ (theGlueData d r).ι I :=
        congrArg (· ≫ (theGlueData d r).ι I) hfI

set_option maxHeartbeats 800000 in
-- the Γ–Spec assembly compares two heavy `MvPolynomial`-classified composites
/-- **Naturality of the chart morphism**: precomposing `φ_I : T_I ⟶ U^I` with any
`p : W ⟶ T_I` is the morphism classified by the matrix presenting the quotient along
`p ≫ ι_{T_I}` — `Scheme.toSpecΓ_naturality` plus the entrywise transport
`presentedMatrix_comp`. Project-local. -/
lemma comp_chartMorphism {T W : Scheme.{0}} (d r : ℕ) (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) (p : W ⟶ (chartLocus x I hI).toScheme)
    [IsIso ((Scheme.Modules.pullback (p ≫ (chartLocus x I hI).ι)).map
      (chartComposite x I hI))] :
    p ≫ chartMorphism d r x I hI
      = W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            presentedMatrix x (p ≫ (chartLocus x I hI).ι) I hI pq.1 pq.2.1)).toRingHom) := by
  have hmat : ∀ (a : Fin d) (b : Fin r),
      presentedMatrix x (p ≫ (chartLocus x I hI).ι) I hI a b
        = (CommRingCat.Hom.hom (Scheme.Hom.appTop p)) (chartMatrix x I hI a b) := by
    intro a b
    rw [chartMatrix_eq_presentedMatrix,
      presentedMatrix_comp x p (chartLocus x I hI).ι I hI]
    exact Matrix.map_apply
  have hring : CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
        (fun pq : Fin d × {q : Fin r // q ∉ I} =>
          presentedMatrix x (p ≫ (chartLocus x I hI).ι) I hI pq.1 pq.2.1)).toRingHom
      = CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom ≫ Scheme.Hom.appTop p := by
    refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
      (fun pq => ?_))
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X]
    exact hmat pq.1 pq.2.1
  have hnat : p ≫ (chartLocus x I hI).toScheme.toSpecΓ
      = W.toSpecΓ ≫ Spec.map (Scheme.Hom.appTop p) := Scheme.toSpecΓ_naturality p
  have hspec : Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
        (fun pq : Fin d × {q : Fin r // q ∉ I} =>
          presentedMatrix x (p ≫ (chartLocus x I hI).ι) I hI pq.1 pq.2.1)).toRingHom)
      = Spec.map (Scheme.Hom.appTop p) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom) :=
    (congrArg Spec.map hring).trans (Spec.map_comp _ _)
  have key : p ≫ ((chartLocus x I hI).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom))
      = W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            presentedMatrix x (p ≫ (chartLocus x I hI).ι) I hI pq.1 pq.2.1)).toRingHom) := calc
    p ≫ ((chartLocus x I hI).toScheme.toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom))
      = (p ≫ (chartLocus x I hI).toScheme.toSpecΓ) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom) := (Category.assoc _ _ _).symm
    _ = (W.toSpecΓ ≫ Spec.map (Scheme.Hom.appTop p)) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom) :=
        congrArg (· ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom)) hnat
    _ = W.toSpecΓ ≫ Spec.map (Scheme.Hom.appTop p) ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom) := Category.assoc _ _ _
    _ = W.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            presentedMatrix x (p ≫ (chartLocus x I hI).ι) I hI pq.1 pq.2.1)).toRingHom) :=
        congrArg (W.toSpecΓ ≫ ·) hspec.symm
  exact key

set_option maxHeartbeats 1600000 in
-- the assembly chains five matrix/localization transports over the pullback scheme
/-- **Overlap compatibility of the chart morphisms** (Nitsure §1 gluing step): on the
intersection `P = T_I ×_T T_J` the composites of the chart morphisms with the glue-data
immersions agree. Both sides are classified (through `comp_chartMorphism`) by the
matrices `M^I_P`, `M^J_P` presenting the pulled-back quotient; the change-of-basis
identity `M^I_P = (M^I_P)_J · M^J_P` (`presentedMatrix_changeOfBasis`) identifies the
`J`-classifier with the localization-transport of the `I`-classifier, and the glue
condition (`chart_point_eq`) closes the square. Project-local — the gluing hypothesis of
`grPointOfRankQuotient`. -/
lemma chartMorphism_glue_compat {T : Scheme.{0}} (d r : ℕ) (x : RankQuotient r d T)
    (I J : (theGlueData d r).J) :
    pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
        (chartMorphism d r x I.1 I.2 ≫ (theGlueData d r).ι I)
      = pullback.snd (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
        (chartMorphism d r x J.1 J.2 ≫ (theGlueData d r).ι J) := by
  -- the two chart composites pull back to isomorphisms on the intersection
  haveI hcI : IsIso ((Scheme.Modules.pullback
      (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
        (chartLocus x I.1 I.2).ι)).map (chartComposite x I.1 I.2)) :=
    isIso_pullback_map_comp _ _ _
  haveI hcJ' : IsIso ((Scheme.Modules.pullback
      (pullback.snd (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
        (chartLocus x J.1 J.2).ι)).map (chartComposite x J.1 J.2)) :=
    isIso_pullback_map_comp _ _ _
  haveI hcJ : IsIso ((Scheme.Modules.pullback
      (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
        (chartLocus x I.1 I.2).ι)).map (chartComposite x J.1 J.2)) := by
    rw [pullback.condition]; exact hcJ'
  -- the `J`-minor of `M^I_P` is invertible (it presents `c_J` against `c_I⁻¹`)
  have hisoMinor : IsIso (matrixEndRect
      ((presentedMatrix x
          (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
            (chartLocus x I.1 I.2).ι) I.1 I.2).submatrix id
        (fun k : Fin d => ((J.1).orderIsoOfFin J.2 k : Fin r)))) := by
    rw [matrixEndRect_presentedMatrix_minor x
      (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
        (chartLocus x I.1 I.2).ι) I.1 I.2 J.1 J.2]
    -- explicit `comp_isIso'` chain (instance inference is unreliable under the diamond)
    exact IsIso.comp_isIso' (Iso.isIso_inv _)
      (IsIso.comp_isIso' hcJ
        (IsIso.comp_isIso' (@IsIso.inv_isIso _ _ _ _ _ hcI) (Iso.isIso_hom _)))
  have hUnitIJ : IsUnit (((presentedMatrix x
      (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
        (chartLocus x I.1 I.2).ι) I.1 I.2).submatrix id
        (fun k : Fin d => ((J.1).orderIsoOfFin J.2 k : Fin r))).det) :=
    (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_isIso_matrixEndRect _ hisoMinor)
  -- the `I`-classifying ring map sends the minor `P^I_J` to that unit
  have hgIunit : IsUnit ((MvPolynomial.aeval (R := ℤ)
      (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
        presentedMatrix x
          (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
            (chartLocus x I.1 I.2).ι) I.1 I.2 pq.1 pq.2.1)).toRingHom
      (minorDet d r I.1 J.1 I.2 J.2)) := by
    have e1 : (MvPolynomial.aeval (R := ℤ)
        (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
          presentedMatrix x
            (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
              (chartLocus x I.1 I.2).ι) I.1 I.2 pq.1 pq.2.1)).toRingHom
          (minorDet d r I.1 J.1 I.2 J.2)
        = (((universalMatrix d r I.1 I.2).submatrix id
            (fun k : Fin d => ((J.1).orderIsoOfFin J.2 k : Fin r))).map
              ⇑((MvPolynomial.aeval (R := ℤ)
                (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
                  presentedMatrix x
                    (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
                      (chartLocus x I.1 I.2).ι) I.1 I.2 pq.1 pq.2.1)).toRingHom)).det :=
      RingHom.map_det _ _
    rw [e1, ← Matrix.submatrix_map, universalMatrix_map_presentedMatrix]
    exact hUnitIJ
  -- the localization-transport of the `I`-classifier IS the `J`-classifier:
  -- entrywise this is the change-of-basis identity `M^J_P = ((M^I_P)_J)⁻¹ · M^I_P`
  have hmatrix : (imageMatrix d r I.1 J.1 I.2 J.2).map
        ⇑(IsLocalization.Away.lift (minorDet d r I.1 J.1 I.2 J.2) hgIunit)
      = presentedMatrix x
          (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
            (chartLocus x I.1 I.2).ι) J.1 J.2 := by
    rw [imageMatrix_map_ringHom d r I.1 J.1 I.2 J.2
        (IsLocalization.Away.lift (minorDet d r I.1 J.1 I.2 J.2) hgIunit)
        ((MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
            presentedMatrix x
              (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
                (chartLocus x I.1 I.2).ι) I.1 I.2 pq.1 pq.2.1)).toRingHom)
        (IsLocalization.Away.lift_comp _ hgIunit),
      universalMatrix_map_presentedMatrix x
        (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
          (chartLocus x I.1 I.2).ι) I.1 I.2]
    exact (congrArg (fun z => ((presentedMatrix x
        (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
          (chartLocus x I.1 I.2).ι) I.1 I.2).submatrix id
        (fun k : Fin d => ((J.1).orderIsoOfFin J.2 k : Fin r)))⁻¹ * z)
      (presentedMatrix_changeOfBasis x
        (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
          (chartLocus x I.1 I.2).ι) I.1 I.2 J.1 J.2)).trans
      (Matrix.nonsing_inv_mul_cancel_left _ _ hUnitIJ)
  -- ring-hom level: `lift(aeval M^I_P) ∘ θ̃_{I,J} = aeval M^J_P`
  have hkey : (IsLocalization.Away.lift (minorDet d r I.1 J.1 I.2 J.2) hgIunit).comp
        (transitionPreMap d r I.1 J.1 I.2 J.2).toRingHom
      = (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ J.1} =>
            presentedMatrix x
              (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
                (chartLocus x I.1 I.2).ι) J.1 J.2 pq.1 pq.2.1)).toRingHom := by
    refine MvPolynomial.ringHom_ext' (Subsingleton.elim _ _) (fun pq => ?_)
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, MvPolynomial.aeval_X]
    rw [transitionPreMap, MvPolynomial.aeval_X]
    calc (IsLocalization.Away.lift (minorDet d r I.1 J.1 I.2 J.2) hgIunit)
          (imageMatrix d r I.1 J.1 I.2 J.2 pq.1 pq.2.1)
        = ((imageMatrix d r I.1 J.1 I.2 J.2).map
            ⇑(IsLocalization.Away.lift (minorDet d r I.1 J.1 I.2 J.2) hgIunit))
            pq.1 pq.2.1 := Matrix.map_apply.symm
      _ = presentedMatrix x
            (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
              (chartLocus x I.1 I.2).ι) J.1 J.2 pq.1 pq.2.1 := by rw [hmatrix]
  -- the glue condition in classifying form
  have hmid : Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
        (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
          presentedMatrix x
            (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
              (chartLocus x I.1 I.2).ι) I.1 I.2 pq.1 pq.2.1)).toRingHom) ≫
        (theGlueData d r).ι I
      = Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ J.1} =>
            presentedMatrix x
              (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
                (chartLocus x I.1 I.2).ι) J.1 J.2 pq.1 pq.2.1)).toRingHom) ≫
        (theGlueData d r).ι J := by
    have h := chart_point_eq d r I J ((MvPolynomial.aeval (R := ℤ)
      (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
        presentedMatrix x
          (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
            (chartLocus x I.1 I.2).ι) I.1 I.2 pq.1 pq.2.1)).toRingHom) hgIunit
    rw [hkey] at h
    exact h.symm
  -- assemble: rewrite both legs through `comp_chartMorphism` and close with `hmid`
  have hI1 := comp_chartMorphism d r x I.1 I.2
    (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι)
  have hJ1 := comp_chartMorphism d r x J.1 J.2
    (pullback.snd (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι)
  have hmatJ : presentedMatrix x
        (pullback.snd (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
          (chartLocus x J.1 J.2).ι) J.1 J.2
      = presentedMatrix x
          (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
            (chartLocus x I.1 I.2).ι) J.1 J.2 :=
    presentedMatrix_congr x pullback.condition.symm J.1 J.2
  rw [hmatJ] at hJ1
  calc pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
        (chartMorphism d r x I.1 I.2 ≫ (theGlueData d r).ι I)
      = (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
          chartMorphism d r x I.1 I.2) ≫ (theGlueData d r).ι I := (Category.assoc _ _ _).symm
    _ = ((pullback (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι).toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
            (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
              presentedMatrix x
                (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
                  (chartLocus x I.1 I.2).ι) I.1 I.2 pq.1 pq.2.1)).toRingHom)) ≫
        (theGlueData d r).ι I := congrArg (· ≫ (theGlueData d r).ι I) hI1
    _ = (pullback (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
            presentedMatrix x
              (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
                (chartLocus x I.1 I.2).ι) I.1 I.2 pq.1 pq.2.1)).toRingHom) ≫
        (theGlueData d r).ι I := Category.assoc _ _ _
    _ = (pullback (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ J.1} =>
            presentedMatrix x
              (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
                (chartLocus x I.1 I.2).ι) J.1 J.2 pq.1 pq.2.1)).toRingHom) ≫
        (theGlueData d r).ι J := by rw [hmid]
    _ = ((pullback (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι).toSpecΓ ≫
          Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
            (fun pq : Fin d × {q : Fin r // q ∉ J.1} =>
              presentedMatrix x
                (pullback.fst (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
                  (chartLocus x I.1 I.2).ι) J.1 J.2 pq.1 pq.2.1)).toRingHom)) ≫
        (theGlueData d r).ι J := (Category.assoc _ _ _).symm
    _ = (pullback.snd (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
          chartMorphism d r x J.1 J.2) ≫ (theGlueData d r).ι J :=
        (congrArg (· ≫ (theGlueData d r).ι J) hJ1).symm
    _ = pullback.snd (chartLocus x I.1 I.2).ι (chartLocus x J.1 J.2).ι ≫
        (chartMorphism d r x J.1 J.2 ≫ (theGlueData d r).ι J) := Category.assoc _ _ _

/-! ### The chart data of the tautological quotient

Over the chart immersion `ι_I` the tautological quotient is presented by the universal
matrix: `pullback_map_glueLift_glueRestrictionHom` identifies `ι_I^* u` with the chart
quotient `u^I` (through the chart restriction isomorphism), the `I`-minor of `u^I` is
the identity, and the presented matrix is the `Γ`-image of `X^I`. These are the
taut-specific inputs of the `represents` inverse laws. -/

/-- **The `I`-columns of the chart quotient give a splitting**: `s_I ≫ u^I = 𝟙`
(matrix content: the `I`-minor of the universal matrix is the identity). Standalone form
of the splitting inside `chartQuotientMap_epi`. Project-local. -/
lemma freeMap_chartQuotientMap (d r : ℕ) (I : Finset (Fin r)) (hI : I.card = d) :
    SheafOfModules.freeMap (R := (affineChart d r I).ringCatSheaf)
        (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫ chartQuotientMap d r I hI
      = 𝟙 (SheafOfModules.free (R := (affineChart d r I).ringCatSheaf) (Fin d)) := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (Fin d)) _ _ (fun k => ?_)
  have key : SheafOfModules.ιFree (R := (affineChart d r I).ringCatSheaf) k ≫
        (SheafOfModules.freeMap (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) ≫
          chartQuotientMap d r I hI)
      = SheafOfModules.ιFree k :=
    (SheafOfModules.ιFree_freeMap_assoc (fun j : Fin d => (I.orderIsoOfFin hI j : Fin r)) k
      (chartQuotientMap d r I hI)).trans (chartQuotientMap_ιFree d r I hI k)
  exact key.trans (Category.comp_id _).symm

/-- **Chart restriction of the tautological quotient**: pulling the tautological
quotient back along the chart immersion `ι_I` and composing with the chart restriction
isomorphism gives the chart quotient `u^I`, up to the free-pullback comparison —
`pullback_map_glueLift_glueRestrictionHom` at the Grassmannian glue data, with the
adjunction transpose collapsed by `Equiv.symm_apply_apply`. Project-local. -/
lemma pullback_map_tautologicalQuotient (d r : ℕ) (I : (theGlueData d r).J) :
    (Scheme.Modules.pullback ((theGlueData d r).ι I)).map (tautologicalQuotient d r) ≫
        (universalQuotient_restrictionIso d r I).hom
      = (Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).hom ≫
        chartQuotientMap d r I.1 I.2 := by
  have h := Scheme.Modules.pullback_map_glueLift_glueRestrictionHom (theGlueData d r)
    (fun J => SheafOfModules.free (R := ((theGlueData d r).U J).ringCatSheaf) (Fin d))
    (bundleTransitionData d r)
    (fun J => bundleTransition_self d r J.1 J.2)
    (fun J J' K => bundleTransition_cocycle d r J J' K)
    (fun J => tautologicalQuotientComponent d r J)
    (fun p => (tautologicalQuotientComponent_transpose d r p.1 p.2).mpr
      (tautologicalQuotient_overlap d r p.1 p.2)) I
  have h2 : ((Scheme.Modules.pullbackPushforwardAdjunction
        ((theGlueData d r).ι I)).homEquiv _ _).symm
        (tautologicalQuotientComponent d r I)
      = (Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).hom ≫
        chartQuotientMap d r I.1 I.2 := by
    rw [tautologicalQuotientComponent]
    exact Equiv.symm_apply_apply _ _
  exact h.trans h2

/-- **Chart pullback of the tautological chart composite**: `ι_I^*(s_I ≫ u)` is the
free-pullback comparison followed by the inverse chart restriction isomorphism — the
`I`-minor of the chart quotient is the identity (`freeMap_chartQuotientMap`), so the
chart composite of the tautological quotient trivialises over its own chart.
Project-local. -/
lemma pullback_map_chartComposite_tautological (d r : ℕ) (I : (theGlueData d r).J) :
    (Scheme.Modules.pullback ((theGlueData d r).ι I)).map
        (chartComposite (tautologicalRankQuotient d r) I.1 I.2)
      = (Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin d)).hom ≫
        (universalQuotient_restrictionIso d r I).inv := by
  -- the pulled-back quotient, in restriction-iso form
  have hq : (Scheme.Modules.pullback ((theGlueData d r).ι I)).map
        ((tautologicalRankQuotient d r).q)
      = ((Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).hom ≫
          chartQuotientMap d r I.1 I.2) ≫
        (universalQuotient_restrictionIso d r I).inv :=
    (Iso.eq_comp_inv _).mpr (pullback_map_tautologicalQuotient d r I)
  -- the pulled-back coordinate inclusion, comparison-intertwined
  have hfm : (Scheme.Modules.pullback ((theGlueData d r).ι I)).map
        (SheafOfModules.freeMap (R := (scheme d r).ringCatSheaf)
          (fun j : Fin d => ((I.1).orderIsoOfFin I.2 j : Fin r)))
      = ((Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin d)).hom ≫
          SheafOfModules.freeMap (fun j : Fin d => ((I.1).orderIsoOfFin I.2 j : Fin r))) ≫
        (Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)).inv :=
    (Iso.eq_comp_inv _).mpr (pullback_map_freeMap_pullbackFreeIso _ _)
  -- split the chart composite and chain the two identifications
  have hsplit : (Scheme.Modules.pullback ((theGlueData d r).ι I)).map
        (chartComposite (tautologicalRankQuotient d r) I.1 I.2)
      = (Scheme.Modules.pullback ((theGlueData d r).ι I)).map
          (SheafOfModules.freeMap (R := (scheme d r).ringCatSheaf)
            (fun j : Fin d => ((I.1).orderIsoOfFin I.2 j : Fin r))) ≫
        (Scheme.Modules.pullback ((theGlueData d r).ι I)).map
          ((tautologicalRankQuotient d r).q) :=
    (Scheme.Modules.pullback ((theGlueData d r).ι I)).map_comp _ _
  rw [hsplit, hq, hfm]
  -- collapse `E.inv ≫ E.hom` and the splitting `s_I ≫ u^I = 𝟙` (term-mode: positional
  -- `simp [Category.assoc]` does not reassociate across the `X.Modules` diamond)
  set E := Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r) with hE
  set Dd := Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin d) with hDd
  set Φ := universalQuotient_restrictionIso d r I with hΦ
  set cqm := chartQuotientMap d r I.1 I.2 with hcqm
  set fm : SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d) ⟶
      SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin r) :=
    SheafOfModules.freeMap (fun j : Fin d => ((I.1).orderIsoOfFin I.2 j : Fin r)) with hfm'
  have hsplit' : fm ≫ cqm = 𝟙 _ := freeMap_chartQuotientMap d r I.1 I.2
  calc ((Dd.hom ≫ fm) ≫ E.inv) ≫ (E.hom ≫ cqm) ≫ Φ.inv
      = (Dd.hom ≫ fm) ≫ E.inv ≫ (E.hom ≫ cqm) ≫ Φ.inv := Category.assoc _ _ _
    _ = (Dd.hom ≫ fm) ≫ E.inv ≫ E.hom ≫ cqm ≫ Φ.inv :=
        congrArg ((Dd.hom ≫ fm) ≫ ·) (congrArg (E.inv ≫ ·) (Category.assoc _ _ _))
    _ = (Dd.hom ≫ fm) ≫ cqm ≫ Φ.inv :=
        congrArg ((Dd.hom ≫ fm) ≫ ·) (Iso.inv_hom_id_assoc E (cqm ≫ Φ.inv))
    _ = Dd.hom ≫ fm ≫ cqm ≫ Φ.inv := Category.assoc _ _ _
    _ = Dd.hom ≫ (fm ≫ cqm) ≫ Φ.inv :=
        congrArg (Dd.hom ≫ ·) (Category.assoc _ _ _).symm
    _ = Dd.hom ≫ 𝟙 _ ≫ Φ.inv :=
        congrArg (Dd.hom ≫ ·) (congrArg (· ≫ Φ.inv) hsplit')
    _ = Dd.hom ≫ Φ.inv := congrArg (Dd.hom ≫ ·) (Category.id_comp _)

/-- The tautological chart composite pulls back to an isomorphism along its own chart
immersion — instance form of `pullback_map_chartComposite_tautological`, the input of
the presented-matrix computation `presentedMatrix_tautological`. Project-local. -/
instance isIso_pullback_chartComposite_tautological (d r : ℕ) (I : (theGlueData d r).J) :
    IsIso ((Scheme.Modules.pullback ((theGlueData d r).ι I)).map
      (chartComposite (tautologicalRankQuotient d r) I.1 I.2)) := by
  rw [pullback_map_chartComposite_tautological]
  exact IsIso.comp_isIso' inferInstance inferInstance

/-- **The chart image lies in the tautological chart locus**: the open range of the
chart immersion `ι_I` is one of the opens over which the tautological chart composite
is invertible. Project-local — provides the cover for the uniqueness law of
`represents`. -/
lemma opensRange_le_chartLocus_tautological (d r : ℕ) (I : (theGlueData d r).J) :
    Scheme.Hom.opensRange ((theGlueData d r).ι I)
      ≤ chartLocus (tautologicalRankQuotient d r) I.1 I.2 := by
  have heq : ((theGlueData d r).ι I).isoOpensRange.inv ≫ (theGlueData d r).ι I
      = (Scheme.Hom.opensRange ((theGlueData d r).ι I)).ι :=
    (Iso.inv_comp_eq _).mpr (Scheme.Hom.isoOpensRange_hom_ι ((theGlueData d r).ι I)).symm
  haveI h1 : IsIso ((Scheme.Modules.pullback
      (((theGlueData d r).ι I).isoOpensRange.inv ≫ (theGlueData d r).ι I)).map
      (chartComposite (tautologicalRankQuotient d r) I.1 I.2)) :=
    isIso_pullback_map_comp _ _ _
  have hmem : IsIso ((Scheme.Modules.pullback
      (Scheme.Hom.opensRange ((theGlueData d r).ι I)).ι).map
      (chartComposite (tautologicalRankQuotient d r) I.1 I.2)) := by
    rw [← heq]; exact h1
  exact le_sSup hmem

set_option maxHeartbeats 800000 in
-- the inverse-collapse steps traverse the `X.Modules` instance diamond
/-- **The tautological quotient is presented by the universal matrix**: over the `I`-th
chart, the matrix presenting the tautological quotient (against its own inverted chart
composite) is the `Γ`-image of the universal matrix `X^I`. The taut-specific layer of
the `represents` inverse laws. Project-local. -/
lemma presentedMatrix_tautological (d r : ℕ) (I : (theGlueData d r).J) :
    presentedMatrix (tautologicalRankQuotient d r) ((theGlueData d r).ι I) I.1 I.2
        (hcI := isIso_pullback_chartComposite_tautological d r I)
      = (universalMatrix d r I.1 I.2).map
          ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
            (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv) := by
  apply matrixEndRect_injective
  letI E := Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin r)
  letI Dd := Scheme.Modules.pullbackFreeIso ((theGlueData d r).ι I) (Fin d)
  letI Φ := universalQuotient_restrictionIso d r I
  letI cqm := chartQuotientMap d r I.1 I.2
  -- the inverse of the pulled-back chart composite, explicitly
  have hinv : @CategoryTheory.inv _ _ _ _
        ((Scheme.Modules.pullback ((theGlueData d r).ι I)).map
          (chartComposite (tautologicalRankQuotient d r) I.1 I.2))
        (isIso_pullback_chartComposite_tautological d r I)
      = Φ.hom ≫ Dd.inv := by
    apply IsIso.inv_eq_of_hom_inv_id
    -- `(Dd.hom ≫ Φ.inv) ≫ Φ.hom ≫ Dd.inv = 𝟙` (term-mode under the diamond)
    exact (congrArg (· ≫ (Φ.hom ≫ Dd.inv))
        (pullback_map_chartComposite_tautological d r I)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (Dd.hom ≫ ·) (Iso.inv_hom_id_assoc Φ Dd.inv)).trans Dd.hom_inv_id))
  have hq : (Scheme.Modules.pullback ((theGlueData d r).ι I)).map
        ((tautologicalRankQuotient d r).q)
      = (E.hom ≫ cqm) ≫ Φ.inv :=
    (Iso.eq_comp_inv _).mpr (pullback_map_tautologicalQuotient d r I)
  have hBC : (Φ.hom ≫ Dd.inv) ≫ Dd.hom = Φ.hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (Φ.hom ≫ ·) Dd.inv_hom_id).trans (Category.comp_id _))
  have hA : ((E.hom ≫ cqm) ≫ Φ.inv) ≫ Φ.hom = E.hom ≫ cqm :=
    (Category.assoc _ _ _).trans
      ((congrArg ((E.hom ≫ cqm) ≫ ·) Φ.inv_hom_id).trans (Category.comp_id _))
  -- assemble entirely by `.trans` (junction unification is up-to-defeq, which crosses
  -- the hidden-instance mismatches that block `rw`/`set` here)
  exact (matrixEndRect_presentedMatrix (tautologicalRankQuotient d r)
      ((theGlueData d r).ι I) I.1 I.2
      (hcI := isIso_pullback_chartComposite_tautological d r I)).trans
    ((congrArg (fun z => E.inv ≫
        (Scheme.Modules.pullback ((theGlueData d r).ι I)).map
          ((tautologicalRankQuotient d r).q) ≫ z ≫ Dd.hom) hinv).trans
      ((congrArg (fun z => E.inv ≫ z ≫ (Φ.hom ≫ Dd.inv) ≫ Dd.hom) hq).trans
        ((congrArg (fun z => E.inv ≫ ((E.hom ≫ cqm) ≫ Φ.inv) ≫ z) hBC).trans
          ((congrArg (E.inv ≫ ·) hA).trans
            ((Iso.inv_hom_id_assoc E cqm).trans
              (chartQuotientMap_eq_matrixEndRect d r I.1 I.2))))))

/-! ### Chart data of a pulled-back quotient: the locus-level bridge

The two inverse laws of `represents` compare the chart data of `rqPullback ψ y` on `T'`
with the `ψ`-pullback of the chart data of `y` on `T`. `chartComposite_rqPullback` is the
morphism-level bridge; `chartLocus_rqPullback` below is the locus-level bridge. -/

/-- **The chart locus of a pullback contains the preimage of the chart locus**
(`lem:gr_chartLocus_rqPullback`): where the chart composite of `y` is invertible, the
chart composite of `ψ^*y` is invertible after pulling back. With
`chartComposite_rqPullback` this is the pseudofunctor comparison `pullbackComp` plus
`isIso_pullback_map_comp` along the factorisation of `V.ι ≫ ψ` through the locus
inclusion. Project-local. -/
lemma chartLocus_rqPullback {T' T : Scheme.{0}} (ψ : T' ⟶ T) {r d : ℕ}
    (y : RankQuotient r d T) (I : Finset (Fin r)) (hI : I.card = d) :
    ψ ⁻¹ᵁ chartLocus y I hI ≤ chartLocus (rqPullback ψ y) I hI := by
  set V : T'.Opens := ψ ⁻¹ᵁ chartLocus y I hI with hV
  -- the composite `V.ι ≫ ψ` factors through the chart-locus inclusion
  have hrange : Set.range (V.ι ≫ ψ).base ⊆ Set.range (chartLocus y I hI).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro t ⟨v, rfl⟩
    have hv : V.ι.base v ∈ V := by
      have : V.ι.base v ∈ Set.range V.ι.base := ⟨v, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    show (V.ι ≫ ψ).base v ∈ (chartLocus y I hI : Set T)
    rw [Scheme.Hom.comp_base]
    exact hv
  set ρ : V.toScheme ⟶ (chartLocus y I hI).toScheme :=
    IsOpenImmersion.lift (chartLocus y I hI).ι (V.ι ≫ ψ) hrange with hρ
  have hfac : ρ ≫ (chartLocus y I hI).ι = V.ι ≫ ψ :=
    IsOpenImmersion.lift_fac _ _ hrange
  -- the chart composite of `y` pulls back to an iso along `V.ι ≫ ψ`
  haveI h1 : IsIso ((Scheme.Modules.pullback (ρ ≫ (chartLocus y I hI).ι)).map
      (chartComposite y I hI)) := isIso_pullback_map_comp _ _ _
  haveI h2 : IsIso ((Scheme.Modules.pullback (V.ι ≫ ψ)).map (chartComposite y I hI)) := by
    rw [← hfac]; exact h1
  -- transport through the pseudofunctor comparison to the iterated pullback
  haveI h3 : IsIso ((Scheme.Modules.pullback V.ι).map
      ((Scheme.Modules.pullback ψ).map (chartComposite y I hI))) := by
    have h4 : IsIso ((Scheme.Modules.pullback ψ ⋙ Scheme.Modules.pullback V.ι).map
        (chartComposite y I hI)) :=
      (NatIso.isIso_map_iff (Scheme.Modules.pullbackComp V.ι ψ) _).mpr h2
    exact h4
  -- conclude: the chart composite of the pullback is iso over `V`
  have hmem : IsIso ((Scheme.Modules.pullback V.ι).map
      (chartComposite (rqPullback ψ y) I hI)) := by
    have hsplit : (Scheme.Modules.pullback V.ι).map (chartComposite (rqPullback ψ y) I hI)
        = (Scheme.Modules.pullback V.ι).map
            (Scheme.Modules.pullbackFreeIso ψ (Fin d)).inv ≫
          (Scheme.Modules.pullback V.ι).map
            ((Scheme.Modules.pullback ψ).map (chartComposite y I hI)) :=
      (congrArg ((Scheme.Modules.pullback V.ι).map)
        (chartComposite_rqPullback ψ y I hI)).trans
        ((Scheme.Modules.pullback V.ι).map_comp _ _)
    rw [hsplit]
    exact IsIso.comp_isIso' inferInstance h3
  exact le_sSup hmem

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 1000000 in
-- the comparison steps traverse the `X.Modules` instance diamond (term-mode throughout)
/-- **The presented matrix of a pulled-back rank quotient**: presenting `ψ^*y` along
`j` is the same as presenting `y` along `j ≫ ψ` — the pullback action `rqPullback`
re-presents the source through `pullbackFreeIso`, and the pseudofunctor comparison
`pullbackComp` rewrites the conjugation accordingly. The transport engine of the
`represents` inverse laws. Project-local. -/
lemma presentedMatrix_rqPullback {T' T W : Scheme.{0}} (ψ : T' ⟶ T) {r d : ℕ}
    (y : RankQuotient r d T) (j : W ⟶ T') (I : Finset (Fin r)) (hI : I.card = d)
    [hc1 : IsIso ((Scheme.Modules.pullback j).map (chartComposite (rqPullback ψ y) I hI))]
    [hc2 : IsIso ((Scheme.Modules.pullback (j ≫ ψ)).map (chartComposite y I hI))] :
    presentedMatrix (rqPullback ψ y) j I hI = presentedMatrix y (j ≫ ψ) I hI := by
  apply matrixEndRect_injective
  letI F := Scheme.Modules.pullback j
  letI G := Scheme.Modules.pullback ψ
  letI H := Scheme.Modules.pullback (j ≫ ψ)
  letI e := Scheme.Modules.pullbackComp j ψ
  letI Qr := Scheme.Modules.pullbackFreeIso j (Fin r)
  letI Qd := Scheme.Modules.pullbackFreeIso j (Fin d)
  letI Pr := Scheme.Modules.pullbackFreeIso ψ (Fin r)
  letI Pd := Scheme.Modules.pullbackFreeIso ψ (Fin d)
  letI Sr := Scheme.Modules.pullbackFreeIso (j ≫ ψ) (Fin r)
  letI Sd := Scheme.Modules.pullbackFreeIso (j ≫ ψ) (Fin d)
  -- the nested pullback of the chart composite is invertible
  haveI hA : IsIso ((Scheme.Modules.pullback ψ ⋙ Scheme.Modules.pullback j).map
      (chartComposite y I hI)) :=
    (NatIso.isIso_map_iff e (chartComposite y I hI)).mpr hc2
  haveI hA' : IsIso (F.map (G.map (chartComposite y I hI))) := hA
  -- expansion of the pulled-back quotient map (definitional unfold of `rqPullback`),
  -- with the `pullbackComp` naturality square folded in
  have hqnat : F.map (G.map y.q)
      = e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r)) ≫
        H.map y.q ≫ e.inv.app y.F :=
    (NatIso.naturality_2 e y.q).symm
  have hqtot : F.map ((rqPullback ψ y).q)
      = F.map Pr.inv ≫
        e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r)) ≫
        H.map y.q ≫ e.inv.app y.F :=
    (F.map_comp _ _).trans (congrArg (F.map Pr.inv ≫ ·) hqnat)
  -- the inverse of the pulled-back chart composite, fully transported
  have hccmap : F.map (chartComposite (rqPullback ψ y) I hI)
      = F.map Pd.inv ≫ F.map (G.map (chartComposite y I hI)) :=
    (congrArg F.map (chartComposite_rqPullback ψ y I hI)).trans (F.map_comp _ _)
  have hinv2 : inv (F.map (G.map (chartComposite y I hI)))
      = e.hom.app y.F ≫
        inv (H.map (chartComposite y I hI)) ≫
        e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) := by
    apply IsIso.inv_eq_of_hom_inv_id
    have hnat : F.map (G.map (chartComposite y I hI)) ≫ e.hom.app y.F
        = e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫
          H.map (chartComposite y I hI) :=
      e.hom.naturality (chartComposite y I hI)
    calc F.map (G.map (chartComposite y I hI)) ≫
          (e.hom.app y.F ≫ inv (H.map (chartComposite y I hI)) ≫
            e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)))
        = (F.map (G.map (chartComposite y I hI)) ≫ e.hom.app y.F) ≫
          inv (H.map (chartComposite y I hI)) ≫
          e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) :=
          (Category.assoc _ _ _).symm
      _ = (e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫
            H.map (chartComposite y I hI)) ≫
          inv (H.map (chartComposite y I hI)) ≫
          e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) :=
          congrArg (· ≫ inv (H.map (chartComposite y I hI)) ≫
            e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d))) hnat
      _ = e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫
          H.map (chartComposite y I hI) ≫
          inv (H.map (chartComposite y I hI)) ≫
          e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) :=
          Category.assoc _ _ _
      _ = e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫
          e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) :=
          congrArg (e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫ ·)
            (IsIso.hom_inv_id_assoc _ _)
      _ = 𝟙 _ := e.hom_inv_id_app _
  have hinvtot : inv (F.map (chartComposite (rqPullback ψ y) I hI))
      = (e.hom.app y.F ≫
          inv (H.map (chartComposite y I hI)) ≫
          e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d))) ≫
        F.map Pd.hom := by
    apply IsIso.inv_eq_of_hom_inv_id
    calc F.map (chartComposite (rqPullback ψ y) I hI) ≫
          (e.hom.app y.F ≫ inv (H.map (chartComposite y I hI)) ≫
            e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d))) ≫
          F.map Pd.hom
        = (F.map Pd.inv ≫ F.map (G.map (chartComposite y I hI))) ≫
          inv (F.map (G.map (chartComposite y I hI))) ≫ F.map Pd.hom := by
          rw [hccmap, hinv2]; rfl
      _ = F.map Pd.inv ≫
          (F.map (G.map (chartComposite y I hI)) ≫
            inv (F.map (G.map (chartComposite y I hI)))) ≫ F.map Pd.hom :=
          (Category.assoc _ _ _).trans
            (congrArg (F.map Pd.inv ≫ ·) (Category.assoc _ _ _).symm)
      _ = F.map Pd.inv ≫ 𝟙 _ ≫ F.map Pd.hom :=
          congrArg (fun z => F.map Pd.inv ≫ z ≫ F.map Pd.hom) (IsIso.hom_inv_id _)
      _ = F.map Pd.inv ≫ F.map Pd.hom :=
          congrArg (F.map Pd.inv ≫ ·) (Category.id_comp _)
      _ = 𝟙 _ := (F.map_comp _ _).symm.trans
          ((congrArg F.map Pd.inv_hom_id).trans (F.map_id _))
  -- free-pullback coherences along the composite
  have f1 : Qr.inv ≫ F.map Pr.inv ≫
        e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r))
      = Sr.inv := by
    have h := pullbackFreeIso_inv_pullbackComp j ψ (Fin r)
    calc Qr.inv ≫ F.map Pr.inv ≫
          e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r))
        = (Qr.inv ≫ F.map Pr.inv) ≫
          e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r)) :=
          (Category.assoc _ _ _).symm
      _ = (Sr.inv ≫ e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r))) ≫
          e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r)) :=
          congrArg (· ≫ e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r))) h.symm
      _ = Sr.inv ≫
          e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r)) ≫
          e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r)) :=
          Category.assoc _ _ _
      _ = Sr.inv ≫ 𝟙 _ := congrArg (Sr.inv ≫ ·) (e.inv_hom_id_app _)
      _ = Sr.inv := Category.comp_id _
  have f2 : e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫
        F.map Pd.hom ≫ Qd.hom
      = Sd.hom := by
    have h := pullbackFreeIso_inv_pullbackComp j ψ (Fin d)
    have h' : e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d))
        = Sd.hom ≫ Qd.inv ≫ F.map Pd.inv :=
      (Iso.hom_inv_id_assoc Sd _).symm.trans (congrArg (Sd.hom ≫ ·) h)
    calc e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫
          F.map Pd.hom ≫ Qd.hom
        = (Sd.hom ≫ Qd.inv ≫ F.map Pd.inv) ≫ F.map Pd.hom ≫ Qd.hom :=
          congrArg (· ≫ F.map Pd.hom ≫ Qd.hom) h'
      _ = Sd.hom ≫ Qd.inv ≫ (F.map Pd.inv ≫ F.map Pd.hom) ≫ Qd.hom := by
          rw [Category.assoc, Category.assoc, Category.assoc]
      _ = Sd.hom ≫ Qd.inv ≫ 𝟙 _ ≫ Qd.hom :=
          congrArg (fun z => Sd.hom ≫ Qd.inv ≫ z ≫ Qd.hom)
            ((F.map_comp _ _).symm.trans
              ((congrArg F.map Pd.inv_hom_id).trans (F.map_id _)))
      _ = Sd.hom ≫ Qd.inv ≫ Qd.hom :=
          congrArg (fun z => Sd.hom ≫ Qd.inv ≫ z) (Category.id_comp _)
      _ = Sd.hom ≫ 𝟙 _ := congrArg (Sd.hom ≫ ·) Qd.inv_hom_id
      _ = Sd.hom := Category.comp_id _
  -- assemble: this is `matrixEndRect_presentedMatrix` on both ends with the transport
  -- coherences `hqtot`/`hinvtot`/`f1`/`f2` in between.  Each individual step elaborates,
  -- but the `calc`-`Trans` chaining over these heavy `X.Modules` morphisms fails to
  -- synthesize in this toolchain (the relation-type metavariable `Trans Eq Eq ?m` is left
  -- unassigned even with every term/instance made explicit).
  -- The transport coherences `hqtot`/`hinvtot`/`f1`/`f2` assemble both `matrixEndRect`
  -- realisations into the same expression `Sr.inv ≫ H.map y.q ≫ inv (...) ≫ Sd.hom`.
  -- Phrased as an explicit `Eq.trans` chain: `calc` cannot synthesize the heavy
  -- `Trans Eq Eq` instance over these `X.Modules` morphisms in this toolchain.
  have s1 : matrixEndRect (presentedMatrix (rqPullback ψ y) j I hI)
      = Qr.inv ≫ F.map ((rqPullback ψ y).q) ≫
        inv (F.map (chartComposite (rqPullback ψ y) I hI)) ≫ Qd.hom :=
    matrixEndRect_presentedMatrix (rqPullback ψ y) j I hI
  have s2 : Qr.inv ≫ F.map ((rqPullback ψ y).q) ≫
        inv (F.map (chartComposite (rqPullback ψ y) I hI)) ≫ Qd.hom
      = Qr.inv ≫
        (F.map Pr.inv ≫
          e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r)) ≫
          H.map y.q ≫ e.inv.app y.F) ≫
        ((e.hom.app y.F ≫
            inv (H.map (chartComposite y I hI)) ≫
            e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d))) ≫
          F.map Pd.hom) ≫ Qd.hom := by
    rw [hqtot, hinvtot]; rfl
  have s3 : Qr.inv ≫
        (F.map Pr.inv ≫
          e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r)) ≫
          H.map y.q ≫ e.inv.app y.F) ≫
        ((e.hom.app y.F ≫
            inv (H.map (chartComposite y I hI)) ≫
            e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d))) ≫
          F.map Pd.hom) ≫ Qd.hom
      = (Qr.inv ≫ F.map Pr.inv ≫
          e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r))) ≫
        H.map y.q ≫
        (e.inv.app y.F ≫ e.hom.app y.F) ≫
        inv (H.map (chartComposite y I hI)) ≫
        (e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫
          F.map Pd.hom ≫ Qd.hom) := by
    simp only [Category.assoc]
  have s4 : (Qr.inv ≫ F.map Pr.inv ≫
          e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r))) ≫
        H.map y.q ≫
        (e.inv.app y.F ≫ e.hom.app y.F) ≫
        inv (H.map (chartComposite y I hI)) ≫
        (e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫
          F.map Pd.hom ≫ Qd.hom)
      = (Qr.inv ≫ F.map Pr.inv ≫
          e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r))) ≫
        H.map y.q ≫
        inv (H.map (chartComposite y I hI)) ≫
        (e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫
          F.map Pd.hom ≫ Qd.hom) := by
    rw [e.inv_hom_id_app y.F, Category.id_comp]
  have s5 : (Qr.inv ≫ F.map Pr.inv ≫
          e.hom.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin r))) ≫
        H.map y.q ≫
        inv (H.map (chartComposite y I hI)) ≫
        (e.inv.app (SheafOfModules.free (R := T.ringCatSheaf) (Fin d)) ≫
          F.map Pd.hom ≫ Qd.hom)
      = Sr.inv ≫ H.map y.q ≫
        inv (H.map (chartComposite y I hI)) ≫ Sd.hom := by
    rw [f1, f2]
  exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans
    (matrixEndRect_presentedMatrix y (j ≫ ψ) I hI).symm))))

/-- **The chart morphism pulls the universal matrix back to the presenting matrix**
(`φ_I^* X^I = M^I`): the `Γ`-image of the universal matrix along `appTop (chartMorphism)`
is the chart matrix. Ring-level form of the defining property of the chart morphism.
Project-local. -/
lemma universalMatrix_map_chartMorphism {T : Scheme.{0}} (d r : ℕ) (x : RankQuotient r d T)
    (I : Finset (Fin r)) (hI : I.card = d) :
    ((universalMatrix d r I hI).map
        ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ))).inv)).map
      ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (chartMorphism d r x I hI)))
    = chartMatrix x I hI := by
  -- the `appTop` of the chart morphism, through `ΓSpecIso` naturality
  have happ : Scheme.Hom.appTop (chartMorphism d r x I hI)
      = (Scheme.ΓSpecIso (CommRingCat.of
          (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ))).hom ≫
        CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom := by
    rw [chartMorphism, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
    exact Scheme.ΓSpecIso_naturality _
  rw [Matrix.map_map]
  -- the composed entry map is `aeval` of the chart-matrix entries
  -- at the morphism level the composite collapses by `Iso.inv_hom_id`; taking `⇑(·.hom)`
  -- keeps the composition unapplied so `CommRingCat.hom_comp` fires
  have hmor : (Scheme.ΓSpecIso (CommRingCat.of
        (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ))).inv ≫
        Scheme.Hom.appTop (chartMorphism d r x I hI)
      = CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom :=
    (Iso.inv_comp_eq _).mpr happ
  have hfun : ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (chartMorphism d r x I hI))) ∘
        ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
          (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ))).inv)
      = ⇑(MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I} =>
            chartMatrix x I hI pq.1 pq.2.1)).toRingHom := by
    have h := congrArg (fun m => ⇑(CommRingCat.Hom.hom m)) hmor
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, CommRingCat.hom_ofHom] at h
    exact h
  -- `rw`/`simp` cannot match the `g ∘ f` term (a hidden coercion-instance mismatch), so
  -- feed `hfun` through `congrArg` and reconcile `chartMatrix = presentedMatrix` separately
  calc (universalMatrix d r I hI).map
        (⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (chartMorphism d r x I hI))) ∘
          ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
            (MvPolynomial (Fin d × {q : Fin r // q ∉ I}) ℤ))).inv))
      = (universalMatrix d r I hI).map
          ⇑(MvPolynomial.aeval (R := ℤ)
            (fun pq : Fin d × {q : Fin r // q ∉ I} =>
              chartMatrix x I hI pq.1 pq.2.1)).toRingHom :=
        congrArg ((universalMatrix d r I hI).map) hfun
    _ = chartMatrix x I hI := by
        rw [chartMatrix_eq_presentedMatrix]
        exact universalMatrix_map_presentedMatrix x (chartLocus x I hI).ι I hI

/-- **Joint faithfulness of the restrictions to an open cover**: two morphisms of
sheaves of modules on `T` that agree after pullback to every member of an open cover
agree. Cover-of-opens analogue of `Scheme.Modules.pullback_map_jointly_faithful`
(same separation argument: sections of the target are detected on the cover).
Project-local. -/
lemma pullback_map_cover_faithful {T : Scheme.{0}} {ι : Type} {V : ι → T.Opens}
    (hV : TopologicalSpace.IsOpenCover V) {M N : T.Modules} {u v : M ⟶ N}
    (h : ∀ i, (Scheme.Modules.pullback (V i).ι).map u
        = (Scheme.Modules.pullback (V i).ι).map v) :
    u = v := by
  -- transfer the hypothesis to the site-level restriction functor, whose sections
  -- are concrete (`Γ(restrict M, O) = Γ(M, ι_i''O)`)
  have hres : ∀ i, (Scheme.Modules.restrictFunctor (V i).ι).map u
      = (Scheme.Modules.restrictFunctor (V i).ι).map v := by
    intro i
    calc (Scheme.Modules.restrictFunctor (V i).ι).map u
        = (Scheme.Modules.restrictFunctorIsoPullback (V i).ι).hom.app M ≫
            (Scheme.Modules.pullback (V i).ι).map u ≫
            (Scheme.Modules.restrictFunctorIsoPullback (V i).ι).inv.app N :=
          (NatIso.naturality_2 (Scheme.Modules.restrictFunctorIsoPullback (V i).ι) u).symm
      _ = (Scheme.Modules.restrictFunctorIsoPullback (V i).ι).hom.app M ≫
            (Scheme.Modules.pullback (V i).ι).map v ≫
            (Scheme.Modules.restrictFunctorIsoPullback (V i).ι).inv.app N := by rw [h i]
      _ = (Scheme.Modules.restrictFunctor (V i).ι).map v :=
          NatIso.naturality_2 (Scheme.Modules.restrictFunctorIsoPullback (V i).ι) v
  ext O x
  -- sheaf separation of the target over the cover `{ι_i''(ι_i⁻¹ O)}` of `O`
  refine TopCat.Sheaf.eq_of_locally_eq'
    (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab T)
    (fun i => (V i).ι ''ᵁ ((V i).ι ⁻¹ᵁ O)) O
    (fun i => homOfLE (((V i).ι).image_preimage_le O)) ?_ _ _ ?_
  · intro pt hpt
    obtain ⟨i, hi⟩ := hV.exists_mem pt
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ⟨pt, hi⟩, ?_, rfl⟩
    show (V i).ι.base ⟨pt, hi⟩ ∈ O
    exact hpt
  · intro i
    -- naturality moves the restriction inside `u.app`/`v.app`; the cover-member
    -- agreement is `hres i` evaluated on sections
    have hu := congr($(u.mapPresheaf.naturality
      (homOfLE (((V i).ι).image_preimage_le O)).op) x)
    have hv := congr($(v.mapPresheaf.naturality
      (homOfLE (((V i).ι).image_preimage_le O)).op) x)
    have hres_app := congr($(congrArg
      (fun (m : (Scheme.Modules.restrictFunctor (V i).ι).obj M ⟶
          (Scheme.Modules.restrictFunctor (V i).ι).obj N) =>
        Scheme.Modules.Hom.app m ((V i).ι ⁻¹ᵁ O)) (hres i))
      ((M.presheaf.map (homOfLE (((V i).ι).image_preimage_le O)).op) x))
    exact hu.symm.trans (hres_app.trans hv)

/-- **The local-to-global inverse of the universal property** (Nitsure §1): a rank-`d`
locally free quotient `q : O_T^r ↠ F` determines a morphism `T ⟶ Gr(d,r)` — the gluing,
over the open cover `{T_I}` of the chart loci (`chartLocus_isOpenCover`), of the
composites `T_I ⟶ U^I ⟶ Gr(d,r)` of the chart morphisms (`chartMorphism`) with the
glue-data immersions; the overlap compatibility is `chartMorphism_glue_compat`. -/
noncomputable def grPointOfRankQuotient {T : Scheme.{0}} (d r : ℕ)
    (x : RankQuotient r d T) : T ⟶ scheme d r :=
  (T.openCoverOfIsOpenCover _ (chartLocus_isOpenCover d r x)).glueMorphisms
    (fun I => chartMorphism d r x I.1 I.2 ≫ (theGlueData d r).ι I)
    (fun I J => chartMorphism_glue_compat d r x I J)

set_option maxHeartbeats 3200000 in
-- Reason: heavy category theory unification
/-- The inverse construction is constant on equivalence classes of quotients: an
isomorphism of targets commuting with the quotient maps induces the same chart loci
(`chartLocus_rel`), the same presenting matrices (`chartMatrixHom` is unchanged since
`q_y ≫ (c_y)⁻¹ = q_x ≫ f ≫ f⁻¹ ≫ (c_x)⁻¹ = q_x ≫ (c_x)⁻¹` after `chartComposite_rel`),
hence the same chart morphisms and the same glued morphism (compare both gluings over
the common cover via `Scheme.OpenCover.hom_ext` + `ι_glueMorphisms`). The remaining
content is the transport of `chartMatrix` along the locus equality. -/
lemma grPointOfRankQuotient_rel {T : Scheme.{0}} (d r : ℕ)
    {x y : RankQuotient r d T} (h : x.Rel y) :
    grPointOfRankQuotient d r x = grPointOfRankQuotient d r y := by
  obtain ⟨f, hf⟩ := h
  refine (T.openCoverOfIsOpenCover _ (chartLocus_isOpenCover d r x)).hom_ext _ _ (fun I => ?_)
  have hL : chartLocus x I.1 I.2 = chartLocus y I.1 I.2 := chartLocus_rel ⟨f, hf⟩ I.1 I.2
  -- the defining property of the two glued morphisms on their own chart loci
  have hx : (chartLocus x I.1 I.2).ι ≫ grPointOfRankQuotient d r x
      = chartMorphism d r x I.1 I.2 ≫ (theGlueData d r).ι I :=
    Scheme.Cover.ι_glueMorphisms (T.openCoverOfIsOpenCover _ (chartLocus_isOpenCover d r x))
      (fun J => chartMorphism d r x J.1 J.2 ≫ (theGlueData d r).ι J)
      (fun J K => chartMorphism_glue_compat d r x J K) I
  have hy : (chartLocus y I.1 I.2).ι ≫ grPointOfRankQuotient d r y
      = chartMorphism d r y I.1 I.2 ≫ (theGlueData d r).ι I :=
    Scheme.Cover.ι_glueMorphisms (T.openCoverOfIsOpenCover _ (chartLocus_isOpenCover d r y))
      (fun J => chartMorphism d r y J.1 J.2 ≫ (theGlueData d r).ι J)
      (fun J K => chartMorphism_glue_compat d r y J K) I
  -- the cover map of the `x`-cover factors through the (equal) `y`-locus
  have hι : (chartLocus x I.1 I.2).ι
      = T.homOfLE hL.le ≫ (chartLocus y I.1 I.2).ι := (T.homOfLE_ι hL.le).symm
  change (chartLocus x I.1 I.2).ι ≫ grPointOfRankQuotient d r x
    = (chartLocus x I.1 I.2).ι ≫ grPointOfRankQuotient d r y
  rw [hx, chartMorphism_rel d r f hf I.1 I.2 hL.le, hι, Category.assoc, Category.assoc, hy]
  rfl

/-! ### The two inverse laws of the universal property

Uniqueness (`left_inv`): over the preimage of each chart-immersion range the glued
morphism and `ψ` are both classified by the `ψ`-image of the universal matrix
(`presentedMatrix_rqPullback` + `presentedMatrix_tautological`), so they agree on an
open cover. Existence (`right_inv`): over each chart locus of `x` the pulled-back
tautological quotient and `x.q` are presented by the same matrix
(`presentedMatrix_rqPullback_grPoint`), so each kernel annihilates the opposite
quotient (`pullback_map_cover_faithful`); the two `Abelian.epiDesc` descents are then
mutually inverse by epi-cancellation, witnessing the equivalence `Rel`. -/

set_option maxHeartbeats 1600000 in
-- the assembly chains Γ–Spec naturality with five matrix transports over `W`
/-- **Uniqueness of the classifying morphism** (`thm:grassmannian_universal_property`,
the `left_inv` law): gluing the chart data of the pulled-back tautological quotient
recovers `ψ`. Checked over the open cover `{ψ⁻¹(ι_I(U^I))}`: there `ψ` factors through
the chart immersion, and both morphisms are classified by the matrix presenting
`ψ^*⟨U, u⟩`, via `comp_chartMorphism`, `presentedMatrix_rqPullback`,
`presentedMatrix_comp` and `presentedMatrix_tautological`. Project-local. -/
lemma grPointOfRankQuotient_rqPullback_tautological (d r : ℕ) {T : Scheme.{0}}
    (ψ : T ⟶ scheme d r) :
    grPointOfRankQuotient d r (rqPullback ψ (tautologicalRankQuotient d r)) = ψ := by
  -- the preimages of the chart-immersion ranges cover `T`
  have hcov : TopologicalSpace.IsOpenCover
      (fun I : (theGlueData d r).J =>
        ψ ⁻¹ᵁ @Scheme.Hom.opensRange _ _ ((theGlueData d r).ι I)
          ((theGlueData d r).ι_isOpenImmersion I)) := by
    refine TopologicalSpace.IsOpenCover.mk ?_
    rw [eq_top_iff]
    intro t _
    obtain ⟨I, y, hy⟩ := (theGlueData d r).ι_jointly_surjective (ψ.base t)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨I, ⟨y, hy⟩⟩
  refine (T.openCoverOfIsOpenCover _ hcov).hom_ext _ _ (fun I => ?_)
  haveI hoi : IsOpenImmersion ((theGlueData d r).ι I) := (theGlueData d r).ι_isOpenImmersion I
  change (ψ ⁻¹ᵁ @Scheme.Hom.opensRange _ _ ((theGlueData d r).ι I) hoi).ι ≫
      grPointOfRankQuotient d r (rqPullback ψ (tautologicalRankQuotient d r))
    = (ψ ⁻¹ᵁ @Scheme.Hom.opensRange _ _ ((theGlueData d r).ι I) hoi).ι ≫ ψ
  set W : T.Opens := ψ ⁻¹ᵁ @Scheme.Hom.opensRange _ _ ((theGlueData d r).ι I) hoi with hWdef
  -- the cover member sits inside the chart locus of the pulled-back quotient
  have hle : W ≤ chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2 := by
    refine le_trans ?_ (chartLocus_rqPullback ψ (tautologicalRankQuotient d r) I.1 I.2)
    intro t ht
    have ht' : ψ.base t ∈ @Scheme.Hom.opensRange _ _ ((theGlueData d r).ι I) hoi := ht
    exact opensRange_le_chartLocus_tautological d r I ht'
  -- `W.ι ≫ ψ` factors through the chart immersion
  have hrange : Set.range (W.ι ≫ ψ).base
      ⊆ Set.range ((theGlueData d r).ι I).base := by
    rintro t ⟨w, rfl⟩
    have hw : W.ι.base w ∈ W := by
      have : W.ι.base w ∈ Set.range W.ι.base := ⟨w, rfl⟩
      rwa [Scheme.Opens.range_ι] at this
    rw [Scheme.Hom.comp_base, TopCat.comp_app]
    show ψ.base (W.ι.base w) ∈ @Scheme.Hom.opensRange _ _ ((theGlueData d r).ι I) hoi
    exact hw
  set ρ : W.toScheme ⟶ (theGlueData d r).U I :=
    @IsOpenImmersion.lift _ _ _ ((theGlueData d r).ι I) (W.ι ≫ ψ) hoi hrange with hρdef
  have hfac : ρ ≫ (theGlueData d r).ι I = W.ι ≫ ψ :=
    @IsOpenImmersion.lift_fac _ _ _ ((theGlueData d r).ι I) (W.ι ≫ ψ) hoi hrange
  -- the defining property of the glued morphism on the chart locus
  have hglue : (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι ≫
        grPointOfRankQuotient d r (rqPullback ψ (tautologicalRankQuotient d r))
      = chartMorphism d r (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2 ≫
        (theGlueData d r).ι I :=
    Scheme.Cover.ι_glueMorphisms (T.openCoverOfIsOpenCover _ (chartLocus_isOpenCover d r (rqPullback ψ (tautologicalRankQuotient d r))))
      (fun J => chartMorphism d r (rqPullback ψ (tautologicalRankQuotient d r)) J.1 J.2 ≫ (theGlueData d r).ι J)
      (fun J K => chartMorphism_glue_compat d r (rqPullback ψ (tautologicalRankQuotient d r)) J K) I
  have hWι : W.ι = T.homOfLE hle ≫
      (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι :=
    (T.homOfLE_ι hle).symm
  -- chart-morphism naturality at the inclusion
  haveI hch : IsIso ((Scheme.Modules.pullback (T.homOfLE hle ≫
      (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι)).map
      (chartComposite (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2)) :=
    isIso_pullback_map_comp (T.homOfLE hle)
      ((chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι)
      (chartComposite (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2)
  have hcomp : T.homOfLE hle ≫
        chartMorphism d r (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2
      = W.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
            presentedMatrix (rqPullback ψ (tautologicalRankQuotient d r))
              (T.homOfLE hle ≫
                (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι)
              I.1 I.2 pq.1 pq.2.1)).toRingHom) :=
    comp_chartMorphism d r (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2
      (T.homOfLE hle)
  -- the presenting matrix is the `ρ`-image of the universal matrix
  haveI hc1 : IsIso ((Scheme.Modules.pullback W.ι).map
      (chartComposite (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2)) :=
    isIso_pullback_map_of_le _ hle (isIso_pullback_isoLocus_map _)
  haveI htaut : IsIso ((Scheme.Modules.pullback ((theGlueData d r).ι I)).map
      (chartComposite (tautologicalRankQuotient d r) I.1 I.2)) :=
    isIso_pullback_chartComposite_tautological d r I
  haveI hc2 : IsIso ((Scheme.Modules.pullback (W.ι ≫ ψ)).map
      (chartComposite (tautologicalRankQuotient d r) I.1 I.2)) := by
    rw [← hfac]
    exact isIso_pullback_map_comp ρ ((theGlueData d r).ι I) (chartComposite (tautologicalRankQuotient d r) I.1 I.2)
  haveI hc3 : IsIso ((Scheme.Modules.pullback (ρ ≫ (theGlueData d r).ι I)).map
      (chartComposite (tautologicalRankQuotient d r) I.1 I.2)) :=
    isIso_pullback_map_comp ρ ((theGlueData d r).ι I) (chartComposite (tautologicalRankQuotient d r) I.1 I.2)
  have hmatrix : presentedMatrix (rqPullback ψ (tautologicalRankQuotient d r))
        (T.homOfLE hle ≫
          (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι) I.1 I.2
      = ((universalMatrix d r I.1 I.2).map
          ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
            (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv)).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop ρ)) := by
    calc presentedMatrix (rqPullback ψ (tautologicalRankQuotient d r))
          (T.homOfLE hle ≫
            (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι) I.1 I.2
        = presentedMatrix (rqPullback ψ (tautologicalRankQuotient d r)) W.ι I.1 I.2 :=
          presentedMatrix_congr _ hWι.symm I.1 I.2
      _ = presentedMatrix (tautologicalRankQuotient d r) (W.ι ≫ ψ) I.1 I.2 :=
          presentedMatrix_rqPullback ψ (tautologicalRankQuotient d r) W.ι I.1 I.2
      _ = presentedMatrix (tautologicalRankQuotient d r) (ρ ≫ (theGlueData d r).ι I)
            I.1 I.2 (hcI := hc3) :=
          @presentedMatrix_congr _ _ _ _ (tautologicalRankQuotient d r) _ _ hfac.symm
            I.1 I.2 hc2 hc3
      _ = (presentedMatrix (tautologicalRankQuotient d r) ((theGlueData d r).ι I)
            I.1 I.2 (hcI := htaut)).map ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop ρ)) :=
          presentedMatrix_comp (tautologicalRankQuotient d r) ρ ((theGlueData d r).ι I)
            I.1 I.2 (hca := htaut) (hcpa := hc3)
      _ = ((universalMatrix d r I.1 I.2).map
            ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
              (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv)).map
            ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop ρ)) := by
          rw [presentedMatrix_tautological d r I]; rfl
  -- the classifying ring map reconstructs `ρ`
  have hclass : CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
        (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
          presentedMatrix (rqPullback ψ (tautologicalRankQuotient d r))
            (T.homOfLE hle ≫
              (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι)
            I.1 I.2 pq.1 pq.2.1)).toRingHom
      = (Scheme.ΓSpecIso (CommRingCat.of
          (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv ≫
        Scheme.Hom.appTop ρ := by
    refine CommRingCat.hom_ext (MvPolynomial.ringHom_ext' (Subsingleton.elim _ _)
      (fun pq => ?_))
    simp only [CommRingCat.hom_ofHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rw [hmatrix]
    simp only [Matrix.map_apply, universalMatrix]
    rw [dif_neg pq.2.2, Subtype.coe_eta]; rfl
  -- assemble
  have hunit : ((theGlueData d r).U I).toSpecΓ ≫
        Spec.map (Scheme.ΓSpecIso (CommRingCat.of
          (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv = 𝟙 _ :=
    toSpecΓ_SpecMap_ΓSpecIso_inv _
  -- assemble: the glued morphism on `W` factors as `ρ ≫ ι_I = W.ι ≫ ψ` (`hfac`), reached
  -- through `hglue`, `hcomp`, `hclass`, `hunit` and Γ–Spec naturality.  Phrased as an
  -- explicit `Eq.trans` chain: `calc` cannot synthesize the `Trans Eq Eq` instance here
  -- (the heavy intermediate `Spec.map`/`toSpecΓ` morphisms leave a per-step diamond goal).
  have u1 : W.ι ≫ grPointOfRankQuotient d r (rqPullback ψ (tautologicalRankQuotient d r))
      = (T.homOfLE hle ≫
          (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι) ≫
        grPointOfRankQuotient d r (rqPullback ψ (tautologicalRankQuotient d r)) :=
    congrArg (· ≫ grPointOfRankQuotient d r
      (rqPullback ψ (tautologicalRankQuotient d r))) hWι
  have u2 : (T.homOfLE hle ≫
          (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι) ≫
        grPointOfRankQuotient d r (rqPullback ψ (tautologicalRankQuotient d r))
      = T.homOfLE hle ≫
        (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι ≫
        grPointOfRankQuotient d r (rqPullback ψ (tautologicalRankQuotient d r)) :=
    Category.assoc _ _ _
  have u3 : T.homOfLE hle ≫
        (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι ≫
        grPointOfRankQuotient d r (rqPullback ψ (tautologicalRankQuotient d r))
      = T.homOfLE hle ≫
        chartMorphism d r (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2 ≫
        (theGlueData d r).ι I := congrArg (T.homOfLE hle ≫ ·) hglue
  have u4 : T.homOfLE hle ≫
        chartMorphism d r (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2 ≫
        (theGlueData d r).ι I
      = (T.homOfLE hle ≫
          chartMorphism d r (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2) ≫
        (theGlueData d r).ι I := (Category.assoc _ _ _).symm
  have u5 : (T.homOfLE hle ≫
          chartMorphism d r (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2) ≫
        (theGlueData d r).ι I
      = (W.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℤ)
          (fun pq : Fin d × {q : Fin r // q ∉ I.1} =>
            presentedMatrix (rqPullback ψ (tautologicalRankQuotient d r))
              (T.homOfLE hle ≫
                (chartLocus (rqPullback ψ (tautologicalRankQuotient d r)) I.1 I.2).ι)
              I.1 I.2 pq.1 pq.2.1)).toRingHom)) ≫
        (theGlueData d r).ι I := congrArg (· ≫ (theGlueData d r).ι I) hcomp
  -- the remaining `Spec`/`toSpecΓ` steps.  Fold `hclass` through `congrArg` (defeq-tolerant,
  -- so the `presentedMatrix` instance arguments reconcile where positional `rw [hclass]`
  -- cannot match), then `Spec.map_comp`, `toSpecΓ` naturality and `hunit` collapse the chart
  -- ring map to `ρ`; `hfac` lands on `W.ι ≫ ψ`.
  refine u1.trans (u2.trans (u3.trans (u4.trans (u5.trans
    ((congrArg (fun m => (W.toScheme.toSpecΓ ≫ Spec.map m) ≫ (theGlueData d r).ι I)
        hclass).trans ?_)))))
  -- `toSpecΓ`-naturality + the `Spec`-`ΓSpec` triangle collapse `W.toSpecΓ ≫ Spec.map(…) = ρ`.
  -- Use `toSpecΓ_SpecMap_ΓSpecIso_inv` directly (stated in the `Spec R` form) rather than
  -- `hunit` (stated via `(theGlueData d r).U I`), since naturality reduces `U I` to `Spec MP`.
  have key : W.toScheme.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of
        (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv ≫ Scheme.Hom.appTop ρ) = ρ := by
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
        toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  rw [key]
  exact hfac

set_option maxHeartbeats 1600000 in
-- pointwise factorisation through the glued morphism (heavy `glueMorphisms` term)
/-- **The chart loci of `x` lie inside the chart loci of the pulled-back tautological
quotient** along `grPointOfRankQuotient x`: on `T_I` the glued morphism factors through
the chart immersion, whose range lies in the tautological chart locus
(`opensRange_le_chartLocus_tautological`), and `chartLocus_rqPullback` transports the
locus back. Project-local — supplies the invertibility instance for the `right_inv`
comparison. -/
lemma chartLocus_le_chartLocus_rqPullback_grPoint {T : Scheme.{0}} (d r : ℕ)
    (x : RankQuotient r d T) (I : (theGlueData d r).J) :
    chartLocus x I.1 I.2
      ≤ chartLocus (rqPullback (grPointOfRankQuotient d r x)
          (tautologicalRankQuotient d r)) I.1 I.2 := by
  haveI hoi : IsOpenImmersion ((theGlueData d r).ι I) := (theGlueData d r).ι_isOpenImmersion I
  refine le_trans ?_ (chartLocus_rqPullback (grPointOfRankQuotient d r x)
    (tautologicalRankQuotient d r) I.1 I.2)
  refine le_trans (?_ : _ ≤ grPointOfRankQuotient d r x ⁻¹ᵁ
    @Scheme.Hom.opensRange _ _ ((theGlueData d r).ι I) hoi) ?_
  · -- the glued morphism maps `T_I` into the chart-immersion range
    have hglue : (chartLocus x I.1 I.2).ι ≫ grPointOfRankQuotient d r x
        = chartMorphism d r x I.1 I.2 ≫ (theGlueData d r).ι I :=
      Scheme.Cover.ι_glueMorphisms (T.openCoverOfIsOpenCover _ (chartLocus_isOpenCover d r x))
        (fun J => chartMorphism d r x J.1 J.2 ≫ (theGlueData d r).ι J)
        (fun J K => chartMorphism_glue_compat d r x J K) I
    intro t ht
    have htr : t ∈ Set.range (chartLocus x I.1 I.2).ι.base := by
      rw [Scheme.Opens.range_ι]; exact ht
    obtain ⟨w, rfl⟩ := htr
    show (grPointOfRankQuotient d r x).base ((chartLocus x I.1 I.2).ι.base w)
      ∈ @Scheme.Hom.opensRange _ _ ((theGlueData d r).ι I) hoi
    have hb : (grPointOfRankQuotient d r x).base ((chartLocus x I.1 I.2).ι.base w)
        = ((theGlueData d r).ι I).base ((chartMorphism d r x I.1 I.2).base w) := by
      have h1 := congrArg
        (fun f : (chartLocus x I.1 I.2).toScheme ⟶ scheme d r => f.base w) hglue
      simp only [Scheme.Hom.comp_base, TopCat.comp_app] at h1
      exact h1
    rw [hb]
    exact ⟨(chartMorphism d r x I.1 I.2).base w, rfl⟩
  · intro t ht
    exact opensRange_le_chartLocus_tautological d r I ht

set_option maxHeartbeats 3200000 in
-- Reason: heavy category theory unification
/-- **The pulled-back tautological quotient is presented over `T_I` by the chart matrix
of `x`**: the chain `presentedMatrix_rqPullback` → glued-morphism factorisation →
`presentedMatrix_comp` → `presentedMatrix_tautological` → `φ_I^* X^I = M^I`. The matrix
heart of the `right_inv` law. Project-local. -/
lemma presentedMatrix_rqPullback_grPoint {T : Scheme.{0}} (d r : ℕ)
    (x : RankQuotient r d T) (I : (theGlueData d r).J)
    [hc : IsIso ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
      (chartComposite (rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)) I.1 I.2))] :
    presentedMatrix (rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)) (chartLocus x I.1 I.2).ι I.1 I.2
      = chartMatrix x I.1 I.2 := by
  have hglue : (chartLocus x I.1 I.2).ι ≫ grPointOfRankQuotient d r x
      = chartMorphism d r x I.1 I.2 ≫ (theGlueData d r).ι I :=
    Scheme.Cover.ι_glueMorphisms (T.openCoverOfIsOpenCover _ (chartLocus_isOpenCover d r x))
      (fun J => chartMorphism d r x J.1 J.2 ≫ (theGlueData d r).ι J)
      (fun J K => chartMorphism_glue_compat d r x J K) I
  haveI htaut : IsIso ((Scheme.Modules.pullback ((theGlueData d r).ι I)).map
      (chartComposite (tautologicalRankQuotient d r) I.1 I.2)) :=
    isIso_pullback_chartComposite_tautological d r I
  haveI h1 : IsIso ((Scheme.Modules.pullback
      (chartMorphism d r x I.1 I.2 ≫ (theGlueData d r).ι I)).map
      (chartComposite (tautologicalRankQuotient d r) I.1 I.2)) :=
    @isIso_pullback_map_comp _ _ _ (chartMorphism d r x I.1 I.2) ((theGlueData d r).ι I)
      _ _ (chartComposite (tautologicalRankQuotient d r) I.1 I.2) htaut
  haveI h2 : IsIso ((Scheme.Modules.pullback
      ((chartLocus x I.1 I.2).ι ≫ grPointOfRankQuotient d r x)).map
      (chartComposite (tautologicalRankQuotient d r) I.1 I.2)) := by
    rw [hglue]; exact h1
  calc presentedMatrix (rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)) (chartLocus x I.1 I.2).ι I.1 I.2
      = presentedMatrix (tautologicalRankQuotient d r)
          ((chartLocus x I.1 I.2).ι ≫ grPointOfRankQuotient d r x) I.1 I.2 :=
        presentedMatrix_rqPullback (grPointOfRankQuotient d r x)
          (tautologicalRankQuotient d r) (chartLocus x I.1 I.2).ι I.1 I.2
    _ = presentedMatrix (tautologicalRankQuotient d r)
          (chartMorphism d r x I.1 I.2 ≫ (theGlueData d r).ι I) I.1 I.2 (hcI := h1) :=
        @presentedMatrix_congr _ _ _ _ (tautologicalRankQuotient d r) _ _ hglue I.1 I.2 h2 h1
    _ = (presentedMatrix (tautologicalRankQuotient d r) ((theGlueData d r).ι I)
          I.1 I.2 (hcI := isIso_pullback_chartComposite_tautological d r I)).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (chartMorphism d r x I.1 I.2))) :=
        presentedMatrix_comp (tautologicalRankQuotient d r)
          (chartMorphism d r x I.1 I.2) ((theGlueData d r).ι I) I.1 I.2
          (hca := isIso_pullback_chartComposite_tautological d r I) (hcpa := h1)
    _ = ((universalMatrix d r I.1 I.2).map
          ⇑(CommRingCat.Hom.hom (Scheme.ΓSpecIso (CommRingCat.of
            (MvPolynomial (Fin d × {q : Fin r // q ∉ I.1}) ℤ))).inv)).map
          ⇑(CommRingCat.Hom.hom (Scheme.Hom.appTop (chartMorphism d r x I.1 I.2))) := by
        rw [presentedMatrix_tautological d r I]; rfl
    _ = chartMatrix x I.1 I.2 := universalMatrix_map_chartMorphism d r x I.1 I.2

set_option maxHeartbeats 1600000 in
-- iso cancellation against the heavy `rqPullback`/`grPoint` terms
/-- **The conjugated chart presentations of `(grPoint x)^*⟨U,u⟩` and of `x` agree over
each chart locus** — both equal `matrixEndRect (chartMatrix x)`. The morphism-level form
of `presentedMatrix_rqPullback_grPoint`, with the free-pullback conjugation cancelled.
Project-local. -/
lemma pullback_map_rqPullback_grPoint_eq {T : Scheme.{0}} (d r : ℕ)
    (x : RankQuotient r d T) (I : (theGlueData d r).J)
    [hc : IsIso ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
      (chartComposite (rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)) I.1 I.2))] :
    (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
        ((rqPullback (grPointOfRankQuotient d r x) (tautologicalRankQuotient d r)).q) ≫
      inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
        (chartComposite (rqPullback (grPointOfRankQuotient d r x)
          (tautologicalRankQuotient d r)) I.1 I.2))
    = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map x.q ≫
      inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
        (chartComposite x I.1 I.2)) := by
  have h1 : matrixEndRect (presentedMatrix (rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)) (chartLocus x I.1 I.2).ι I.1 I.2)
      = matrixEndRect (presentedMatrix x (chartLocus x I.1 I.2).ι I.1 I.2) :=
    congrArg matrixEndRect ((presentedMatrix_rqPullback_grPoint d r x I).trans
      (chartMatrix_eq_presentedMatrix x I.1 I.2))
  rw [matrixEndRect_presentedMatrix, matrixEndRect_presentedMatrix] at h1
  have h2 := (cancel_epi
    (Scheme.Modules.pullbackFreeIso (chartLocus x I.1 I.2).ι (Fin r)).inv).mp h1
  have h3 : ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
        ((rqPullback (grPointOfRankQuotient d r x) (tautologicalRankQuotient d r)).q) ≫
        inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
          (chartComposite (rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)) I.1 I.2))) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I.1 I.2).ι (Fin d)).hom
      = ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map x.q ≫
        inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
          (chartComposite x I.1 I.2))) ≫
        (Scheme.Modules.pullbackFreeIso (chartLocus x I.1 I.2).ι (Fin d)).hom :=
    (Category.assoc _ _ _).trans (h2.trans (Category.assoc _ _ _).symm)
  exact (cancel_mono
    (Scheme.Modules.pullbackFreeIso (chartLocus x I.1 I.2).ι (Fin d)).hom).mp h3

set_option maxHeartbeats 1600000 in
-- kernel/epi-descent assembly against the heavy pullback terms
/-- **Pulling the tautological pair back along the glued morphism recovers `x`**
(`thm:grassmannian_universal_property`, the `right_inv` law): the equivalence witness is
assembled with no descent gluing — over each chart locus both quotients are presented by
the same matrix (`pullback_map_rqPullback_grPoint_eq`), so each kernel annihilates the
opposite quotient (`pullback_map_cover_faithful` over `chartLocus_isOpenCover`); the two
`Abelian.epiDesc` descents are mutually inverse by epi-cancellation. Project-local. -/
lemma rqPullback_grPointOfRankQuotient_rel {T : Scheme.{0}} (d r : ℕ)
    (x : RankQuotient r d T) :
    (rqPullback (grPointOfRankQuotient d r x) (tautologicalRankQuotient d r)).Rel x := by
  haveI hex' : Epi ((rqPullback (grPointOfRankQuotient d r x)
      (tautologicalRankQuotient d r)).q) :=
    (rqPullback (grPointOfRankQuotient d r x) (tautologicalRankQuotient d r)).epi
  haveI hex : Epi x.q := x.epi
  -- the chart-locus invertibility instances
  haveI hinst : ∀ I : (theGlueData d r).J,
      IsIso ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
        (chartComposite (rqPullback (grPointOfRankQuotient d r x)
          (tautologicalRankQuotient d r)) I.1 I.2)) := fun I =>
    isIso_pullback_map_of_le _ (chartLocus_le_chartLocus_rqPullback_grPoint d r x I)
      (isIso_pullback_isoLocus_map _)
  -- each kernel annihilates the opposite quotient, chart-locally
  have hker1 : kernel.ι ((rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)).q) ≫ x.q = 0 := by
    refine pullback_map_cover_faithful (chartLocus_isOpenCover d r x) (fun I => ?_)
    haveI := hinst I
    have heq := pullback_map_rqPullback_grPoint_eq d r x I
    -- `x.q` through the shared presentation
    have hxq : (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map x.q
        = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            ((rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)).q) ≫
          (inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (chartComposite (rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)) I.1 I.2)) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite x I.1 I.2)) := by
      calc (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map x.q
          = ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map x.q ≫
              inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
                (chartComposite x I.1 I.2))) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite x I.1 I.2) := by
            rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        _ = ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              ((rqPullback (grPointOfRankQuotient d r x)
                (tautologicalRankQuotient d r)).q) ≫
              inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
                (chartComposite (rqPullback (grPointOfRankQuotient d r x)
                  (tautologicalRankQuotient d r)) I.1 I.2))) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite x I.1 I.2) :=
            congrArg (· ≫ (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite x I.1 I.2)) heq.symm
        _ = _ := Category.assoc _ _ _
    calc (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
          (kernel.ι ((rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q) ≫ x.q)
        = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (kernel.ι ((rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)).q)) ≫
          (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map x.q :=
          (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map_comp _ _
      _ = ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (kernel.ι ((rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)).q)) ≫
          (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            ((rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)).q)) ≫
          (inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (chartComposite (rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)) I.1 I.2)) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite x I.1 I.2)) :=
          (congrArg ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (kernel.ι ((rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)).q)) ≫ ·) hxq).trans
            (Category.assoc _ _ _).symm
      _ = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (kernel.ι ((rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)).q) ≫
              (rqPullback (grPointOfRankQuotient d r x)
                (tautologicalRankQuotient d r)).q) ≫
          (inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (chartComposite (rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)) I.1 I.2)) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite x I.1 I.2)) :=
          congrArg (· ≫ _)
            ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map_comp _ _).symm
      _ = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map 0 ≫
          (inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (chartComposite (rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)) I.1 I.2)) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite x I.1 I.2)) :=
          congrArg (· ≫ _)
            (congrArg (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (kernel.condition ((rqPullback (grPointOfRankQuotient d r x) (tautologicalRankQuotient d r)).q)))
      _ = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map 0 := by
          rw [Functor.map_zero, zero_comp, Functor.map_zero]
  have hker2 : kernel.ι x.q ≫ (rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)).q = 0 := by
    refine pullback_map_cover_faithful (chartLocus_isOpenCover d r x) (fun I => ?_)
    haveI := hinst I
    have heq := pullback_map_rqPullback_grPoint_eq d r x I
    have hxq' : (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
          ((rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q)
        = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map x.q ≫
          (inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (chartComposite x I.1 I.2)) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite (rqPullback (grPointOfRankQuotient d r x)
                (tautologicalRankQuotient d r)) I.1 I.2)) := by
      calc (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            ((rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)).q)
          = ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              ((rqPullback (grPointOfRankQuotient d r x)
                (tautologicalRankQuotient d r)).q) ≫
              inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
                (chartComposite (rqPullback (grPointOfRankQuotient d r x)
                  (tautologicalRankQuotient d r)) I.1 I.2))) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite (rqPullback (grPointOfRankQuotient d r x)
                (tautologicalRankQuotient d r)) I.1 I.2) := by
            rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        _ = ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map x.q ≫
              inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
                (chartComposite x I.1 I.2))) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite (rqPullback (grPointOfRankQuotient d r x)
                (tautologicalRankQuotient d r)) I.1 I.2) :=
            congrArg (· ≫ _) heq
        _ = _ := Category.assoc _ _ _
    calc (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
          (kernel.ι x.q ≫ (rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q)
        = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map (kernel.ι x.q) ≫
          (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            ((rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)).q) :=
          (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map_comp _ _
      _ = ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map (kernel.ι x.q) ≫
          (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map x.q) ≫
          (inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (chartComposite x I.1 I.2)) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite (rqPullback (grPointOfRankQuotient d r x)
                (tautologicalRankQuotient d r)) I.1 I.2)) :=
          (congrArg ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (kernel.ι x.q) ≫ ·) hxq').trans (Category.assoc _ _ _).symm
      _ = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (kernel.ι x.q ≫ x.q) ≫
          (inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (chartComposite x I.1 I.2)) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite (rqPullback (grPointOfRankQuotient d r x)
                (tautologicalRankQuotient d r)) I.1 I.2)) :=
          congrArg (· ≫ _)
            ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map_comp _ _).symm
      _ = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map 0 ≫
          (inv ((Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
            (chartComposite x I.1 I.2)) ≫
            (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map
              (chartComposite (rqPullback (grPointOfRankQuotient d r x)
                (tautologicalRankQuotient d r)) I.1 I.2)) :=
          congrArg (· ≫ _)
            (congrArg (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map (kernel.condition x.q))
      _ = (Scheme.Modules.pullback (chartLocus x I.1 I.2).ι).map 0 := by
          rw [Functor.map_zero, zero_comp, Functor.map_zero]
  -- the two epi-descents are mutually inverse
  have hfg : Abelian.epiDesc ((rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)).q) x.q hker1 ≫
        Abelian.epiDesc x.q ((rqPullback (grPointOfRankQuotient d r x)
          (tautologicalRankQuotient d r)).q) hker2
      = 𝟙 _ := by
    rw [← cancel_epi ((rqPullback (grPointOfRankQuotient d r x)
      (tautologicalRankQuotient d r)).q)]
    calc (rqPullback (grPointOfRankQuotient d r x) (tautologicalRankQuotient d r)).q ≫
          (Abelian.epiDesc ((rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q) x.q hker1 ≫
            Abelian.epiDesc x.q ((rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)).q) hker2)
        = ((rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q ≫
            Abelian.epiDesc ((rqPullback (grPointOfRankQuotient d r x)
              (tautologicalRankQuotient d r)).q) x.q hker1) ≫
          Abelian.epiDesc x.q ((rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q) hker2 := (Category.assoc _ _ _).symm
      _ = x.q ≫ Abelian.epiDesc x.q ((rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q) hker2 :=
          congrArg (· ≫ Abelian.epiDesc x.q _ hker2) (Abelian.comp_epiDesc _ _ _)
      _ = (rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q := Abelian.comp_epiDesc _ _ _
      _ = (rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q ≫ 𝟙 _ := (Category.comp_id _).symm
  have hgf : Abelian.epiDesc x.q ((rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)).q) hker2 ≫
        Abelian.epiDesc ((rqPullback (grPointOfRankQuotient d r x)
          (tautologicalRankQuotient d r)).q) x.q hker1
      = 𝟙 _ := by
    rw [← cancel_epi x.q]
    calc x.q ≫ (Abelian.epiDesc x.q ((rqPullback (grPointOfRankQuotient d r x)
          (tautologicalRankQuotient d r)).q) hker2 ≫
          Abelian.epiDesc ((rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q) x.q hker1)
        = (x.q ≫ Abelian.epiDesc x.q ((rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q) hker2) ≫
          Abelian.epiDesc ((rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q) x.q hker1 := (Category.assoc _ _ _).symm
      _ = (rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q ≫
          Abelian.epiDesc ((rqPullback (grPointOfRankQuotient d r x)
            (tautologicalRankQuotient d r)).q) x.q hker1 :=
          congrArg (· ≫ Abelian.epiDesc _ x.q hker1) (Abelian.comp_epiDesc _ _ _)
      _ = x.q := Abelian.comp_epiDesc _ _ _
      _ = x.q ≫ 𝟙 _ := (Category.comp_id _).symm
  exact ⟨⟨Abelian.epiDesc ((rqPullback (grPointOfRankQuotient d r x)
      (tautologicalRankQuotient d r)).q) x.q hker1,
    Abelian.epiDesc x.q ((rqPullback (grPointOfRankQuotient d r x)
      (tautologicalRankQuotient d r)).q) hker2, hfg, hgf⟩,
    Abelian.comp_epiDesc _ _ _⟩

/-- **`Gr(d,r)` represents the Grassmannian functor** (`thm:grassmannian_universal_property`):
the tautological quotient `⟨U, u⟩` exhibits `Gr(d,r)` as the fine moduli space of rank-`d`
quotients of `O^r`, i.e. `Hom(T, Gr(d,r)) ≅ Grass(r,d)(T)` naturally in `T`.

The forward map sends `ψ : T ⟶ Gr(d,r)` to the pullback `ψ^*(U, u)` of the tautological
pair (`tautologicalRankQuotient`); naturality (`homEquiv_comp`) is the already-proven
pseudofunctoriality `(functor d r).map_comp` evaluated at the tautological point. The
inverse is the chart-by-chart construction `grPointOfRankQuotient`; the two inverse laws
are the remaining content (they consume the chart restriction isomorphisms
`universalQuotient_restrictionIso` and the glued-scheme universal property). -/
noncomputable def represents (d r : ℕ) (hd : 1 ≤ d) (hdr : d ≤ r) :
    (functor d r).RepresentableBy (scheme d r) where
  homEquiv {T} :=
    { toFun := fun ψ => Quotient.mk _ (rqPullback ψ (tautologicalRankQuotient d r))
      invFun := Quotient.lift (grPointOfRankQuotient d r)
        (fun _ _ h => grPointOfRankQuotient_rel d r h)
      left_inv := fun ψ => by
        -- `grPointOfRankQuotient (ψ^* (U, u)) = ψ`: chart-locally, the pulled-back
        -- matrix of sections is the `ψ`-image of the universal one, so the glued
        -- morphism is `ψ` by uniqueness over the chart cover.
        exact grPointOfRankQuotient_rqPullback_tautological d r ψ
      right_inv := fun q => by
        -- `(grPointOfRankQuotient x)^* (U, u) ~ x`: over each chart locus both
        -- quotients are presented by the chart matrix, so the two `Abelian.epiDesc`
        -- descents witness the equivalence (no descent gluing needed).
        induction q using Quotient.ind with
        | _ x => exact Quotient.sound (rqPullback_grPointOfRankQuotient_rel d r x) }
  homEquiv_comp {T T'} f g := by
    -- pseudofunctoriality of `rqPullback` at the tautological point — this is
    -- `(functor d r).map_comp` evaluated at `⟦(U, u)⟧`
    have h := congrArg (fun m => m (Quotient.mk _ (tautologicalRankQuotient d r)))
      ((functor d r).map_comp g.op f.op)
    exact h

end AlgebraicGeometry.Grassmannian
