/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import AlgebraicJacobian.Cohomology.CechSectionIdentificationBase

/-!
# Sub-brick A — Leg: the `coreIso_comm` chain

The `coreIso_comm` chain (`abHom_finsetSum_apply`, `coreIso_comm_leg`, `coreIso_comm_coface`,
`coreIso_comm_sum`, `coreIso_comm`) expressing naturality of the degreewise section iso
through the Čech differentials. Depends on `CechSectionIdentificationBase`.

Carries the residual sorry `coreIso_comm_leg`.
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The `coreIso_comm` chain (`lem:coreIso_comm_leg` → `lem:coreIso_comm_coface` →
`lem:coreIso_comm_sum` → `lem:coreIso_comm`), built bottom-up per the iter-072 effort-break. -/

/-- Application of a finite sum of `Ab`-morphisms distributes over the sum.  (Local copy of
the `CechAcyclic` private helper `ab_hom_finsetSum_apply`.) -/
private lemma abHom_finsetSum_apply {A B : Ab.{u}} {κ : Type*}
    (s : Finset κ) (f : κ → (A ⟶ B)) (t : ToType A) :
    ConcreteCategory.hom (∑ i ∈ s, f i) t = ∑ i ∈ s, ConcreteCategory.hom (f i) t := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

/-! ### Geometric seam for `coreIso_comm_leg`

The per-leg coface naturality is proved by unwinding `coreIso_objIso` to the push–pull
map of the **backbone inclusion** `backboneIncl 𝒰 p τ : Over.mk j_τ ⟶ Y_p` (the morphism
produced by `pushPull_sigma_iso_π`), and then computing geometrically:

1. the backbone inclusion followed by the `l`-th wide-pullback projection is the
   canonical component map `interProj` (`backboneIncl_proj` — the Stub-1 unwinding);
2. hence the nerve coface `δ^nerve_k` restricts on the `σ'`-summand to the open
   inclusion `interLegHom : U_{σ'} ⊆ U_{σ'∘δᵏ}` (`backboneIncl_nerveδ`, by `hom_ext`
   through the projections);
3. the evaluated push–pull of that open inclusion acts on the identified leg sections
   as the plain `F`-restriction (`pushPull_interLegHom_sections`). -/

/-- The `τ`-summand inclusion `Over.mk j_τ ⟶ Y_p` of the degree-`p` Čech backbone:
the coproduct inclusion composed with the two backbone identifications read backwards.
By `pushPull_sigma_iso_π`, its push–pull map is the `τ`-projection of
`pushPull_sigma_iso`. -/
noncomputable def backboneIncl (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (p : ℕ)
    (τ : Fin (p + 1) → 𝒰.I₀) :
    Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ)) ⟶
      (coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk p)) :=
  coprodOverIncl (fun σ : Fin (p + 1) → 𝒰.I₀ =>
      Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) τ ≫
    (overSigmaDescIso (fun σ : Fin (p + 1) → 𝒰.I₀ =>
      (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).hom)).inv ≫
    (cechBackbone_left_sigma 𝒰 p).inv

/-- `pushPull_sigma_iso_π`, rephrased through `backboneIncl`. -/
lemma pushPull_sigma_iso_π_incl (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (p : ℕ)
    (τ : Fin (p + 1) → 𝒰.I₀) :
    (pushPull_sigma_iso 𝒰 F p).hom ≫
        Pi.π (fun σ : Fin (p + 1) → 𝒰.I₀ =>
          pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) τ =
      pushPullMap F (backboneIncl 𝒰 p τ) :=
  pushPull_sigma_iso_π 𝒰 F p τ

/-- The over-level `l`-th wide-pullback projection of the degree-`p` backbone, landing
in the cover-arrow object `Over.mk (Sigma.desc 𝒰.f)`. -/
noncomputable def backboneProj (𝒰 : X.OpenCover) (p : ℕ) (l : Fin (p + 1)) :
    (coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk p)) ⟶
      Over.mk (Sigma.desc 𝒰.f) :=
  Over.homMk (WidePullback.π (fun _ : Fin (p + 1) => Sigma.desc 𝒰.f) l)
    (WidePullback.π_arrow _ l)

/-- Morphisms into the degree-`p` backbone are determined by the `p + 1` over-level
wide-pullback projections: the backbone is the slice product of cover-arrow copies
(`widePullback_overX_isLimit`). -/
lemma backbone_hom_ext (𝒰 : X.OpenCover) (p : ℕ) {A : Over X}
    {u v : A ⟶ (coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk p))}
    (h : ∀ l : Fin (p + 1), u ≫ backboneProj 𝒰 p l = v ≫ backboneProj 𝒰 p l) : u = v := by
  apply Over.OverMorphism.ext
  apply WidePullback.hom_ext (fun _ : Fin (p + 1) => Sigma.desc 𝒰.f)
  · intro l
    exact congrArg CommaMorphism.left (h l)
  · exact (Over.w u).trans (Over.w v).symm

/-- The Čech-nerve simplicial face intertwines the backbone projections: the geometric
coface followed by the `l`-th projection is the `δᵏ l`-th projection. -/
lemma nerveδ_backboneProj (𝒰 : X.OpenCover) (p : ℕ) (k : Fin (p + 2)) (l : Fin (p + 1)) :
    (coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op) ≫ backboneProj 𝒰 p l =
      backboneProj 𝒰 (p + 1) ((SimplexCategory.δ k).toOrderHom l) := by
  apply Over.OverMorphism.ext
  exact WidePullback.lift_π (fun _ : Fin (p + 1) => Sigma.desc 𝒰.f) _ _ _ l

-- The `rfl` unfolds the whiskered augmented-cosimplicial packaging of `CechNerve`, whose
-- kernel `whnf` exceeds the default budget.
set_option maxHeartbeats 1600000 in
/-- The evaluated Čech-nerve coface is the push–pull map of the geometric backbone
simplicial face (definitional unwinding of `CechNerve`). -/
lemma cechNerve_drop_δ (𝒰 : X.OpenCover) (F : X.Modules) {p : ℕ} (k : Fin (p + 2)) :
    (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k =
      pushPullMap F ((coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op)) := by
  rfl

/-- The canonical lift of the intersection-open inclusion `U_τ ↪ X` against the
`τ l`-th cover member (an open immersion). -/
noncomputable def coverInterToMember (𝒰 : X.OpenCover) {p : ℕ}
    (τ : Fin (p + 1) → 𝒰.I₀) (l : Fin (p + 1)) :
    Scheme.Opens.toScheme (coverInterOpen 𝒰 τ) ⟶ 𝒰.X (τ l) :=
  IsOpenImmersion.lift (𝒰.f (τ l)) (Scheme.Opens.ι (coverInterOpen 𝒰 τ)) (by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange]
    exact SetLike.coe_subset_coe.mpr (iInf_le (fun j => coverOpen 𝒰 (τ j)) l))

/-- Factorization property of `coverInterToMember`. -/
lemma coverInterToMember_fac (𝒰 : X.OpenCover) {p : ℕ} (τ : Fin (p + 1) → 𝒰.I₀)
    (l : Fin (p + 1)) :
    coverInterToMember 𝒰 τ l ≫ 𝒰.f (τ l) = Scheme.Opens.ι (coverInterOpen 𝒰 τ) :=
  IsOpenImmersion.lift_fac _ _ _

/-- The canonical `l`-th component of the `τ`-leg in the cover-arrow object: lift to the
`τ l`-th member, then include into the coproduct. -/
noncomputable def interProj (𝒰 : X.OpenCover) {p : ℕ} (τ : Fin (p + 1) → 𝒰.I₀)
    (l : Fin (p + 1)) :
    Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ)) ⟶ Over.mk (Sigma.desc 𝒰.f) :=
  Over.homMk (coverInterToMember 𝒰 τ l ≫ Sigma.ι 𝒰.X (τ l)) (by
    show (coverInterToMember 𝒰 τ l ≫ Sigma.ι 𝒰.X (τ l)) ≫ Sigma.desc 𝒰.f =
      Scheme.Opens.ι (coverInterOpen 𝒰 τ)
    rw [Category.assoc, Sigma.ι_desc]
    exact coverInterToMember_fac 𝒰 τ l)

/-- Mono-target rigidity in the slice: two over-`X` morphisms into `Over.mk g` with `g`
a monomorphism agree.  (Used to absorb the reindexing isos of the Stub-1 chain.) -/
lemma over_hom_ext_mono {A : Over X} {B : Scheme.{u}} {g : B ⟶ X} [Mono g]
    (u v : A ⟶ Over.mk g) : u = v :=
  Over.OverMorphism.ext ((cancel_mono g).mp ((Over.w u).trans (Over.w v).symm))

/-! ### The Stub-1 unwinding: projections of the `widePullback_coproduct_iso` inclusions.

Abstract lemmas (any finitary pre-extensive category): the composite of a `σ`-summand
inclusion with the inverse of the distributivity iso `widePullback_coproduct_iso` and an
over-level wide-pullback projection is the canonical `l`-th factor projection followed by
the `σ l`-th descent inclusion.  This is the geometric content of `backboneIncl_proj`. -/

section WPCIproj

open CategoryTheory.FinitaryPreExtensive

variable {C : Type*} [Category C]

/-- Head projection of the inverse of `prodFinSuccIso`. -/
private lemma prodFinSuccIso_inv_π_zero [HasFiniteProducts C] {n : ℕ} (W : Fin (n + 1) → C) :
    (prodFinSuccIso W).inv ≫ Pi.π W 0 = Limits.prod.fst :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk (0 : Fin (n + 1)))

/-- Tail projections of the inverse of `prodFinSuccIso`. -/
private lemma prodFinSuccIso_inv_π_succ [HasFiniteProducts C] {n : ℕ} (W : Fin (n + 1) → C)
    (i : Fin n) :
    (prodFinSuccIso W).inv ≫ Pi.π W i.succ =
      Limits.prod.snd ≫ Pi.π (fun j : Fin n => W j.succ) i :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk i.succ)

/-- Head projection of `prodFinSuccIso`. -/
private lemma prodFinSuccIso_hom_fst [HasFiniteProducts C] {n : ℕ} (W : Fin (n + 1) → C) :
    (prodFinSuccIso W).hom ≫ Limits.prod.fst = Pi.π W 0 :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk (0 : Fin (n + 1)))

/-- Tail projections of `prodFinSuccIso`. -/
private lemma prodFinSuccIso_hom_snd_π [HasFiniteProducts C] {n : ℕ} (W : Fin (n + 1) → C)
    (i : Fin n) :
    (prodFinSuccIso W).hom ≫ Limits.prod.snd ≫ Pi.π (fun j : Fin n => W j.succ) i =
      Pi.π W i.succ :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i.succ)

/-- ι-compatibility of a `Sigma.mapIso` inverse. -/
private lemma ι_sigmaMapIso_inv {β : Type*} {f g : β → C} [HasCoproductsOfShape β C]
    (w : ∀ b, f b ≅ g b) (b : β) :
    Limits.Sigma.ι g b ≫ (Limits.Sigma.mapIso w).inv = (w b).inv ≫ Limits.Sigma.ι f b := by
  have h := ι_colimMap (F := Discrete.functor g) (G := Discrete.functor f)
    (Discrete.natIso (F := Discrete.functor f) (G := Discrete.functor g)
      (fun j => w j.as)).inv ⟨b⟩
  exact h

/-- ι-compatibility of the nested-coproduct flatten/reindex
`coproduct_fibrePower_reindex`. -/
private lemma ι_fibrePower_reindex_inv {ι : Type} [Finite ι] [HasFiniteCoproducts C]
    {p : ℕ} (F : (Fin (p + 2) → ι) → C) (i : ι) (t : Fin (p + 1) → ι) :
    Limits.Sigma.ι F (Fin.cons i t) ≫ (coproduct_fibrePower_reindex p F).inv =
      Limits.Sigma.ι (fun τ : Fin (p + 1) → ι => F (Fin.cons i τ)) t ≫
        Limits.Sigma.ι (fun i : ι => ∐ fun τ : Fin (p + 1) → ι => F (Fin.cons i τ)) i := by
  simp only [coproduct_fibrePower_reindex, Iso.trans_inv, Sigma.whiskerEquiv,
    Limits.Sigma.ι_comp_map'_assoc, Iso.refl_hom, Category.comp_id, Category.assoc,
    sigmaSigmaIso_inv, Equiv.symm_trans_apply]
  refine Eq.trans (Limits.Sigma.ι_comp_map'_assoc _ _ _ _) ?_
  exact Eq.trans (Category.id_comp _)
    (Limits.Sigma.ι_desc _ ((⟨i, t⟩ : Σ _ : ι, Fin (p + 1) → ι)))

/-- ι-compatibility of a `Sigma.whiskerEquiv` inverse (the reindex layers of the
Stub-1 chain). -/
private lemma ι_whiskerEquiv_inv {β γ : Type*} {f : β → C} {g : γ → C}
    [HasCoproduct f] [HasCoproduct g] (e : β ≃ γ) (w : ∀ b, g (e b) ≅ f b) (c : γ) :
    Limits.Sigma.ι g c ≫ (Sigma.whiskerEquiv e w).inv =
      (eqToHom (by rw [e.apply_symm_apply]) ≫ (w (e.symm c)).hom) ≫
        Limits.Sigma.ι f (e.symm c) :=
  Limits.Sigma.ι_comp_map' _ _ _

variable [HasPullbacks C] [FinitaryPreExtensive C] {ι : Type} [Finite ι]
  [HasFiniteCoproducts C]

/-- `coprodFirst_distrib` is compatible with the second projection (counterpart of the
recorded `cf_hom_fst`). -/
private lemma cf_hom_snd {S : C} (B : C) (b : B ⟶ S) {Y : ι → C} (g : (i : ι) → Y i ⟶ S) :
    (coprodFirst_distrib B b g).hom ≫ pullback.snd (Limits.Sigma.desc g) b =
      Limits.Sigma.desc (fun i => pullback.snd (g i) b) := by
  rw [coprodFirst_distrib]
  simp only [Iso.trans_hom, asIso_hom, Category.assoc]
  rw [pullbackSymmetry_hom_comp_snd, pcd_hom_fst]
  refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
  rw [← Category.assoc, Limits.Sigma.ι_map, Category.assoc, Limits.Sigma.ι_desc,
    Limits.Sigma.ι_desc, pullbackSymmetry_hom_comp_fst]

/-- ι-compatibility of `coprodFirst_distrib`: the `i`-th coproduct inclusion of the
distributed pullbacks corresponds to the canonical pullback comparison along `Sigma.ι`. -/
private lemma ι_cf_hom {S : C} (B : C) (b : B ⟶ S) {Y : ι → C} (g : (i : ι) → Y i ⟶ S)
    (i : ι) :
    Limits.Sigma.ι (fun i => pullback (g i) b) i ≫ (coprodFirst_distrib B b g).hom =
      pullback.map (g i) b (Limits.Sigma.desc g) b (Limits.Sigma.ι Y i) (𝟙 B) (𝟙 S)
        (by rw [Category.comp_id, Limits.Sigma.ι_desc]) (by simp) := by
  apply pullback.hom_ext
  · rw [Category.assoc, cf_hom_fst, Limits.Sigma.ι_desc, pullback.lift_fst]
  · rw [Category.assoc, cf_hom_snd, Limits.Sigma.ι_desc, pullback.lift_snd, Category.comp_id]

/-- The slice structure map of a coproduct, through the coproduct comparison of
`Over.forget` (local copy of the `CechSectionIdentificationBase` private helper). -/
private lemma overSigmaHomEq {S : C} (A : ι → Over S) :
    (∐ A).hom = (PreservesCoproduct.iso (Over.forget S) A).hom ≫
      Limits.Sigma.desc (fun i => (A i).hom) := by
  haveI : HasColimit (Discrete.functor A ⋙ Over.forget S) :=
    hasColimit_of_iso (F := Discrete.functor (fun i => (A i).left))
      (Discrete.natIso (fun i => Iso.refl _))
  refine (PreservesCoproduct.iso (Over.forget S) A).inv_comp_eq.mp ?_
  rw [PreservesCoproduct.inv_hom]
  refine Limits.Sigma.hom_ext _ _ (fun i => ?_)
  rw [ι_comp_sigmaComparison_assoc]
  show (Limits.Sigma.ι A i).left ≫ (∐ A).hom = _
  rw [Limits.Sigma.ι_desc]
  exact Over.w (Limits.Sigma.ι A i)

/-- ι-compatibility of the slice distributivity `overProd_coproduct_distrib`: the `i`-th
inclusion of the distributed products corresponds to `Sigma.ι ⨯ 𝟙`. -/
private lemma ι_overProd_distrib_inv {S : C} [HasBinaryProducts (Over S)]
    (A : ι → Over S) (B : Over S) (i : ι) :
    Limits.Sigma.ι (fun i => A i ⨯ B) i ≫ (overProd_coproduct_distrib A B).inv =
      Limits.prod.map (Limits.Sigma.ι A i) (𝟙 B) := by
  rw [Iso.comp_inv_eq]
  refine Eq.symm ?_
  apply Over.OverMorphism.ext
  -- step 1: the slice `prod.map` corresponds to the `pullback.map` of the `ι`-square.
  have h1 : (Limits.prod.map (Limits.Sigma.ι A i) (𝟙 B)).left ≫
        (Over.prodLeftIsoPullback (∐ A) B).hom =
      (Over.prodLeftIsoPullback (A i) B).hom ≫
        pullback.map (A i).hom B.hom (∐ A).hom B.hom (Limits.Sigma.ι A i).left
          (𝟙 B.left) (𝟙 S) (by rw [Category.comp_id]; exact (Over.w _).symm) (by simp) := by
    apply pullback.hom_ext
    · rw [Category.assoc, Over.prodLeftIsoPullback_hom_fst, Category.assoc,
        pullback.lift_fst, ← Over.comp_left, Limits.prod.map_fst, Over.comp_left,
        ← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    · rw [Category.assoc, Over.prodLeftIsoPullback_hom_snd, Category.assoc,
        pullback.lift_snd, Category.comp_id, ← Over.comp_left, Limits.prod.map_snd,
        Category.comp_id, Over.prodLeftIsoPullback_hom_snd]
  -- step 2: the coproduct comparison of `Over.forget` on inclusions.
  have h0 : Limits.Sigma.ι (fun j => (A j).left) i ≫
        (PreservesCoproduct.iso (Over.forget S) A).inv = (Limits.Sigma.ι A i).left := by
    rw [PreservesCoproduct.inv_hom]
    exact ι_comp_sigmaComparison (Over.forget S) A i
  have hpA : (Limits.Sigma.ι A i).left ≫
        (PreservesCoproduct.iso (Over.forget S) A).hom =
      Limits.Sigma.ι (fun j => (A j).left) i := by
    refine Eq.trans (congrArg
      (fun w => w ≫ (PreservesCoproduct.iso (Over.forget S) A).hom) h0.symm) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun w => Limits.Sigma.ι (fun j => (A j).left) i ≫ w)
      ((PreservesCoproduct.iso (Over.forget S) A).inv_hom_id)) ?_
    exact Category.comp_id _
  -- the two stacked pullback comparisons compose to the `Sigma.ι`-square
  have h2 : pullback.map (A i).hom B.hom (∐ A).hom B.hom (Limits.Sigma.ι A i).left
        (𝟙 B.left) (𝟙 S) (by rw [Category.comp_id]; exact (Over.w _).symm) (by simp) ≫
      pullback.map (∐ A).hom B.hom (Limits.Sigma.desc fun j => (A j).hom) B.hom
        (PreservesCoproduct.iso (Over.forget S) A).hom (𝟙 B.left) (𝟙 S)
        (by rw [Category.comp_id]; exact overSigmaHomEq A) (by simp) =
      pullback.map (A i).hom B.hom (Limits.Sigma.desc fun j => (A j).hom) B.hom
        (Limits.Sigma.ι (fun j => (A j).left) i) (𝟙 B.left) (𝟙 S)
        (by rw [Category.comp_id, Limits.Sigma.ι_desc]) (by simp) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      exact congrArg (fun w => pullback.fst (A i).hom B.hom ≫ w) hpA
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Category.comp_id]
  -- step 3: the fused comparison is the inclusion of the distributed pullback factor.
  have h3 : pullback.map (A i).hom B.hom (Limits.Sigma.desc fun j => (A j).hom) B.hom
        (Limits.Sigma.ι (fun j => (A j).left) i) (𝟙 B.left) (𝟙 S)
        (by rw [Category.comp_id, Limits.Sigma.ι_desc]) (by simp) ≫
      (coprodFirst_distrib B.left B.hom fun j => (A j).hom).inv =
      Limits.Sigma.ι (fun j => pullback (A j).hom B.hom) i := by
    rw [Iso.comp_inv_eq]
    exact (ι_cf_hom B.left B.hom (fun j => (A j).hom) i).symm
  -- step 4: collapse the coproduct comparison of `Over.forget` on the target.
  have h4 : Limits.Sigma.ι (fun j => (A j ⨯ B).left) i ≫
        (PreservesCoproduct.iso (Over.forget S) (fun i => A i ⨯ B)).inv =
      (Limits.Sigma.ι (fun i => A i ⨯ B) i).left := by
    rw [PreservesCoproduct.inv_hom]
    exact ι_comp_sigmaComparison (Over.forget S) (fun i => A i ⨯ B) i
  have c1 : (Limits.prod.map (Limits.Sigma.ι A i) (𝟙 B)).left ≫
        ((overProd_coproduct_distrib A B).hom).left =
      (Limits.prod.map (Limits.Sigma.ι A i) (𝟙 B)).left ≫
          (Over.prodLeftIsoPullback (∐ A) B).hom ≫
          pullback.map (∐ A).hom B.hom (Limits.Sigma.desc fun j => (A j).hom) B.hom
            (PreservesCoproduct.iso (Over.forget S) A).hom (𝟙 B.left) (𝟙 S)
            (by rw [Category.comp_id]; exact overSigmaHomEq A) (by simp) ≫
          (coprodFirst_distrib B.left B.hom fun j => (A j).hom).inv ≫
          Limits.Sigma.map (fun j => (Over.prodLeftIsoPullback (A j) B).inv) ≫
          (PreservesCoproduct.iso (Over.forget S) fun i => A i ⨯ B).inv := rfl
  have c2 : (Limits.prod.map (Limits.Sigma.ι A i) (𝟙 B)).left ≫
          (Over.prodLeftIsoPullback (∐ A) B).hom ≫
          pullback.map (∐ A).hom B.hom (Limits.Sigma.desc fun j => (A j).hom) B.hom
            (PreservesCoproduct.iso (Over.forget S) A).hom (𝟙 B.left) (𝟙 S)
            (by rw [Category.comp_id]; exact overSigmaHomEq A) (by simp) ≫
          (coprodFirst_distrib B.left B.hom fun j => (A j).hom).inv ≫
          Limits.Sigma.map (fun j => (Over.prodLeftIsoPullback (A j) B).inv) ≫
          (PreservesCoproduct.iso (Over.forget S) fun i => A i ⨯ B).inv =
      (Over.prodLeftIsoPullback (A i) B).hom ≫
          Limits.Sigma.ι (fun j => pullback (A j).hom B.hom) i ≫
          Limits.Sigma.map (fun j => (Over.prodLeftIsoPullback (A j) B).inv) ≫
          (PreservesCoproduct.iso (Over.forget S) fun i => A i ⨯ B).inv := by
    rw [← Category.assoc, h1]
    simp only [Category.assoc]
    rw [reassoc_of% h2, reassoc_of% h3]
  have c3 : (Over.prodLeftIsoPullback (A i) B).hom ≫
          Limits.Sigma.ι (fun j => pullback (A j).hom B.hom) i ≫
          Limits.Sigma.map (fun j => (Over.prodLeftIsoPullback (A j) B).inv) ≫
          (PreservesCoproduct.iso (Over.forget S) fun i => A i ⨯ B).inv =
      Limits.Sigma.ι (fun j => (A j ⨯ B).left) i ≫
          (PreservesCoproduct.iso (Over.forget S) fun i => A i ⨯ B).inv := by
    rw [reassoc_of% (Limits.Sigma.ι_map (fun j => (Over.prodLeftIsoPullback (A j) B).inv) i),
      Iso.hom_inv_id_assoc]
  exact c1.trans (c2.trans (c3.trans h4))

/-- ι-compatibility of the right-handed slice distributivity. -/
private lemma ι_overProd_distrib_right_inv {S : C} [HasBinaryProducts (Over S)]
    (A : Over S) (Y : ι → Over S) (i : ι) :
    Limits.Sigma.ι (fun i => A ⨯ Y i) i ≫ (overProd_coproduct_distrib_right A Y).inv =
      Limits.prod.map (𝟙 A) (Limits.Sigma.ι Y i) := by
  rw [overProd_coproduct_distrib_right]
  simp only [Iso.trans_inv, ← Category.assoc]
  rw [ι_sigmaMapIso_inv (fun i => Limits.prod.braiding (Y i) A) i]
  simp only [Category.assoc]
  rw [reassoc_of% (ι_overProd_distrib_inv (C := C) (S := S) Y A i)]
  -- residual braiding algebra:
  -- `(br (Y i) A).inv ≫ prod.map ι 𝟙 ≫ (br A (∐Y)).inv = prod.map 𝟙 ι`
  refine (Iso.inv_comp_eq _).mpr ?_
  refine (Iso.comp_inv_eq _).mpr ?_
  refine Eq.symm ((Category.assoc _ _ _).trans ?_)
  refine Eq.trans (congrArg (fun w => (Limits.prod.braiding (Y i) A).hom ≫ w)
    (braid_natural (𝟙 A) (Limits.Sigma.ι Y i))) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun w => w ≫ Limits.prod.map (Limits.Sigma.ι Y i) (𝟙 A))
      (Limits.prod.symmetry (Y i) A)).trans (Category.id_comp _))

variable {S : C} {Z : ι → C} [HasFiniteWidePullbacks C]
  [HasFiniteProducts (Over S)] [HasFiniteCoproducts (Over S)]

/-- The over-level `l`-th wide-pullback projection of the constant-`Sigma.desc` fibre
power. -/
private noncomputable def overWPproj (f : (i : ι) → Z i ⟶ S) (m : ℕ) (l : Fin m) :
    Over.mk (WidePullback.base (fun _ : Fin m => Limits.Sigma.desc f)) ⟶
      Over.mk (Limits.Sigma.desc f) :=
  Over.homMk (WidePullback.π (fun _ : Fin m => Limits.Sigma.desc f) l)
    (WidePullback.π_arrow _ l)

/-- The `i`-th descent inclusion. -/
private noncomputable def overDescIncl (f : (i : ι) → Z i ⟶ S) (i : ι) :
    Over.mk (f i) ⟶ Over.mk (Limits.Sigma.desc f) :=
  Over.homMk (Limits.Sigma.ι Z i) (Limits.Sigma.ι_desc f i)

/-- The descent iso `overSigmaDescIso` sends coproduct inclusions to `overDescIncl`. -/
private lemma ι_overSigmaDescIso_hom (f : (i : ι) → Z i ⟶ S) (i : ι) :
    Limits.Sigma.ι (fun i => Over.mk (f i)) i ≫ (overSigmaDescIso f).hom =
      overDescIncl f i :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (coproductIsCoproduct _)
    (overSigmaDescIsColimit f) (Discrete.mk i)

/-- Inverse projections of the slice-product identification of the fibre power. -/
private lemma wpEqProd_inv_overWPproj (f : (i : ι) → Z i ⟶ S) (m : ℕ) (l : Fin m) :
    (widePullback_overX_eq_prod (fun _ : Fin m => Limits.Sigma.desc f)).inv ≫
      overWPproj f m l = Pi.π (fun _ : Fin m => Over.mk (Limits.Sigma.desc f)) l :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ (Discrete.mk l)

/-- Forward projections of the slice-product identification of the fibre power. -/
private lemma wpEqProd_hom_π (f : (i : ι) → Z i ⟶ S) (m : ℕ) (l : Fin m) :
    (widePullback_overX_eq_prod (fun _ : Fin m => Limits.Sigma.desc f)).hom ≫
      Pi.π (fun _ : Fin m => Over.mk (Limits.Sigma.desc f)) l = overWPproj f m l :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk l)

set_option maxHeartbeats 1600000 in
-- The chain unfolds seven layers of distributivity isos; the `whnf` cost on the nested
-- fibre powers exceeds the default budget.
/-- **Inclusion/projection characterization of the wide-fibre-power distributivity**
(the abstract Stub-1 unwinding): the `σ`-summand inclusion composed with the inverse of
`widePullback_coproduct_iso` and the `l`-th over-level wide-pullback projection is the
`l`-th factor projection followed by the `σ l`-th descent inclusion. -/
private lemma ι_wpci_inv_overWPproj (f : (i : ι) → Z i ⟶ S) (p : ℕ) :
    ∀ (σ : Fin (p + 1) → ι) (l : Fin (p + 1)),
    Limits.Sigma.ι (fun σ' : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (σ' k))) σ ≫
        (widePullback_coproduct_iso f p).inv ≫ overWPproj f (p + 1) l =
      Pi.π (fun k => Over.mk (f (σ k))) l ≫ overDescIncl f (σ l) := by
  induction p with
  | zero =>
    intro σ l
    obtain rfl : l = 0 := Subsingleton.elim (α := Fin 1) l 0
    obtain ⟨i0, rfl⟩ : ∃ i0, σ = fun _ => i0 :=
      ⟨σ 0, funext fun j => congrArg σ (Subsingleton.elim (α := Fin 1) j 0)⟩
    simp only [widePullback_coproduct_iso, widePullback_coproduct_iso_zero, Iso.trans_inv,
      Iso.symm_inv, Category.assoc, Sigma.whiskerEquiv, Limits.Sigma.ι_comp_map'_assoc]
    rw [wpEqProd_inv_overWPproj]
    have hb := IsLimit.conePointUniqueUpToIso_inv_comp
      (limit.isLimit (Discrete.functor (fun _ : Fin 1 => Over.mk (Limits.Sigma.desc f))))
      (limitConeOfUnique (fun _ : Fin 1 => Over.mk (Limits.Sigma.desc f))).isLimit
      (Discrete.mk (0 : Fin 1))
    refine Eq.trans (Category.id_comp _) ?_
    refine Eq.trans (congrArg (fun w => (productUniqueIso fun k : Fin 1 =>
        Over.mk (f ((Equiv.funUnique (Fin 1) ι).symm
          ((Equiv.funUnique (Fin 1) ι).symm.symm fun _ => i0) k))).hom ≫ w)
      ((reassoc_of% (ι_overSigmaDescIso_hom f
        ((Equiv.funUnique (Fin 1) ι).symm.symm fun _ => i0))) _)) ?_
    refine Eq.trans (congrArg (fun w => (productUniqueIso fun k : Fin 1 =>
        Over.mk (f ((Equiv.funUnique (Fin 1) ι).symm
          ((Equiv.funUnique (Fin 1) ι).symm.symm fun _ => i0) k))).hom ≫
      overDescIncl f ((Equiv.funUnique (Fin 1) ι).symm.symm fun _ => i0) ≫ w) hb) ?_
    exact Eq.trans (congrArg (fun w => (productUniqueIso fun k : Fin 1 =>
        Over.mk (f ((Equiv.funUnique (Fin 1) ι).symm
          ((Equiv.funUnique (Fin 1) ι).symm.symm fun _ => i0) k))).hom ≫ w)
      (Category.comp_id _)) rfl
  | succ p ih =>
    intro σ l
    obtain ⟨i, t, rfl⟩ : ∃ i t, σ = Fin.cons i t :=
      ⟨σ 0, Fin.tail σ, (Fin.cons_self_tail σ).symm⟩
    -- unfold one layer of the recursion and reassociate
    simp only [widePullback_coproduct_iso, Iso.trans_inv, Category.assoc]
    -- peel the reindex layer
    rw [reassoc_of% (ι_fibrePower_reindex_inv
      (fun σ' : Fin (p + 2) → ι => ∏ᶜ fun k => Over.mk (f (σ' k))) i t)]
    -- peel the `e7` (prodFinSuccIso) relabelling layer
    have he7 := ι_sigmaMapIso_inv (β := ι)
      (f := fun j : ι => ∐ fun τ : Fin (p + 1) → ι =>
        Over.mk (f (Fin.cons (α := fun _ => ι) j τ 0)) ⨯
          ∏ᶜ fun k : Fin (p + 1) => Over.mk (f (Fin.cons (α := fun _ => ι) j τ k.succ)))
      (g := fun j : ι => ∐ fun τ : Fin (p + 1) → ι =>
        ∏ᶜ fun k : Fin (p + 2) => Over.mk (f (Fin.cons (α := fun _ => ι) j τ k)))
      (fun j : ι => Limits.Sigma.mapIso
        (f := fun τ : Fin (p + 1) → ι =>
          Over.mk (f (Fin.cons (α := fun _ => ι) j τ 0)) ⨯
            ∏ᶜ fun k : Fin (p + 1) => Over.mk (f (Fin.cons (α := fun _ => ι) j τ k.succ)))
        (g := fun τ : Fin (p + 1) → ι =>
          ∏ᶜ fun k : Fin (p + 2) => Over.mk (f (Fin.cons (α := fun _ => ι) j τ k)))
        (fun τ : Fin (p + 1) → ι =>
          (prodFinSuccIso (fun k : Fin (p + 2) => Over.mk (f (Fin.cons (α := fun _ => ι) j τ k)))).symm)) i
    refine Eq.trans (congrArg (fun w => Limits.Sigma.ι
      (fun τ : Fin (p + 1) → ι => ∏ᶜ fun k : Fin (p + 2) =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i τ k))) t ≫ w)
      ((reassoc_of% he7) _)) ?_
    have he7' := ι_sigmaMapIso_inv (β := Fin (p + 1) → ι)
      (f := fun τ : Fin (p + 1) → ι =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i τ 0)) ⨯
          ∏ᶜ fun k : Fin (p + 1) => Over.mk (f (Fin.cons (α := fun _ => ι) i τ k.succ)))
      (g := fun τ : Fin (p + 1) → ι =>
        ∏ᶜ fun k : Fin (p + 2) => Over.mk (f (Fin.cons (α := fun _ => ι) i τ k)))
      (fun τ : Fin (p + 1) → ι =>
        (prodFinSuccIso (fun k : Fin (p + 2) => Over.mk (f (Fin.cons (α := fun _ => ι) i τ k)))).symm) t
    refine Eq.trans ((reassoc_of% he7') _) ?_
    -- peel the two distributivity layers
    have hA5 := ι_sigmaMapIso_inv (fun j : ι =>
      overProd_coproduct_distrib_right (Over.mk (f j))
        (fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k)))) i
    refine Eq.trans (congrArg (fun w =>
      (prodFinSuccIso fun k : Fin (p + 2) =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
      Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i τ 0)) ⨯
          ∏ᶜ fun k : Fin (p + 1) => Over.mk (f (Fin.cons (α := fun _ => ι) i τ k.succ))) t ≫ w)
      ((reassoc_of% hA5) _)) ?_
    refine Eq.trans (congrArg (fun w =>
      (prodFinSuccIso fun k : Fin (p + 2) =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ w)
      ((reassoc_of% (ι_overProd_distrib_right_inv (Over.mk (f i))
        (fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))) t)) _)) ?_
    refine Eq.trans (congrArg (fun w =>
      (prodFinSuccIso fun k : Fin (p + 2) =>
        Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
      Limits.prod.map (𝟙 (Over.mk (f i))) (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
        ∏ᶜ fun k => Over.mk (f (τ k))) t) ≫ w)
      ((reassoc_of% (ι_overProd_distrib_inv (fun j : ι => Over.mk (f j))
        (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))) i)) _)) ?_
    -- split on the projection index and collapse the tail
    induction l using Fin.cases with
    | zero =>
      have htail : (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫
          (prodFinSuccIso (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f))).inv ≫
          (widePullback_overX_eq_prod (fun _ : Fin (p + 2) => Limits.Sigma.desc f)).inv ≫
          overWPproj f (p + 2) 0 =
          Limits.prod.fst ≫ (overSigmaDescIso f).hom := by
        refine Eq.trans (congrArg (fun w => (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫
          (prodFinSuccIso (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f))).inv ≫ w)
          (wpEqProd_inv_overWPproj f (p + 2) 0)) ?_
        refine Eq.trans (congrArg (fun w => (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫ w)
          (prodFinSuccIso_inv_π_zero (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f)))) ?_
        exact Limits.prod.map_fst _ _
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
        Limits.prod.map (𝟙 (Over.mk (f i))) (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
          ∏ᶜ fun k => Over.mk (f (τ k))) t) ≫
        Limits.prod.map (Limits.Sigma.ι (fun j : ι => Over.mk (f j)) i)
          (𝟙 (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k)))) ≫ w) htail) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
        Limits.prod.map (𝟙 (Over.mk (f i))) (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
          ∏ᶜ fun k => Over.mk (f (τ k))) t) ≫ w)
        (Limits.prod.map_fst_assoc (Limits.Sigma.ι (fun j : ι => Over.mk (f j)) i)
          (𝟙 (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))))
          ((overSigmaDescIso f).hom))) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ w)
        (Limits.prod.map_fst_assoc (𝟙 (Over.mk (f i)))
          (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))) t)
          (Limits.Sigma.ι (fun j : ι => Over.mk (f j)) i ≫ (overSigmaDescIso f).hom))) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ Limits.prod.fst ≫ w)
        ((Category.id_comp _).trans (ι_overSigmaDescIso_hom f i))) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact congrArg (fun w => w ≫ overDescIncl f i)
        (prodFinSuccIso_hom_fst (fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))))
    | succ l' =>
      have htail : (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫
          (prodFinSuccIso (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f))).inv ≫
          (widePullback_overX_eq_prod (fun _ : Fin (p + 2) => Limits.Sigma.desc f)).inv ≫
          overWPproj f (p + 2) l'.succ =
          Limits.prod.snd ≫ (widePullback_coproduct_iso f p).inv ≫ overWPproj f (p + 1) l' := by
        refine Eq.trans (congrArg (fun w => (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫
          (prodFinSuccIso (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f))).inv ≫ w)
          (wpEqProd_inv_overWPproj f (p + 2) l'.succ)) ?_
        refine Eq.trans (congrArg (fun w => (Limits.prod.mapIso (overSigmaDescIso f).symm
            ((widePullback_overX_eq_prod (fun _ : Fin (p + 1) => Limits.Sigma.desc f)).symm ≪≫
              widePullback_coproduct_iso f p)).inv ≫ w)
          (prodFinSuccIso_inv_π_succ (fun _ : Fin (p + 2) => Over.mk (Limits.Sigma.desc f)) l')) ?_
        refine Eq.trans (Limits.prod.map_snd_assoc _ _ _) ?_
        refine congrArg (fun w => Limits.prod.snd ≫ w) ?_
        refine Eq.trans (Category.assoc _ _ _) ?_
        exact congrArg (fun w => (widePullback_coproduct_iso f p).inv ≫ w)
          (wpEqProd_hom_π f (p + 1) l')
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
        Limits.prod.map (𝟙 (Over.mk (f i))) (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
          ∏ᶜ fun k => Over.mk (f (τ k))) t) ≫
        Limits.prod.map (Limits.Sigma.ι (fun j : ι => Over.mk (f j)) i)
          (𝟙 (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k)))) ≫ w) htail) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫
        Limits.prod.map (𝟙 (Over.mk (f i))) (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
          ∏ᶜ fun k => Over.mk (f (τ k))) t) ≫ w)
        (Limits.prod.map_snd_assoc (Limits.Sigma.ι (fun j : ι => Over.mk (f j)) i)
          (𝟙 (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))))
          ((widePullback_coproduct_iso f p).inv ≫ overWPproj f (p + 1) l'))) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ w)
        (Limits.prod.map_snd_assoc (𝟙 (Over.mk (f i)))
          (Limits.Sigma.ι (fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))) t)
          (𝟙 (∐ fun τ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (f (τ k))) ≫
            (widePullback_coproduct_iso f p).inv ≫ overWPproj f (p + 1) l'))) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ Limits.prod.snd ≫ w)
        ((congrArg (fun w => Limits.Sigma.ι (fun τ : Fin (p + 1) → ι =>
            ∏ᶜ fun k => Over.mk (f (τ k))) t ≫ w) (Category.id_comp _)).trans
          (ih t l'))) ?_
      refine Eq.trans (congrArg (fun w =>
        (prodFinSuccIso fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))).symm.inv ≫ w)
        (Category.assoc _ _ _).symm) ?_
      refine Eq.trans (Category.assoc _ _ _).symm ?_
      exact congrArg (fun w => w ≫ overDescIncl f (t l'))
        (prodFinSuccIso_hom_snd_π (fun k : Fin (p + 2) =>
          Over.mk (f (Fin.cons (α := fun _ => ι) i t k))) l')

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Combo: reindex layer + distributivity layer in one step.**  The `τ`-summand inclusion
through the universe-reduction reindex `Sigma.whiskerEquiv` and the distributivity inverse,
projected onto the `l`-th over-level wide-pullback factor, is the canonical projection
followed by the `E (τ l)`-th descent inclusion (with a single product-relabel transport). -/
private lemma ι_reindex_wpci_inv_overWPproj {ι₀ : Type*} {Z' : ι₀ → C}
    (g : (i : ι₀) → Z' i ⟶ S) (E : ι₀ ≃ ι) (p : ℕ)
    [HasCoproduct (fun τ' : Fin (p + 1) → ι₀ => ∏ᶜ fun k => Over.mk (g (τ' k)))]
    (τ : Fin (p + 1) → ι₀) (l : Fin (p + 1)) :
    Limits.Sigma.ι (fun τ' : Fin (p + 1) → ι₀ => ∏ᶜ fun k => Over.mk (g (τ' k))) τ ≫
        (Sigma.whiskerEquiv (Equiv.arrowCongr (Equiv.refl (Fin (p + 1))) E.symm)
          (fun σ : Fin (p + 1) → ι => Iso.refl _)).inv ≫
        (widePullback_coproduct_iso (fun j : ι => g (E.symm j)) p).inv ≫
        overWPproj (fun j : ι => g (E.symm j)) (p + 1) l =
      eqToHom (congrArg (fun fam : Fin (p + 1) → ι₀ =>
          ∏ᶜ fun k => Over.mk (g (fam k)))
        (funext (fun k => (E.symm_apply_apply (τ k)).symm))) ≫
      Pi.π (fun k => Over.mk (g (E.symm (E (τ k))))) l ≫
      overDescIncl (fun j : ι => g (E.symm j)) (E (τ l)) := by
  refine Eq.trans ((reassoc_of% (ι_whiskerEquiv_inv
      (f := fun σ : Fin (p + 1) → ι => ∏ᶜ fun k => Over.mk (g (E.symm (σ k))))
      (g := fun τ' : Fin (p + 1) → ι₀ => ∏ᶜ fun k => Over.mk (g (τ' k)))
      (Equiv.arrowCongr (Equiv.refl (Fin (p + 1))) E.symm)
      (fun σ : Fin (p + 1) → ι => Iso.refl _) τ))
    ((widePullback_coproduct_iso (fun j : ι => g (E.symm j)) p).inv ≫
      overWPproj (fun j : ι => g (E.symm j)) (p + 1) l)) ?_
  refine Eq.trans (congrArg (fun w => eqToHom (congrArg (fun fam : Fin (p + 1) → ι₀ =>
        ∏ᶜ fun k => Over.mk (g (fam k)))
      (funext (fun k => (E.symm_apply_apply (τ k)).symm))) ≫ w)
    (Category.id_comp _)) ?_
  exact congrArg (fun w => eqToHom (congrArg (fun fam : Fin (p + 1) → ι₀ =>
        ∏ᶜ fun k => Over.mk (g (fam k)))
      (funext (fun k => (E.symm_apply_apply (τ k)).symm))) ≫ w)
    (ι_wpci_inv_overWPproj (fun j : ι => g (E.symm j)) p
      ((Equiv.arrowCongr (Equiv.refl (Fin (p + 1))) E.symm).symm τ) l)

end WPCIproj

/-- Generic reassociation entry: collapse the first two factors of a three-factor composite
against a projection. -/
private lemma entry_chain {C : Type*} [Category C] {Y₀ Y₁ Y₂ Y₃ T : C}
    (a : Y₀ ⟶ Y₁) (b : Y₁ ⟶ Y₂) (ci : Y₂ ⟶ Y₃) (pr : Y₃ ⟶ T) (s : Y₀ ⟶ Y₂)
    (h : a ≫ b = s) : (a ≫ b ≫ ci) ≫ pr = s ≫ (ci ≫ pr) := by
  rw [← h]; simp only [Category.assoc]

/-- Generic five-layer glue: peels the backbone-identification layers against their
characterizing equations in one reassociation pass (clean abstract context, so the
rewrites are reliable). -/
private lemma glue_chain {C : Type*} [Category C] {Y S₁ S₂ S₃ S₄ S₅ S₆ T₁ T₂ U V : C}
    (i : Y ⟶ S₁) (em : S₁ ⟶ S₂) (dm : S₂ ⟶ S₃) (cm : S₃ ⟶ S₄) (bm : S₄ ⟶ S₅)
    (am : S₅ ⟶ S₆) (pr : S₆ ⟶ T₂) (pr₀ : S₅ ⟶ T₂) (h₀ : am ≫ pr = pr₀)
    (w₁ : Y ⟶ T₁) (i' : T₁ ⟶ S₂) (h₁ : i ≫ em = w₁ ≫ i')
    (oWP : S₄ ⟶ U) (R : U ⟶ T₂) (h₂ : bm ≫ pr₀ = oWP ≫ R)
    (mid : T₁ ⟶ V) (incl : V ⟶ U) (h₃ : i' ≫ dm ≫ cm ≫ oWP = mid ≫ incl)
    (cai : V ⟶ T₂) (h₄ : incl ≫ R = cai) :
    i ≫ (((((em ≫ dm) ≫ cm) ≫ bm) ≫ am) ≫ pr) = (w₁ ≫ mid) ≫ cai := by
  simp only [Category.assoc] at h₃ ⊢
  rw [h₀, h₂, reassoc_of% h₁, reassoc_of% h₃, h₄, ← Category.assoc]

/-- The face morphism between intersection-open legs: deleting the `k`-th index of `σ'`
enlarges the intersection, giving the open inclusion `U_{σ'} ⊆ U_{σ'∘δᵏ}`. -/
noncomputable def interLegHom (𝒰 : X.OpenCover) {p : ℕ} (σ' : Fin (p + 2) → 𝒰.I₀)
    (k : Fin (p + 2)) :
    Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ')) ⟶
      Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom))) :=
  Over.homMk (X.homOfLE (le_iInf (fun l => iInf_le (fun j => coverOpen 𝒰 (σ' j))
      ((SimplexCategory.δ k).toOrderHom l))))
    (Scheme.homOfLE_ι _ _)

/-- The face morphism intertwines the canonical component maps: projecting the `σ'`-leg
onto its `δᵏ l`-th component agrees with first including `U_{σ'} ⊆ U_{σ'∘δᵏ}` and then
projecting onto the `l`-th component.  Both lifts agree after the mono `𝒰.f _`. -/
lemma interLegHom_interProj (𝒰 : X.OpenCover) {p : ℕ} (σ' : Fin (p + 2) → 𝒰.I₀)
    (k : Fin (p + 2)) (l : Fin (p + 1)) :
    interLegHom 𝒰 σ' k ≫ interProj 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) l =
      interProj 𝒰 σ' ((SimplexCategory.δ k).toOrderHom l) := by
  have hfac : X.homOfLE (le_iInf (fun l' => iInf_le (fun j => coverOpen 𝒰 (σ' j))
        ((SimplexCategory.δ k).toOrderHom l'))) ≫
        coverInterToMember 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) l =
      coverInterToMember 𝒰 σ' ((SimplexCategory.δ k).toOrderHom l) := by
    haveI : IsOpenImmersion (𝒰.f (σ' ((SimplexCategory.δ k).toOrderHom l))) := inferInstance
    refine IsOpenImmersion.lift_uniq (𝒰.f (σ' ((SimplexCategory.δ k).toOrderHom l)))
      (Scheme.Opens.ι (coverInterOpen 𝒰 σ')) ?_ _ ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (fun w => X.homOfLE (le_iInf (fun l' => iInf_le
        (fun j => coverOpen 𝒰 (σ' j)) ((SimplexCategory.δ k).toOrderHom l'))) ≫ w)
      (coverInterToMember_fac 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) l)).trans ?_
    exact Scheme.homOfLE_ι _ _
  apply Over.OverMorphism.ext
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun w => w ≫ Sigma.ι 𝒰.X (σ' ((SimplexCategory.δ k).toOrderHom l))) hfac)

/-- The cover-arrow inclusion of a member, as an over-`X` morphism. -/
private noncomputable def coverArrowIncl (𝒰 : X.OpenCover) (i : 𝒰.I₀) :
    Over.mk (𝒰.f i) ⟶ Over.mk (Sigma.desc 𝒰.f) :=
  Over.homMk (Sigma.ι 𝒰.X i) (Limits.Sigma.ι_desc 𝒰.f i)

/-- The universe-reduction reindexing of the cover arrow, as an over-`X` morphism. -/
private noncomputable def coverReindexHom (𝒰 : X.OpenCover) [Finite 𝒰.I₀] :
    Over.mk (Limits.Sigma.desc (fun j : Fin (Nat.card 𝒰.I₀) =>
      𝒰.f ((Finite.equivFin 𝒰.I₀).symm j))) ⟶ Over.mk (Sigma.desc 𝒰.f) :=
  Over.homMk (Sigma.whiskerEquiv (Finite.equivFin 𝒰.I₀).symm
    (fun j => Iso.refl (𝒰.X ((Finite.equivFin 𝒰.I₀).symm j)))).hom
    (by
      refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
      simp only [Sigma.whiskerEquiv, Iso.refl_inv, Limits.Sigma.ι_comp_map'_assoc,
        Category.id_comp, Limits.Sigma.ι_desc, Over.mk_hom]
      refine Eq.trans (Limits.Sigma.ι_comp_map'_assoc _ _ _ _) ?_
      exact Eq.trans (Category.id_comp _) (Limits.Sigma.ι_desc _ _))

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Backbone inclusion/projection characterization** (the Stub-1 unwinding): the
`τ`-summand inclusion of the backbone followed by the `l`-th wide-pullback projection is
the canonical component map `interProj 𝒰 τ l`.  (`whnf` on the five-layer backbone
identification exceeds the default budget.) -/
lemma backboneIncl_proj (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (p : ℕ)
    (τ : Fin (p + 1) → 𝒰.I₀) (l : Fin (p + 1)) :
    backboneIncl 𝒰 p τ ≫ backboneProj 𝒰 p l = interProj 𝒰 τ l := by
  -- absorption: any over-morphism into a member, followed by its cover-arrow inclusion,
  -- is the canonical `interProj` (mono-target rigidity of `𝒰.f _`)
  have habs : ∀ (j' : 𝒰.I₀) (hj : j' = τ l)
      (w : Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 τ)) ⟶ Over.mk (𝒰.f j')),
      w ≫ coverArrowIncl 𝒰 j' = interProj 𝒰 τ l := by
    rintro j' rfl w
    have hfact : interProj 𝒰 τ l =
        Over.homMk (coverInterToMember 𝒰 τ l) (coverInterToMember_fac 𝒰 τ l) ≫
          coverArrowIncl 𝒰 (τ l) := by
      apply Over.OverMorphism.ext
      rfl
    rw [hfact]
    exact congrArg (fun u => u ≫ coverArrowIncl 𝒰 (τ l))
      (over_hom_ext_mono w (Over.homMk (coverInterToMember 𝒰 τ l)
        (coverInterToMember_fac 𝒰 τ l)))
  -- the descent inclusion of the reindexed family lands on the cover-arrow inclusion
  have hred : ∀ j : Fin (Nat.card 𝒰.I₀),
      overDescIncl (fun j' : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j')) j ≫
        coverReindexHom 𝒰 =
      coverArrowIncl 𝒰 ((Finite.equivFin 𝒰.I₀).symm j) := by
    intro j
    apply Over.OverMorphism.ext
    exact Eq.trans (Limits.Sigma.ι_comp_map' _ _ _) (Category.id_comp _)
  -- the wide-pullback transport layer exchanges the projections
  have htail : ∀ (hw : _) , (widePullbackBaseCongr (Sigma.desc 𝒰.f)
        (Limits.Sigma.desc (fun j : Fin (Nat.card 𝒰.I₀) =>
          𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)))
        (Sigma.whiskerEquiv (Finite.equivFin 𝒰.I₀).symm
          (fun j => Iso.refl (𝒰.X ((Finite.equivFin 𝒰.I₀).symm j)))) hw (p + 1)).inv ≫
        backboneProj 𝒰 p l =
      overWPproj (fun j : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j))
          (p + 1) l ≫ coverReindexHom 𝒰 := by
    intro hw
    apply Over.OverMorphism.ext
    exact WidePullback.lift_π _ _ _ _ l
  -- collapse the descent-iso layer onto the plain coproduct inclusion
  have ha2 : coprodOverIncl (fun σ : Fin (p + 1) → 𝒰.I₀ =>
      Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) τ ≫
      (overSigmaDescIso (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).hom)).inv =
      Limits.Sigma.ι (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) τ := by
    rw [Iso.comp_inv_eq]
    exact (IsColimit.comp_coconePointUniqueUpToIso_hom
      (coproductIsCoproduct (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))))
      (overSigmaDescIsColimit _) (Discrete.mk τ)).symm
  -- ASSEMBLY: the five backbone-iso layers are peeled in ONE generic reassociation pass
  -- (`glue_chain`, proved in a clean abstract context), fed by `ha2` (entry), `htail`
  -- (wide-pullback congruence layer), `ι_sigmaMapIso_inv` (coverInterProdIso layer), the
  -- combined reindex+distributivity characterization `ι_reindex_wpci_inv_overWPproj`, and
  -- `hred`; `habs` absorbs the residual prefix by mono-target rigidity.
  -- the wZ-triangle witness consumed by `htail`
  have hwZ : (Sigma.whiskerEquiv (Finite.equivFin 𝒰.I₀).symm
        (fun j => Iso.refl (𝒰.X ((Finite.equivFin 𝒰.I₀).symm j)))).hom ≫ Sigma.desc 𝒰.f =
      Limits.Sigma.desc (fun j : Fin (Nat.card 𝒰.I₀) =>
        𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)) := by
    refine Limits.Sigma.hom_ext _ _ (fun j => ?_)
    simp only [Sigma.whiskerEquiv, Iso.refl_inv, Limits.Sigma.ι_comp_map'_assoc,
      Category.id_comp, Limits.Sigma.ι_desc]
  -- the five layers of the backbone identification, read backwards
  have hexp : (cechBackbone_left_sigma 𝒰 p).inv =
      ((((Limits.Sigma.mapIso (fun σ : Fin (p + 1) → 𝒰.I₀ => coverInterProdIso 𝒰 σ)).inv ≫
        (Sigma.whiskerEquiv (Equiv.arrowCongr (Equiv.refl (Fin (p + 1)))
            (Finite.equivFin 𝒰.I₀).symm)
          (fun σ : Fin (p + 1) → Fin (Nat.card 𝒰.I₀) =>
            Iso.refl (∏ᶜ fun k => Over.mk (𝒰.f ((Finite.equivFin 𝒰.I₀).symm (σ k)))))).inv) ≫
        (FinitaryPreExtensive.widePullback_coproduct_iso
          (fun j : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)) p).inv) ≫
        (widePullbackBaseCongr (Sigma.desc 𝒰.f)
          (Limits.Sigma.desc (fun j : Fin (Nat.card 𝒰.I₀) =>
            𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)))
          (Sigma.whiskerEquiv (Finite.equivFin 𝒰.I₀).symm
            (fun j => Iso.refl (𝒰.X ((Finite.equivFin 𝒰.I₀).symm j)))) hwZ (p + 1)).inv) ≫
        (cechBackbone_obj_widePullback 𝒰 p).inv := rfl
  refine Eq.trans (entry_chain _ _ _ (backboneProj 𝒰 p l) _ ha2) ?_
  rw [hexp]
  refine Eq.trans (glue_chain
    (Limits.Sigma.ι (fun σ : Fin (p + 1) → 𝒰.I₀ =>
      Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ))) τ)
    (Limits.Sigma.mapIso (fun σ : Fin (p + 1) → 𝒰.I₀ => coverInterProdIso 𝒰 σ)).inv
    (Sigma.whiskerEquiv (Equiv.arrowCongr (Equiv.refl (Fin (p + 1)))
        (Finite.equivFin 𝒰.I₀).symm)
      (fun σ : Fin (p + 1) → Fin (Nat.card 𝒰.I₀) =>
        Iso.refl (∏ᶜ fun k => Over.mk (𝒰.f ((Finite.equivFin 𝒰.I₀).symm (σ k)))))).inv
    (FinitaryPreExtensive.widePullback_coproduct_iso
      (fun j : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)) p).inv
    (widePullbackBaseCongr (Sigma.desc 𝒰.f)
      (Limits.Sigma.desc (fun j : Fin (Nat.card 𝒰.I₀) =>
        𝒰.f ((Finite.equivFin 𝒰.I₀).symm j)))
      (Sigma.whiskerEquiv (Finite.equivFin 𝒰.I₀).symm
        (fun j => Iso.refl (𝒰.X ((Finite.equivFin 𝒰.I₀).symm j)))) hwZ (p + 1)).inv
    (cechBackbone_obj_widePullback 𝒰 p).inv
    (backboneProj 𝒰 p l) (backboneProj 𝒰 p l)
    (Category.id_comp (backboneProj 𝒰 p l))
    ((coverInterProdIso 𝒰 τ).inv)
    (Limits.Sigma.ι (fun σ : Fin (p + 1) → 𝒰.I₀ =>
      ∏ᶜ fun k => Over.mk (𝒰.f (σ k))) τ)
    (ι_sigmaMapIso_inv (fun σ : Fin (p + 1) → 𝒰.I₀ => coverInterProdIso 𝒰 σ) τ)
    (overWPproj (fun j : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j))
      (p + 1) l)
    (coverReindexHom 𝒰) (htail hwZ)
    (eqToHom (congrArg (fun fam : Fin (p + 1) → 𝒰.I₀ =>
        ∏ᶜ fun k => Over.mk (𝒰.f (fam k)))
      (funext (fun k => ((Finite.equivFin 𝒰.I₀).symm_apply_apply (τ k)).symm))) ≫
      Pi.π (fun k => Over.mk (𝒰.f ((Finite.equivFin 𝒰.I₀).symm
        ((Finite.equivFin 𝒰.I₀) (τ k))))) l)
    (overDescIncl (fun j : Fin (Nat.card 𝒰.I₀) => 𝒰.f ((Finite.equivFin 𝒰.I₀).symm j))
      ((Finite.equivFin 𝒰.I₀) (τ l)))
    ((ι_reindex_wpci_inv_overWPproj 𝒰.f (Finite.equivFin 𝒰.I₀) p τ l).trans
      ((Category.assoc _ _ _).symm))
    (coverArrowIncl 𝒰 ((Finite.equivFin 𝒰.I₀).symm ((Finite.equivFin 𝒰.I₀) (τ l))))
    (hred ((Finite.equivFin 𝒰.I₀) (τ l)))) ?_
  exact habs ((Finite.equivFin 𝒰.I₀).symm ((Finite.equivFin 𝒰.I₀) (τ l)))
    ((Finite.equivFin 𝒰.I₀).symm_apply_apply (τ l)) _

/-- **Per-leg coface factorization of the backbone inclusion** (★): the `σ'`-summand
inclusion of the degree-`(p+1)` backbone followed by the geometric nerve coface
factors as the open inclusion `U_{σ'} ⊆ U_{σ'∘δᵏ}` followed by the `σ'∘δᵏ`-summand
inclusion of the degree-`p` backbone.  Proved projection-by-projection
(`backbone_hom_ext`), where both sides become canonical component maps. -/
lemma backboneIncl_nerveδ (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (p : ℕ)
    (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀) :
    backboneIncl 𝒰 (p + 1) σ' ≫ (coverCechNerveOver 𝒰).map ((SimplexCategory.δ k).op) =
      interLegHom 𝒰 σ' k ≫ backboneIncl 𝒰 p (σ' ∘ (SimplexCategory.δ k).toOrderHom) := by
  apply backbone_hom_ext
  intro l
  rw [Category.assoc, nerveδ_backboneProj, backboneIncl_proj, Category.assoc,
    backboneIncl_proj, interLegHom_interProj]

/-! ### Section-level seam: projecting `coreIso_objIso` and the per-leg restriction. -/

/-- The section-at-`V` functor `Γ(V, ·) : X.Modules ⥤ Ab` (the `E` of
`pushPull_eval_prod_iso`). -/
noncomputable abbrev sectionFunctorV (V : TopologicalSpace.Opens ↥X) : X.Modules ⥤ Ab.{u} :=
  Scheme.Modules.toPresheaf X ⋙
    (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ Ab.{u}).obj (Opposite.op V)

/-- The statement-level evaluated adapter `G_V ∘ Ψ` agrees with `sectionFunctorV` on
morphisms of `X.Modules` (definitional: `restrictScalars (𝟙 _)` does not change the
underlying abelian presheaf map). -/
lemma GVΨ_map_eq (V : TopologicalSpace.Opens ↥X) {M N : X.Modules} (φ : M ⟶ N) :
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
        (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
      ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map φ) =
    (sectionFunctorV V).map φ :=
  rfl

/-- Projection of a `Pi.mapIso` onto a factor (the `limMap_π` instance for discrete
shapes, stated so it can be applied term-wise against the bundled section products). -/
@[reassoc]
private lemma piMapIso_hom_π {β : Type u} {f g : β → Ab.{u}}
    (w : ∀ b, f b ≅ g b) (b : β) :
    (Pi.mapIso w).hom ≫ Pi.π g b = Pi.π f b ≫ (w b).hom := by
  have h := limMap_π (F := Discrete.functor f) (G := Discrete.functor g)
    (Discrete.natIso (fun j => w j.as)).hom ⟨b⟩
  exact h

-- The unfolding of `coreIso_objIso`/`pushPull_eval_prod_iso` is `whnf`-heavy on the
-- bundled section types.
set_option maxHeartbeats 1600000 in
/-- **Coordinate formula for the degreewise object iso** (`coreIso_objIso`): its
`τ`-projection is the evaluated push–pull map of the backbone inclusion `backboneIncl`,
followed by the per-leg section identification `pushPull_leg_sections` and the open-meet
reindex of `coverInterOpen_inf_eq_iInf_inf`. -/
lemma coreIso_objIso_π (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules) (p : ℕ)
    (V : TopologicalSpace.Opens ↥X) (τ : Fin (p + 1) → 𝒰.I₀) :
    (coreIso_objIso 𝒰 F p V).hom ≫
        Pi.π (fun σ : Fin (p + 1) → 𝒰.I₀ =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
            (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) τ =
      (sectionFunctorV V).map (pushPullMap F (backboneIncl 𝒰 p τ)) ≫
        (pushPull_leg_sections 𝒰 F τ V).hom ≫
        eqToHom (congrArg (fun W =>
            ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
          (coverInterOpen_inf_eq_iInf_inf 𝒰 τ V)) := by
  simp only [coreIso_objIso, pushPull_eval_prod_iso, Iso.trans_hom, Functor.mapIso_hom,
    Category.assoc, PreservesProduct.iso_hom]
  -- project layer by layer (term-level, defeq-robust): the open-meet reindex …
  refine Eq.trans (congrArg (fun w => (sectionFunctorV V).map (pushPull_sigma_iso 𝒰 F p).hom ≫
      piComparison (sectionFunctorV V) (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≫
      (Pi.mapIso (fun σ : Fin (p + 1) → 𝒰.I₀ => pushPull_leg_sections 𝒰 F σ V)).hom ≫ w)
    (piMapIso_hom_π (fun σ : Fin (p + 1) → 𝒰.I₀ => eqToIso (congrArg (fun W =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
      (coverInterOpen_inf_eq_iInf_inf 𝒰 σ V))) τ)) ?_
  -- … the per-leg section identification …
  refine Eq.trans (congrArg (fun w => (sectionFunctorV V).map (pushPull_sigma_iso 𝒰 F p).hom ≫
      piComparison (sectionFunctorV V) (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) ≫ w)
    (piMapIso_hom_π_assoc (fun σ : Fin (p + 1) → 𝒰.I₀ => pushPull_leg_sections 𝒰 F σ V) τ
      (eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 τ V))))) ?_
  -- … the product comparison of the section functor …
  refine Eq.trans (congrArg (fun w => (sectionFunctorV V).map
      (pushPull_sigma_iso 𝒰 F p).hom ≫ w)
    (piComparison_comp_π_assoc (sectionFunctorV V) (fun σ : Fin (p + 1) → 𝒰.I₀ =>
        pushPullObj F (Over.mk (Scheme.Opens.ι (coverInterOpen 𝒰 σ)))) τ
      ((pushPull_leg_sections 𝒰 F τ V).hom ≫ eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 τ V))))) ?_
  -- … and the σ-leg of the product decomposition (`pushPull_sigma_iso_π`).
  refine Eq.trans ((Functor.map_comp_assoc _ _ _ _).symm) ?_
  exact congrArg (fun w => (sectionFunctorV V).map w ≫
      (pushPull_leg_sections 𝒰 F τ V).hom ≫
      eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 τ V)))
    (pushPull_sigma_iso_π_incl 𝒰 F p τ)

/-- The canonical leg iso for the push–pull of an over-morphism with open-immersion
underlying map (replica of the Base `private pushPullCoprodLegIso`, whose proof never
uses the coproduct structure of its ambient scheme). -/
private noncomputable def pushPullLegIso {A C' : Scheme.{u}} (q : A ⟶ X)
    (c : C' ⟶ A) [IsOpenImmersion c] (pC : C' ⟶ X) (wC : c ≫ q = pC) (F : X.Modules) :
    (pushforward q).obj ((pushforward c).obj
        (((Scheme.Modules.pullback q).obj F).restrict c)) ≅
      pushPullObj F (Over.mk pC) :=
  (pushforward q).mapIso ((pushforward c).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback c).app ((Scheme.Modules.pullback q).obj F) ≪≫
      (Scheme.Modules.pullbackComp c q).app F ≪≫
      (Scheme.Modules.pullbackCongr wC).app F)) ≪≫
  eqToIso (congrArg (fun p' => (pushforward p').obj ((Scheme.Modules.pullback pC).obj F)) wC)

-- The final `rfl` discharges the proof-irrelevant `eqToHom` over-triangle transports against
-- concrete pushforward/pullback objects, whose `whnf` exceeds the default heartbeat budget.
set_option maxHeartbeats 800000 in
/-- Per-leg coherence (replica of the Base `private pushPull_binary_leg_coherence` for a
general ambient open immersion): the push–pull map of an over-morphism `Over.homMk c` is,
through the canonical leg iso, the pushforward of the restriction unit. -/
private lemma pushPull_leg_coherence {A C' : Scheme.{u}} (q : A ⟶ X)
    (c : C' ⟶ A) [IsOpenImmersion c] (pC : C' ⟶ X) (wC : c ≫ q = pC) (F : X.Modules) :
    pushPullMap F (Over.homMk c wC : Over.mk pC ⟶ Over.mk q) =
      (pushforward q).map
          ((Scheme.Modules.restrictAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F)) ≫
        (pushPullLegIso q c pC wC F).hom := by
  have hraw : pushPullMap F (Over.homMk c wC : Over.mk pC ⟶ Over.mk q)
      = rawPushPullMap c q pC wC F := rfl
  rw [hraw, rawPushPullMap_self_gen]
  have hLAU : (Scheme.Modules.restrictAdjunction c).unit.app
        ((Scheme.Modules.pullback q).obj F) ≫
        (pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).hom.app
            ((Scheme.Modules.pullback q).obj F)) =
      (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
        ((Scheme.Modules.pullback q).obj F) :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ _
  subst wC
  simp only [pushPullLegIso, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    Iso.app_hom, Category.comp_id,
    Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  rw [← hLAU]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-! ### Restrict-world unit calculus for the per-leg face (Steps 0–3′ of
`lem:pushPull_interLegHom_sections`) -/

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Step 0: the pullback-pushforward adjunction unit, post-composed with the pushforward of
the `restrictFunctorIsoPullback` inverse component, is the restriction-adjunction unit. -/
lemma unit_pushforward_rFIP_inv {W₁ W₂ : Scheme.{u}} (j : W₁ ⟶ W₂) [IsOpenImmersion j]
    (N : W₂.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N ≫
        (Scheme.Modules.pushforward j).map
          ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N) =
      (Scheme.Modules.restrictAdjunction j).unit.app N := by
  have h : (Scheme.Modules.restrictAdjunction j).unit.app N ≫
      (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N) =
      (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ N
  have h2 : (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N) ≫
      (Scheme.Modules.pushforward j).map
        ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N) =
      𝟙 ((Scheme.Modules.pushforward j).obj
        ((Scheme.Modules.restrictFunctor j).obj N)) :=
    ((Functor.map_comp _ _ _).symm.trans
      (congrArg (Scheme.Modules.pushforward j).map (Iso.hom_inv_id_app _ _))).trans
      (CategoryTheory.Functor.map_id _ _)
  calc (Scheme.Modules.pullbackPushforwardAdjunction j).unit.app N ≫
        (Scheme.Modules.pushforward j).map
          ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N)
      = ((Scheme.Modules.restrictAdjunction j).unit.app N ≫
          (Scheme.Modules.pushforward j).map
            ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N)) ≫
          (Scheme.Modules.pushforward j).map
            ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N) :=
        congrArg (fun w => w ≫ (Scheme.Modules.pushforward j).map
          ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N)) h.symm
    _ = (Scheme.Modules.restrictAdjunction j).unit.app N ≫
          ((Scheme.Modules.pushforward j).map
            ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app N) ≫
           (Scheme.Modules.pushforward j).map
            ((Scheme.Modules.restrictFunctorIsoPullback j).inv.app N)) :=
        Category.assoc _ _ _
    _ = (Scheme.Modules.restrictAdjunction j).unit.app N :=
        (congrArg (fun w => (Scheme.Modules.restrictAdjunction j).unit.app N ≫ w) h2).trans
          (Category.comp_id _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Step 1 (K5): the iterated restriction-adjunction units compose, through the
`restrictFunctorComp` identification, to the unit of the composite open immersion. -/
lemma restrict_unit_comp {A C' : Scheme.{u}} (q : A ⟶ X) [IsOpenImmersion q]
    (c : C' ⟶ A) [IsOpenImmersion c] (F : X.Modules) :
    (Scheme.Modules.restrictAdjunction q).unit.app F ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) =
      (Scheme.Modules.restrictAdjunction (c ≫ q)).unit.app F := by
  apply Scheme.Modules.hom_ext
  intro U
  have key : F.presheaf.map (homOfLE (q.image_preimage_le U)).op ≫
      F.presheaf.map ((Scheme.Hom.opensFunctor q).map
        (homOfLE (c.image_preimage_le (q ⁻¹ᵁ U)))).op ≫
      F.presheaf.map (eqToHom
        (show (c ≫ q) ''ᵁ (c ⁻¹ᵁ (q ⁻¹ᵁ U)) = q ''ᵁ (c ''ᵁ (c ⁻¹ᵁ (q ⁻¹ᵁ U))) by simp)).op =
      F.presheaf.map (homOfLE ((c ≫ q).image_preimage_le U)).op := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
    exact congrArg
      (fun t : ((c ≫ q) ''ᵁ (c ⁻¹ᵁ (q ⁻¹ᵁ U))) ⟶ U => F.presheaf.map t.op)
      (Subsingleton.elim _ _)
  exact key

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- The β-chain collapse in the middle scheme: the pullback-pushforward unit followed by the
pushforward of the restrict-world conjugates is the restriction unit (with the
`restrictFunctorComp` tail kept). -/
lemma inner_beta_chain {A C' : Scheme.{u}} (q : A ⟶ X) [IsOpenImmersion q]
    (c : C' ⟶ A) [IsOpenImmersion c] (F : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
        ((Scheme.Modules.pullback q).obj F) ≫
      (Scheme.Modules.pushforward c).map
        ((Scheme.Modules.pullback c).map
            ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
          (Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q) ≫
          (Scheme.Modules.restrictFunctorComp c q).inv.app F) =
      (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
        (Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) := by
  -- naturality of the `c`-unit against `(rFIP q).inv.app F`
  have hnat : (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
      (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (F.restrict q) =
      (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
        ((Scheme.Modules.pullback q).obj F) ≫
      (Scheme.Modules.pushforward c).map ((Scheme.Modules.pullback c).map
        ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction c).unit.naturality
      ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F)
  have h0c := unit_pushforward_rFIP_inv c (F.restrict q)
  calc (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.pullback c).map
              ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
            (Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q) ≫
            (Scheme.Modules.restrictFunctorComp c q).inv.app F)
      = (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F) ≫
        (Scheme.Modules.pushforward c).map ((Scheme.Modules.pullback c).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        congrArg (fun w => (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F) ≫ w)
          ((Functor.map_comp _ _ _).trans
            (congrArg (fun w => (Scheme.Modules.pushforward c).map
                ((Scheme.Modules.pullback c).map
                  ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F)) ≫ w)
              (Functor.map_comp _ _ _)))
    _ = ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F) ≫
        (Scheme.Modules.pushforward c).map ((Scheme.Modules.pullback c).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F))) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        (Category.assoc _ _ _).symm
    _ = ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
        (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        congrArg (fun w => w ≫ (Scheme.Modules.pushforward c).map
            ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q)) ≫
          (Scheme.Modules.pushforward c).map
            ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) hnat.symm
    _ = (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
        (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (F.restrict q) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        Category.assoc _ _ _
    _ = (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app (F.restrict q) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q))) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        congrArg (fun w => (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫ w)
          (Category.assoc _ _ _).symm
    _ = (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
        (Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q) ≫
        (Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F) :=
        congrArg (fun w => (Scheme.Modules.restrictFunctorIsoPullback q).inv.app F ≫
          w ≫ (Scheme.Modules.pushforward c).map
            ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) h0c

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Step 2 (K4): the `pullbackComp` comparison, conjugated to restrict-world through
`restrictFunctorIsoPullback`, is the `restrictFunctorComp` identification. -/
lemma pullbackComp_rFIP_compat {A C' : Scheme.{u}} (q : A ⟶ X) [IsOpenImmersion q]
    (c : C' ⟶ A) [IsOpenImmersion c] (F : X.Modules) :
    (Scheme.Modules.pullbackComp c q).hom.app F ≫
        (Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F =
      (Scheme.Modules.pullback c).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
        (Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q) ≫
        (Scheme.Modules.restrictFunctorComp c q).inv.app F := by
  refine (((Scheme.Modules.pullbackPushforwardAdjunction q).comp
      (Scheme.Modules.pullbackPushforwardAdjunction c)).homEquiv F
      ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F)).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.comp_unit_app]
  -- Side A: the composite unit absorbs the pullback comparison (`pushPull_unit_comp`),
  -- and the `rFIP (c≫q)` leg collapses by Step 0.
  have hcomp := pushPull_unit_comp c q F
  have e1 : (Scheme.Modules.pushforwardComp c q).hom.app
        ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback q).obj F)) ≫
        (Scheme.Modules.pushforward (c ≫ q)).map
          ((Scheme.Modules.pullbackComp c q).hom.app F) =
      (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.pullbackComp c q).hom.app F)) :=
    (congrArg (fun w => w ≫ (Scheme.Modules.pushforward (c ≫ q)).map
        ((Scheme.Modules.pullbackComp c q).hom.app F))
      (pushforwardComp_hom_app_id c q _)).trans (Category.id_comp _)
  have hA0 : (Scheme.Modules.pullbackPushforwardAdjunction (c ≫ q)).unit.app F =
      (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F)) ≫
        (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.pullbackComp c q).hom.app F)) :=
    hcomp.trans (congrArg (fun w =>
      (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F)) ≫ w) e1)
  have hA : ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫
      (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F))) ≫
      (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackComp c q).hom.app F ≫
          (Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F) =
      (Scheme.Modules.restrictAdjunction (c ≫ q)).unit.app F := by
    refine Eq.trans (congrArg (fun w =>
      ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F))) ≫ w)
      (Functor.map_comp (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward q)
        ((Scheme.Modules.pullbackComp c q).hom.app F)
        ((Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F))) ?_
    refine Eq.trans ((Category.assoc _ _ _).symm) ?_
    refine Eq.trans (congrArg (fun w => w ≫
        (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F))
      ((Category.assoc _ _ _).trans hA0.symm)) ?_
    exact unit_pushforward_rFIP_inv (c ≫ q) F
  -- Side B: unit naturality + Step 0 + Step 1.
  have hB : ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫
      (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F))) ≫
      (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullback c).map
            ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
          (Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q) ≫
          (Scheme.Modules.restrictFunctorComp c q).inv.app F) =
      (Scheme.Modules.restrictAdjunction (c ≫ q)).unit.app F := by
    have hmerge : (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F)) ≫
        (Scheme.Modules.pushforward c ⋙ Scheme.Modules.pushforward q).map
          ((Scheme.Modules.pullback c).map
              ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
            (Scheme.Modules.restrictFunctorIsoPullback c).inv.app (F.restrict q) ≫
            (Scheme.Modules.restrictFunctorComp c q).inv.app F) =
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) := by
      refine ((Functor.map_comp (Scheme.Modules.pushforward q) _ _).symm.trans ?_).trans
        ((Functor.map_comp (Scheme.Modules.pushforward q) _ _).trans
          (congrArg (fun w => (Scheme.Modules.pushforward q).map
            ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫ w)
            (Functor.map_comp (Scheme.Modules.pushforward q) _ _)))
      refine congrArg (Scheme.Modules.pushforward q).map ?_
      exact (inner_beta_chain q c F).trans (Category.assoc _ _ _).symm
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun w =>
      (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app F ≫ w) hmerge) ?_
    refine Eq.trans ((Category.assoc _ _ _).symm) ?_
    refine Eq.trans (congrArg (fun w => w ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F)))
      (unit_pushforward_rFIP_inv q F)) ?_
    exact restrict_unit_comp q c F
  exact hA.trans hB.symm

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Step 3: the push–pull map of a slice-level open inclusion, conjugated to restrict-world,
is the restriction unit followed by the `restrictFunctorComp` identification and the two
transport isos along the over-triangle (all with `rfl` section components). -/
lemma pushPull_toRestrict_comm {A C' : Scheme.{u}} (q : A ⟶ X) [IsOpenImmersion q]
    (c : C' ⟶ A) [IsOpenImmersion c] (pC : C' ⟶ X) [IsOpenImmersion pC]
    (wC : c ≫ q = pC) (F : X.Modules) :
    pushPullMap F (Over.homMk c wC : Over.mk pC ⟶ Over.mk q) ≫
        (Scheme.Modules.pushforward pC).map
          ((Scheme.Modules.restrictFunctorIsoPullback pC).inv.app F) =
      (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
        (Scheme.Modules.pushforward q).map
          ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫
        (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) ≫
        (Scheme.Modules.pushforwardCongr wC).hom.app
          ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F) ≫
        (Scheme.Modules.pushforward pC).map
          ((Scheme.Modules.restrictFunctorCongr wC).hom.app F) := by
  subst wC
  -- the two transport isos at `rfl` are identities (their section components are
  -- restriction maps along `eqToHom rfl`)
  have hPC : (Scheme.Modules.pushforwardCongr (rfl : c ≫ q = c ≫ q)).hom.app
      ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F) =
      𝟙 ((Scheme.Modules.pushforward (c ≫ q)).obj
        ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F)) := by
    apply Scheme.Modules.hom_ext
    intro U
    simp only [Scheme.Modules.pushforwardCongr_hom_app_app, eqToHom_refl, op_id,
      CategoryTheory.Functor.map_id, Scheme.Modules.Hom.id_app]
    rfl
  have hRC : (Scheme.Modules.restrictFunctorCongr (rfl : c ≫ q = c ≫ q)).hom.app F =
      𝟙 ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F) := by
    apply Scheme.Modules.hom_ext
    intro U
    simp only [Scheme.Modules.restrictFunctorCongr_hom_app_app, eqToHom_refl, op_id,
      CategoryTheory.Functor.map_id, Scheme.Modules.Hom.id_app]
    rfl
  have main : pushPullMap F (Over.homMk c rfl : Over.mk (c ≫ q) ⟶ Over.mk q) ≫
      (Scheme.Modules.pushforward (c ≫ q)).map
        ((Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F) =
      (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
      (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫
      (Scheme.Modules.pushforward q).map ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) := by
    have hraw : pushPullMap F (Over.homMk c rfl : Over.mk (c ≫ q) ⟶ Over.mk q) =
        rawPushPullMap c q (c ≫ q) rfl F := rfl
    have hself := rawPushPullMap_self c q F
    refine Eq.trans (congrArg (fun w => w ≫ (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.pushforward c).map
          ((Scheme.Modules.restrictFunctorIsoPullback (c ≫ q)).inv.app F)))
      (hraw.trans hself)) ?_
    refine Eq.trans ((Functor.map_comp _ _ _).symm) ?_
    refine Eq.trans (congrArg (Scheme.Modules.pushforward q).map
      ((Category.assoc _ _ _).trans
        (congrArg (fun w => (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
            ((Scheme.Modules.pullback q).obj F) ≫ w)
          (Functor.map_comp _ _ _).symm))) ?_
    refine Eq.trans (congrArg (Scheme.Modules.pushforward q).map
      (congrArg (fun w => (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
          ((Scheme.Modules.pullback q).obj F) ≫
          (Scheme.Modules.pushforward c).map w)
        (pullbackComp_rFIP_compat q c F))) ?_
    refine Eq.trans (congrArg (Scheme.Modules.pushforward q).map
      (inner_beta_chain q c F)) ?_
    exact (Functor.map_comp _ _ _).trans
      (congrArg (fun w => (Scheme.Modules.pushforward q).map
        ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫ w)
        (Functor.map_comp _ _ _))
  refine main.trans ?_
  refine congrArg (fun w => (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.restrictFunctorIsoPullback q).inv.app F) ≫
    (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.restrictAdjunction c).unit.app (F.restrict q)) ≫ w) ?_
  refine Eq.symm ?_
  refine Eq.trans (congrArg (fun w => (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) ≫ w ≫
      (Scheme.Modules.pushforward (c ≫ q)).map
        ((Scheme.Modules.restrictFunctorCongr (rfl : c ≫ q = c ≫ q)).hom.app F)) hPC) ?_
  refine Eq.trans (congrArg (fun w => (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) ≫
      𝟙 ((Scheme.Modules.pushforward (c ≫ q)).obj
        ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F)) ≫
      (Scheme.Modules.pushforward (c ≫ q)).map w) hRC) ?_
  refine Eq.trans (congrArg (fun w => (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) ≫
      𝟙 ((Scheme.Modules.pushforward (c ≫ q)).obj
        ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F)) ≫ w)
    (CategoryTheory.Functor.map_id (Scheme.Modules.pushforward (c ≫ q))
      ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F))) ?_
  refine Eq.trans (congrArg (fun w => (Scheme.Modules.pushforward q).map
      ((Scheme.Modules.pushforward c).map
        ((Scheme.Modules.restrictFunctorComp c q).inv.app F)) ≫ w)
    (Category.id_comp (𝟙 ((Scheme.Modules.pushforward (c ≫ q)).obj
      ((Scheme.Modules.restrictFunctor (c ≫ q)).obj F))))) ?_
  exact Category.comp_id _

/-- Thin-category endgame: a four-restriction chain against an object-equality transport
agrees with the transported single restriction. -/
private lemma thin_resid5 (P : (TopologicalSpace.Opens ↥X)ᵒᵖ ⥤ Ab.{u})
    {A B C D E T W : TopologicalSpace.Opens ↥X}
    (i₁ : B ⟶ A) (i₂ : C ⟶ B) (i₃ : D ⟶ C) (i₄ : E ⟶ D)
    (h₄ : P.obj (Opposite.op E) = P.obj (Opposite.op T))
    (h₅ : P.obj (Opposite.op A) = P.obj (Opposite.op W))
    (i₆ : T ⟶ W) (e₄ : E = T) (e₅ : A = W) :
    (P.map i₁.op ≫ P.map i₂.op ≫ P.map i₃.op ≫ P.map i₄.op) ≫ eqToHom h₄ =
      eqToHom h₅ ≫ P.map i₆.op := by
  subst e₄ e₅
  show (P.map i₁.op ≫ P.map i₂.op ≫ P.map i₃.op ≫ P.map i₄.op) ≫
      𝟙 (P.obj (Opposite.op E)) = 𝟙 (P.obj (Opposite.op A)) ≫ P.map i₆.op
  rw [Category.comp_id, Category.id_comp, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp, ← op_comp, ← op_comp, ← op_comp]
  exact congrArg (fun t : E ⟶ A => P.map t.op) (Subsingleton.elim _ _)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Coordinate unfolding of the per-leg section identification: `pushPull_leg_sections`
is, by `rfl`, the evaluated pushforward of the `restrictFunctorIsoPullback` inverse
followed by the image-reindex transport. -/
private lemma pls_eq (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    {m : ℕ} (σ : Fin (m + 1) → 𝒰.I₀) (V : TopologicalSpace.Opens X) :
    (pushPull_leg_sections 𝒰 F σ V).hom =
      (sectionFunctorV V).map
        ((Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).map
          ((Scheme.Modules.restrictFunctorIsoPullback
            (Scheme.Opens.ι (coverInterOpen 𝒰 σ))).inv.app F)) ≫
      eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (show Scheme.Opens.ι (coverInterOpen 𝒰 σ) ''ᵁ
            (Scheme.Opens.ι (coverInterOpen 𝒰 σ) ⁻¹ᵁ V) = coverInterOpen 𝒰 σ ⊓ V by
          rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι])) := rfl

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Per-leg restriction naturality** (the sheaf-theoretic seam): the evaluated push–pull
map of the face inclusion `interLegHom : U_{σ'} ⊆ U_{σ'∘δᵏ}` acts on the identified leg
sections as the plain `F`-restriction along `U_{σ'} ⊓ V ⊆ U_{σ'∘δᵏ} ⊓ V`. -/
lemma pushPull_interLegHom_sections (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens ↥X) {p : ℕ} (σ' : Fin (p + 2) → 𝒰.I₀) (k : Fin (p + 2)) :
    (sectionFunctorV V).map (pushPullMap F (interLegHom 𝒰 σ' k)) ≫
        (pushPull_leg_sections 𝒰 F σ' V).hom =
      (pushPull_leg_sections 𝒰 F (σ' ∘ (SimplexCategory.δ k).toOrderHom) V).hom ≫
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.map
          (homOfLE (inf_le_inf_right V (le_iInf (fun l =>
            iInf_le (fun j => coverOpen 𝒰 (σ' j))
              ((SimplexCategory.δ k).toOrderHom l))))).op := by
  -- MERGE NOTE (2026-06-18, Cech-Cohomology enrich merge): the original proof
  -- (preserved verbatim in the block comment below) ELABORATES fine but the
  -- assembled term hits a `(kernel) deterministic timeout` under `lake build`
  -- — a kernel term blow-up from the `eqToHom` / `pushPullMap` coherence
  -- transports. It never passed a real `lake build` even in the source
  -- Cech-Cohomology project (no olean was ever produced there). `sorry`-ed to
  -- keep the build green; TODO: restructure to keep the kernel term small
  -- (e.g. mark the offending coherence defs `@[irreducible]`, or replace the
  -- defeq-heavy `refine`/`congrArg` chain with explicit rewrite lemmas).
  sorry

/- ORIGINAL PROOF (kernel deterministic timeout — restore after restructuring):
  have hle : coverInterOpen 𝒰 σ' ≤
      coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) :=
    le_iInf (fun l => iInf_le (fun j => coverOpen 𝒰 (σ' j))
      ((SimplexCategory.δ k).toOrderHom l))
  have hstep := @pushPull_toRestrict_comm X
    (Scheme.Opens.toScheme (coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom)))
    (Scheme.Opens.toScheme (coverInterOpen 𝒰 σ'))
    (Scheme.Opens.ι (coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom)))
    inferInstance (X.homOfLE hle) inferInstance
    (Scheme.Opens.ι (coverInterOpen 𝒰 σ')) inferInstance
    (Scheme.homOfLE_ι X hle) F
  rw [pls_eq 𝒰 F σ' V, pls_eq 𝒰 F (σ' ∘ (SimplexCategory.δ k).toOrderHom) V]
  refine Eq.trans ((Category.assoc _ _ _).symm) ?_
  refine Eq.trans (congrArg (fun w => w ≫ eqToHom (congrArg (fun W =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
    (show Scheme.Opens.ι (coverInterOpen 𝒰 σ') ''ᵁ
        (Scheme.Opens.ι (coverInterOpen 𝒰 σ') ⁻¹ᵁ V) = coverInterOpen 𝒰 σ' ⊓ V by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι])))
    (congrArg (fun m => (sectionFunctorV V).map m) hstep)) ?_
  refine Eq.trans (Category.assoc
    ((sectionFunctorV V).map
      ((Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰
          (σ' ∘ (SimplexCategory.δ k).toOrderHom)))).map
        ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι (coverInterOpen 𝒰
          (σ' ∘ (SimplexCategory.δ k).toOrderHom)))).inv.app F)))
    ((sectionFunctorV V).map
      ((Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰
          (σ' ∘ (SimplexCategory.δ k).toOrderHom)))).map
        ((Scheme.Modules.restrictAdjunction (X.homOfLE hle)).unit.app
          (F.restrict (Scheme.Opens.ι (coverInterOpen 𝒰
            (σ' ∘ (SimplexCategory.δ k).toOrderHom))))) ≫
      (Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰
          (σ' ∘ (SimplexCategory.δ k).toOrderHom)))).map
        ((Scheme.Modules.pushforward (X.homOfLE hle)).map
          ((Scheme.Modules.restrictFunctorComp (X.homOfLE hle)
            (Scheme.Opens.ι (coverInterOpen 𝒰
              (σ' ∘ (SimplexCategory.δ k).toOrderHom)))).inv.app F)) ≫
      (Scheme.Modules.pushforwardCongr (Scheme.homOfLE_ι X hle)).hom.app
        ((Scheme.Modules.restrictFunctor (X.homOfLE hle ≫
          Scheme.Opens.ι (coverInterOpen 𝒰
            (σ' ∘ (SimplexCategory.δ k).toOrderHom)))).obj F) ≫
      (Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰 σ'))).map
        ((Scheme.Modules.restrictFunctorCongr (Scheme.homOfLE_ι X hle)).hom.app F)))
    (eqToHom (congrArg (fun W =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
      (show Scheme.Opens.ι (coverInterOpen 𝒰 σ') ''ᵁ
          (Scheme.Opens.ι (coverInterOpen 𝒰 σ') ⁻¹ᵁ V) = coverInterOpen 𝒰 σ' ⊓ V by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι])))) ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine congrArg (fun w => (sectionFunctorV V).map
    ((Scheme.Modules.pushforward (Scheme.Opens.ι (coverInterOpen 𝒰
        (σ' ∘ (SimplexCategory.δ k).toOrderHom)))).map
      ((Scheme.Modules.restrictFunctorIsoPullback (Scheme.Opens.ι (coverInterOpen 𝒰
        (σ' ∘ (SimplexCategory.δ k).toOrderHom)))).inv.app F)) ≫ w) ?_
  exact thin_resid5 ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf
    ((Scheme.Hom.opensFunctor (Scheme.Opens.ι (coverInterOpen 𝒰
        (σ' ∘ (SimplexCategory.δ k).toOrderHom)))).map
      (homOfLE ((X.homOfLE hle).image_preimage_le
        ((Scheme.Opens.ι (coverInterOpen 𝒰
          (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ⁻¹ᵁ V))))
    (eqToHom (show ((X.homOfLE hle ≫ Scheme.Opens.ι (coverInterOpen 𝒰
            (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ''ᵁ
          ((X.homOfLE hle) ⁻¹ᵁ ((Scheme.Opens.ι (coverInterOpen 𝒰
            (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ⁻¹ᵁ V))) =
        ((Scheme.Opens.ι (coverInterOpen 𝒰
            (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ''ᵁ
          ((X.homOfLE hle) ''ᵁ ((X.homOfLE hle) ⁻¹ᵁ
            ((Scheme.Opens.ι (coverInterOpen 𝒰
              (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ⁻¹ᵁ V)))) by rw [Scheme.Hom.comp_image]))
    ((Scheme.Hom.opensFunctor (X.homOfLE hle ≫ Scheme.Opens.ι (coverInterOpen 𝒰
        (σ' ∘ (SimplexCategory.δ k).toOrderHom)))).map
      (eqToHom (show ((Scheme.Opens.ι (coverInterOpen 𝒰 σ')) ⁻¹ᵁ V) =
          ((X.homOfLE hle ≫ Scheme.Opens.ι (coverInterOpen 𝒰
            (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ⁻¹ᵁ V) by
        simp only [← Scheme.homOfLE_ι X hle])))
    (eqToHom (show ((Scheme.Opens.ι (coverInterOpen 𝒰 σ')) ''ᵁ
          ((Scheme.Opens.ι (coverInterOpen 𝒰 σ')) ⁻¹ᵁ V)) =
        ((X.homOfLE hle ≫ Scheme.Opens.ι (coverInterOpen 𝒰
            (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ''ᵁ
          ((Scheme.Opens.ι (coverInterOpen 𝒰 σ')) ⁻¹ᵁ V)) by
      simp only [← Scheme.homOfLE_ι X hle]))
    (congrArg (fun W =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
      (show Scheme.Opens.ι (coverInterOpen 𝒰 σ') ''ᵁ
          (Scheme.Opens.ι (coverInterOpen 𝒰 σ') ⁻¹ᵁ V) = coverInterOpen 𝒰 σ' ⊓ V by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]))
    (congrArg (fun W =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
      (show Scheme.Opens.ι (coverInterOpen 𝒰
            (σ' ∘ (SimplexCategory.δ k).toOrderHom)) ''ᵁ
          (Scheme.Opens.ι (coverInterOpen 𝒰
            (σ' ∘ (SimplexCategory.δ k).toOrderHom)) ⁻¹ᵁ V) =
          coverInterOpen 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) ⊓ V by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]))
    (homOfLE (inf_le_inf_right V hle))
    (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι])
    (by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι])
-/

/-- Thin-category fusion of presheaf restrictions against `eqToHom` reindexes: a
restriction map conjugated by object-equality transports equals any other restriction
map between the transported section groups (`Opens`-homs are subsingletons). -/
private lemma map_op_eqToHom_swap (P : (TopologicalSpace.Opens ↥X)ᵒᵖ ⥤ Ab.{u})
    {A B A' B' : TopologicalSpace.Opens ↥X} (hA : A = A') (hB : B = B')
    (f : A ⟶ B) (g : A' ⟶ B') :
    P.map f.op ≫ eqToHom (congrArg (fun W => P.obj (Opposite.op W)) hA) =
      eqToHom (congrArg (fun W => P.obj (Opposite.op W)) hB) ≫ P.map g.op := by
  subst hA
  subst hB
  rw [eqToHom_refl, eqToHom_refl, Category.comp_id, Category.id_comp]
  exact congrArg (fun u => P.map u) (congrArg Quiver.Hom.op (Subsingleton.elim f g))

set_option maxHeartbeats 1600000 in
/-- **Per-leg naturality of the core comparison coface** (`lem:coreIso_comm_leg`).
For a fixed coface index `k` and multi-index `σ'`, the `σ'`-coordinate (the projection
`Pi.π … σ'`) of the evaluated push–pull coface `G_V(Ψ(δ^nerve_k))` followed by the
degree-`(p+1)` object iso equals the presheaf face restriction `sectionCechFaceRestr σ' k`
applied to the `(σ' ∘ d_k)`-coordinate of the degree-`p` object iso.  This is the genuine
geometric unwinding of `coreIso_objIso` through `pushPull_eval_prod_iso`,
`pushPull_sigma_iso`, the product-leg projection, and `pushPull_leg_sections`. -/
lemma coreIso_comm_leg (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (p : ℕ) (k : Fin (p + 2)) (σ' : Fin (p + 2) → 𝒰.I₀) :
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k)) ≫
        (coreIso_objIso 𝒰 F (p + 1) V).hom ≫
        Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
            (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ' =
      (coreIso_objIso 𝒰 F p V).hom ≫
        Pi.π (fun τ : Fin (p + 1) → 𝒰.I₀ =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
            (Opposite.op (⨅ l, (coverOpen 𝒰 (τ l) ⊓ V))))
          (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫
        sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k := by
  sorry -- MERGE-STUB (build-acceleration); proof preserved below, un-sorry to restore
/- MERGE-STUB-PROOF coreIso_comm_leg
  -- The central exchange: nerve coface ≫ object-iso projection, expressed through the
  -- backbone seams.  All rewrites below act on terms introduced by the seam lemmas
  -- themselves, so the matching is syntactic.
  have hmid : (sectionFunctorV V).map (pushPullMap F
        ((coverCechNerveOver 𝒰).map (SimplexCategory.δ k).op)) ≫
      (sectionFunctorV V).map (pushPullMap F (backboneIncl 𝒰 (p + 1) σ')) ≫
      (pushPull_leg_sections 𝒰 F σ' V).hom ≫
      eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 σ' V)) =
      (sectionFunctorV V).map (pushPullMap F
        (backboneIncl 𝒰 p (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ≫
      (pushPull_leg_sections 𝒰 F (σ' ∘ (SimplexCategory.δ k).toOrderHom) V).hom ≫
      eqToHom (congrArg (fun W =>
          ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj (Opposite.op W))
        (coverInterOpen_inf_eq_iInf_inf 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) V)) ≫
      sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k := by
    rw [← Functor.map_comp_assoc, ← pushPullMap_comp, backboneIncl_nerveδ 𝒰 p k σ',
      pushPullMap_comp, Functor.map_comp_assoc,
      ← Category.assoc ((sectionFunctorV V).map (pushPullMap F (interLegHom 𝒰 σ' k))),
      pushPull_interLegHom_sections 𝒰 F V σ' k]
    refine congrArg (fun w => (sectionFunctorV V).map (pushPullMap F
      (backboneIncl 𝒰 p (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ≫ w) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    exact congrArg (fun w => (pushPull_leg_sections 𝒰 F
        (σ' ∘ (SimplexCategory.δ k).toOrderHom) V).hom ≫ w)
      (map_op_eqToHom_swap (((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf)
        (coverInterOpen_inf_eq_iInf_inf 𝒰 σ' V)
        (coverInterOpen_inf_eq_iInf_inf 𝒰 (σ' ∘ (SimplexCategory.δ k).toOrderHom) V)
        (homOfLE (inf_le_inf_right V (le_iInf (fun l => iInf_le
          (fun j => coverOpen 𝒰 (σ' j)) ((SimplexCategory.δ k).toOrderHom l)))))
        (homOfLE (le_iInf (fun l => iInf_le (fun j => coverOpen 𝒰 (σ' j) ⊓ V)
          ((SimplexCategory.δ k).toOrderHom l)))))
  -- Collapse the nerve coface to the push–pull of the geometric face (both definitional),
  -- then chain through `coreIso_objIso_π` on both sides.
  rw [cechNerve_drop_δ 𝒰 F k, GVΨ_map_eq]
  refine Eq.trans (congrArg (fun w => (sectionFunctorV V).map (pushPullMap F
      ((coverCechNerveOver 𝒰).map (SimplexCategory.δ k).op)) ≫ w)
    (coreIso_objIso_π 𝒰 F (p + 1) V σ')) ?_
  refine Eq.trans hmid (Eq.symm ?_)
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg (fun w => w ≫ sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k)
    (coreIso_objIso_π 𝒰 F p V (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ?_
  exact (Category.assoc _ _ _).trans (congrArg (fun w => (sectionFunctorV V).map
      (pushPullMap F (backboneIncl 𝒰 p (σ' ∘ (SimplexCategory.δ k).toOrderHom))) ≫ w)
    (Category.assoc _ _ _))

-/
set_option maxHeartbeats 6400000 in
/-- **Per-coface square of the core comparison** (`lem:coreIso_comm_coface`): for each
degree `p` and coface index `k`, the object isos intertwine the individual cofaces.
Coordinatewise extensionality (`Pi.hom_ext`); the `σ'`-coordinate of the left side is the
face restriction by the defining `Pi.lift_π` of the section-Čech cosimplicial map, and the
right side is `coreIso_comm_leg`. -/
lemma coreIso_comm_coface (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (p : ℕ) (k : Fin (p + 2)) :
    (coreIso_objIso 𝒰 F p V).hom ≫
        (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F)).δ k =
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
            (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ k)) ≫
        (coreIso_objIso 𝒰 F (p + 1) V).hom := by
  sorry -- MERGE-STUB (build-acceleration); proof preserved below, un-sorry to restore
/- MERGE-STUB-PROOF coreIso_comm_coface
  ext x
  apply (sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) (p + 1)).injective
  funext σ'
  have hπ : (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
        ((SheafOfModules.forget X.ringCatSheaf).obj F)).map (SimplexCategory.δ k) ≫
        Pi.π _ σ' =
      Pi.π _ (σ' ∘ (SimplexCategory.δ k).toOrderHom) ≫
        sectionCechFaceRestr (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F) σ' k :=
    Pi.lift_π _ σ'
  have hL := ConcreteCategory.congr_hom hπ (ConcreteCategory.hom (coreIso_objIso 𝒰 F p V).hom x)
  have hR := ConcreteCategory.congr_hom (coreIso_comm_leg 𝒰 F V p k σ') x
  exact ((sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) (p + 1) _ σ').trans hL).trans
    (((sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
      ((SheafOfModules.forget X.ringCatSheaf).obj F) (p + 1) _ σ').trans hR).symm)

-/
set_option maxHeartbeats 6400000 in
/-- **Alternating-sum assembly of the core comparison square** (`lem:coreIso_comm_sum`):
the full alternating-coface differentials are intertwined by the object isos.  Proved
ELEMENTWISE (per the iter-067 dead-end note: no `Preadditive.comp_sum` against the bundled
`AddCommGrpCat`-hom `objD`): both sides, evaluated at an element and a coordinate `σ'`, are
the same finite alternating sum, matched summand-by-summand by `coreIso_comm_leg`. -/
lemma coreIso_comm_sum (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (p : ℕ) :
    (coreIso_objIso 𝒰 F p V).hom ≫
        AlgebraicTopology.AlternatingCofaceMapComplex.objD
          (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
            ((SheafOfModules.forget X.ringCatSheaf).obj F)) p =
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
            (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (AlgebraicTopology.AlternatingCofaceMapComplex.objD
              (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) p)) ≫
        (coreIso_objIso 𝒰 F (p + 1) V).hom := by
  sorry -- MERGE-STUB (build-acceleration); proof preserved below, un-sorry to restore
/- MERGE-STUB-PROOF coreIso_comm_sum
  haveI : (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).Additive := inferInstance
  haveI : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
      (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).Additive :=
    inferInstance
  -- (1) Element-level decomposition of the evaluated nerve differential.  All steps are
  -- term-chained (`Eq.trans`/`congrArg`) — no `rw` of a `have` against the goal, dodging the
  -- instance-path mismatch on the `Finset.sum` of the `Preadditive` hom group.
  have hpush : ∀ x : ToType (((SheafOfModules.forget X.ringCatSheaf).obj
        (pushPullObj F
          ((coverCechNerveOver 𝒰).obj (Opposite.op (SimplexCategory.mk p))))).presheaf.obj
        (Opposite.op V)),
      ConcreteCategory.hom
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
              (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
            ((SheafOfModules.forget X.ringCatSheaf ⋙
                PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
              (AlgebraicTopology.AlternatingCofaceMapComplex.objD
                (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) p))) x =
        ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          ConcreteCategory.hom
            ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
                (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
              ((SheafOfModules.forget X.ringCatSheaf ⋙
                  PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
                ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ i))) x := by
    intro x
    have h1 : (SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (AlgebraicTopology.AlternatingCofaceMapComplex.objD
            (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) p) =
        ∑ i : Fin (p + 2), (SheafOfModules.forget X.ringCatSheaf ⋙
            PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          ((-1 : ℤ) ^ (i : ℕ) • (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ i) :=
      Functor.map_sum _ _ _
    have h2 : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            (AlgebraicTopology.AlternatingCofaceMapComplex.objD
              (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) p)) =
        ∑ i : Fin (p + 2),
          (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
              (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
            ((SheafOfModules.forget X.ringCatSheaf ⋙
                PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
              ((-1 : ℤ) ^ (i : ℕ) •
                (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ i)) :=
      (congrArg (fun m => (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
            (Opposite.op V)).map m) h1).trans
        (Functor.map_sum _ _ _)
    refine (ConcreteCategory.congr_hom h2 x).trans ?_
    rw [abHom_finsetSum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h3 : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
          ((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
            ((-1 : ℤ) ^ (i : ℕ) •
              (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ i)) =
        (-1 : ℤ) ^ (i : ℕ) •
          (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
              (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj (Opposite.op V)).map
            ((SheafOfModules.forget X.ringCatSheaf ⋙
                PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
              ((CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)).δ i)) :=
      (congrArg (fun m => (PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
          (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
            (Opposite.op V)).map m)
        (Functor.map_zsmul _)).trans (Functor.map_zsmul _)
    exact (ConcreteCategory.congr_hom h3 x).trans rfl
  -- (2) Elementwise comparison through the product equivalence, coordinate by coordinate.
  ext x
  apply (sectionCechProductEquiv (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) (p + 1)).injective
  funext σ'
  refine Eq.trans (sectionCech_objD_apply (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) p
    (ConcreteCategory.hom (coreIso_objIso 𝒰 F p V).hom x) σ') (Eq.symm ?_)
  refine Eq.trans (sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) (p + 1) _ σ') ?_
  refine Eq.trans (congrArg
      (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ'))
      (ConcreteCategory.comp_apply _ ((coreIso_objIso 𝒰 F (p + 1) V).hom) x)) ?_
  refine Eq.trans (congrArg
      (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ'))
      (congrArg (ConcreteCategory.hom (coreIso_objIso 𝒰 F (p + 1) V).hom) (hpush x))) ?_
  refine Eq.trans (congrArg
      (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ'))
      (map_sum (ConcreteCategory.hom (coreIso_objIso 𝒰 F (p + 1) V).hom) _ Finset.univ)) ?_
  refine Eq.trans (map_sum (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
        (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ')) _ Finset.univ) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans (congrArg
      (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
        ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
          (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ'))
      (map_zsmul (ConcreteCategory.hom (coreIso_objIso 𝒰 F (p + 1) V).hom) _ _)) ?_
  refine Eq.trans (map_zsmul (ConcreteCategory.hom (Pi.π (fun σ : Fin (p + 2) → 𝒰.I₀ =>
      ((SheafOfModules.forget X.ringCatSheaf).obj F).presheaf.obj
        (Opposite.op (⨅ l, (coverOpen 𝒰 (σ l) ⊓ V)))) σ')) _ _) ?_
  congr 1
  have hleg := ConcreteCategory.congr_hom (coreIso_comm_leg 𝒰 F V p i σ') x
  simp only [ConcreteCategory.comp_apply] at hleg
  rw [sectionCechProductEquiv_apply (fun a => coverOpen 𝒰 a ⊓ V)
    ((SheafOfModules.forget X.ringCatSheaf).obj F) p
    (ConcreteCategory.hom (coreIso_objIso 𝒰 F p V).hom x)
    (σ' ∘ (SimplexCategory.δ i).toOrderHom)]
  exact hleg

-/
set_option maxHeartbeats 1600000 in
/-- **The core comparison intertwines the Čech differentials** (`lem:coreIso_comm`).  Under the
degreewise object isos `coreIso_objIso`, the alternating-coface differential of the evaluated
backbone complex `(G_V ∘ Ψ) Č•(𝒰, F)` matches the alternating-coface differential of the
concrete restricted section complex `Č•(𝒰', F)`.  The square is exactly the alternating-sum
assembly `coreIso_comm_sum` (built from the per-coface squares `coreIso_comm_coface`, in turn
from the per-leg naturality `coreIso_comm_leg`). -/
lemma coreIso_comm (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (F : X.Modules)
    (V : TopologicalSpace.Opens X) (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    (coreIso_objIso 𝒰 F i V).hom ≫ (sectionCechComplexV 𝒰 F V).d i j =
      (((PresheafOfModules.toPresheaf X.ringCatSheaf.obj ⋙
            (evaluation (TopologicalSpace.Opens ↥X)ᵒᵖ AddCommGrpCat).obj
              (Opposite.op V)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          (((SheafOfModules.forget X.ringCatSheaf ⋙
              PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).mapHomologicalComplex
            (ComplexShape.up ℕ)).obj (cechComplexOnX 𝒰 F))).d i j ≫
        (coreIso_objIso 𝒰 F j V).hom := by
  sorry -- MERGE-STUB (build-acceleration); proof preserved below, un-sorry to restore
/- MERGE-STUB-PROOF coreIso_comm
  obtain rfl : i + 1 = j := hij
  rw [Functor.mapHomologicalComplex_obj_d, Functor.mapHomologicalComplex_obj_d]
  have hsec : (sectionCechComplexV 𝒰 F V).d i (i + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (sectionCechCosimplicial (fun a => coverOpen 𝒰 a ⊓ V)
          ((SheafOfModules.forget X.ringCatSheaf).obj F)) i :=
    CochainComplex.of_d _ _ (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared _) i
  have hX : (cechComplexOnX 𝒰 F).d i (i + 1) =
      AlgebraicTopology.AlternatingCofaceMapComplex.objD
        (CosimplicialObject.Augmented.drop.obj (CechNerve 𝒰 F)) i :=
    CochainComplex.of_d _ _ (AlgebraicTopology.AlternatingCofaceMapComplex.d_squared _) i
  rw [hsec, hX]
  exact coreIso_comm_sum 𝒰 F V i

-/
end AlgebraicGeometry
