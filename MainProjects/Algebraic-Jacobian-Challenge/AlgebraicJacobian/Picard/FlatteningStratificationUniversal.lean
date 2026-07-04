/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Picard.EntryIdealStratum
import AlgebraicJacobian.Picard.GenericFlatnessGeometric

/-!
# Universal property of the rank strata (Nitsure §4, `n = 0`, Stage D)

This file proves the *representability* layer of the flat-locus
stratification: a morphism `q : T ⟶ X` whose pulled-back module is flat of
constant fiber rank `e` factors uniquely through the rank-`e` stratum
`stratumι : stratum G e hcov ⟶ X` of `AlgebraicJacobian.Picard.EntryIdealStratum`,
and the stratum itself carries a flat pullback.  These are parts (i)+(ii)
of the special case `n = 0` of the flattening-stratification theorem in
[Nitsure §4], feeding `AlgebraicGeometry.flatLocusStratification_universal`.

## Contents

* §1 — bridges: matrix presentations of pullback section modules
  (`exists_matrixPresentation_pullback_sections`, via the Lane F section
  formula `pullback_app_isoTensor_baseMap_sectionLinearEquiv`), transport of
  flatness between the natural and the `appLE`-restriction module structures
  (`flat_compHom_congr`), and extraction of section flatness from
  `CoherentSheafFlat (𝟙 T)` (`flat_sections_of_coherentSheafFlat_id`,
  `coherentSheafFlat_id_of_charts`).
* §2 — the rank dictionary: `rankAtStalk` of an affine section module
  computes the `pointRank` (`rankAtStalk_sections_eq_pointRank`), and the
  point rank of a pullback module is the point rank at the image point
  (`pointRank_pullback`; no flatness hypotheses, via
  `Ideal.fiberRank_baseChange`).
* §3 — Stage D1: the kernel bound `strataData_le_ker` (a flat
  constant-rank-`e` pullback kills the strata ideal) and the unique
  factorization `existsUnique_stratumLift` through the closed immersion
  `stratumι` (`IsClosedImmersion.lift`).
* §4 — Stage D2: the stratum pullback is flat over the stratum
  (`coherentSheafFlat_stratum`): on chart preimages the section module is
  presented with vanishing relation matrix, hence free.

Blueprint chapter: `Picard_FlatteningStratification.tex`,
§`sec:flatstrat_universal`.
Source: [Nitsure], §4, proof of the flattening-stratification theorem,
special case `n = 0` (`references/nitsure-hilbert-quot-src/`
`nitsure-hilbert-quot.tex`, L1849–L1885).
-/

universe u

open TensorProduct CategoryTheory

namespace AlgebraicGeometry

open Module

namespace Scheme.Modules

/-! ## §1 Presentations of pullback sections and flatness bridges -/

section PullbackPresentation

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (G : X.Modules) [G.IsQuasicoherent]

/-- Elementwise fibre-side `appLE` coherence: restricting the image of
`appLE` equals `appLE` into the smaller open. -/
private lemma appLE_res_apply' {W W' : Y.Opens} {V : X.Opens}
    (e : W ≤ g ⁻¹ᵁ V) (h : W' ≤ W) (u : Γ(X, V)) :
    (Y.presheaf.map (homOfLE h).op).hom ((g.appLE V W e).hom u) =
      (g.appLE V W' (h.trans e)).hom u := by
  have h1 := congrArg (fun (φ : Γ(X, V) ⟶ Γ(Y, W')) => φ.hom u)
    (Scheme.Hom.appLE_map (f := g) e (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h1

/-- Elementwise base-side `appLE` coherence: `appLE` of a restricted base
section equals `appLE` from the larger base open. -/
private lemma appLE_base_res_apply' {V' V : X.Opens} {W : Y.Opens}
    (h : V' ≤ V) (e' : W ≤ g ⁻¹ᵁ V') (e : W ≤ g ⁻¹ᵁ V) (u : Γ(X, V)) :
    (g.appLE V' W e').hom ((X.presheaf.map (homOfLE h).op).hom u) =
      (g.appLE V W e).hom u := by
  have h1 := congrArg (fun (φ : Γ(X, V) ⟶ Γ(Y, W)) => φ.hom u)
    (Scheme.Hom.map_appLE (f := g) e' (homOfLE h).op)
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using h1

/-- **Matrix presentations pull back to section modules** (the geometric
base-change of a local presentation, [Nitsure §4]: "the pulled-back
sequence is exact by right-exactness of tensor products").  For a morphism
`g : Y ⟶ X`, an affine `V ⊆ X`, an affine `W ⊆ g⁻¹V` and an `ee`-generator
presentation `P` of `Γ(G, V)`, the section module `Γ(g^*G, W)` admits an
`ee`-generator presentation whose relation matrix is the image of that of
`P` under `g.appLE`. -/
theorem exists_matrixPresentation_pullback_sections
    {V : X.Opens} (hV : IsAffineOpen V) {W : Y.Opens} (hW : IsAffineOpen W)
    (e : W ≤ g ⁻¹ᵁ V) {ee mm : ℕ}
    (P : MatrixPresentation Γ(X, V) Γ(G, V) ee mm) :
    ∃ P' : MatrixPresentation Γ(Y, W)
      Γ((Scheme.Modules.pullback g).obj G, W) ee mm,
      P'.relMatrix = P.relMatrix.map (g.appLE V W e).hom := by
  letI : Algebra Γ(X, V) Γ(Y, W) := (g.appLE V W e).hom.toAlgebra
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj G, W) :=
    Module.compHom _ (g.appLE V W e).hom
  obtain ⟨⟨eqv, -⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g G hW hV e
  refine ⟨(P.baseChange Γ(Y, W)).congr eqv, ?_⟩
  rw [Module.MatrixPresentation.congr_relMatrix,
    Module.MatrixPresentation.baseChange_relMatrix,
    RingHom.algebraMap_toAlgebra]

end PullbackPresentation

section FlatBridge

/-- Transport of `Module.Flat` between the canonical module structure and a
`Module.compHom` structure along a pointwise-identity ring endomorphism
(the `appLE` of the identity morphism is the identity restriction, but not
definitionally the identity ring hom). -/
private lemma flat_compHom_congr {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] (f : R →+* R) (hf : ∀ r, f r = r) :
    (letI : Module R M := Module.compHom M f
     Module.Flat R M) ↔ Module.Flat R M := by
  have h : (Module.compHom M f : Module R M) = ‹Module R M› :=
    Module.ext' _ _ fun r m => by
      show f r • m = r • m
      rw [hf r]
  exact (congrArg (fun i : Module R M => @Module.Flat R M _ _ i) h).to_iff

variable {T : Scheme.{u}}

/-- The `appLE` of the identity morphism at equal opens is pointwise the
identity. -/
private lemma id_appLE_apply {W : T.Opens}
    (e : W ≤ (𝟙 T : T ⟶ T) ⁻¹ᵁ W) (r : Γ(T, W)) :
    ((𝟙 T : T ⟶ T).appLE W W e).hom r = r := by
  rw [Scheme.id_appLE]
  exact presheaf_map_self (X := T) e r

/-- **Extraction of section flatness from flatness over the identity**: if
`G` is flat over `T` via `𝟙 T` (the encoding of "the coherent sheaf `G` is
flat" in `Scheme.CoherentSheafFlat`), then the sections over every affine
open form a flat module over the section ring. -/
theorem flat_sections_of_coherentSheafFlat_id {G : T.Modules}
    (h : Scheme.CoherentSheafFlat (𝟙 T) G) {W : T.Opens}
    (hW : IsAffineOpen W) : Module.Flat Γ(T, W) Γ(G, W) :=
  (flat_compHom_congr ((𝟙 T : T ⟶ T).appLE W W (le_refl W)).hom
    (id_appLE_apply _)).mp (h hW hW (le_refl W))

/-- **Flatness over the identity from an affine cover of flat sections**:
if the sections of `G` over each member of an affine open cover of `T` are
flat over the respective section rings, then `G` is flat over `T` via
`𝟙 T`. -/
theorem coherentSheafFlat_id_of_charts (G : T.Modules) [G.IsQuasicoherent]
    {ι : Type u} (Wc : ι → T.Opens) (hWc : ∀ j, IsAffineOpen (Wc j))
    (hcover : ∀ y : T, ∃ j, y ∈ Wc j)
    (hflat : ∀ j, Module.Flat Γ(T, Wc j) Γ(G, Wc j)) :
    Scheme.CoherentSheafFlat (𝟙 T) G := by
  intro U hU V hV eV
  exact flat_section_of_affine_cover (𝟙 T) G Wc hWc Wc hWc
    (fun j => le_refl _) hcover
    (fun j => (flat_compHom_congr
      ((𝟙 T : T ⟶ T).appLE (Wc j) (Wc j) (le_refl _)).hom
      (id_appLE_apply _)).mpr (hflat j)) hU hV eV

end FlatBridge

/-! ## §2 The rank dictionary -/

section RankDictionary

variable {T : Scheme.{u}} (G : T.Modules) [G.IsQuasicoherent]

/-- A prime of the section ring of an affine open is the prime ideal of
the corresponding point. -/
private lemma primeIdealOf_fromSpec {W : T.Opens} (hW : IsAffineOpen W)
    (p : PrimeSpectrum Γ(T, W)) (hmem : (hW.fromSpec p : T) ∈ W) :
    hW.primeIdealOf ⟨hW.fromSpec p, hmem⟩ = p := by
  have hinj : Function.Injective hW.fromSpec :=
    hW.fromSpec.isOpenEmbedding.injective
  exact hinj (by rw [hW.fromSpec_primeIdealOf])

/-- **The stalk rank of an affine section module computes the point rank**:
for a quasi-coherent `G` with flat, finite sections `Γ(G, W)` over an
affine `W`, the rank of `Γ(G, W)` at a prime `p` is the point rank of `G`
at the corresponding point `fromSpec p` [Nitsure §4: flatness plus finite
presentation make the fibre dimension compute the local rank]. -/
theorem rankAtStalk_sections_eq_pointRank {W : T.Opens}
    (hW : IsAffineOpen W) [Module.Flat Γ(T, W) Γ(G, W)]
    [Module.Finite Γ(T, W) Γ(G, W)] (p : PrimeSpectrum Γ(T, W)) :
    Module.rankAtStalk Γ(G, W) p = pointRank T G (hW.fromSpec p) := by
  have hmem : (hW.fromSpec p : T) ∈ W := by
    have h0 : (hW.fromSpec p : T) ∈ Set.range hW.fromSpec :=
      Set.mem_range_self p
    rwa [hW.range_fromSpec] at h0
  rw [Module.rankAtStalk_eq,
    pointRank_eq_chartFiberRank G (V := ⟨W, hW⟩) _ hmem]
  show p.asIdeal.fiberRank Γ(G, W) = chartFiberRank G _ hmem
  rw [chartFiberRank]
  exact Ideal.fiberRank_congr_ideal
    (congrArg PrimeSpectrum.asIdeal (primeIdealOf_fromSpec hW p hmem)).symm

end RankDictionary

section PointRankPullback

variable {X Y : Scheme.{u}} (g : Y ⟶ X) (G : X.Modules) [G.IsQuasicoherent]

/-- **The point rank of a pullback module is the point rank at the image
point** (no flatness or finiteness hypotheses; the geometric form of
`Ideal.fiberRank_baseChange`): for any morphism `g : Y ⟶ X` and
quasi-coherent `G` on `X`,
`pointRank (g^*G) y = pointRank G (g y)`. -/
theorem pointRank_pullback (y : Y) :
    haveI := pullback_isQuasicoherent_hom g G ‹_›
    pointRank Y ((Scheme.Modules.pullback g).obj G) y = pointRank X G (g y) := by
  haveI := pullback_isQuasicoherent_hom g G ‹_›
  -- affine charts around the image point and the point
  obtain ⟨V, hV, hgyV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (x := g y) (U := ⊤) trivial
  have hyV : y ∈ g ⁻¹ᵁ V := hgyV
  obtain ⟨W, hW, hyW, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y) (U := g ⁻¹ᵁ V) hyV
  -- both sides through the two charts
  rw [pointRank_eq_chartFiberRank _ (V := ⟨W, hW⟩) y hyW,
    pointRank_eq_chartFiberRank G (V := ⟨V, hV⟩) (g y) hgyV]
  -- the section formula for the pullback module over the affine pair
  letI : Algebra Γ(X, V) Γ(Y, W) := (g.appLE V W hWle).hom.toAlgebra
  letI : Module Γ(X, V) Γ((Scheme.Modules.pullback g).obj G, W) :=
    Module.compHom _ (g.appLE V W hWle).hom
  obtain ⟨⟨eqv, -⟩⟩ :=
    pullback_app_isoTensor_baseMap_sectionLinearEquiv g G hW hV hWle
  -- fiber rank through the equivalence, then base change
  have h1 : ((hW.primeIdealOf ⟨y, hyW⟩).asIdeal).fiberRank
      Γ((Scheme.Modules.pullback g).obj G, W) =
      ((hW.primeIdealOf ⟨y, hyW⟩).asIdeal).fiberRank
        (TensorProduct Γ(X, V) Γ(Y, W) Γ(G, V)) :=
    Ideal.fiberRank_congr _ eqv.symm
  have h2 := Ideal.fiberRank_baseChange (R := Γ(X, V)) (A := Γ(Y, W))
    Γ(G, V) ((hW.primeIdealOf ⟨y, hyW⟩).asIdeal)
  -- identify the contracted prime with the prime of the image point
  have h3 : ((hW.primeIdealOf ⟨y, hyW⟩).asIdeal).comap
      (algebraMap Γ(X, V) Γ(Y, W)) =
      (hV.primeIdealOf ⟨g y, hgyV⟩).asIdeal := by
    have h4 := IsAffineOpen.comap_primeIdealOf_appLE (f := g)
      V hV W hW hWle hyW
    have h5 : algebraMap Γ(X, V) Γ(Y, W) = (g.appLE V W hWle).hom := rfl
    rw [h5]
    exact congrArg PrimeSpectrum.asIdeal h4
  show ((hW.primeIdealOf ⟨y, hyW⟩).asIdeal).fiberRank
      Γ((Scheme.Modules.pullback g).obj G, W) =
    ((hV.primeIdealOf ⟨g y, hgyV⟩).asIdeal).fiberRank Γ(G, V)
  rw [h1, h2]
  exact Ideal.fiberRank_congr_ideal h3

end PointRankPullback

/-! ## §3 Stage D1: unique factorization through the stratum -/

section StageD1

variable {X T : Scheme.{u}} (G : X.Modules) [G.IsQuasicoherent] {e : ℕ}

set_option maxHeartbeats 800000 in
/-- **The kernel bound** (the hard half of Nitsure's universal property,
`n = 0`, [Nitsure §4]: "`f^*𝓕` is locally free of rank `e` iff `f^*ψ = 0`
iff `f` factors through `V_e`"): if the pullback of `G` along `q : T ⟶ X`
is flat over `T` of constant point rank `e`, then the strata ideal sheaf is
contained in the kernel of `q` — every local relation matrix pulls back to
the zero matrix, so its entries die in `Γ(T, ·)`. -/
theorem strataData_le_ker (hcov : ChartsCover G e) (q : T ⟶ X)
    (hflat : Scheme.CoherentSheafFlat (𝟙 T)
      ((Scheme.Modules.pullback q).obj G))
    (hrank : ∀ t : T,
      haveI := pullback_isQuasicoherent_hom q G ‹_›
      pointRank T ((Scheme.Modules.pullback q).obj G) t = e) :
    strataData G e hcov ≤ q.ker := by
  haveI := pullback_isQuasicoherent_hom q G ‹_›
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr fun U => ?_
  intro r hr
  rw [RingHom.mem_ker]
  -- a finite family of `e`-presentation charts covering `U`
  obtain ⟨N, Vc, mmc, Pc, hVcU, hcovU⟩ :=
    ChartsCover.exists_finite_charts G hcov U
  -- the pulled-back section dies on an affine neighbourhood of each point
  apply T.IsSheaf.section_ext fun t ht => ?_
  obtain ⟨i, hti⟩ := hcovU (q.base t) ht
  have htVc : t ∈ q ⁻¹ᵁ (Vc i).1 := hti
  obtain ⟨W, hW, htW, hWle⟩ :=
    exists_isAffineOpen_mem_and_subset (x := t) (U := q ⁻¹ᵁ (Vc i).1) htVc
  have hV : W ≤ q ⁻¹ᵁ U.1 := fun y hy => hVcU i (hWle hy)
  refine ⟨W, hV, htW, ?_⟩
  -- the relation matrix of the chart pulls back to zero on `W`
  haveI hFlatW : Module.Flat Γ(T, W)
      Γ((Scheme.Modules.pullback q).obj G, W) :=
    flat_sections_of_coherentSheafFlat_id hflat hW
  obtain ⟨P', hP'⟩ := exists_matrixPresentation_pullback_sections q G
    (Vc i).2 hW hWle (Pc i)
  haveI : Module.Finite Γ(T, W) Γ((Scheme.Modules.pullback q).obj G, W) :=
    Module.Finite.of_surjective P'.proj P'.surjective_proj
  have h0 : P'.relMatrix = 0 :=
    P'.relMatrix_eq_zero_of_flat fun p =>
      (rankAtStalk_sections_eq_pointRank _ hW p).trans (hrank _)
  -- hence the entry ideal is killed by `q.appLE (Vc i) W`
  letI : Algebra Γ(X, (Vc i).1) Γ(T, W) := (q.appLE (Vc i).1 W hWle).hom.toAlgebra
  have hker : (Pc i).entryIdeal ≤
      RingHom.ker (algebraMap Γ(X, (Vc i).1) Γ(T, W)) :=
    (_root_.Module.MatrixPresentation.relMatrix_map_eq_zero_iff
      (A := Γ(T, W))).mp (hP' ▸ h0)
  -- the strata-ideal condition at the chart
  have hmem : X.presheaf.map (homOfLE (hVcU i)).op r ∈ (Pc i).entryIdeal :=
    (mem_strataIdeal_iff G).mp hr (Vc i) (hVcU i) (mmc i) (Pc i)
  have hzero : (q.appLE (Vc i).1 W hWle).hom
      (X.presheaf.map (homOfLE (hVcU i)).op r) = 0 :=
    RingHom.mem_ker.mp (hker hmem)
  -- assemble: restriction of `q.app U r` to `W` is `q.appLE (Vc i) W` of
  -- the restricted section
  have hres : (T.presheaf.map (homOfLE hV).op).hom ((q.app U.1).hom r) =
      (q.appLE U.1 W hV).hom r := rfl
  show (T.presheaf.map (homOfLE hV).op).hom ((q.app U.1).hom r) =
    (T.presheaf.map (homOfLE hV).op).hom 0
  rw [map_zero, hres, ← appLE_base_res_apply' q (hVcU i) hWle hV r, hzero]

/-- **Unique factorization through the rank-`e` stratum** [Nitsure §4,
part (ii), `n = 0` case]: a morphism `q : T ⟶ X` whose pulled-back module
is flat over `T` of constant point rank `e` factors uniquely through the
closed immersion of the rank-`e` stratum. -/
theorem existsUnique_stratumLift (hcov : ChartsCover G e) (q : T ⟶ X)
    (hflat : Scheme.CoherentSheafFlat (𝟙 T)
      ((Scheme.Modules.pullback q).obj G))
    (hrank : ∀ t : T,
      haveI := pullback_isQuasicoherent_hom q G ‹_›
      pointRank T ((Scheme.Modules.pullback q).obj G) t = e) :
    ∃! l : T ⟶ stratum G e hcov, l ≫ stratumι G e hcov = q := by
  have hker : (stratumι G e hcov).ker ≤ q.ker := by
    have h1 : (stratumι G e hcov).ker = strataData G e hcov :=
      Scheme.IdealSheafData.ker_subschemeι (strataData G e hcov)
    rw [h1]
    exact strataData_le_ker G hcov q hflat hrank
  refine ⟨IsClosedImmersion.lift (stratumι G e hcov) q hker,
    IsClosedImmersion.lift_fac _ _ hker, fun l' hl' => ?_⟩
  rw [← cancel_mono (stratumι G e hcov), hl',
    IsClosedImmersion.lift_fac]

end StageD1

/-! ## §4 Stage D2: the stratum pullback is flat -/

section StageD2

variable {X : Scheme.{u}} (G : X.Modules) [G.IsQuasicoherent] {e : ℕ}

set_option maxHeartbeats 800000 in
/-- **The rank-`e` stratum flattens `G`** [Nitsure §4, `n = 0`: on `V_e`
the pulled-back presentation has vanishing relation matrix, so `𝓕|_{V_e}`
is free of rank `e`]: the pullback of `G` along the stratum immersion is
flat over the stratum. -/
theorem coherentSheafFlat_stratum (hcov : ChartsCover G e) :
    Scheme.CoherentSheafFlat (𝟙 (stratum G e hcov))
      ((Scheme.Modules.pullback (stratumι G e hcov)).obj G) := by
  haveI := pullback_isQuasicoherent_hom (stratumι G e hcov) G ‹_›
  -- the chart preimages cover the stratum
  have hcover : ∀ z : stratum G e hcov,
      ∃ j : {V : X.affineOpens // IsPresentationChart G e V},
        z ∈ stratumι G e hcov ⁻¹ᵁ j.1.1 := by
    intro z
    obtain ⟨V, hzV, hchart⟩ := hcov ((stratumι G e hcov).base z)
    exact ⟨⟨V, hchart⟩, hzV⟩
  -- flat sections on each chart preimage: the pulled-back presentation
  -- has vanishing relation matrix, so the section module is free
  have hflatj : ∀ j : {V : X.affineOpens // IsPresentationChart G e V},
      Module.Flat Γ(stratum G e hcov, stratumι G e hcov ⁻¹ᵁ j.1.1)
        Γ((Scheme.Modules.pullback (stratumι G e hcov)).obj G,
          stratumι G e hcov ⁻¹ᵁ j.1.1) := by
    intro j
    obtain ⟨mm, ⟨P⟩⟩ := j.2
    obtain ⟨P', hP'⟩ := exists_matrixPresentation_pullback_sections
      (stratumι G e hcov) G j.1.2 (j.1.2.preimage (stratumι G e hcov))
      le_rfl P
    have h0 : P'.relMatrix = 0 := by
      rw [hP']
      ext a b
      simp only [Matrix.map_apply, Matrix.zero_apply]
      -- the entry lies in the strata ideal, the kernel of `stratumι.app`
      have hmem : ((stratumι G e hcov).app j.1.1).hom (P.relMatrix a b) = 0 := by
        have h1 : P.relMatrix a b ∈
            RingHom.ker (((strataData G e hcov).subschemeι.app j.1.1).hom) := by
          rw [Scheme.IdealSheafData.ker_subschemeι_app]
          show P.relMatrix a b ∈ strataIdeal G e j.1
          rw [strataIdeal_eq_entryIdeal G P]
          exact P.relMatrix_mem_entryIdeal a b
        exact RingHom.mem_ker.mp h1
      -- `appLE` at `le_rfl` is `app` followed by the trivial restriction
      show ((stratumι G e hcov).appLE j.1.1
        (stratumι G e hcov ⁻¹ᵁ j.1.1) le_rfl).hom (P.relMatrix a b) = 0
      have happ : ((stratumι G e hcov).appLE j.1.1
          (stratumι G e hcov ⁻¹ᵁ j.1.1) le_rfl).hom (P.relMatrix a b) =
          ((stratum G e hcov).presheaf.map (homOfLE le_rfl).op).hom
            (((stratumι G e hcov).app j.1.1).hom (P.relMatrix a b)) := rfl
      rw [happ, hmem, map_zero]
    haveI := P'.free_of_relMatrix_eq_zero h0
    infer_instance
  intro U hU V hV eV
  exact coherentSheafFlat_id_of_charts
    ((Scheme.Modules.pullback (stratumι G e hcov)).obj G)
    (fun j : {V : X.affineOpens // IsPresentationChart G e V} =>
      stratumι G e hcov ⁻¹ᵁ j.1.1)
    (fun j => j.1.2.preimage (stratumι G e hcov)) hcover hflatj hU hV eV

end StageD2

end Scheme.Modules

end AlgebraicGeometry
