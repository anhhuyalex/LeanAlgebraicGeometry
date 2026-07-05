I now have everything needed. Here is the structured report.

---

# Report: three (four) patterns in `GrassmannianQuot.lean`

All paths absolute; the target file is
`/home/Axel/LeanAlgebraicGeometry-Horizon/MainProjects/Algebraic-Jacobian-Challenge/AlgebraicJacobian/Picard/GrassmannianQuot.lean`.

Supporting infrastructure lives in the two imported project files
`.../AlgebraicJacobian/Picard/GlueDescent.lean` and `.../AlgebraicJacobian/Picard/QuotScheme.lean` (both imported at the top of the target file, lines 1-3).

---

## 1. Discharging the C1/C2 cocycle hypotheses of `Scheme.Modules.glue`

`Scheme.Modules.glue` is invoked exactly once to build the sheaf, at **lines 1835-1840**:

```lean
noncomputable def universalQuotient (d r : ℕ) : (scheme d r).Modules :=
  Scheme.Modules.glue (theGlueData d r)
    (fun I => SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d))
    (bundleTransitionData d r)
    (fun I => bundleTransition_self d r I.1 I.2)          -- _hC1
    (fun I J K => bundleTransition_cocycle d r I J K)     -- _hC2
```

(The same two arguments are re-supplied verbatim wherever the glued object is re-derived: `glueLift` at 2234, `glueRestrictionIso` at 2423, `pullback_map_glueLift_glueRestrictionHom` at 2484, and 4457.)

The signature they satisfy is `glue` in GlueDescent.lean (lines 106-131): `_hC1 : ∀ i, g i i = eqToIso (...)` and `_hC2 : ∀ i j k, <pullbackBaseChangeTransport chain> = <...>` (the full C2 shape is quoted in §1c below).

### 1a. `_hC1` = `bundleTransition_self` (line 452)

```lean
theorem bundleTransition_self (d r : ℕ) (I : Finset (Fin r)) (hI : I.card = d) :
    bundleTransition d r I I hI hI
      = eqToIso (congrArg
          (fun φ => (Scheme.Modules.pullback φ).obj
            (SheafOfModules.free (R := (affineChart d r I).ringCatSheaf) (Fin d)))
          (show chartIncl d r I I hI hI
              = chartTransition d r I I hI hI ≫ chartIncl d r I I hI hI from by
            rw [chartTransition_self, Category.id_comp]))
```

Technique (docstring 437-451 + body 460-481): on the diagonal overlap `t_{II}=𝟙`, so the matrix factor `(X^I_I)⁻¹` collapses. The proof builds a single-overlap `have hB : matrixToFreeIso ... = Iso.refl _` closed by `matrixToFreeIso_hom`, `universalMinorInv_self`, `map_one`, `matrixEnd_one`; then unfolds `bundleTransition`, `erw [hB, Iso.refl_trans]`, and cancels the two free-pullback comparisons through the generic lemma `Scheme.Modules.pullbackFreeIso_trans_symm_eqToIso hφ (Fin d)` (proved by `subst`, so the kernel never whnf's the concrete `chartIncl`/`chartTransition`).

### 1b. `_hC2` = `bundleTransition_cocycle` (line 1802) — proved by explicit computation, NOT a uniqueness trick

```lean
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
  apply Iso.ext
  simp only [Iso.trans_hom]
  exact bundleTransition_cocycle_transport d r I J K
```

So `bundleTransition_cocycle` reduces the **iso**-level C2 to an underlying-**morphism** equality via `Iso.ext` + `simp [Iso.trans_hom]`, delegating to the hom-level lemma `bundleTransition_cocycle_transport` (line 1640).

**This is an explicit computation, not a uniqueness/mono trick.** Summary of the technique (lines 1631-1826):

- `bundleTransition_cocycle_transport` (1640-1790) expands each of the three `pullbackBaseChangeTransport` isos, via the abstract core `pullbackBaseChangeTransport_matrixToFreeIso`, into a normal form `Q ≫ matrixEnd(base-changed Cramer inverse) ≫ Q⁻¹` (the three `have eIJ/eJK/eIK`, lines 1665-1718).
- The endpoint `pullbackCongr` casts are collapsed against the free-pullback comparisons by generic `subst`-lemmas `pullbackFreeIso_inv_congr_hom_assoc`, `pullbackCongr_hom_app_free_assoc`, `pullbackFreeIso_inv_congr` (rewrite at 1746-1751).
- The two middle `matrixEnd`s are fused with `matrixEnd_comp` (in a separate `have hfuse`, 1754-1788, because mixed-provenance comp nodes block a positional `rw`).
- The resulting matrix identity is exactly the base-change bridge `baseChange_bridge d r I.1 J.1 K.1 ...` (the `have hbridge`, 1720-1742), i.e. the σ-image of the matrix-level Cramer-inverse cocycle.
- That matrix cocycle is `bundleTransition_cocycle_matrix` (line 644): `(X^J_K)⁻¹·(X^I_J)⁻¹ = (X^I_K)⁻¹`, itself proved by taking the `I`-minor (`submatrix id ...`) of the image-matrix cocycle `cocycle_imageMatrix_eq'` and pushing it through the localisation maps (`mul_submatrix_col'`, `map_map_eq_of_comp'`, `universalMatrix_map_transitionPreMap`, `imageMatrix_submatrix_I`).

Both C2 proofs carry `set_option maxHeartbeats 1600000 in` (lines 1627, 1792) to cover `isDefEq`/`whnf` cost across the `X.Modules` diamond on the heavy triple-overlap localisation objects.

---

## 2. Local-freeness of the glued sheaf

Declaration `universalQuotient_isLocallyFreeOfRank` at **line 2432**:

```lean
theorem universalQuotient_isLocallyFreeOfRank (d r : ℕ) :
    SheafOfModules.IsLocallyFreeOfRank (universalQuotient d r) d := by
  refine ⟨(theGlueData d r).J, fun I => ((theGlueData d r).ι I).opensRange, ?_, fun I => ?_⟩
  · rw [eq_top_iff]
    intro x _
    obtain ⟨I, y, rfl⟩ := (theGlueData d r).ι_jointly_surjective x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨I, y, rfl⟩
  · refine ⟨?_⟩
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
```

The predicate itself is project-local, `SheafOfModules.IsLocallyFreeOfRank` in QuotScheme.lean lines 564-567: `∃ (ι) (U : ι → X.Opens), (⨆ i, U i = ⊤) ∧ ∀ i, Nonempty ((pullback (U i).ι).obj M ≅ free (ULift (Fin d)))`.

Proof technique:
- **Trivializing cover** = the chart-immersion ranges `fun I => ((theGlueData d r).ι I).opensRange`. Covering (`⨆ = ⊤`) is discharged from `(theGlueData d r).ι_jointly_surjective` + `Opens.mem_iSup` (lines 2434-2438).
- **On each member**, the restriction of `universalQuotient` to the open `ι_I.opensRange` is identified with `O^d` by transporting the descent restriction iso along the factorization `ι_I = isoOpensRange.hom ≫ opensRange.ι`. The chain (2444-2452) inverts the chart-parametrization iso `e = ι.isoOpensRange` through the pullback pseudofunctor coherences (`pullbackId`, `pullbackCongr`, `pullbackComp`, `pullback e.inv |>.mapIso`), splices in `ι.isoOpensRange_hom_ι`, applies the key iso `universalQuotient_restrictionIso`, then `pullbackFreeIso e.inv (Fin d)` and a `freeFunctor.mapIso (Equiv.ulift.symm.toIso)` to land in the `ULift (Fin d)` free sheaf demanded by the predicate.

Key intermediate lemma — the chart restriction iso `universalQuotient_restrictionIso` (line 2417):

```lean
noncomputable def universalQuotient_restrictionIso (d r : ℕ) (I : (theGlueData d r).J) :
    (Scheme.Modules.pullback ((theGlueData d r).ι I)).obj (universalQuotient d r)
      ≅ SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d) :=
  Scheme.Modules.glueRestrictionIso (theGlueData d r)
    (fun I => SheafOfModules.free (R := ((theGlueData d r).U I).ringCatSheaf) (Fin d))
    (bundleTransitionData d r)
    (fun I => bundleTransition_self d r I.1 I.2)
    (fun I J K => bundleTransition_cocycle d r I J K) I
```

Its docstring (2412-2416) notes the underlying morphism is the adjoint transpose of the `I`-th descent-equalizer projection and iso-ness rides on `Scheme.Modules.isIso_glueRestrictionHom` (GlueDescent.lean line 3330 — this is where effective descent / the cocycle conditions are consumed). So the "chart sheaves free ⇒ glued sheaf locally free" step is: glued restriction ≅ chart free sheaf (via effective descent), transported from the abstract opens `(U i)` to the concrete opens of the glued scheme through the pullback pseudofunctor coherences.

---

## 3. The `Abelian.epiDesc` uniqueness pattern (≈ lines 4929-5588)

### 3a. `pullback_map_cover_faithful` (line 4934) — full statement

```lean
lemma pullback_map_cover_faithful {T : Scheme.{0}} {ι : Type} {V : ι → T.Opens}
    (hV : TopologicalSpace.IsOpenCover V) {M N : T.Modules} {u v : M ⟶ N}
    (h : ∀ i, (Scheme.Modules.pullback (V i).ι).map u
        = (Scheme.Modules.pullback (V i).ι).map v) :
    u = v
```

Docstring (4929-4933): "two morphisms of sheaves of modules on `T` that agree after pullback to every member of an open cover agree" — the cover-of-opens analogue of `Scheme.Modules.pullback_map_jointly_faithful` (which is the glue-data version, GlueDescent.lean line 1210). Proof (4938-4977): transfer to the site-level `restrictFunctor` via `restrictFunctorIsoPullback` naturality (`NatIso.naturality_2`), then sheaf-separate the target with `TopCat.Sheaf.eq_of_locally_eq'` over the cover `{ι_i''(ι_i⁻¹ O)}`, using `hV.exists_mem` for the covering condition and presheaf naturality (`u.mapPresheaf.naturality`) to reduce to `hres i` on sections.

Note this is a **faithfulness/mono-style** lemma (detecting *equality* on a cover), not itself an epi lemma; it is what drives the two kernel-vanishing facts below.

### 3b. The `Abelian.epiDesc` proof: `rqPullback_grPointOfRankQuotient_rel` (line 5372)

This is the `right_inv` law. It produces a `RankQuotient.Rel` witness (`Rel x y := ∃ f : x.F ≅ y.F, x.q ≫ f.hom = y.q`, def at line 2271) by exhibiting the two quotients (agreeing on the chart-locus cover) as mutually-inverse epi-descents.

**Epi instances** are threaded in by hand from the structure fields (5375-5378):

```lean
  haveI hex' : Epi ((rqPullback (grPointOfRankQuotient d r x)
      (tautologicalRankQuotient d r)).q) :=
    (rqPullback (grPointOfRankQuotient d r x) (tautologicalRankQuotient d r)).epi
  haveI hex : Epi x.q := x.epi
```

(`RankQuotient` carries `epi : Epi q` as a field, line 2264; `rqPullback` re-establishes it via `map_epi`/`epi_comp`, lines 2304-2311.)

**Two kernel-vanishing facts, each via `pullback_map_cover_faithful`** (5387-5389 and 5466-5468):

```lean
  have hker1 : kernel.ι ((rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)).q) ≫ x.q = 0 := by
    refine pullback_map_cover_faithful (chartLocus_isOpenCover d r x) (fun I => ?_)
    haveI := hinst I
    have heq := pullback_map_rqPullback_grPoint_eq d r x I
    ...
  have hker2 : kernel.ι x.q ≫ (rqPullback (grPointOfRankQuotient d r x)
        (tautologicalRankQuotient d r)).q = 0 := by
    refine pullback_map_cover_faithful (chartLocus_isOpenCover d r x) (fun I => ?_)
    ...
```

Each reduces (long `calc` chains 5402-5536) to showing `pullback.map (kernel.ι q ≫ q') = pullback.map 0` chart-locally: the shared chart presentation (`pullback_map_rqPullback_grPoint_eq`, giving `heq`, plus the chart-locus invertibility instances `hinst I` from `isIso_pullback_map_of_le`/`chartLocus_le_chartLocus_rqPullback_grPoint`) rewrites `x.q` as `q' ≫ (iso)`, then `kernel.condition` and `Functor.map_zero`/`zero_comp` finish.

**The two descents shown mutually inverse** by epi-cancellation (5538-5588). `hfg` (hom ≫ inv = 𝟙):

```lean
  have hfg : Abelian.epiDesc ((rqPullback ...).q) x.q hker1 ≫
        Abelian.epiDesc x.q ((rqPullback ...).q) hker2 = 𝟙 _ := by
    rw [← cancel_epi ((rqPullback ...).q)]
    calc (rqPullback ...).q ≫ (Abelian.epiDesc ((rqPullback ...).q) x.q hker1 ≫
            Abelian.epiDesc x.q ((rqPullback ...).q) hker2)
        = ((rqPullback ...).q ≫ Abelian.epiDesc ((rqPullback ...).q) x.q hker1) ≫
          Abelian.epiDesc x.q ((rqPullback ...).q) hker2 := (Category.assoc _ _ _).symm
      _ = x.q ≫ Abelian.epiDesc x.q ((rqPullback ...).q) hker2 :=
          congrArg (· ≫ Abelian.epiDesc x.q _ hker2) (Abelian.comp_epiDesc _ _ _)
      _ = (rqPullback ...).q := Abelian.comp_epiDesc _ _ _
      _ = (rqPullback ...).q ≫ 𝟙 _ := (Category.comp_id _).symm
```

`hgf` (inv ≫ hom = 𝟙) is symmetric, using `rw [← cancel_epi x.q]` and `Abelian.comp_epiDesc` twice (5563-5583).

The incantation pattern is uniform: `rw [← cancel_epi <the relevant epi>]` to reduce a descent identity to a claim about `q ≫ (…)`, then `Category.assoc` + `Abelian.comp_epiDesc _ _ _` (the computation rule `q ≫ Abelian.epiDesc q g w = g`) collapse each factor.

**Assembling the `Rel` witness** (5584-5588):

```lean
  exact ⟨⟨Abelian.epiDesc ((rqPullback ...).q) x.q hker1,
    Abelian.epiDesc x.q ((rqPullback ...).q) hker2, hfg, hgf⟩,
    Abelian.comp_epiDesc _ _ _⟩
```

i.e. the iso `x.F ≅ y.F` is built from the two descents as `⟨hom, inv, hfg, hgf⟩`, and the commuting condition `q ≫ f.hom = q'` is again `Abelian.comp_epiDesc`.

The analogous `left_inv` uniqueness law `grPointOfRankQuotient_rqPullback_tautological` (line 5043) uses the same open-cover comparison but through `presentedMatrix_*` classification rather than epiDesc.

### 3c. Is `Abelian (SheafOfModules …)` used as an instance directly? Yes.

There is **no** `Abelian`/`instance` declaration anywhere in the project files for this — `grep -n "instance.*Abelian"` over the three project files returns nothing but comment/docstring mentions. `kernel`, `kernel.ι`, `kernel.condition`, `Abelian.epiDesc`, `Abelian.comp_epiDesc` all resolve purely through typeclass inference against the **Mathlib** instance chain:

- `X.Modules := SheafOfModules.{u} X.ringCatSheaf` — Mathlib `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:37`.
- `noncomputable instance : Abelian X.Modules` — Mathlib `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:48`, which is `inferInstanceAs (Abelian (SheafOfModules X.ringCatSheaf))`.
- that in turn is `noncomputable instance : Abelian (SheafOfModules.{v} R)` — Mathlib `Mathlib/Algebra/Category/ModuleCat/Sheaf/Abelian.lean:40` (built by `abelianOfAdjunction` / `CategoryTheory.Abelian.Transfer`).

So abelian-ness of sheaves of modules is imported from Mathlib and used entirely as an ambient instance; the project never names it.

---

## 4. General-purpose "epi detected on a cover" lemmas (case-insensitive `epi` sweep)

There is **no** standalone lemma of the form "a morphism of sheaves of modules is epi iff epi on a cover." Instead the file achieves chart-wise epi-reflection inline in `tautologicalQuotient_epi`, and provides the affine free-splitting lemmas. Relevant declarations:

- **`tautologicalQuotient_epi` (line 2467)** — `theorem tautologicalQuotient_epi (d r : ℕ) : Epi (tautologicalQuotient d r)`. This is the actual "epi is detected chart-locally" argument. It proves chart-wise epi-ness `hchart` (each `pullback (ι I) .map (tautologicalQuotient)` is epi via `epi_comp'` + `chartQuotientMap_epi`), then reflects to global epi by `constructor; intro Z a b hab; apply Scheme.Modules.pullback_map_jointly_faithful (theGlueData d r); intro I; …; exact (cancel_epi …).mp …` (lines 2508-2518). The reflection engine is the imported **`Scheme.Modules.pullback_map_jointly_faithful`** (GlueDescent.lean line 1210, a faithfulness lemma) combined with `cancel_epi` — there is no dedicated epi-on-cover lemma.

- **`chartQuotientMap_epi` (line 356)** — `lemma chartQuotientMap_epi (d r : ℕ) (I : Finset (Fin r)) (hI : I.card = d) : Epi (chartQuotientMap d r I hI)`. Specific: the chart quotient is a **split** epi (via `IsSplitEpi.mk'` + `.epi`, line 369), split by the coordinate inclusion `s_I`.

- **`exists_section_of_epi_free_spec` (line 1234)** — general: `[Epi ψ] → ∃ Φ, Φ ≫ ψ = 𝟙` for `ψ` between free sheaves on `Spec R`. Any epimorphism between free sheaves on `Spec R` splits (docstring 1221-1229: via the fully faithful `tilde.functor`, `ModuleCat.epi_iff_surjective`, and projectivity of the free module `Module.projective_lifting_property`).

- **`exists_rightInverse_of_epi_matrixEndRect_spec` (line 1286)** — `(M : Matrix … Γ(Spec R,⊤)) (h : Epi (matrixEndRect M)) → ∃ G, M * G = 1`. Matrix form of the above.

- **`exists_rightInverse_of_epi_matrixEndRect` (line 1302)** — same over any affine `S` (`[IsAffine S]`), transported along `S.isoSpec` through `pullback_conj_matrixEndRect`. This is the "epi ⇒ presenting matrix has a right inverse" lemma feeding the Nakayama covering step.

- **`pullback_map_cover_faithful` (line 4934)** and its glue-data sibling **`Scheme.Modules.pullback_map_jointly_faithful`** (GlueDescent.lean line 1210) — cover-faithfulness (equality/mono detection on a cover); used above to reflect epi indirectly via `cancel_epi`, not epi-detection lemmas per se.
