# Analogy: Γ on affine quasi-coherent modules sends epis to surjections (seam 2)

## Mode
api-alignment

## Slug
gf-gamma-exact

## Iteration
047

## Question
For `lem:gf_affine_qcoh_Gamma_epi`: on `V ≅ Spec B`, the global-sections functor on
quasi-coherent `O_V`-modules sends a sheaf epimorphism `π : G ↠ F` to a SURJECTIVE
`B`-module map `Γ(π)`. The blueprint currently hand-waves "global sections on affine are
exact." What is the Mathlib-grounded mechanism?

## Project artifact(s)
- `blueprint/.../Picard_FlatteningStratification.tex:1657-1696` — `lem:gf_affine_qcoh_Gamma_epi` (seam 2), proof hand-waves affine exactness.
- `AlgebraicJacobian/Picard/QuotScheme.lean:454-700` — project's object-wise gap1/gap2 (`isLocalizedModule_*`, `isIso_fromTildeΓ_*`).

## Headline finding
**The framing in the directive is now obsolete.** It assumes the qcoh≃Mod descent exists
only object-wise. But **Mathlib `Mathlib/AlgebraicGeometry/Modules/Tilde.lean` now carries
the full GLOBAL tilde–Γ adjunction**, including the natural counit, the unit iso, faithfulness,
and the essential-image characterization. The seam-2 lemma is a ~12-line consequence of it.
No H¹-vanishing build, no new equivalence, no exactness-from-scratch.

## Decisions identified

### Decision: how to obtain "sheaf epi of qcoh on affine ⟹ surjective on Γ"
- **Mathlib idiom**: use the adjunction `tilde.functor R ⊣ moduleSpecΓFunctor` and the fact
  that a **faithful** functor reflects epimorphisms. Cite:
  - `AlgebraicGeometry.moduleSpecΓFunctor : (Spec (.of R)).Modules ⥤ ModuleCat R`
    (Tilde.lean:50) — THIS is `Γ` on affine modules (`modulesSpecToSheaf ⋙ forget ⋙ evaluation at op ⊤`).
    So the blueprint's `Γ(π)` = `moduleSpecΓFunctor.map π`.
  - `AlgebraicGeometry.tilde.adjunction : tilde.functor R ⊣ moduleSpecΓFunctor` (Tilde.lean:279).
  - counit `= AlgebraicGeometry.Scheme.Modules.fromTildeΓNatTrans : moduleSpecΓFunctor ⋙ tilde.functor ⟶ 𝟭`
    (Tilde.lean:248), whose **`.app M := M.fromTildeΓ` definitionally** (Tilde.lean:250) — so
    `fromTildeΓ` IS the adjunction counit and IS natural; `.naturality` is the carrying square.
  - `AlgebraicGeometry.instFaithful…tilde.functor` (`tilde.functor R` is `Faithful`).
  - `CategoryTheory.Functor.reflectsEpimorphisms_of_faithful` (instance: `Faithful ⟹ ReflectsEpimorphisms`).
  - `CategoryTheory.Functor.epi_of_epi_map` (`[ReflectsEpimorphisms] → Epi (F.map f) → Epi f`).
  - `ModuleCat.epi_iff_surjective` (Epi in `ModuleCat R` ↔ surjective).
- **Project's current path**: hand-rolled object-wise isos (`isLocalizedModule_basicOpen`,
  `isIso_fromTildeΓ_*`) plus a blueprint hand-wave that affine Γ is exact.
- **Gap**: divergent-with-cost — the object-wise machinery cannot carry an epi; the global
  adjunction can, and is already in Mathlib.
- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision: where do `[IsIso G.fromTildeΓ]`/`[IsIso F.fromTildeΓ]` come from
- **Mathlib idiom**: `AlgebraicGeometry.isIso_fromTildeΓ_iff : IsIso M.fromTildeΓ ↔ (tilde.functor R).essImage M`
  (Tilde.lean) and `isIso_fromTildeΓ_of_presentation` (a presented module forces it). For the
  free source `O_V^{⊕I}` (presented) this is immediate; for the finite-type `F` the project's
  G1-core (`isIso_fromTildeΓ_of_isLocalizedModule_restrict`, `QuotScheme.lean:614`) supplies it
  from quasi-coherence.
- **Verdict**: PROCEED (project's quasicoherence→IsIso bridge is the right feeder; Mathlib has
  no `IsQuasicoherent`-predicate version, only essImage / IsLocalizing).

## Proof skeleton (Mathlib-grounded, ~12 lines)
```lean
open CategoryTheory AlgebraicGeometry in
theorem gf_affine_qcoh_Gamma_epi {R : CommRingCat} {G F : (Spec R).Modules}
    (π : G ⟶ F) [Epi π] [IsIso G.fromTildeΓ] [IsIso F.fromTildeΓ] :
    Function.Surjective (moduleSpecΓFunctor.map π).hom := by
  rw [← ModuleCat.epi_iff_surjective]
  -- counit naturality: (Γ⋙~).map π ≫ F.fromTildeΓ = G.fromTildeΓ ≫ π
  have hnat := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality π
  -- ⇒ ~(Γ π) = G.fromTildeΓ ≫ π ≫ inv F.fromTildeΓ  : composite of iso, epi, iso ⇒ Epi
  haveI : Epi ((tilde.functor R).map (moduleSpecΓFunctor.map π)) := by
    have h : (tilde.functor R).map (moduleSpecΓFunctor.map π)
           = G.fromTildeΓ ≫ π ≫ inv F.fromTildeΓ := by
      -- rearrange hnat (fromTildeΓNatTrans.app X = X.fromTildeΓ, (𝟭).map π = π)
      simp only [Functor.comp_map, Functor.id_map] at hnat
      rw [← hnat]; simp
    rw [h]; infer_instance
  -- tilde.functor is faithful ⇒ reflects epis
  exact (tilde.functor R).epi_of_epi_map ‹_›
```
(Exact `simp`/`rw` glue may need a line or two of tuning, but every ingredient is a named
Mathlib decl. `Γ(π)` in the blueprint = `moduleSpecΓFunctor.map π`; its `.hom` is the B-linear map.)

## Recommendation
Restate `gf_affine_qcoh_Gamma_epi` against `moduleSpecΓFunctor` + `tilde.adjunction`, taking
`[Epi π]` and the two `IsIso _.fromTildeΓ` instances as hypotheses. Drop the "affine Γ is exact"
hand-wave in the blueprint proof and replace it with: *the tilde counit is iso on quasi-coherent
objects, so the counit-naturality square makes `~(Γπ)` an epi; `tilde.functor` is faithful, hence
reflects epimorphisms, so `Γπ` is epi in `ModuleCat R`, i.e. surjective.* This is the structural
content of "H¹(affine,qcoh)=0" delivered for free by Mathlib's adjunction — no cohomology build.
Mechanism ranking: **(b)+(a) merged via the adjunction counit is the answer; (c) genuine
H¹-vanishing is NOT needed.**
