# Analogy: δ/μ-side monoidal-adjunction idiom for `hcompat` (mate oplax δ = strong μ⁻¹)

## Mode
api-alignment

## Slug
recon022

## Iteration
022

## Question
Does Mathlib already provide the idiom the project hand-reconciles in
`pullbackTensorMap_isIso_of_isOpenImmersion` (the `e`+`hcompat` step), namely:
strong-monoidal left adjoint ⇒ `Adjunction.IsMonoidal` ⇒ mate oplax `δ = μIso.inv`;
mate/conjugate uniqueness for oplax structures; and restrict⊣extend monoidal?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:4139` — `pullbackTensorMap_isIso_of_isOpenImmersion`; residual `hcompat : (leftAdjointOplaxMonoidal hadj).δ M N = μIsoβ.inv`.
- `…:1138` — `presheafPushforwardLaxMonoidal φ` (project lax on `pushforward φ`, built independently from `restrictScalars φ'`).
- `…:1160` — `presheafPullbackOplaxMonoidal φ = (pullbackPushforwardAdjunction φ).leftAdjointOplaxMonoidal`.
- `…:524-545` — `hadj := pushforwardPushforwardAdj …`; `pushforward β` STRONG via `restrictScalarsMonoidalOfBijective β'`.
- `…:1476` — `presheafUnit_comp_map_eta` (η-side, already fires via `Adjunction.unit_app_unit_comp_map_η`).

## Mathlib facts located (pin b80f227, `Mathlib/CategoryTheory/Monoidal/Functor.lean`)

| Decl | Line | Statement |
|---|---|---|
| `Adjunction.rightAdjointLaxMonoidal` | 897 | `[F.OplaxMonoidal] → G.LaxMonoidal` (the mate: `μ_G := homEquiv(δ_F ≫ (counit⊗counit))`). |
| `Adjunction.IsMonoidal` (class, Prop) | 952 | fields `leftAdjoint_ε : ε G = unit ≫ G.map (η F)`, `leftAdjoint_μ X Y : μ G X Y = unit ≫ G.map (δ F _ _ ≫ (counit X ⊗ₘ counit Y))`. |
| free instance | 957 | `letI := adj.rightAdjointLaxMonoidal; adj.IsMonoidal` — mate ⇒ IsMonoidal, by `rfl`. |
| `unit_app_tensor_comp_map_δ` | 973 | δ-side twin of `unit_app_unit_comp_map_η`: `unit (X⊗Y) ≫ G.map (δ F X Y) = (unit X ⊗ₘ unit Y) ≫ μ G _ _`. Needs `[IsMonoidal]`. |
| `map_μ_comp_counit_app_tensor` | 983 | `F.map (μ G X Y) ≫ counit (X⊗Y) = δ F _ _ ≫ (counit X ⊗ₘ counit Y)`. Needs `[IsMonoidal]`. |
| `Adjunction.leftAdjointOplaxMonoidal` | 1009 | `[G.LaxMonoidal] → F.OplaxMonoidal` (the mate: `δ_F X Y := (homEquiv).symm((unit⊗unit) ≫ μ_G)`). |
| free instance | 1053 | `letI := adj.leftAdjointOplaxMonoidal; adj.IsMonoidal`. |
| `Adjunction.laxMonoidalEquivOplaxMonoidal` | 1070 | **`G.LaxMonoidal ≃ F.OplaxMonoidal`** (`toFun = leftAdjointOplaxMonoidal`, `invFun = rightAdjointLaxMonoidal`). The conjugate-UNIQUENESS lemma (Q2). |
| `Functor.Monoidal` | 367 | extends `LaxMonoidal` + `OplaxMonoidal`; `μ_δ`, `δ_μ` make μ,δ mutually inverse. |
| `Functor.Monoidal.μIso` / `instance IsIso (δ F)` | 389/396 | strong ⇒ `δ F X Y = (μIso F X Y).inv = μIso.inv`. So `pushforward β` strong ⇒ its derived-oplax `δ = μIsoβ.inv`. |
| `ModuleCat.instLaxMonoidalRestrictScalars` | `…/ModuleCat/Monoidal/Adjunction.lean:102` | Mathlib **DEFINES** `restrictScalars f` lax `:= (extendRestrictScalarsAdj f).rightAdjointLaxMonoidal` — i.e. as the mate of the STRONG `extendScalars f`. (Q3: yes, restrict⊣extend IS known monoidal — but only the ModuleCat-fibre version; no PresheafOfModules.) |

## Decisions identified

### Decision: is `hcompat` reinventing a Mathlib idiom?
- **Mathlib idiom**: `Adjunction.IsMonoidal` + the δ-side lemmas (973/983) + the Equiv `laxMonoidalEquivOplaxMonoidal` (1070). `hcompat` ⟺ `hadj.IsMonoidal` (the `leftAdjoint_μ` field, transposed). The manual `e`+`hcompat` re-derives by hand what these decls package.
- **Gap**: divergent-with-cost. The SCAFFOLDING exists; the project bypasses it.
- **Verdict**: ALIGN_WITH_MATHLIB (for the scaffolding) — use `Adjunction.IsMonoidal hadj` as the carrier and the named lemmas, not a bespoke `e`/`hcompat`.

### Decision: does strongness ALONE discharge `hcompat` (a free constructor)?
- **Mathlib idiom**: NO blanket "`F.Monoidal` ⇒ `adj.IsMonoidal`". `IsMonoidal` is a compatibility between the SPECIFIC oplax-`F` / lax-`G` PAIR. It is free (line 957) ONLY when `G`'s lax IS `rightAdjointLaxMonoidal` (the mate). The project's `presheafPushforwardLaxMonoidal φ'` is built independently (general φ, no adjoint), so it is NOT definitionally the mate.
- **Gap**: NEEDS_MATHLIB_GAP_FILL is wrong here — the missing piece is a PROJECT proof, not a Mathlib decl. The genuine content "project lax on `pushforward φ'` = `hadj.rightAdjointLaxMonoidal` (mate of `pushforward β`'s strong structure)" is irreducible and must be proven sectionwise.
- **Verdict**: PROCEED on the obligation existing; ALIGN_WITH_MATHLIB on how to package it.

## Recommendation
Replace the bespoke `e`+`hcompat` with: **(1)** prove `instance : hadj.IsMonoidal`
(`pushforward β` carrying its STRONG `Monoidal`→`OplaxMonoidal`, `pushforward φ'` carrying
`presheafPushforwardLaxMonoidal`). Its two fields are sectionwise `restrictScalars` identities
— prove by `homEquiv`-injectivity + `tensor_ext (fun _ _ ↦ rfl)`, exactly the style of
`ModuleCat/Monoidal/Adjunction.lean` (`μIso_inv_natural_left := …homEquiv…injective (tensor_ext …)`).
**(2)** Discharge `hcompat` from `[hadj.IsMonoidal]`: `IsMonoidal` is precisely field-equality
`project-lax = rightAdjointLaxMonoidal[strong-oplax]`, so by `laxMonoidalEquivOplaxMonoidal`
`right_inv` (`leftAdjointOplaxMonoidal (rightAdjointLaxMonoidal O) = O`) the mate oplax on
`pushforward β` equals its strong oplax, whence `(leftAdjointOplaxMonoidal hadj).δ M N = δ_strong = μIsoβ.inv`
via `Functor.Monoidal.μIso`/`δ` (`μIso_inv`). The δ-side lemmas `unit_app_tensor_comp_map_δ` (973)
and `map_μ_comp_counit_app_tensor` (983) are the exact twins of the η-side `unit_app_unit_comp_map_η`
the project already uses — they become available the moment `hadj.IsMonoidal` is in scope.
The ONE irreducible obligation is step (1); strongness does not give it for free.
