# Higher direct images `Rⁱ f_*` — missing Mathlib infrastructure

File: `AlgebraicJacobian/Cohomology/HigherDirectImage.lean`
Blueprint: `blueprint/src/chapters/Cohomology_HigherDirectImage.tex`
Sources: Stacks 02KE (quasi-coherence), 02KG (relative affine vanishing), 02KH (flat base change).

Scaffolded iter-233 (prover). The file compiles cleanly (exit 0); the four
declarations are present with honest types; all three proof obligations are
`sorry` with documented routes. Below are the precise missing ingredients, in
dependency order, for the plan agent to assign in `mathlib-build` mode.

## Gap 0 (FOUNDATIONAL): `HasInjectiveResolutions X.Modules` / `EnoughInjectives X.Modules`

`higherDirectImage f i F := ((pushforward f).rightDerived i).obj F` requires the
instance `HasInjectiveResolutions X.Modules` (which follows from
`EnoughInjectives X.Modules`). Verified absent from current Mathlib:

- `Abelian X.Modules` IS available (`AlgebraicGeometry.Scheme.Modules.instAbelian`).
- `EnoughInjectives X.Modules` does NOT synthesize.
- `IsGrothendieckAbelian X.Modules` does NOT synthesize. The general instance
  `CategoryTheory.Sheaf.instIsGrothendieckAbelian` is for `Sheaf J A` (a fixed
  value category `A`), NOT for `SheafOfModules R` (modules over a sheaf of rings).
  `CategoryTheory.IsGrothendieckAbelian.enoughInjectives` would then give enough
  injectives, but the Grothendieck-abelian instance for `SheafOfModules` is the
  missing link.

**Current workaround (in the file):** carry `[HasInjectiveResolutions X.Modules]`
(and `[HasInjectiveResolutions X'.Modules]` for base change) as an honest
hypothesis on `higherDirectImage` and all three lemmas. This keeps the
definition axiom-free and sorry-free; the statements are conditional on the
instance. NO sorried instance was introduced (deliberately — that would silently
contaminate every downstream consumer).

**Missing ingredient (exact statement to prove):**
`instance : CategoryTheory.IsGrothendieckAbelian.{u} (X.Modules)` for `X : Scheme.{u}`
(equivalently `EnoughInjectives X.Modules`). `SheafOfModules` over a site is a
Grothendieck abelian category (AB5 + a generator); this is standard but appears
not to be in Mathlib for `SheafOfModules`. Estimated large (multi-hundred LOC) —
proving AB5 (exact filtered colimits) and exhibiting a generator for
`SheafOfModules R`, then `IsGrothendieckAbelian.enoughInjectives`. Once landed,
the `[HasInjectiveResolutions …]` hypotheses can be dropped, making the blueprint
signatures unconditional.

Informal agent NOT consulted: `MOONSHOT_API_KEY` is set but returns HTTP 401
(invalid authentication); no other key (`DEEPSEEK/OPENROUTER/OPENAI/GEMINI_API_KEY`)
present. Conclusion above is from `lean_leansearch` + `lean_local_search` +
direct `#synth` probes.

## Gap 1: explicit description `Rⁱ f_* F = sheafify (V ↦ Hⁱ(f⁻¹V, F|_{f⁻¹V}))`

Needed for BOTH `higherDirectImage_affine_eq_zero` (02KG) and
`higherDirectImage_isQuasiCoherent` (02KE). The right-derived-functor definition
gives no handle on sections over opens of `S`. Mathlib lacks, for
`Scheme.Modules`:

- the comparison `((pushforward f).rightDerived i).obj F ≅`
  `sheafification of (V ↦ Hⁱ(f⁻¹ V, F|_{f⁻¹ V}))` (Stacks
  `cohomology-lemma-describe-higher-direct-images`), and
- vanishing of higher sheaf cohomology of a quasi-coherent sheaf on an affine
  scheme (`Hⁱ(Spec A, M~) = 0` for `i ≥ 1`), at the `Scheme.Modules` level.

With these, affine vanishing (02KG) is short: `f` affine ⇒ `f⁻¹V` affine for
affine `V` ⇒ the defining presheaf vanishes on the affine basis ⇒ sheafification
is `0`.

## Gap 2: relative Mayer–Vietoris for `Scheme.Modules`

Needed for the inductive step of `higherDirectImage_isQuasiCoherent` (02KE):
the long exact sequence
`0 → h_*G → a_*(G|U) ⊕ b_*(G|V) → c_*(G|_{U∩V}) → R¹h_*G → ⋯`
for `U` q.c. open, `V` affine open. Absent from Mathlib at this level.

## Gap 3: Čech-to-cohomology / spectral-sequence comparison

Needed for `flatBaseChange_higherDirectImage_isIso` (02KH, `i ≥ 1`):
Čech cohomology computes sheaf cohomology on a separated scheme with an affine
cover; base change of the Čech complex `Č(𝒰_B, F_B) ≅ Č(𝒰, F) ⊗_A B`; exactness
of `- ⊗_A B` (flatness) commuting with `Hⁱ`; and, for the q.s. case, the
Čech-to-cohomology spectral sequence propagating the iso to the abutment.

NOTE: the theorem is currently stated as `Nonempty (g^*(Rⁱf_*F) ≅ Rⁱf'_*(g'^*F))`
(iso EXISTENCE), because the canonical higher base-change map (the `i ≥ 1`
analogue of `pushforwardBaseChangeMap` from `FlatBaseChange.lean`) is not yet
constructed. Constructing that map (derived-functor naturality / mate of the
base-change 2-cell) is itself a prerequisite if the `IsIso (canonical map)` form
is wanted.
