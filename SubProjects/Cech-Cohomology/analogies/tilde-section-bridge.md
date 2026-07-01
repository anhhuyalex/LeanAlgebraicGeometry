# Analogy: reconciling the three tilde-section accessors into one per-σ AddEquiv

## Mode
api-alignment

## Slug
tilde-bridge

## Iteration
022

## Question
Mathlib's canonical idiom for moving between (1) the `AddCommGrp`-valued underlying
presheaf of `(toPresheafOfModules (Spec R)).obj G`, (2) the `ModuleCat R`-valued sheaf
sections of `modulesSpecToSheaf.obj (tilde M)` / `tilde.toOpen`, and (3) the explicit
`LocalizedModule (powers s_σ) M`; and whether the section-Čech complex should have been
built on a different accessor.

## Project artifact(s)
- `PresheafCech.lean:303-336` — `sectionCechCosimplicial` / `sectionCechComplex`, read
  via accessor (1) (`F.presheaf.obj (op V)`, Ab-valued).
- `CechAcyclic.lean:1165-1170` — `qcohSectionsAwayLocalized` (accessor (2)↔(3),
  `IsLocalizedModule` on `tilde.toOpen`).
- `CechAcyclic.lean:1183-1198` — `qcohRestriction_eq_comparison` (accessor (2) restriction
  = `AwayComparison.comparison`).
- `CechAcyclic.lean:882-900` — `SectionCechModule.dCoeff` / `dCoface` / `dDiff` (accessor
  (3), the `LocalizedModule` complex `D•`).
- `CechAcyclic.lean:1284-1326` — `sectionCechFaceRestr` (accessor (1) restriction) and
  `sectionCech_objD_apply` (objD = alternating sum of `sectionCechFaceRestr`).

## HEADLINE FINDING (empirically verified by `rfl`)

**Accessors (1) and (2) are DEFINITIONALLY EQUAL** — same carrier type, same additive
structure, *and* same restriction maps. There is no coherence iso to build; the blocker
the directive describes dissolves into `rfl`. Three independent `lean_run_code` checks
(all `success: true`, no `sorry`/`axiom`):

```lean
-- (a) carriers agree
example (R : CommRingCat) (M : ModuleCat R) (U : (Spec R).Opens) :
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj (op U) : Type _)
      = (((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M)).presheaf.obj (op U) : Type _) :=
  rfl

-- (b) per-σ AddEquiv (the exact blocked goal) constructs and typechecks
noncomputable example (R : CommRingCat) (M : ModuleCat R) (g : R) :
    ToType (((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M)).presheaf.obj (op (basicOpen g)))
      ≃+ LocalizedModule (Submonoid.powers g) M :=
  (IsLocalizedModule.iso (Submonoid.powers g) (tilde.toOpen M (basicOpen g)).hom).toAddEquiv.symm

-- (c) restriction maps coincide on the underlying function
example (R : CommRingCat) (M : ModuleCat R) {a b : R}
    (i : (basicOpen b : (Spec R).Opens) ⟶ basicOpen a)
    (x : ToType (((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M)).presheaf.obj (op (basicOpen a)))) :
    (ConcreteCategory.hom (((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M)).presheaf.map i.op)) x
      = (((modulesSpecToSheaf.obj (tilde M)).presheaf.map i.op).hom) x :=
  rfl
```

**Why it is defeq** — every functor on the (1)/(2) path is carrier- and add-structure-
preserving:
- `toPresheafOfModules X = SheafOfModules.forget _`, and `forget.obj G = G.val` (an `@[simps]`
  def, `Sheaf.lean:59`, `ModuleCat/Sheaf.lean:67`). `(...).presheaf` is `G.val.presheaf`, the
  `Cᵒᵖ ⥤ Ab` whose `.obj (op U)` carrier is `G.val.obj (op U)`.
- `modulesSpecToSheaf = forgetToSheafModuleCat (op ⊤) hX ⋙ sheafCompose _ (restrictScalars …)`
  (`Tilde.lean:42`). `forgetToSheafModuleCat.obj G` has presheaf
  `(forgetToPresheafModuleCat (op ⊤) hX).obj G.val` (`ModuleCat/Sheaf.lean:98`), whose value
  is `forgetToPresheafModuleCatObjObj (op ⊤) hX G.val Y = (restrictScalars …).obj (G.val.obj Y)`
  — carrier `= G.val.obj Y` by the `rfl` lemma `forgetToPresheafModuleCatObjObj_coe`
  (`ModuleCat/Presheaf.lean:377`).
- `ModuleCat.restrictScalars` (`ChangeOfRings.lean:85`, `RestrictScalars.obj'`) and
  `sheafCompose` leave the carrier and AddCommGroup untouched (only the scalar ring changes);
  the restriction map of accessor (2) is `forgetToPresheafModuleCatObjMap`, whose `.hom` is
  `fun x => G.val.map f x` (`ModuleCat/Presheaf.lean:387`, rfl-lemma
  `forgetToPresheafModuleCatObjMap_apply`) — literally accessor (1)'s restriction.

The nearest *named* Mathlib coherence is `SheafOfModules.toSheafCompSheafToPresheafIso`
(`ModuleCat/Sheaf.lean:109`), which is `Iso.refl _` — confirming Mathlib's design that these
forgetful coherences are definitional. For the ModuleCat-valued `modulesSpecToSheaf` path the
prover does not even need an iso: `rfl` discharges it.

## Decisions identified

### Decision: coherence iso (1)↔(2)
- **Mathlib idiom**: definitional identity — the underlying-Ab presheaf of a
  `SheafOfModules` and the `forget₂ (ModuleCat R) Ab` of its `forgetToSheafModuleCat`
  sections are the *same* presheaf up to scalar ring. Cite: `SheafOfModules.forget`
  (`ModuleCat/Sheaf.lean:67`), `forgetToPresheafModuleCatObjObj_coe`
  (`ModuleCat/Presheaf.lean:377`), `ModuleCat.restrictScalars`/`RestrictScalars.obj'`
  (`ChangeOfRings.lean:85`), `SheafOfModules.toSheafCompSheafToPresheafIso = Iso.refl`
  (`ModuleCat/Sheaf.lean:109`).
- **Project's path**: directive proposed *building a bridge iso*. Unnecessary.
- **Gap**: identical (defeq). No bridge lemma required.
- **Verdict**: PROCEED — use `rfl`; do not build or search for a coherence iso.

### Decision: Ab-valued vs ModuleCat-valued section complex
- **Mathlib idiom**: the homological-exactness toolchain the proof rides on is Ab-shaped:
  `ShortComplex.ab_exact_iff_function_exact` (already used,
  `CechAcyclic.lean:1256`), `Function.Exact.of_ladder_addEquiv_of_exact`
  (`Mathlib.Algebra.Exact.Basic`), `alternatingCofaceMapComplex Ab`, `preadditiveYoneda`.
- **Project's path**: section complex lives in `Ab` (accessor 1).
- **Gap**: identical — the Ab choice *is* the aligned one. The (1)↔(3) bridge to
  `LocalizedModule` is `rfl` + one `IsLocalizedModule.iso`, so the Ab detour the directive
  worried about does not exist.
- **Cost of the rejected alternative (rebuild on ModuleCat)**: would force re-deriving the
  *entire* downstream stack in ModuleCat — `freeYonedaHomAddEquiv`,
  `homCechSectionCosimplicialIso`, `cechComplex_hom_identification`, `homCechComplexMapOpIso`
  (all proved iter-019/020, all Ab-valued) plus swapping `ab_exact_iff` for
  `moduleCat_exact_iff` — for **zero** correctness benefit. Massive churn.
- **Verdict**: PROCEED — keep the Ab-valued `sectionCechComplex`. Do NOT rebuild.

### Decision: AddEquiv-from-two-localisations + exactness transport
- **Mathlib idiom**: `IsLocalizedModule.iso S f : LocalizedModule S M ≃ₗ[R] M'`
  (`Mathlib.Algebra.Module.LocalizedModule.Basic`, verified present); take `.toAddEquiv.symm`.
  Uniqueness/naturality via `IsLocalizedModule.iso_symm_comp`
  (`↑(iso S f).symm ∘ₗ f = mkLinearMap S M`), `iso_mk_one`, and `IsLocalizedModule.ext`.
  Transport exactness with `Function.Exact.of_ladder_addEquiv_of_exact`
  (`Mathlib.Algebra.Exact.Basic`, verified present — signature takes three `≃+`, two square
  commutes `g ∘ e = e ∘ f` as `AddMonoidHom`, and `Function.Exact f₁₂ f₂₃`).
- **Project's path**: directive proposed exactly this. Correct.
- **Gap**: identical.
- **Verdict**: ALIGN_WITH_MATHLIB (this is the route; in-proposal, so adopt directly).

## Recommendation

**Bridge the accessors via defeq — do NOT rebuild on ModuleCat.** Concrete path:

1. **Per-σ AddEquiv** (verified to typecheck):
   ```lean
   haveI := qcohSectionsAwayLocalized M s σ      -- IsLocalizedModule (powers (∏ s_{σk})) (toOpen …).hom
   (IsLocalizedModule.iso _ (tilde.toOpen M (⨅ k, basicOpen (s (σ k)))).hom).toAddEquiv.symm
   ```
   Its target is *defeq* to `ToType (((toPresheafOfModules (Spec R)).obj (tilde M)).presheaf.obj
   (op (⨅ k, basicOpen (s (σ k)))))` (accessor 1) — no transport tactic needed.

2. **Per-coface naturality square** (`φ_σ` intertwines `sectionCechFaceRestr` with `dCoface`):
   - `sectionCechFaceRestr … = F.presheaf.map (homOfLE …).op` (accessor 1) `=` (by check (c),
     defeq) accessor (2) restriction `(modulesSpecToSheaf.obj (tilde M)).presheaf.map (…).op`.
   - `qcohRestriction_eq_comparison M i hb` rewrites accessor (2) restriction to
     `AwayComparison.comparison (toOpen M (D a)).hom (toOpen M (D b)).hom hb`.
   - `dCoface` is `AwayComparison.comparison (mkLinearMap …) (mkLinearMap …) …` (definition).
   - `φ_σ`, via `IsLocalizedModule.iso_symm_comp`, satisfies `↑φ_σ ∘ₗ (toOpen …).hom = mkLinearMap …`.
   - Close the square with `IsLocalizedModule.ext (powers …) (toOpen … or mkLinearMap …)` or the
     project's `AwayComparison.comparison_unique` (`CechAcyclic.lean:549`): both composites agree
     after precomposing with the localisation structure map (reduce to `comparison_apply` /
     `iso_mk_one`).

3. **Degreewise product AddEquiv + ladder**: upgrade `sectionCechProductEquiv`
   (`CechAcyclic.lean:1221`, currently an `Equiv`) to an `AddEquiv` for the Ab `∏ᶜ` — the one
   genuine (small) piece of work; follow the additivity pattern of `freeYonedaHomAddEquiv`
   (`PresheafCech.lean:274`, `Concrete.productEquiv` componentwise + `Pi`). Compose with `φ_σ`
   to get `(sectionCechCosimplicial …).obj [p] ≃+ D^p`. Assemble the two ladder squares from
   `sectionCech_objD_apply` (objD = alt-sum of `sectionCechFaceRestr`) and `dDiff_apply`
   (dDiff = alt-sum of `dCoface`) + step 2 per coface. Feed to
   `Function.Exact.of_ladder_addEquiv_of_exact` with `dDiff_exact`, then
   `sectionCech_isZero_homology_of_objD_exact` (`CechAcyclic.lean:1247`) closes positive-degree
   vanishing.

**Cost of NOT aligning**: none for keeping Ab. The only avoidable cost is *thinking* a
coherence iso must be built — it must not; that would be dead infrastructure around a `rfl`.
