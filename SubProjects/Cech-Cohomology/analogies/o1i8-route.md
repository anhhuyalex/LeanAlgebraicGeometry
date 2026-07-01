# Analogy: shortest Mathlib-aligned path to 01I8 (`[IsQuasicoherent F] → IsIso F.fromTildeΓ` on `Spec R`)

## Mode
api-alignment

## Slug
o1i8-route

## Iteration
036

## Question
Given Mathlib's `tilde`/`Presentation`/`QuasicoherentData` layer, what is the SHORTEST
Mathlib-aligned path to `[IsQuasicoherent F] → IsIso F.fromTildeΓ` on an affine, and does it
let the project DROP Route-P sub-steps (P1a affine-restriction, P2 global-generation,
P3 kernel-qcoh, `tildePreservesFiniteLimits`)?

## Project artifact(s)
- `QcohTildeSections.lean` — conditional + presentation + genSections forms of 01I8;
  `isLocalizedModule_of_span_cover` (P1b, done) is the finite-spanning-cover descent engine.
- `TildeExactness.lean` — `tildePreservesFiniteLimits` build (stalk crux `stalkMapₗ_eq` done).
- `QcohRestrictBasicOpen.lean` — P1a as `F|_{D(f)} ≅ tilde(M_f)` (L2 blocked: tilde base-change absent).

## The two candidate routes (both bottom out at Stacks 01HV localization-of-sections)

- **Route A (global Presentation):** `IsQuasicoherent F` ⟹ global `F.Presentation`
  (= `F.GeneratingSections` σ + `(kernel σ.π).GeneratingSections` τ) ⟹
  `isIso_fromTildeΓ_of_presentation` (Tilde.lean:398). The project's
  `isIso_fromTildeΓ_of_genSections` already wraps the last step axiom-clean.
- **Route B (direct sections-localization):** `fromTildeΓ : tilde(ΓF) → F` is iso ⟺ iso on the
  basis `{D(f)}` (or on stalks). Its `D(f)`-component is exactly
  `IsLocalizedModule.lift (.powers f) (toOpen ...) (ΓF → Γ(D f,F))` (Tilde.lean:200-203), so the
  component is iso ⟺ the **section-restriction map `Γ(X,F) → Γ(D(f),F)` is `IsLocalizedModule (.powers f)`**.
  Descend over a finite `D(g_i)` cover via the *already-built* `isLocalizedModule_of_span_cover`.

## Decisions identified

### Decision 1 — Local `QuasicoherentData` → global `Presentation` on affine: does Mathlib provide it?
- **Mathlib idiom**: `QuasicoherentData.bind` (Quasicoherent.lean:360) only **merges covers**
  (`I := Σ i, (D i).I`) — local data → local data. `IsQuasicoherent` is `Nonempty QuasicoherentData`
  (local). Mathlib has NO functor `QuasicoherentData M → Presentation M` and NO
  qcoh-closed-under-kernels / abelian-subcategory lemma (`grep` of
  `Mathlib/Algebra/Category/ModuleCat/Sheaf/` for `IsQuasicoherent.*kernel|abelian|exact`
  returns nothing). `Presentation.isQuasicoherent` only goes the easy way (global → local).
- **Project's path**: `isIso_fromTildeΓ_of_genSections` + Handoff steps 1–3.
- **Gap**: NEEDS_MATHLIB_GAP_FILL. The local→global step is genuinely Stacks 01I8 / Hartshorne II.5.5;
  Mathlib does not shortcut it. The hard analytic core is **01HV localization-of-sections**
  (`Γ(D(f),F)=Γ(X,F)_f`), absent from Mathlib for abstract qcoh `F`.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision 2 — Is `tildePreservesFiniteLimits` needed, and is the "no toSheaf" blocker false?
- **Blocker claim is FALSE**: `SheafOfModules.toSheaf R` exists AND **reflects isomorphisms**
  (`Presheaf/Sheafification.lean:41`), preserves finite limits (`Sheaf/Limits.lean:118`), so it is
  `ReflectsFiniteLimits` (`Finite.lean:175 reflectsFiniteLimits_of_reflectsIsomorphisms`). Then
  `preservesFiniteLimits_of_reflects_of_preserves (tilde.functor R) (toSheaf R)` (`Finite.lean:163`)
  reduces `tildePreservesFiniteLimits` to **`PreservesFiniteLimits (tilde.functor R ⋙ toSheaf R)`** —
  i.e. tilde-as-a-TopCat-sheaf preserves kernels, which is stalk-wise flatness of localization
  (stalk of `tilde M` at `x` = `M_{p_x}`, Tilde.lean:131). That residual is exactly the project's
  done stalk crux `stalkMapₗ_eq`/`tilde_stalkFunctor_map_toStalk`. So the build is ~1 lemma from done,
  and `toSheaf` is a CLEANER scaffold than the project's `tildePreservesFiniteLimits_of_toPresheaf`
  (which routed through PresheafOfModules objectwise — harder, since `Γ(U,tilde M)` for general `U`
  is not a localization).
- **But it is NOT on the shortest path**: `isIso_fromTildeΓ_of_presentation` does **not** use tilde
  exactness (it uses tilde preserving *colimits* as a left adjoint). `tildePreservesFiniteLimits` is
  needed only to make Route-A step P3 (kernel σ.π quasicoherent) work — and even there it does NOT
  cleanly discharge kernel-qcoh for an *abstract* `F` (that still needs qcoh-closed-under-kernels,
  which Mathlib lacks). Route B needs none of it.
- **Verdict**: DIVERGE_INTENTIONALLY — drop from the critical path (keep the done stalk lemmas as
  dormant assets; do NOT spend iters finishing it for Route A).

### Decision 3 — P1a framing: sheaf-iso/base-change vs `IsLocalizedModule` of section-restriction
- **Mathlib idiom**: Mathlib states the whole `tilde`/`fromTildeΓ` local theory in the
  **`IsLocalizedModule`** language: `toOpen M (D f)` is `IsLocalizedModule (.powers f)`
  (Tilde.lean:115), `toStalk` is `IsLocalizedModule x.primeCompl` (Tilde.lean:131), and
  `fromTildeΓ`'s `D(f)`-component is literally `IsLocalizedModule.lift` of the section-restriction
  (Tilde.lean:200-203). The project's own P1b `isLocalizedModule_of_span_cover` and STRATEGY P1
  (`Γ(D(f),F)=Γ(X,F)_f via IsLocalizedModule.mk`) are already in this language.
- **Project's path (shipped)**: `QcohRestrictBasicOpen` builds `F|_{D(f)} ≅ tilde(M_f)` via
  `Scheme.Modules.restrict` + `basicOpenIsoSpecAway` + a presentation transport, whose L2
  `tilde_restrict_basicOpen` needs a **tilde base-change** lemma absent from Mathlib.
- **Gap**: divergent-with-cost. The sheaf-iso/base-change packaging is STRICTLY heavier than needed
  and hits an absent-Mathlib wall, when the lighter `IsLocalizedModule (.powers f) (Γ(X,F)→Γ(D(f),F))`
  packaging (a) is what `fromTildeΓ`-on-basic-opens actually consumes, (b) descends via the already
  built `isLocalizedModule_of_span_cover`, and (c) avoids base change entirely.
- **Verdict**: ALIGN_WITH_MATHLIB.

## Recommendation
Target **Route B**. Reframe P1a from `F|_{D(f)} ≅ tilde(M_f)` to
`IsLocalizedModule (.powers f) (sectionRestriction : Γ(X,F) → Γ(D(f),F))` for quasi-coherent `F`,
proved by `isLocalizedModule_of_span_cover` over a finite `D(g_i)` cover on which the given
`QuasicoherentData` presentations make `F` concretely tilde-of-a-module (no base change). Then close
01I8 by: `forget`/`toSheaf` reflects isos ⟹ check `fromTildeΓ` on the basis `{D(f)}` ⟹ each
component is `IsLocalizedModule.lift` of an `IsLocalizedModule` map ⟹ iso. This drops P1a's
base-change wall, `tildePreservesFiniteLimits`, P2 global-generation, and P3 kernel-qcoh from the
critical path. Keep `isIso_fromTildeΓ_of_genSections` and the `tildePreservesFiniteLimits` stalk
lemmas as correct-but-dormant assets (Route A remains a fallback but is strictly longer and needs the
unsupported kernel-qcoh fact).
