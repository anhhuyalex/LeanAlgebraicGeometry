# Analogy: Route B for Stacks 01I8 — the affine base-change bridge

## Mode
api-alignment

## Slug
bridge

## Iteration
037

## Question
Route B reduces 01I8 (`IsQuasicoherent F → IsIso F.fromTildeΓ` on `Spec R`) to the keystone
"for qcoh `F`, `f ∈ R`, the section-restriction `ρ_f : Γ(Spec R,F) → Γ(D(f),F)` is
`IsLocalizedModule (powers f)`", descended over a finite standard cover via the DONE
`isLocalizedModule_of_span_cover`. The per-`gⱼ` step transports `F` to `D(gⱼ) ≅ Spec R_{gⱼ}`,
gives the transported module a global `Presentation`, and applies the DONE
`section_isLocalizedModule_of_presentation`. What is the cleanest Mathlib-aligned way to build the
remaining glue, and does Route B close without a third absent-Mathlib wall?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/QcohTildeSections.lean:408-504` — local-model lemmas
  (`tilde_section_isLocalizedModule`, `section_isLocalizedModule_of_isIso_fromTildeΓ`,
  `section_isLocalizedModule_of_presentation`) + span-cover descent — all DONE.
- `AlgebraicJacobian/Cohomology/QcohRestrictBasicOpen.lean:38-59` — `modulesRestrictBasicOpen`,
  `modulesRestrictBasicOpenIso : modulesRestrictBasicOpen f F ≅ pullback (specAwayToSpec f) F`,
  `specAwayToSpec_eq : specAwayToSpec f = Spec.map (algebraMap R R_f)` — DONE.

## Key Mathlib facts located (cited)

Tilde (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`):
- `Scheme.Modules.fromTildeΓ` (195); `isIso_fromTildeΓ_iff : IsIso M.fromTildeΓ ↔ essImage (tilde.functor R)` (340);
  `isIso_fromTildeΓ_of_presentation (M) (P : M.Presentation) : IsIso M.fromTildeΓ` (398).
- `instance IsLocalizedModule (.powers f) (toOpen M (basicOpen f)).hom` (115) — the localized-sections
  fact, but only for `tilde M`.
- The entire `IsQuasicoherent` section is 344–410; it ENDS at `isIso_fromTildeΓ_of_presentation`.
  **There is NO `IsLocalizing` predicate and NO `isIso_fromTildeΓ_iff_isLocalizing`.** The directive's
  conjecture that the keystone is "definitionally `IsLocalizing`" is FALSE — no such decl exists.

Quasicoherent (`Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`):
- `structure Presentation` (44) = `generators : M.GeneratingSections` + `relations : (kernel π).GeneratingSections`.
- `Presentation.ofIsIso (f : M ⟶ N) [IsIso f] (σ : M.Presentation) : N.Presentation` (132).
- `Presentation.map (F : SheafOfModules R ⥤ SheafOfModules S) [PreservesColimitsOfSize F]
   (η : F.obj (unit R) ≅ unit S) : Presentation (F.obj M)` (179) — **transports a presentation along
   any colimit-preserving, unit-preserving functor, even across different sites.**
- `structure QuasicoherentData M` (201): a cover `X : I → C`, `coversTop`, and a
  `presentation (i) : (M.over (X i)).Presentation` (208) — a FULL presentation per cover member.
- `QuasicoherentData.ofIsIso (f : M ⟶ N) [IsIso f] (σ : M.QuasicoherentData) : N.QuasicoherentData`
  (323), with `presentation i := Presentation.ofIsIso (f.over (X i)) (σ.presentation i)` (328).
- `IsQuasicoherent` (249); `IsQuasicoherent.of_coversTop` (377).

Pushforward / `over` (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PushforwardContinuous.lean`):
- `over (M) (X) := (pushforward (𝟙 _)).obj M : SheafOfModules (R.over X)` (53) — restriction lives in
  the LOCALIZED-SITE picture (`Over X` of the opens site).
- `instance IsLeftAdjoint (pushforward (𝟙 (R.over x)))` (282) ⟹ `over` preserves colimits.
- `pushforwardPushforwardEquivalence (eqv : C ≌ D) … : SheafOfModules R ≌ SheafOfModules S` (~305) —
  **a site equivalence + compatible ring-sheaf data yields an EQUIVALENCE of sheaf-of-modules
  categories.** This is the engine that bridges two pictures of "restriction to an open".

Pullback (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`, `…/PullbackContinuous.lean`):
- `(pullback φ).IsLeftAdjoint` (PullbackContinuous 63); `pullbackObjUnitToUnit φ : (pullback φ).obj (unit S) ⟶ unit R`
  (88) with `instance [F.Final] : IsIso (pullbackObjUnitToUnit φ)` (105); `freeFunctorCompPullbackIso` (144).
  ⟹ `pullback` along a final-site map preserves colimits AND the unit-as-iso, so `Presentation.map` applies.

Scheme restriction (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`):
- `restrictFunctor f := SheafOfModules.pushforward (F := f.opensFunctor) …` (319) — scheme picture
  (opens of the open SUBSCHEME), `(restrictFunctor f).IsLeftAdjoint` (356).
- `restrict_obj : Γ(M.restrict f, U) = Γ(M, f ''ᵁ U) := rfl` (328) — **section comparison is definitional.**
- `restrictFunctorIsoPullback : restrictFunctor f ≅ pullback f` (371).

## Decisions identified

### Decision: Q1 — section comparison `Γ(Spec R_g, transported F) ≅ Γ(U, F)`, linear, restriction-compatible
- **Mathlib idiom**: `restrict_obj` (Sheaf.lean:328) makes `Γ(M.restrict f, U) = Γ(M, f ''ᵁ U)` hold by
  `rfl`; `restrict_map` (331) does the same for the restriction maps. The transported sections ARE the
  sections of `F` over the image open, definitionally, with the presheaf `.map` as the linear comparison.
  The project already exploits this style (the local-model proofs read `(…).presheaf.map (homOfLE …).op).hom`).
- **Project path**: read sections through `modulesSpecToSheaf.obj (…).presheaf.map`; compatibility with
  further restriction to `D(f)∩U` is presheaf functoriality (`map_comp`).
- **Gap**: identical — no parallel API. Cheap, `rfl`/naturality bookkeeping.
- **Verdict**: **PROCEED**.

### Decision: Q2 — presentation of the transported module
- **Mathlib idiom**: TWO composable transporters exist. `Presentation.map` (Quasicoherent.lean:179)
  carries a presentation along a colimit-preserving + unit-iso functor (the `over`-restriction and the
  `pullback`/`restrict` functors all qualify: left adjoints + `pullbackObjUnitToUnit` iso under Final /
  `over` unit-iso). `Presentation.ofIsIso` (132) carries it across an iso. Nested `over` is supported
  (Quasicoherent.lean:353-354 carries the `(J.over X).over Y` instances), so restricting
  `Presentation (F.over Uᵢ)` further to `F.over D(gⱼ)` (`D(gⱼ) ⊆ Uᵢ`) is in-framework.
- **Project path**: none yet — the project's `modulesRestrictBasicOpen` is the scheme `restrict`/`pullback`
  transport, but the presentation SOURCE (`QuasicoherentData`) lives in the `over` picture, and the two are
  never connected.
- **Gap**: divergent-with-cost. The transporters exist, but they bottom out on the picture bridge (Q4/B3):
  `Presentation (F.over U)` is over the localized site `(Opens Spec R).over U`, whereas the project's
  tilde machinery needs a `Presentation` of an honest `(Spec R_g).Modules`. Connecting them needs B3.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (the transport is free; the bridge it rides on is the gap).

### Decision: Q3 — quasicoherence locality / `IsLocalizing`
- **Mathlib idiom**: NONE for the pieces the directive hoped for. `IsLocalizing` and
  `isIso_fromTildeΓ_iff_isLocalizing` **do not exist** (Tilde IsQuasicoherent section ends at line 410 with
  `isIso_fromTildeΓ_of_presentation`). `IsQuasicoherent` of a restriction is NOT a Mathlib lemma; it is
  recoverable from `QuasicoherentData` + `over`/`pullback` colimit-preservation but Mathlib ships no
  `(F.restrict j).IsQuasicoherent` instance. No basic-open-cover-gives-global-presentation lemma exists.
- **Project path**: the keystone must be proved as the explicit chain, not read off a definition.
- **Gap**: divergent — the hoped-for definitional shortcut is absent.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (no shortcut; chain is required, but every link's primitive exists).

### Decision: Q4 — route validity (is there a third wall?)
- **Finding**: YES, there is a third obligation, but it has a Mathlib ENGINE. The `over`-picture object
  `F.over D(gⱼ)` (`SheafOfModules ((Spec R).ringCatSheaf.over D(gⱼ))`, where the presentation lives) must be
  identified with the scheme-picture object `modulesRestrictBasicOpen gⱼ F` (an honest `(Spec R_{gⱼ}).Modules`,
  where the tilde/`fromTildeΓ` machinery lives). Call it **B3 = `restrict-over-compat`**.
- **It is NOT `lemma-widetilde-pullback`.** `modulesRestrictBasicOpenIso` relates the iterated `restrict` to
  `pullback (specAwayToSpec f)` — BOTH scheme-picture. It never mentions `over`, so it does NOT discharge B3.
  B3 is a genuinely distinct, third obligation.
- **But B3 is bounded, not a deep-math wall.** Mathlib's `pushforwardPushforwardEquivalence`
  (PushforwardContinuous ~305) is the engine: feed it the site equivalence
  `(Opens Spec R).over D(gⱼ) ≃ Opens(Spec R_{gⱼ})` (the open-subscheme opens identification, already in
  Mathlib's `opensFunctor`/open-immersion machinery and used inside `restrictFunctor`) plus the
  structure-sheaf compatibility, and it yields the equivalence of module categories whose object
  correspondence is B3. Every primitive exists; no missing theory. Contrast Route P's two walls
  ("localized sections for general qcoh", "tilde preserves finite limits") which needed genuinely new
  mathematics. **Route B converts two deep-math walls into one categorical-bookkeeping bridge.**
- **Gap**: divergent-with-cost (a real, medium build) but not divergent-and-blocked.
- **Verdict**: **PROCEED** — build Route B; treat B3 as the single load-bearing lane.

## Route B build decomposition (ordered; Mathlib cite per step)

- **B0 [DONE]** topology brick `exists_finite_basicOpen_subcover`, pure-algebra
  `isLocalizedModule_of_span_cover`, local-model `section_isLocalizedModule_of_presentation`,
  `modulesRestrictBasicOpen`/`Iso`/`specAwayToSpec_eq`.
- **B1 [small, Mathlib]** From `IsQuasicoherent F` take `QuasicoherentData F` (Quasicoherent.lean:249/201);
  get opens `Uᵢ` (`coversTop`) + `Presentation (F.over Uᵢ)` (208). Translate `J.CoversTop X` to
  `⨆ Uᵢ = ⊤` to feed B0's subcover refiner → finite `D(gⱼ) ⊆ U_{φⱼ}`, `span{gⱼ}=R`.
- **B2 [medium, in-framework]** Restrict `Presentation (F.over U_{φⱼ})` to `Presentation (F.over D(gⱼ))`
  via `Presentation.map` (Quasicoherent.lean:179) along the further-`over` (left adjoint
  PushforwardContinuous:282; unit-iso). Nested-over instances exist (Quasicoherent.lean:353).
- **B3 [THE BRIDGE — medium-large, the obligation]** `F.over D(gⱼ) ≅ modulesRestrictBasicOpen gⱼ F` carrying
  presentations. Engine: `pushforwardPushforwardEquivalence` (PushforwardContinuous ~305) instantiated at
  the site equivalence `(Opens Spec R).over D(gⱼ) ≃ Opens(Spec R_{gⱼ})` + structure-sheaf compatibility.
  Distinct from `lemma-widetilde-pullback`; NOT discharged by `modulesRestrictBasicOpenIso`.
- **B4 [small, Mathlib]** Transport `Presentation (F.over D(gⱼ))` across B3 and `modulesRestrictBasicOpenIso`
  via `Presentation.ofIsIso` (Quasicoherent.lean:132) → `Presentation (modulesRestrictBasicOpen gⱼ F)`.
- **B5 [trivial, DONE consumer]** `section_isLocalizedModule_of_presentation` per `gⱼ`.
- **B6 [small, DONE consumer]** Descend with `isLocalizedModule_of_span_cover`; section comparison is
  `restrict_obj`-`rfl` (Sheaf.lean:328).

## Recommendation
**PROCEED with Route B.** It is strictly better than Route P: it replaces two genuine-mathematics walls
with a single categorical bridge (B3) that has a Mathlib engine (`pushforwardPushforwardEquivalence`) and no
missing primitive. Section comparison (Q1) is `rfl`-cheap; presentation transport (Q2) is free given B3
(`Presentation.map`/`Presentation.ofIsIso`); the `IsLocalizing` shortcut (Q3) does NOT exist so the keystone
must be the explicit chain. The single load-bearing lane is **B3 (`restrict-over-compat`)** — flag it as the
real work, dispatch it as its own lane, and do NOT let downstream prose assume it is already discharged by
`modulesRestrictBasicOpenIso`. Estimate for B3+B1+B2+B4 wiring: ~150-350 LOC, fiddly (site-equivalence /
`IsContinuous` / sheafify-instance plumbing) but with no mathematical obstruction.
