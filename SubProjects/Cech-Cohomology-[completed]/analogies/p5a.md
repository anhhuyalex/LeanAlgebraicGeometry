# Analogy: P5a — feasibility of the `higher_direct_image_presheaf` (01XJ) lane

## Mode
api-alignment

## Slug
p5a

## Iteration
017

## Question
Can we open a prover lane for `lem:higher_direct_image_presheaf` (Stacks 01XJ) —
`Rⁱ f_* F = sheafify(V ↦ Hⁱ(f⁻¹V, F))` for `F : X.Modules` — on TODAY's Mathlib,
and what is the cleanest API path? Re-validate the four building blocks and say
whether the iter-011 design in `analogies/p5a-01xj.md` still holds.

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/HigherDirectImage.lean:47` — `higherDirectImage f i F = ((pushforward f).rightDerived i).obj F`, `[HasInjectiveResolutions X.Modules]`.
- `AlgebraicJacobian/Cohomology/CechHigherDirectImage.lean:771` — `cech_computes_higherDirectImage` (PROTECTED; the *Čech↔derived* comparison, a **different** statement from 01XJ; still `sorry`).
- `AlgebraicJacobian/Cohomology/AcyclicResolution.lean:155,227` — P4 engine `Functor.IsRightAcyclic` + `rightDerivedIsoOfAcyclicResolution`.
- `AlgebraicJacobian/Cohomology/CechAcyclic.lean:74` — `CechAcyclic.affine` (P3; the analytic core, `sorry`, blocked on the L1 categorical bridge).

## Re-validation of iter-011 citations (all CONFIRMED on today's Mathlib)
- `CategoryTheory.Sheaf.H` / `cohomologyPresheafFunctor` / `Sheaf.H'` — `CategoryTheory/Sites/SheafCohomology/Basic.lean:58,90,105`. Still **only** for `Sheaf J AddCommGrpCat`, gated `[HasSheafify][HasExt]`. Not for `SheafOfModules`.
- `SheafOfModules.toSheaf` + `PreservesFiniteLimits` instance — `Algebra/Category/ModuleCat/Sheaf/Limits.lean` (`SheafOfModules.instPreservesFiniteLimitsSheafAddCommGrpCatToSheaf`). PRESENT.
- `PresheafOfModules.sheafification` (left adjoint, `sheafificationAdjunction`) `PreservesFiniteLimits` — `Algebra/Category/ModuleCat/Presheaf/Sheafification.lean:54,190`. **Stronger than iter-011 cited**: the module-side sheafification itself preserves finite limits (and being a left adjoint, all colimits ⇒ preserves homology).
- `Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms` — `CategoryTheory/Preadditive/Injective/Preserves.lean:49`. PRESENT.
- `Functor.rightDerived` — `CategoryTheory/Abelian/RightDerived.lean:108`. PRESENT.
- `Scheme.Modules.pushforward` / `pushforwardComp` (`_hom_app_app = 𝟙` by `rfl`) — `AlgebraicGeometry/Modules/Sheaf.lean:151,210,214`. PRESENT.
- **ABSENT (re-confirmed by grep):** no Grothendieck/Leray spectral sequence; no `R(g∘f) ≅ Rg∘Rf` (only `NatTrans.rightDerived_comp` for `α≫β`); no packaged `Rⁱf_* = sheafify(...)` comparison; no standalone module-valued `Hⁱ(open,F)`.

## NEW finding vs iter-011 — the `[HasInjectiveResolutions X.Modules]` discharge chain shrank
Mathlib now ships a complete instance chain:
- `IsGrothendieckAbelian.enoughInjectives : EnoughInjectives C` — `CategoryTheory/Abelian/GrothendieckCategory/EnoughInjectives.lean:374` (`@[stacks 079H]`).
- `HasInjectiveResolutions C` from `[Abelian C][EnoughInjectives C]` — `CategoryTheory/Abelian/Injective/Resolution.lean:343,345`.

So `IsGrothendieckAbelian (SheafOfModules R) ⟹ EnoughInjectives ⟹ HasInjectiveResolutions` is now **fully automatic** in Mathlib. The ONLY missing link to inhabit `[HasInjectiveResolutions X.Modules]` is a single instance `IsGrothendieckAbelian (SheafOfModules R)` (ABSENT — grep over `CategoryTheory/Sites/`, `Algebra/Category/ModuleCat/Sheaf/` empty; instances exist only for `ModuleCat R`, `AddCommGrpCat`, `Ind C`, `HomologicalComplex`). This dramatically shrinks the P3b target: instead of building enough-injectives from scratch, P3b now needs only the one Grothendieck-abelian instance (needs `Abelian` ✓ + AB5/`HasColimits` + a separator `HasSeparator`). NOTE: P5a does **not** need this instance — it carries the typeclass as a hypothesis exactly as the existing signatures do.

## Decisions identified

### Decision 1 (Q1): standalone module-valued `Hⁱ(f⁻¹V, F)` over an open
- **Mathlib idiom**: `Sheaf.H'`/`cohomologyPresheaf` (AddCommGrpCat-valued site sheaves) only; nothing for `SheafOfModules`.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL. Recommendation unchanged — **do not materialise** a standalone `Hⁱ(open,F)`; use the narrow basis-local form (only `Hᵏ` of an explicit `ModuleCat` complex appears, which Mathlib has).

### Decision 2 (Q2): `Rⁱf_* = sheafify(V ↦ Hⁱ(f⁻¹V,F))`
- **Mathlib idiom**: no packaged comparison; the engine "cohomology sheaf = sheafify(objectwise homology)" is buildable from `PresheafOfModules.sheafification`/`SheafOfModules.toSheaf` preserving finite limits + colimits (⇒ homology) and `X.Modules` abelian.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (build; do not route through a δ-functor).

### Decision 3 (Q3): derived functors of `pushforward`, `HasInjectiveResolutions X.Modules`
- `Functor.rightDerived` PRESENT; typeclass NOT inhabited by Mathlib but now discharge-able via the one Grothendieck-abelian instance (see NEW finding). P5a proceeds carrying it as a hypothesis.
- **Verdict**: PROCEED (as hypothesis); typeclass inhabitation is the P3b lane's, not P5a's.

### Decision 4 (Q4): `Hⁱ(U,F)` as a functor of `V` / open-immersion composition
- Idiom: state via `ExactAt`/`QuasiIso`; `pushforward f ⋙ (jₛ)_* = (gₛ)_*` by `pushforwardComp` (`rfl`); "(jₛ)_* preserves injectives" via `preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms`. No spectral sequence needed.
- **Verdict**: ALIGN on the acyclic-resolution route (project P4 engine), NEEDS_MATHLIB_GAP_FILL only for the affine Serre-vanishing analytic core (shared with `CechAcyclic.affine`).

## Recommendation
**PROCEED** — open `higher_direct_image_presheaf` (01XJ) as a parallel lane next iter, carrying `[HasInjectiveResolutions X.Modules]` as a hypothesis. The iter-011 design in `analogies/p5a-01xj.md` **still holds in full** — every cited declaration verified present, every ABSENT item re-confirmed absent. Use the **basis-local vanishing criterion** form (Decision 1/2), not a standalone `Hⁱ(open,F)` object. Project-side new infra: (i) "cohomology sheaf = sheafify(objectwise homology)" lemma, (ii) "a sheaf of modules is 0 iff its sections vanish on a basis", (iii) the affine Serre-vanishing core (shared with `CechAcyclic.affine`, the project's irreducible analytic step). Mathlib provides everything categorical around these: sheafification + finite-limit/colimit preservation, abelian structure, `rightDerived`, `pushforwardComp`, injective-preservation. The new Grothendieck-abelian discharge chain is a bonus: it converts the long-standing `[HasInjectiveResolutions]` blocker into a single isolated instance target for the P3b lane.
