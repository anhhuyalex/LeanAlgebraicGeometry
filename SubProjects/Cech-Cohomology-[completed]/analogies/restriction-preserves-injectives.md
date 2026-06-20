# Analogy: cheapest Mathlib route to "restriction preserves injectives" for the Ext-realized absolute cohomology

## Mode
api-alignment

## Slug
restrict-inj

## Iteration
026

## Question
What is the cheapest Lean route, using only today's Mathlib, to realize `H^p(U, F)` so that the
01EO dimension shift has (i) `H^0 = Γ(U,-)`, (ii) injective vanishing, (iii) a covariant LES —
specifically, is `Injective I → Injective (restrictFunctor j I)` (restriction preserves injectives)
buildable, or can it be sidestepped? Plus the H⁰=Γ plumbing (Q2).

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/PresheafCech.lean:216` — `injective_toPresheafOfModules` (the
  `Injective.injective_of_adjoint` + `sheafificationAdjunction` pattern already shipped).
- `AlgebraicJacobian/Cohomology/PresheafCech.lean:245` — `freeYonedaHomEquiv`:
  `Hom_{PMod}(free(yoneda V), F) ≃ F(V)` (already shipped; this is the load-bearing reuse).
- `blueprint/.../Cohomology_CechHigherDirectImage.tex` `def:absolute_cohomology` (~line 2787) and the
  01EO proof (lines 3109–3174).

## Headline finding

**"Restriction preserves injectives" is the WRONG problem to solve. It is genuinely hard
(needs `j_!`, a real Mathlib gap), and it is UNNECESSARY.** Switch the realization to **Form B**,
`H^p(U,F) := Ext^p_{Mod(O_X)}(j_!O_U, F)`, and realize the single object `j_!O_U` as
`sheafification(free(yoneda U))` — built from pieces the project *already has*. Under Form B all three
structural facts the 01EO dimension shift consumes are free, and restriction-preserves-injectives is
never invoked.

The directive's premise that "build j_! → Form B" both require the full extension-by-zero **functor**
is the bug. Form B needs only the **single object** `j_!O_U`, and that object is, up to iso,
`sheafify(free(yoneda U))` — no Kan extension over general modules, no exactness proof, no topology
extension-by-zero. The corepresenting bijection is `sheafificationAdjunction.homEquiv ∘ freeYonedaHomEquiv`,
a composite of two adjunction bijections already in hand.

## Decisions identified

### Decision: how to realize `H^p(U,-)` (and therefore whether restriction-preserves-injectives is needed)

- **Mathlib idiom**: `CategoryTheory.Abelian.Ext` on the abelian category `X.Modules`
  (`= SheafOfModules X.ringCatSheaf`), with `HasExt.standard`, `Ext.homEquiv₀`,
  `Ext.eq_zero_of_injective`, and `Ext.covariant_sequence_exact₁/₂/₃`. Injective vanishing in Mathlib's
  Ext requires the **second** argument injective; the covariant LES is in the **second** variable.
  Cite: `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`,
  `Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives`.

- **Project's current path (Form A, in the def)**: `H^p(U,F) := Ext^p_{Mod(O_U)}(O_U, F|_U)`.
  First argument `O_U`, second `F|_U = restrictFunctor j F`, category `U.Modules`. Injective vanishing
  then needs `Ext^{n+1}(O_U, I|_U) = 0`, i.e. `I|_U` injective — **exactly** restriction-preserves-
  injectives. There is no other source of that vanishing (`O_U` is not projective), so Form A ⟺
  restriction-preserves-injectives.

- **Gap**: divergent-with-cost. Form A forces a Mathlib gap-fill (`j_!`); Form B (already written in the
  blueprint as the "equivalently …" clause) avoids it entirely.

- **Cost of Form A**: the only Mathlib route to restriction-preserves-injectives is
  `Injective.injective_of_adjoint` applied to `j_! ⊣ restrictFunctor` with `j_!` mono-preserving.
  Mathlib has **no** `j_!` and **no** second adjunction making `restrictFunctor` a right adjoint
  (verified: the *only* adjunction is `restrictAdjunction f : restrictFunctor f ⊣ pushforward f`,
  the wrong direction; its counit is iso, which only shows `pushforward` is fully faithful and gives
  *pushforward*-preserves-injectives, not restriction). Building the `j_!` **functor**
  `U.Modules ⥤ X.Modules` (left Kan extension along `Opens U ↪ Opens X` + sheafification + module
  structure + the adjunction triangle + mono/exactness) is genuine new infrastructure, est. **200–500+
  LOC** with real risk — a NEEDS_MATHLIB_GAP_FILL.

- **Verdict**: **ALIGN_WITH_MATHLIB — adopt Form B**; treat restriction-preserves-injectives as
  unnecessary and do not build it.

### Decision: how to build the corepresenting object `j_!O_U` for Form B

- **Mathlib idiom**: corepresent the functor `F ↦ Γ(U, F) = F(U)` on `X.Modules`. Sheafify the
  presheaf-of-modules object that corepresents `F ↦ F(U)` at the presheaf level.
  `free(yoneda U)` is that presheaf object (the project's `freeYonedaHomEquiv`), and
  `PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)` transports corepresentability
  through sheafification:
  ```
  Hom_{X.Modules}(sheafify(free(yoneda U)), F)
    ≅ Hom_{PMod}(free(yoneda U), forget F)        -- sheafificationAdjunction.homEquiv
    ≅ (forget F)(U) = F(U) = Γ(U, F).             -- freeYonedaHomEquiv U F  (already shipped)
  ```
  Note `sheafify(free(yoneda U))` IS `j_!O_U` up to iso: `free(yoneda U)(V) = O_X(V)` for `V ≤ U` and
  `0` otherwise — literally the presheaf extension-by-zero `p_!O_U`, whose sheafification is `j_!O_U`.
  Cite: `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification.sheafificationAdjunction` and
  `…sheafificationAdjunction_homEquiv_apply`; project `freeYonedaHomEquiv`
  (`PresheafCech.lean:245`) and its additive upgrade `freeYonedaHomAddEquiv`.

- **Project's current path**: none yet (Form A keeps `O_U` and `F|_U`).

- **Gap**: divergent-with-cost only if Form A is kept; under Form B this is a small new def + lemma.

- **Cost**: **LOW, ~50–80 LOC**, all composed from shipped pieces:
  1. `def jShriekOU (U : Opens X) : X.Modules :=`
     `(PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj`
     `  ((PresheafOfModules.free X.ringCatSheaf.obj).obj (yoneda.obj U))`  — 1 def.
  2. corepresentability iso `Hom(jShriekOU U, F) ≃ F(U)`, natural & additive: compose
     `(sheafificationAdjunction _).homEquiv _ _` with `freeYonedaHomAddEquiv U F` — ~15–30 LOC
     (naturality/additivity inherited from the two adjunction equivs).
  3. `def H (p) (U) (F) := AddCommGrp.of (Ext (jShriekOU U) F p)` — 1 line.
  4. `H^0 ≅ Γ`: `Ext.homEquiv₀ ▸ corepr` — ~5 LOC.
  5. injective vanishing `H^{n+1}(U,I)=0`: `Ext.eq_zero_of_injective` (I injective, *second* arg) —
     1-line wrapper. **No restriction-preserves-injectives.**
  6. LES from SES in `X.Modules`: `Ext.covariant_sequence_exact*` at fixed first arg `jShriekOU U` —
     ~10–20 LOC of wrappers.

- **Verdict**: **PROCEED** (build it; it is cheap and Mathlib-aligned).

### Decision (Q2): the `Hom(O_U, M) ≅ Γ(U,M)` plumbing

- **Mathlib idiom**: `SheafOfModules.unit R : SheafOfModules R` is `O` as a module over itself, and
  `SheafOfModules.unitHomEquiv : (unit R ⟶ M) ≃ M.sections` is exactly
  `Hom_{O}(O, M) ≅ Γ(M)` (global sections of the sheaf-of-modules). Cite:
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.{unit, unitHomEquiv, unit_val}`. For degree-0 Ext use
  `CategoryTheory.Abelian.Ext.homEquiv₀ : Ext X Y 0 ≃ (X ⟶ Y)` then `unitHomEquiv`.
- **Verdict**: **PROCEED** — fully available; nothing to build. (Under Form B you don't even need
  `unit`/`unitHomEquiv`: step 4 above gives `H^0 ≅ F(U)` directly from the corepresentability chain.
  `unitHomEquiv` is the answer to Q2-as-posed and the fallback if Form A is ever retained.)

## Routes ranked (Q1)

| Route | What it is | Cost | Buildable today? |
|---|---|---|---|
| **(c)/(d) Form B via `sheafify(free(yoneda U))`** | corepresenting object + Ext over `O_X` | **LOW ~50–80 LOC** | **YES — recommended** |
| (b) second adjunction making `restrictFunctor` a right adjoint | apply `injective_of_adjoint` | — | **NO** — verified absent (only `restrictFunctor ⊣ pushforward`) |
| (a) build full `j_!` functor + exactness, keep Form A (or Form-B-via-functor) | extension-by-zero infra | HIGH 200–500+ LOC, risky | gap-fill only |

## Recommendation

Adopt **Form B**: `H^p(U,F) := Ext^p_{X.Modules}(jShriekOU U, F)` with
`jShriekOU U := sheafification(free(yoneda U))`. This makes injective vanishing and the covariant LES
free (second-variable Ext, SES stays in `X.Modules` — no restriction of the SES, no `F|_U`, no `O_U`),
and `H^0 ≅ Γ(U,F)` follows from `sheafificationAdjunction.homEquiv ∘ freeYonedaHomEquiv` —
both already shipped. **Do not build `j_!` and do not prove restriction-preserves-injectives**; they
are unnecessary under Form B and the only Mathlib route to them is a 200–500 LOC gap-fill. The
blueprint's `def:absolute_cohomology` already lists the Form B expression, so the change is to make
Form B the *primary* realization (and the three structural clauses now read off `jShriekOU U` as the
fixed first argument in `Mod(O_X)`, not `O_U` in `Mod(O_U)`). Q2 plumbing for the H⁰ clause:
`Ext.homEquiv₀` then either the Form-B corepresentability chain (preferred) or
`SheafOfModules.unitHomEquiv` (Form A fallback).
