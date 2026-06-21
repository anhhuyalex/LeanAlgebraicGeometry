# Analogy: redefine `tensorObj := ⊗_loc` vs. bridge a hand-built product to Mathlib's `LocalizedMonoidal`

## Mode
api-alignment

## Slug
snap-instance-design

## Iteration
020

## Question
Mathlib's `CategoryTheory.Localization.Monoidal` gives `X.Modules` a free symmetric monoidal
structure via the type synonym `LocalizedMonoidal L W ε` (`⊗_loc`). The project instead hand-builds
a parallel product `tensorObj F G := (F♭ ⊗_p G♭)^#` and bridges it to `⊗_loc` by `tensorObjLocalizedIso
= μ⁻¹ ; (c_F ⊗ c_G)`. The bridge coherence `tensorObjAssoc_eq_localizedAssociator` is 8-iter STUCK on
a dual-`MonoidalCategory`-instance μ-token-divergence. Should the project align with Mathlib (drop the
hand-built product, route everything through the single `⊗_loc`), and at what cost?

## Project artifact(s)
- `AlgebraicJacobian/Picard/SectionGradedRing.lean:87` — `MonoidalPresheaf X` (presheaf monoidal instance #1).
- `:94` `tensorObj`, `:142` `tensorObjUnitIso`, `:155` `tensorBraiding`, `:168` `tensorObjRightUnitor`,
  `:1317` `tensorObjAssoc` — the hand-built parallel product + structural isos.
- `:196` `sectionsMul` — the lax section-multiplication; domain is the presheaf tensor at `⊤`.
- `:1450` `modulesLocalizedMonoidal` (= `LocalizedMonoidal …`, instance #2), `:1462` `tensorObjLocalizedIso` (the bridge iso).
- `:1645`–`:2598` the bridge-coherence machinery (`tensorBraiding_eq_localizedBraiding`, 7 seam lemmas,
  3 head lemmas, `hK_lhs`/`hK_rhs`, `tensorObjAssoc_eq_localizedAssociator`); single open `sorry` at `:2219`.
- `:1603` `tensorPowAdd`, `:3075` `tensorPowAdd_assoc`, `:3134` `sectionsMul_mul_assoc`, `:2912`
  `sectionMul_assoc_core` — the SNAP cone consumers.

## Mathlib reference read
`Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean` (494 L; the `…/Monoidal.lean` shim is
deprecated since 2025-10-20 → `…/Monoidal/Basic.lean`).
- L11–28 module docstring: "we construct a monoidal category structure **on `D`** such that the
  localization functor is monoidal. The structure is actually defined on a type synonym
  `LocalizedMonoidal L W ε`." → INTENT: `D` (= `X.Modules`) is the carrier you compute in; `⊗_loc`
  IS the localized tensor.
- L84–88 `LocalizedMonoidal` is a `def … := D` type synonym; L172–180 `monoidalCategoryStruct`
  defines `tensorObj X Y := ((tensorBifunctor).obj X).obj Y` directly.
- L184 `μ (X Y : C) : (L').obj X ⊗ (L').obj Y ≅ (L').obj (X ⊗ Y)` — a strong-monoidality comparison
  for **`L'`-images**, NOT a hook for an external hand-built product.
- L234 `associator_hom_app`, L212 `leftUnitor_hom_app`, L223 `rightUnitor_hom_app` fire ONLY when
  objects are literally `(L').obj _` — the exact reason the project's `α_ A B C` (A,B,C arbitrary
  `X.Modules`) won't normalize.
- L441 `MonoidalCategory (LocalizedMonoidal …)` — pentagon/triangle/hexagon proven for free.
- L465–471 `instance : (toMonoidalCategory L W ε).Monoidal` — the localization functor `L'` is a
  strong monoidal functor; its `associativity`/`left_unitality`/`right_unitality` fields (proven by
  `simp [associator_hom_app]` etc.) ARE the lax-functor coherences a section-level multiplication needs.

## Decisions identified

### Decision: one monoidal product vs. two (the load-bearing decision)

- **Mathlib idiom**: ONE product. `LocalizedMonoidal L W ε` is the canonical carrier; downstream
  consumers tensor in `⊗_loc` and import coherence from `MonoidalCategory (LocalizedMonoidal …)`.
  Mathlib has NO "bridge a hand-built product to `⊗_loc` via μ" pattern anywhere — μ exists to relate
  `L'`-images, never to certify a parallel product. Cite: `Localization/Monoidal/Basic.lean:84-188,441,465`.
- **Project's current path**: TWO `MonoidalCategory` instances on (defeq copies of) the same category —
  presheaf-level `MonoidalPresheaf X` and the localized `modulesLocalizedMonoidal X` — with a hand-built
  `tensorObj`/`tensorObjAssoc` on the first and `⊗_loc` on the second, glued by `tensorObjLocalizedIso`.
- **Gap**: divergent-with-cost (critical). The two instances give `≫`/`⊗ₘ`/μ two token-distinct
  (defeq) spellings; reconciling them inside the associator-coherence proof forces whnf of `μ` →
  `Localization.fac` → the 8-iter isDefEq/whnf bomb. This is the canonical **parallel-API anti-pattern**.
- **Cost of divergence**: ~900 lines of bridge machinery (`:1619`–`:2598`) whose SOLE purpose is to
  re-prove, by hand, coherence Mathlib already proved for `⊗_loc`; the cone is stuck behind it.
- **Verdict**: **ALIGN_WITH_MATHLIB**.

### Decision: section-computability of `tensorObj` (the iter-005 rejection rationale)

- iter-005 rejected Option A because the hand-built `tensorObj`/`tensorObjAssoc` are *transparent*:
  `sectionMul_assoc_core` (`:2912`), `sectionMul_braiding_core`, `unitor_sectionsMul` close by **`rfl`**
  on the presheaf structural maps at `⊤`. `α_loc` is opaque (`Localization.lift₂`), so a naive
  `tensorObj := ⊗_loc` breaks those `rfl`s — the genuine "blast radius".
- **But this is recoverable, not blocking.** The section coherences are exactly the lax-monoidal-functor
  coherences of `Γ ∘ L'`, which Mathlib PROVES in `Functor.Monoidal (L')` (`Basic.lean:465-471`,
  fields `associativity`/`left_unitality`/`right_unitality`). Under Option A the `rfl`-on-representatives
  proofs are replaced by these Mathlib lax-coherence lemmas — a re-proof, not a loss.
- **Decisive asymmetry (μ placement)**: μ MUST appear somewhere (the localization is genuinely a
  quotient). The choice is WHERE:
  - **Option A** spends μ ONCE, in the *definition* of `sectionsMul`/`tensorObjLocalizedIso`, where it
    is opaque and never syntactically reconciled → no bomb.
  - **Option B (current)** forces μ into the associator-coherence *proof*, where it must be syntactically
    manipulated across the dual-instance boundary → bomb.
  Option A is bomb-free precisely because it never reconciles μ with a second associator.
- **Verdict**: DIVERGE rationale REJECTED — the section-computability argument does not survive contact
  with `Functor.Monoidal (L')`.

## Recommendation

**ALIGN_WITH_MATHLIB — collapse to the single localized instance (directive options (a)≡(b); (d) is its
consumer half).** Mechanism, ranked:

1. **(a)≡(b) [TOP]** Make `⊗_loc` the only product. Either (b-instance) give `X.Modules` a
   `MonoidalCategory` instance `:= inferInstanceAs (MonoidalCategory (modulesLocalizedMonoidal X))` and
   write `F ⊗ G`/`α_ F G H` everywhere, or (a-thin, more surgical) keep the names but set
   `tensorObj F G := MonoidalCategory.tensorObj (C := modulesLocalizedMonoidal X) F G`,
   `tensorObjAssoc := α_loc`, `tensorBraiding := β_loc`, `tensorObjUnitIso := λ_loc`. Then
   `tensorObjAssoc_eq_localizedAssociator` is `rfl`, the `:2219` crux `sorry` is **deleted not proved**,
   `tensorPowAdd_assoc` follows from `MonoidalCategory.pentagon`, and the section cores re-route through
   `Functor.Monoidal (L')`. `tensorObjLocalizedIso` collapses to `Iso.refl`/counit-only.
2. **(d)** restructure `sectionsMul`/`tensorPow` to consume `⊗_loc` — this is the downstream half of (a),
   not a standalone alternative.
3. **(c) DISCARD** a `@[simp]` comp-collapse / keystone-restate transport idiom (iter-013's own proposal,
   `:2436`). It only reconciles the `≫` *head*; the real divergence is the **object arguments** of μ
   (`(toPshMod X).obj (A.tensorObj B)` at a COMPOSITE object vs `L'A♭ ⊗_loc L'B♭`), which no simp lemma
   reconciles without forcing whnf of μ. This is the family that has been failing since iter-013; it
   entrenches the anti-pattern.

**Cost (all in ONE file — `grep` confirms `tensorObj`/`sectionsMul`/`tensorPow` appear in NO other
`.lean`):** redefine 5 structural defs; re-touch `sectionsMul` (+ a μ/counit composite),
`tensorObjLocalizedIso` (→ refl); DELETE ~900 L of bridge (`:1619`–`:2598`: `laxMonoidal_μ_eq`,
`oplaxMonoidal_δ_eq`, `tensorBraiding_eq_localizedBraiding`, 7 seam lemmas, 3 head lemmas, `hK_lhs`/`hK_rhs`,
the bridge); re-prove ~10 coherences (`tensorPowAdd_{zero,rightUnit,braiding,assoc}`, the 3 section cores,
`sectionsMul_{one_mul,mul_one,mul_assoc,mul_comm}`) — now EASY via Mathlib pentagon/triangle/hexagon +
`Functor.Monoidal (L')`. KEEP the localization-precondition machinery (`:812`–`:1248` `ztensor_whisker_localIso`,
`isIso_sheafification_whiskerRight_unit`, `W_isMonoidal`) — it discharges `⊗_loc`'s existence and is
unaffected. Net: a large DELETION + simplification, not new infrastructure.

**Unitor bridge `tensorObjUnitIso_eq_localizedLeftUnitor` (does not exist):** under the CURRENT dual
design it hits the SAME wall — relating `λ_p^# ; counit` to `λ_loc` crosses ε (`localizedMonoidalUnitIso`)
and the counit with μ at the unit node, structurally the one-factor analogue of `hK_rhs`/`hK_lhs`
(Mathlib's `leftUnitor_hom_app:212` fires only at `(L').obj _`, exactly as `associator_hom_app` fails on
`α_ A B C`). It is NOT independently closeable cleanly; the project sidestepped *needing* it by proving
`unitor_sectionsMul` directly at the section level (just as `sectionMul_assoc_core` is direct `rfl`).
Under Option A it becomes `rfl`. This confirms the bottleneck is the DESIGN (dual instance), not the proof.
