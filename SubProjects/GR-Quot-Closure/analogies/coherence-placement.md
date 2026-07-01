# Analogy: discharging a LARGE concrete instance of a proven generic monoidal coherence across a comp-instance diamond

## Mode
api-alignment

## Slug
coherence-placement

## Iteration
017

## Question
(1) Is there a Mathlib-idiomatic way to define the transported `monoidalCategory` on `X.Modules` so its
underlying `CategoryStruct.comp` is *syntactically* `instCategory`'s (no diamond) while still inheriting
pentagon/triangle from `LocalizedMonoidal`? (2) Independent of the diamond, what is Mathlib's idiom for
cheaply discharging a LARGE concrete instance of a proven generic coherence, where naive
`exact <generic> …` does whole-term `isDefEq` > 4M heartbeats?

## Project artifact(s)
- `SectionGradedRing.lean:1643-1647` — `monoidalCategory := inferInstanceAs (MonoidalCategory (LocalizedMonoidal …))`.
- `SectionGradedRing.lean:2543-2569` — `tensorObjAssoc_associator_counit_coherence` (generic, `[MonoidalCategory M]`, axiom-clean, `maxHeartbeats 800000`).
- `SectionGradedRing.lean:2579-2737` — `★ tensorObjAssoc_eta_factor_sheaf`; massaging (`hηL/hηR/hα`, `simp only [hc,…]`, `erw`) succeeds, only the final `exact <generic>` placement is `sorry` (line 2737).
- `SectionGradedRing.lean:2747-2844` — `tensorObjAssoc_eta_factor` (B4), consumes `★` as `key`; compiles modulo `★`.

## Root-cause re-diagnosis (decision-critical)
The >4M-heartbeat cost is **not term size alone — it is the comp/monoidal-instance diamond forcing a
full traversal**. The `simp only [hc, …]` at `:2708` normalizes the goal's every `≫` UP to the
`LocalizedMonoidal` head. But the failed closer `exact tensorObjAssoc_associator_counit_coherence …`
leaves `M` to default to `X.Modules`, whose ambient `[Category]` is `instCategory` ⇒ the generic's
conclusion instantiates with the **native** comp head. Goal = synonym-head, lemma = native-head ⇒
`isDefEq` cannot short-circuit on syntactic equality and must unfold the entire ~1.2M-char term across
the rfl-diamond at every node. **If the two heads were syntactically equal, `isDefEq` would short-circuit
at the top and 1.2M chars would be cheap.** Head-alignment, not term-shrinking, is the lever.

## Decisions identified

### Decision 1: Can redefining `monoidalCategory` (Mathlib transport idiom) eliminate the diamond at source?
- **Mathlib idiom**: YES, Mathlib exposes native-comp transports —
  - `CategoryTheory.Monoidal.transport (e : C ≌ D) : MonoidalCategory D` (`Mathlib/CategoryTheory/Monoidal/Transport.lean`): builds the structure on `D` using `D`'s **own** `[Category D]` (no synonym).
  - `CategoryTheory.Monoidal.induced (F : D ⥤ C) [F.Faithful] (fData : InducingFunctorData F) : MonoidalCategory D` (same file): puts a `MonoidalCategory` on `D` over `D`'s native `[Category D]` + a supplied `[MonoidalCategoryStruct D]`, **inheriting pentagon/triangle by pulling them back through the faithful `F`** — exactly "native comp + borrowed coherence."
  So `inferInstanceAs` off the synonym is NOT the only idiom; `induced`/`transport` are the native-comp ones.
- **BUT this does NOT dissolve THIS diamond.** The diamond is introduced by the **Mathlib API lemmas**
  `Localization.Monoidal.μ_natural_left/right`, `associator_hom_app`, … which are *stated and proved
  inside* `LocalizedMonoidal L W ε`-comp (`Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean`).
  Those lemma statements are immovably synonym-headed; `★` must `rw`/`erw` with them, so synonym-headed
  subterms enter the goal regardless of how `monoidalCategory` is defined. Redefining the instance
  native-headed only **flips which side mismatches** — the project's `tensorObjAssoc`/`sheafification.map`
  are already native; the diamond is intrinsic to *mixing Mathlib's localized-monoidal API with native
  project morphisms*, not to the instance.
- **Gap**: divergent-with-cost, but the divergence is NOT the cause of this wall.
- **Verdict**: PROCEED on the instance as-is for this blocker. `Monoidal.induced` would be the
  Mathlib-aligned definition **if starting fresh** (avoid the synonym from day one), but retrofitting it
  now is high-cost and does not remove the synonym-headed-API diamond. NOT the fix.

### Decision 2: Cheap placement idiom for a large concrete instance of a proven generic coherence
- **Mathlib idiom**: keep one comp head and make the application **syntactic**. Two granularities:
  - **Local (2b, head-aligned `exact`)**: pin the generic's `M` to the synonym so its conclusion
    instantiates with the SAME head the `hc`-normalized goal already carries ⇒ `exact`'s `isDefEq`
    short-circuits. This is "stay in the synonym" applied at the single final step (Analogue 1 of
    `analogies/comp-instance-diamond.md`).
  - **Global (route 2 / stay-in-synonym)**: restate `★` (and the `tensorObjAssoc`/`tensorObjIso`
    references it threads) entirely in `LocalizedMonoidal`-comp so there is ONE head everywhere from the
    start — mirroring Mathlib's own `pentagon`/`triangle` proofs, which never leave the synonym.
- **Project's current path**: `exact <generic>` with `M` defaulting to `X.Modules` (native) against a
  synonym-headed goal ⇒ diamond-bridging whole-term `isDefEq` > 4M.
- **Directive's proposed 2a (abstract `★`'s STATEMENT, push concrete to B4)**: REJECT — B4
  (`:2773 have key := tensorObjAssoc_eta_factor_sheaf A B C`) consumes `★` as the *concrete* sheaf
  equation in `erw […, key, …]`. Abstracting `★`'s statement breaks B4; the only salvageable core of 2a
  (abstract the *residual* and apply the generic with explicit args) is identical to 2b.
- **2c `convert … using N` / `congr`**: REJECT — `convert`/`congr` run whole-term `kabstract`/congruence
  traversal over the 1.2M-char term, the same wall.
- **Verdict**: ALIGN — head-aligned syntactic application (2b first, global synonym restatement as
  fallback). Pure `@`-explicit (2b) avoids unification *search* but, on its own, still bridges the
  diamond unless the instance is also pinned — so 2b = explicit-args AND `M := synonym`.

## Recommendation
**Try first (lowest cost, one-line diff at `:2737`)**: replace the `sorry` with the generic coherence
**pinned to the synonym instance and given its isos explicitly**, so it instantiates with the synonym
comp/monoidal head the goal already carries post-`hc`:
```lean
exact tensorObjAssoc_associator_counit_coherence
  (M := LocalizedMonoidal (sheafificationMon X) (sheafificationW X) (localizationUnitIso X))
  eA eB eC eF eR n m1 m3 m4 m5 m6 (sheafification_map_unit_eq _)
```
Harvest the explicit `eA … m6` from the residual goal via `lean_goal` at `:2737`; supplying the five
isos + `n` pins all objects so no unification search runs, and `(M := synonym)` aligns the comp head ⇒
the closing `isDefEq` should short-circuit instead of traversing the diamond. **Residual risk**: the
`▷`/`◁`/`α_` *monoidal-struct* heads (project `monoidalCategory` vs `Localization.Monoidal`'s, rfl-defeq
but syntactically distinct) form a secondary diamond `hc` does not bridge; if `exact` still blows 200k,
this risk has materialized.

**Fallback (medium cost, low residual risk)**: restate `tensorObjAssoc_eta_factor_sheaf` uniformly in
`LocalizedMonoidal`-comp (build its LHS/RHS from `Localization.Monoidal` ops, not project
`monoidalCategory` ops), so a *single* head appears throughout and the final `exact` is purely
syntactic; reconcile the one resulting equation at B4 by a single `rfl`/defeq. This is Mathlib's own
discipline in `Localization/Monoidal/Basic.lean` (`pentagon`/`triangle` never leave the synonym) and is
the durable fix if the local head-alignment still leaves a struct-diamond.

**Do NOT** pursue: redefining `monoidalCategory` via `Monoidal.induced`/`transport` to kill the diamond
(ineffective here — diamond is from the synonym-headed Mathlib API, not the instance), directive-2a as
written (breaks B4), or `convert`/`congr` (whole-term traversal).
