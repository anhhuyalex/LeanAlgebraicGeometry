# Analogy: statement-pinned localized-monoidal reassociation `(W ≫ T) ≫ α → W ≫ (T ≫ α)`

## Mode
api-alignment

## Slug
snap-reassoc-pin

## Iteration
018

## Question
**Part A:** Design a STATEMENT-PINNED localized-monoidal reassoc helper that rewrites
`(W ≫ T) ≫ α → W ≫ (T ≫ α)` bomb-free over `modulesLocalizedMonoidal X`, applied via
`congrArg`-peel. Can Mathlib `Category.assoc`/`associator_naturality` be wrapped, or is a
project-local pinned restatement required?
**Part B:** Can the dual `MonoidalCategory` instance (`pshModMonoidal` bare form vs
`PresheafOfModules.monoidalCategory` synonym `MonoidalPresheaf X`) be ELIMINATED by re-ascribing
the sheafification functor / `modulesLocalizedMonoidal` domain to the synonym? Blast radius?
NOW vs LATER?

## Project artifact(s)
- `SectionGradedRing.lean:87` — `MonoidalPresheaf X` abbrev (synonym form).
- `:1402–1414` — `pshModMonoidal`/`Braided`/`Symmetric` bare-form re-exports.
- `:1450–1452` — `modulesLocalizedMonoidal` (`LocalizedMonoidal` synonym).
- `:1900–2049` — `tensorObjAssoc_hK_lhs_head` (iter-016 statement-pinned fix, GREEN, the template).
- `:2054–2205` — `tensorObjAssoc_eq_localizedAssociator_hK_lhs` (the sorry; reassoc is the residual).

---

## HEADLINE: a pinned reassoc *lemma applied via congrArg-peel* CANNOT work. The directive's
## premise is refuted empirically. ALL three in-proof reassoc mechanisms bomb on the current goal.

The goal at the `hK_lhs` sorry (L2205) is exactly:
```
μ_{(A⊗B)♭,C♭}.inv ≫ ((W ≫ T) ≫ (α_ A B C).hom) = K
  W = ((A.tensorObj B).counit.hom ≫ μ_{A♭,B♭}.inv) ▷ (L'C♭)      -- whiskerRight, localized
  T = (c_A ⊗ₘ c_B) ⊗ₘ c_C                                          -- tensorHom, localized
  K = assocCommonForm A B C  (unfolded)
```
Need: `(W ≫ T) ≫ α → W ≫ (T ≫ α)`, then `associator_naturality`+`associator_hom_app`
(VERIFIED bomb-free once the LHS is literally `W ≫ T ≫ α`).

### Three probes at L2205 (`lean_multi_attempt`, iter-018) — ALL hit the 200000-hb isDefEq bomb:
1. `rw [Category.assoc]` → **bomb** (confirms iter-017).
2. **Fully-spelled, `(C := modulesLocalizedMonoidal X)`-pinned `congrArg`-peel**
   `refine (congrArg (fun t => μ.inv ≫ t) (Category.assoc W T α)).trans ?_`
   with `W,T,α` written out verbatim → **bomb**.  ← *This is the directive's hoped-for fix. It fails.*
3. **Head-lemma `show`-to-uniform recast** (same bracketing, `(C := …)`-ascribed, bare object
   spelling) → **bomb**, reported at the leading `μ.inv` object `(toPresheafOfModules X).obj (A.tensorObj B)`.

### Why the pinned lemma cannot help (the actual mechanism)
- A `congrArg`-peel is bomb-free **only** when the equation's BOTH sides are EXACT current-goal
  subterms (this is why iter-017's `hsplit` peel at L2171 worked). A reassociation *by definition*
  introduces the bracketing `W ≫ (T ≫ α)` — and the composite `T ≫ α` is **NOT a subterm** of the
  goal (the goal has `(W ≫ T) ≫ α`). Elaborating `Category.assoc W T α` therefore must FORM `T ≫ α`
  fresh and FORM `(W ≫ T) ≫ α` fresh, both of which re-check object identities over
  `modulesLocalizedMonoidal X`. Pinning the *lemma statement* does nothing: the bomb is in the
  *application-site elaboration*, not the lemma.
- The trigger is the **leading `μ.inv` at the sheaf-FOLDED composite object** `(A.tensorObj B)♭`
  (= `(sheafification.obj (A♭⊗B♭))♭`). `A.tensorObj B` is the sheaf-level tensor (`def tensorObj`,
  L94); inside the goal it sits *folded*, while the surrounding localized factors carry `(L').obj _`
  image-form objects. Any defeq that touches both forms must `whnf` the fold — and `tensorObj`/the
  localized `⊗` route through `Localization.Monoidal.μ` → `Localization.fac` → the documented bomb.

### Why the head lemma's `show`+`simp[Category.assoc]` (L1943→1980) WORKS but hK_lhs's doesn't
The difference is NOT the tactic — it's the OBJECT SPELLING in the *statement*:
| | leading μ object | RHS | reassoc result |
|---|---|---|---|
| `tensorObjAssoc_hK_lhs_head` (GREEN) | `sheafification.obj (tensorObj (C:=MonoidalPresheaf X) A♭ B♭)` — **unfolded + presheaf-pinned** (L1903–1905) | `𝟙 _` (after `cancel_epi`) | `simp [Category.assoc]` GREEN (L1980) |
| `hK_lhs` mid-proof goal (BOMBS) | `(toPresheafOfModules X).obj (A.tensorObj B)` — **folded** | unfolded `assocCommonForm` | every mechanism bombs |

The head lemma's statement was written so that by the time `simp [Category.assoc]` runs, **every
μ-object is a pinned, unfolded `(L').obj _` form** — reassoc matching is then purely syntactic, no
`whnf`. hK_lhs's reassoc runs on a goal that still carries the folded `A.tensorObj B` inside the
leading μ, so any defeq bombs.

---

## Decisions identified

### Decision A: how to do the reassoc step
- **Mathlib idiom**: `Category.assoc` / `@[reassoc] associator_naturality`. In Mathlib's own
  `LocalizedMonoidal` pentagon/triangle proofs these fire freely **because every object is phrased
  at `(L').obj X` for a single `C`-object `X`** (via `EssSurj`/`objObjPreimageIso`,
  `Basic.lean:331–334,414–415`) — uniform image-form objects ⇒ syntactic reassoc, no `whnf`.
- **Project path (attempted)**: apply `Category.assoc`/pinned-lemma/`show` to the *mid-proof goal*
  that mixes folded `A.tensorObj B` with `(L').obj _`. All bomb.
- **Gap**: divergent-with-cost. Not a missing lemma; a goal-shape problem.
- **Verdict**: ALIGN_WITH_MATHLIB — phrase the reassoc inside a pinned statement whose μ-objects are
  all unfolded `(L').obj _` image-forms, exactly as the head lemma does. **No reassoc lemma exists or
  is needed.**

### Decision B: the dual `MonoidalCategory` instance (Part B)
- **Mathlib idiom**: ONE canonical monoidal instance per category.
- **Project path**: `pshModMonoidal`/`Braided`/`Symmetric` bare-form re-exports coexist with the
  synonym instance. Load-bearing: `LocalizedMonoidal L W ε` requires `[MonoidalCategory C]` where
  `C` = source of `L` = the **bare** form `PresheafOfModules X.ringCatSheaf.obj` (hover confirmed:
  `LocalizedMonoidal … [MonoidalCategory C] (L : C ⥤ D) …`). Deleting the re-exports makes
  `modulesLocalizedMonoidal X` itself fail to elaborate.
- **Gap**: divergent-with-cost, but NOT cleanly fixable by deletion.
- **Verdict**: DIVERGE_INTENTIONALLY *for now* — keep the dual instance; fix via object-phrasing
  discipline instead (see below). Re-ascription refactor is HIGH-risk; defer.

---

## Part A — recommendation (prover-fireable)

**Do NOT write a reassoc helper.** Instead replicate the head-lemma statement-pinning for the
reassoc+naturalise step. Concretely, add a standalone pinned lemma (sibling of
`tensorObjAssoc_hK_lhs_head`), e.g. `tensorObjAssoc_hK_lhs_native`, whose **statement** is:

```
private lemma tensorObjAssoc_hK_lhs_native (A B C : X.Modules) :
    (Localization.Monoidal.μ (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)) (Wsheaf X)
          (localizedMonoidalUnitIso X)
          ((toPresheafOfModules X).obj (sheafification.obj          -- UNFOLDED, not A.tensorObj B
            (MonoidalCategory.tensorObj (C := MonoidalPresheaf X)
              ((toPresheafOfModules X).obj A) ((toPresheafOfModules X).obj B))))
          ((toPresheafOfModules X).obj C)).inv ≫
        MonoidalCategoryStruct.whiskerRight (C := modulesLocalizedMonoidal X)
            (<c_{A⊗B} ≫ μ_{A♭,B♭}.inv, all objects spelled as (L').obj _>)
            (sheafification.obj ((toPresheafOfModules X).obj C)) ≫
        MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
            (MonoidalCategoryStruct.tensorHom (C := modulesLocalizedMonoidal X)
              A.sheafificationCounitIso.hom B.sheafificationCounitIso.hom) C.sheafificationCounitIso.hom ≫
        (MonoidalCategoryStruct.associator (C := modulesLocalizedMonoidal X) A B C).hom
      = <native-α expansion: (α_ (L'A♭)(L'B♭)(L'C♭)).hom-driven RHS, all (L').obj _> := by
  -- objects already pinned/unfolded ⇒ reassoc is syntactic:
  simp only [Category.assoc]              -- GREEN here (head-lemma precedent L1980), bombs only on folded goals
  rw [Localization.Monoidal.associator_naturality
        (sheafificationCounitIso A).hom (sheafificationCounitIso B).hom (sheafificationCounitIso C).hom,
      Localization.Monoidal.associator_hom_app]   -- both fire on `W ≫ T ≫ α`
  …                                       -- then μ-pair cancels + tensorObjAssoc_hK_lhs_head closes
```

Then `hK_lhs` chains: `simp only [tensorObj]` (unfold the leading μ-object once), apply the pinned
lemma, then `tensorObjAssoc_hK_lhs_head` for the head. The decisive rule: **the folded
`A.tensorObj B` must NEVER appear inside a μ-object at the moment a reassoc/naturality/`Category.assoc`
runs — unfold it to `sheafification.obj (tensorObj (C:=MonoidalPresheaf X) A♭ B♭)` and pin it in the
STATEMENT.** This is the iter-016 fix generalised from the head reduction to the reassoc step.

**Confirm on `Category.assoc`/`associator_naturality`:** Mathlib's lemmas are fine *as-is* — they
fire bomb-free once the goal's objects are pinned image-forms (verified by the directive's own
"`rw [associator_naturality, associator_hom_app]` fires on a literal `W ≫ T ≫ α`"). They CANNOT be
wrapped into a pinned reassoc lemma applied via `congrArg`-peel (probe #2 bombs). The pinning must be
at the *whole-goal statement* level, never at a peeled sub-lemma.

---

## Part B — blast radius + verdict

**`LocalizedMonoidal` requires the bare-form `MonoidalCategory`** (hover-confirmed). So
`pshModMonoidal` et al. are NOT removable in isolation — `modulesLocalizedMonoidal X` ceases to
elaborate, which cascades sorries into **everything** (foundation, all 4 seams, both keystones,
`hK_rhs`, head — every decl built on the localized structure).

To eliminate the dual instance you must re-ascribe the localization to a functor whose *literal*
domain is the synonym, e.g. `sheafification' : MonoidalPresheaf X ⥤ X.Modules :=
PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)` (defeq domain, L85 comment), then define
`modulesLocalizedMonoidal` over `sheafification'`. Blast radius of THAT:

| Surface | Refs bare functor `…sheafification (𝟙 X.ringCatSheaf.obj)` | Breaks on re-ascription? |
|---|---|---|
| `μ`/localization spellings in file | **51 occurrences** (grep) | YES — each μ term becomes token-distinct from the new `sheafification'`-keyed instance (defeq, not syntactic) |
| foundation (`tensorObjLocalizedIso`, `localizedMonoidalUnitIso`) | bare | YES |
| 4 seams + 2 keystones (`…whiskerRight/Left_unit_eq_mu'`, etc.) | bare | YES |
| `hK_rhs` (GREEN), head (GREEN) | bare | YES — μ-token identity (the thing they rely on) would have to be re-established against `sheafification'` |

The forms are defeq (L85), so it is *possible*, but it is a **file-wide functor-term rename across
~51 μ sites in one commit**, and mid-refactor it re-introduces exactly the token-mismatch isDefEq
bombs the project is fighting (any decl still on the old spelling vs any on the new one). NOT
low-risk; high cascade probability.

**The effective durable fix is NOT instance deletion — it is the object-phrasing discipline**
(pin every μ-object to `(L').obj _`/`MonoidalPresheaf X`-headed forms; never let `tensorObj` sit
folded inside a μ-object). This is already validated GREEN by `tensorObjAssoc_hK_lhs_head` and is
exactly Part A. It removes the bomb class *without* touching the dual instance.

### Verdict: close `hK_lhs` INCREMENTALLY NOW (Part A pinned-lemma pattern). DEFER — and likely
### ABANDON — the instance-deletion refactor.
Reasons: (1) deletion is blocked by `LocalizedMonoidal`'s instance requirement; the only route
(functor re-ascription) is a 51-site cascade that re-creates the bomb class transiently; (2) the
object-phrasing discipline already neutralises the bomb without the refactor; (3) the head lemma
proves the incremental path closes. Revisit instance unification only as a final cosmetic pass after
the bridge is sorry-free, if at all.

## Recommendation
Generalise the iter-016 statement-pinning from the head reduction to the reassoc/naturalise step:
a `tensorObjAssoc_hK_lhs_native` lemma stated entirely in unfolded `(L').obj _` image-forms, where
`simp [Category.assoc]` + `associator_naturality` + `associator_hom_app` fire syntactically (head
lemma precedent). Keep the dual instance. Do not attempt instance deletion now.
