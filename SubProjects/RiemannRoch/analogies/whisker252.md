# Analogy: normalising `◁`/`▷` whisker calculus across two defeq `MonoidalCategoryStruct` instances (sheafification `.val`/`forget₂` carrier)

## Mode
api-alignment

## Slug
whisker252

## Iteration
252

## Question
The `sorry` in `sheafifyTensorUnitIso_hom_natural` (~L1954 of
`AlgebraicJacobian/Picard/TensorObjSubstrate.lean`) reduces, after
`sheafifyTensorUnitIso_hom_eq` + `simp only [MonoidalCategory.tensorHom_def]`, to a pure
whisker identity. The directive asked: (1) a canonical Mathlib idiom to normalise `◁`/`▷`
across two defeq-but-not-syntactic `MonoidalCategoryStruct` instances so `whisker_exchange`,
`comp_whiskerRight`, `whiskerLeft_comp` fire; (2) the precise form of a "second
carrier-normalisation brick" analogous to `sheafifyTensorUnitIso_hom_eq := rfl`; (3) a Mathlib
precedent for the same sheafification/`forget₂`-carrier situation.

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1909-1954` — `sheafifyTensorUnitIso_hom_natural` (the open `sorry`).
- `…:1853-1868` — `sheafifyTensorUnitIso_hom_eq := rfl` (first carrier brick; uses `MonoidalCategory.whiskerRight/whiskerLeft (C := PsM forget₂)`).
- `…:1061-1095` — `sheafifyTensorUnitIso` (def; carries `letI instMS` at L1071).
- `…:331-372` — `tensorObj_assoc_iso` (carries the same `letI instMS` at L339).
- `…` — `restrictScalarsId_map` (project lemma, the `restrictScalars (𝟙)` syntactic strip).

## Root cause (established LIVE via lean_multi_attempt, not inferred)

The carrier `_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)` is where the
`MonoidalCategoryStruct`/`MonoidalCategory` instance actually lives. The DEFEQ spellings
`PresheafOfModules (Sheaf.val X.ringCatSheaf)` ≡ `PresheafOfModules X.ringCatSheaf.obj` do **not**
resolve an instance — instance synthesis is head-symbol-keyed and FAILS on them:

> `failed to synthesize  MonoidalCategoryStruct (_root_.PresheafOfModules X.ringCatSheaf.obj)`
> `failed to synthesize  MonoidalCategoryStruct (_root_.PresheafOfModules (Sheaf.val X.ringCatSheaf))`

(That synthesis failure is exactly why `sheafifyTensorUnitIso` (L1071) and `tensorObj_assoc_iso`
(L339) carry `letI instMS := inferInstanceAs (…forget₂…)`.)

The sheafification unit `η = (sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 …)).unit` and the
objects `(sheafification.obj _).val` are spelled over the `Sheaf.val` carrier. The η-whiskers
in the goal were FROZEN into `sheafifyTensorUnitIso.hom` when `instMS` (a `letI`-bound instance,
distinct *term* from the globally-synthesised one even though defeq) was in scope; the
`p ⊗ₘ q` whiskers produced by `MonoidalCategory.tensorHom_def` use the directly-synthesised
instance. **`MonoidalCategory.whiskerRight` is NOT a separate decl** (empty local-search) — it is
the `MonoidalCategoryStruct.whiskerRight` projection via the `MonoidalCategory` namespace; so the
split is purely the *instance term* (instMS-letI vs synthesised), not a projection path.

Consequences, all VERIFIED by replaying tactics at the goal:

- `rw [← whisker_exchange]`, `rw [Category.assoc]`, `rw [whisker_exchange]` **DO fire** inside a
  single-instance group (e.g. `p ▷ Q ≫ P' ◁ q`). The directive's "ALL fail to fire" premise is
  false — the calculus works within a group.
- Plain `rw`/`simp [Category.assoc]` **cannot reassociate ACROSS the `≫` joining the two groups**
  (the RHS join unifies; the LHS join — `(…p,q whiskers…) ≫ (…η whiskers…)` — does not; `simp`
  leaves it bracketed, a 2nd `Category.assoc` errors `(?f ≫ ?g) ≫ ?h not found`).
- `erw [Category.assoc]` **DOES bridge that join** (keyed-defeq; right-associates the LHS fully).
  This is the same `.val`/`forget₂` `erw` idiom that closed D2′ (memory `ts-d2-closed-iter250`).
- BUT `whisker_exchange` **cannot fire on the cross-group crossing** `P' ◁ q ≫ η_{P'} ▷ Q'` even
  via `erw`, because the single `whisker_exchange` lemma must serve BOTH whiskers with ONE
  instance, and the two whiskers carry different (defeq) instance terms.
- Folding whiskers back to `⊗ₘ` (`← tensorHom_def`, `← tensorHom_comp_tensorHom`) **fails even
  via `erw`** → the "convert to `tensorHom` and use the interchange axiom" route is dead.

## Decisions identified

### Decision: author a NEW `:= rfl` "whisker-projection" carrier brick (the directive's proposal) vs. unify the instance at the source

- **Mathlib idiom**: Mathlib has **no** lemma that normalises `◁`/`▷` across two defeq instances.
  The whisker calculus (`MonoidalCategory.whisker_exchange`, `comp_whiskerRight`,
  `whiskerLeft_comp`, `tensorHom_def`/`tensorHom_def'`) is the canonical idiom and is keyed on
  the *single* `MonoidalCategoryStruct` instance Lean infers. The Mathlib mechanism for
  transporting an instance across a defeq type spelling is **`inferInstanceAs`** (precisely the
  project's `letI instMS := inferInstanceAs (…)` at L339/L1071). For cross-spelling *rewriting*,
  the idiom is `erw` (keyed-defeq matching). There is no `whiskerLeft_def`/`whiskerRight_def`
  unfolding to `tensorHom`, and no `@[simp]` whisker-normalisation set.
- **Project's proposed path**: a second `:= rfl` brick restating each `f ▷ X`/`X ◁ f` on the
  canonical instance (or converting the goal to `tensorHom`).
- **Gap**: divergent-and-wrong (as a cure). A `:= rfl` projection brick cannot reconcile the two
  *instance terms* in a way `whisker_exchange` can consume (the crossing mixes them under one
  lemma var); the `tensorHom` conversion is dead (folding fails, VERIFIED).
- **Cost of divergence**: a new parallel brick would not unblock `whisker_exchange` on the
  crossing; iterations spent tuning it would repeat the D2′ 11-iter detour. Worse, it adds a
  third bespoke carrier brick alongside `sheafifyTensorUnitIso_hom_eq`/`restrictScalarsId_map`
  without addressing the instance split.
- **Verdict**: ALIGN_WITH_MATHLIB (use `inferInstanceAs`-transport + `erw`, the project's already
  proven idiom) — do **not** author a new whisker-projection brick.

## Recommendation (concrete, ranked; lemma names verified)

The single true blocker is the **instance split** between the `p,q` group and the η group. Fix it
at the *source* so both groups share one instance, then the calculus fires.

**Primary fix — unify the instance, then run the whisker calculus with `erw` join-bridges:**

1. Add, at the very top of `sheafifyTensorUnitIso_hom_natural` (verbatim copy of L339/L1071):
   ```lean
   letI instMS : MonoidalCategoryStruct (_root_.PresheafOfModules (Sheaf.val X.ringCatSheaf)) :=
     inferInstanceAs (MonoidalCategoryStruct
       (_root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat)))
   ```
   so that `p ⊗ₘ q` (and its `tensorHom_def` whiskers) elaborate against the SAME instance as the
   η-whiskers baked into `sheafifyTensorUnitIso.hom`. This is the `inferInstanceAs` instance
   transport Mathlib intends for defeq-carrier synthesis failure. (NOTE: verifying this in
   isolation via `lean_multi_attempt` is blocked by a tool artifact — `inferInstanceAs` reports
   "expected type contains metavariables" when injected mid-proof — but the identical `letI` is
   proven to compile at L339 and L1071.)
2. Keep `rw [sheafifyTensorUnitIso_hom_eq, sheafifyTensorUnitIso_hom_eq] ; rw/erw [← Functor.map_comp …] ; congr 1`.
3. Do **not** `simp only [MonoidalCategory.tensorHom_def]` blindly. Expose crossings with
   `erw [Category.assoc]` (VERIFIED to bridge the formerly-split node), then apply the whisker
   calculus on the now-single-instance, now-adjacent crossings:
   - `MonoidalCategory.whisker_exchange` on the middle crossings,
   - `MonoidalCategory.comp_whiskerRight` / `MonoidalCategory.whiskerLeft_comp` (used `←`) to merge,
   managing associativity with further `erw [Category.assoc]` between steps (the whisker lemmas
   need the `◁`/`▷` syntactically ADJACENT under one `≫`).
4. Finish with sheafification-unit naturality:
   `(PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.val)).unit.naturality p`
   (and `… q`). VERIFIED shape:
   `p ≫ η_{P'} = η_P ≫ (sheafification ⋙ SheafOfModules.forget ⋙ restrictScalars (𝟙)).map p`.
   The RHS carries a spurious `restrictScalars (𝟙)` vs the goal's
   `(SheafOfModules.forget _).map (sheafification.map p)` — strip it with the project lemma
   `restrictScalarsId_map` (the same syntactic `restrictScalars (𝟙)` strip used in D2′), then the
   two sides coincide.

**Fallback fix — `convert` past the crossing:** if the whisker calculus is still fiddly, after
unifying the instance reduce both sides to `(p ≫ η_{P'}) ▷ Q ≫ (a P').val ◁ (q ≫ η_{Q'})` and the
RHS analogue, then `convert` + `congr 1` + the two `unit.naturality`/`restrictScalarsId_map`
rewrites on the resulting `(p ≫ η_{P'}) = (η_P ≫ …)` subgoals.

**Lemma inventory (verified to exist / fire):**
`MonoidalCategory.tensorHom_def` (fires forward; `[reassoc]`),
`MonoidalCategory.whisker_exchange`, `MonoidalCategory.comp_whiskerRight`,
`MonoidalCategory.whiskerLeft_comp`, `Category.assoc` (apply via `erw` to bridge the join),
`AlgebraicGeometry.Scheme.Modules.restrictScalarsId_map`,
`(PresheafOfModules.sheafificationAdjunction _).unit.naturality`.
Do NOT rely on `← MonoidalCategory.tensorHom_def` or
`MonoidalCategory.tensorHom_comp_tensorHom` here — both fail to fold the brick η-whiskers
(VERIFIED), so the `tensorHom`-interchange route is closed.

## Precedent (directive Q3)
This IS a recurring Mathlib-shaped situation, handled in-project the Mathlib-aligned way:
`Sheaf.val X.ringCatSheaf ≡ X.presheaf ⋙ forget₂ CommRingCat RingCat` by `rfl`, but
`PresheafOfModules`'s monoidal structure synthesises only on the explicit `forget₂` spelling
(Mathlib's `PresheafOfModules`/`SheafOfModules` monoidal API is built on `CommRingCat`-valued
bases; the `RingCat`-valued composite gets the struct only through the composition, and the
`.obj`/`.val` re-spelling defeats head-keyed synthesis). The intended remedy is `inferInstanceAs`
instance transport (the `letI instMS` idiom), not an upstream PR; cross-spelling rewriting uses
`erw`. Same shape, same cure as D2′.
