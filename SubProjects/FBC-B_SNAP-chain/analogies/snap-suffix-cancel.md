# Analogy: apply a known reassoc fact when the goal's suffix is a defeq-fragile term

## Mode
api-alignment

## Slug
snap-suffix-cancel

## Iteration
019

## Question
Is `generalize`-the-suffix the right Mathlib idiom for "apply a known reassoc fact
`head : f = g` to a goal `f ≫ tail = g ≫ tail` whose `tail` is a heavy
defeq-fragile localized composite that whnf-bombs every full-goal `rw`/`erw`/`simp`"?

## Project artifact(s)
- `AlgebraicJacobian/Picard/SectionGradedRing.lean:2058-2122` — `tensorObjAssoc_hK_lhs_native`,
  the `sorry` whose post-reduction goal is `head ≫ tail = s1.inv ≫ tail`.
- `…:1900-2049` — `tensorObjAssoc_hK_lhs_head` (the proven `head : f = s1.inv`), itself
  closed via a `show`-to-uniform-localized recast on a SMALLER (tail-free) goal.
- `…:1847-1880` — `assocCommonForm`, whose unfold exposes the RHS `s1.inv ≫ tail`.

## Decisions identified

### Decision: which idiom applies an equality of the *prefix* of a composite
- **Mathlib idiom**: the `@[reassoc]` attribute and the `reassoc_of%` term elaborator
  (`Mathlib.Tactic.CategoryTheory.Reassoc`, confirmed via leansearch:
  `Mathlib.Tactic.Reassoc.reassocExpr'`). `@[reassoc] lemma head : f = g` auto-generates
  `head_assoc {Z'} (h : … ⟶ Z') : f ≫ h = g ≫ h` with `Category.assoc`
  (`Mathlib.CategoryTheory.Category.Basic`) baked in. Standard application: `rw [head_assoc]`
  or `exact head_assoc _`. **This idiom assumes composition is cheap to unify.**
- **Project's path / proposal**: comp here is NOT cheap — the
  `LocalizedMonoidal`↔`modulesLocalizedMonoidal X` comp-instance forces `kabstract`/`isDefEq`
  to whnf the μ/`Localization.fac` terms in `tail`, so the idiomatic `rw [reassoc_of% head]`
  over the full goal bombs (200000 hb). Proposal: `generalize hT : tail = t` to delete `tail`
  from every term the unifier touches, then `exact reassoc_of% head`.
- **Gap**: divergent-but-justified. Mathlib has NO category-theory precedent for "generalize a
  fragile suffix" because Mathlib's comps never whnf-bomb; the project is off the idiomatic
  path for an environmental reason (instance heaviness), not a modelling error. `generalize`
  is a sound *general Lean* technique (kabstract-based abstraction), correctly used here.
- **Cost of divergence**: none structural — `generalize` is local to this proof, leaves no
  parallel API. Only cost is the one-line `hT` and the occurrence-match obligation (Q2).
- **Verdict**: PROCEED (with the refinement below).

## Why generalize works here (and its limit)
The bomb is the motive/`kabstract` re-typechecking the WHOLE goal — including `tail` — under
the comp-instance. `generalize hT : tail = t` replaces `tail` by an opaque local `t`
(its type is a fixed `_ ⟶ _` hom-type, independent of the abstraction → motive stays
type-correct, low risk). The follow-up `exact reassoc_of% head` then unifies only
`f' ≫ t =?= f ≫ t`, i.e. the **prefix** `f' =?= f`; `t` is never whnf'd. The heavy `tail`
is gone from the unifier. **NECESSARY-not-sufficient** (the project's recurring
statement-pinning pattern, cf. `fbc-b2-crux-state` / the head lemma itself): the residual
prefix unification (head-lemma μ's vs goal μ's) survives, and if their *spellings* differ it
may still bomb — apply the head lemma's own `show`-to-uniform-localized recast to the now
tail-free prefix before `exact`. generalize makes that recast tractable (no tail dragged).

## Q2 — will generalize match `tail` on both sides
`generalize` uses `kabstract` (defeq up to *instances* transparency, keyed on `tail`'s head
symbol) — cheaper than a full motive recheck, but NOT purely syntactic. Requirement: LHS-`tail`
and RHS-`tail` must be token-identical, else only matched occurrences abstract and the residual
`exact` either fails or forces a `tail =?= tail` defeq → the same bomb. **The load-bearing
guard is already in the plan**: step-1 `conv_rhs => rw [assocCommonForm]; simp only […]`
re-spells the RHS tail to match the native LHS tail (prover-confirmed bomb-free). After
`generalize`, verify BOTH sides show `t` (if one still shows the literal composite, the
alignment was incomplete). Motive-ill-typed failure: low risk here (`t` is a non-dependent
hom).

## Q3 — strictly better statement-level shape
Yes. Add `@[reassoc]` to `tensorObjAssoc_hK_lhs_head` (or define the sibling
`…_head_assoc {Z'} (g) : μ.inv ≫ (c ▷ Z) ≫ μ'.hom ≫ g = s1.inv ≫ g :=
reassoc_of% tensorObjAssoc_hK_lhs_head A B C`). Then close `native` with
`exact tensorObjAssoc_hK_lhs_head_assoc _ _ _ _` after the conv_rhs alignment. This is the
genuine Mathlib idiom, is one step, and AVOIDS the generalize occurrence-mismatch (the `?g`
metavar is assigned by structural `≫`-matching). It **moves the bomb off `tail`** (g never
whnf'd) but does NOT avoid the prefix residual — and it STILL needs LHS/RHS tail
token-identical so the single `?g` unifies on both sides without a defeq check. So `@[reassoc]`
+ `exact _` and `generalize` + `reassoc_of%` are equivalent in where a bomb could remain (the
prefix); the `@[reassoc]` form is cleaner and more idiomatic, `generalize` is the more forceful
fallback when even structural tail-matching trips the instance.

## Recommendation
PROCEED with the suffix-removal route. Prefer the **`@[reassoc]` sibling lemma** as primary:
`@[reassoc]` on `tensorObjAssoc_hK_lhs_head`, then after the (mandatory, load-bearing)
`conv_rhs` tail-alignment, `exact tensorObjAssoc_hK_lhs_head_assoc _ _ _ _`. Keep
`generalize hT : tail = t; exact reassoc_of% tensorObjAssoc_hK_lhs_head A B C` as the fallback
if structural tail-matching in the `exact` still trips the comp-instance. For EITHER route, if
the prefix unification bombs, re-apply the head lemma's `show`-to-uniform-localized recast to
the tail-free prefix first — that residual, not the suffix, is the real remaining wall.
