# Analogy: cancelling a two-source `Localization.Monoidal.μ` hom∘inv pair

## Mode
api-alignment

## Slug
snap-mu-identity

## Iteration
016

## Question
Canonical way to cancel `μ.hom ≫ μ.inv` for `Localization.Monoidal.μ` when the two occurrences are
defeq-but-not-token-identical (directive hypothesised "hidden `Localization.fac`/`IsIso` witnesses
inside μ"). Sub-qs: (1) reducible-transparency μ-cancel simp lemma? (2) μ's witness a `Subsingleton`
for `Subsingleton.elim`/`convert`? (3) does Mathlib's own LocalizedMonoidal coherence form+cancel
such pairs, or avoid them?

## Project artifact(s)
- `SectionGradedRing.lean:1890–1975` — `tensorObjAssoc_hK_lhs_head` (the residual single μ-pair cancel; sorry @1975).
- `SectionGradedRing.lean:1980–2045` — `tensorObjAssoc_eq_localizedAssociator_hK_lhs` (interchange-merge sorry; same wall).
- `SectionGradedRing.lean:1777–1793` — keystone `sheafification_whiskerRight_unit_eq_mu'`.
- `SectionGradedRing.lean:1402–1414` — `pshModMonoidal` (and braided/symmetric) re-export = ROOT CAUSE.
- `SectionGradedRing.lean:87` — `MonoidalPresheaf X` abbrev.

## HEADLINE: the directive's premise is MIS-DIAGNOSED, and the wall is a project-local dual instance
`μ L W ε X Y` (`Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean:184`) is
`((tensorBifunctorIso L W ε).app X).app Y` — a **plain function of `L W ε X Y` with NO `IsIso` /
`Localization.fac` witness argument**. Two occurrences at the same `L W ε X Y` are LITERALLY the
same term. So:
- there is **no per-occurrence witness** to `Subsingleton.elim`/`convert` (sub-q 2 = vacuous; the
  fac/IsIso data lives inside `Lifting₂.iso` and is fully determined by `L W ε`, not a free arg);
- the ONLY thing that can differ between two μ occurrences is the **explicit object arguments `X Y`**.

EMPIRICAL ROOT CAUSE (LSP, iter-016, at the @1975 sorry, goal already flattened by `show`+`simp
[Category.assoc]`): the two cancelling μ pp-print **identically** as
`μ … ((toPresheafOfModules X).obj (sheafification.obj ((toPresheafOfModules X).obj A ⊗ (toPresheafOfModules X).obj B))) ((toPresheafOfModules X).obj C)`
yet `rw [Iso.hom_inv_id_assoc]` → "pattern `Iso.hom ?self ≫ Iso.inv ?self` not found" and
`simp only [Iso.hom_inv_id_assoc]` → "no progress". The hidden difference is the **`⊗` inside the
object argument**: the project has TWO defeq-but-distinct `MonoidalCategory` instance TERMS on the
presheaf category —
  - `PresheafOfModules.monoidalCategory` (found via the synonym `MonoidalPresheaf X`), used by the
    keystone's explicit `MonoidalCategory.tensorObj (C := MonoidalPresheaf X) …`;
  - `pshModMonoidal` (L1402 re-export on the bare form `PresheafOfModules X.ringCatSheaf.obj`),
    picked by default synthesis when the `show`/statement writes `A♭ ⊗ B♭`.
One μ comes from the keystone (instance #1), the other from the lemma statement (instance #2); pp
hides the instance, so they look identical but are different terms ⇒ the syntactic cancel can't fire.
(The file already documents the same hazard for `◁` at L2082.)

Reconciling them in-proof is NOT cheap: `rw [show (A♭ ⊗ B♭) = MonoidalCategory.tensorObj (C := MonoidalPresheaf X) … from rfl]`
**(deterministic) isDefEq-timeout at 200000 heartbeats** — checking instance#2-tensor =?= instance#1-tensor
whnf's μ → `Localization.fac` → the documented kernel bomb. So `erw`/`simp`-with-defeq/`convert` all bomb.

## Decisions identified

### Decision: how to cancel the two-source μ-pair
- **Mathlib idiom**: `Iso.hom_inv_id` / `Iso.hom_inv_id_assoc` (+ `inv_hom_id` variants), keyed on the
  iso term by discrimination tree — fires at the matcher's transparency, does **NOT** whnf μ. This is
  EXACTLY what Mathlib's own `pentagon` (`Basic.lean:361–370`) and `triangle` (`418–435`) use to
  collapse their many μ.hom∘μ.inv pairs (e.g. `simp only [… Iso.inv_hom_id, … Iso.inv_hom_id_assoc]`,
  `← cancel_mono (μ …).inv`). There is no μ-specific cancel lemma and none is needed.
- **Why it doesn't fire here**: the project's two μ occurrences are NOT token-identical (object-arg
  instance divergence above), so the syntactic match fails; forcing it via defeq bombs.
- **Gap**: divergent-with-cost. Not a missing lemma — a route/instance-shape problem.
- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision: the `pshModMonoidal` re-export (dual monoidal instance)
- **Mathlib idiom**: ONE canonical monoidal instance per category; phrase coherence at `(L').obj X`
  for a single `C`-object obtained via `EssSurj`/`objObjPreimageIso` (`Basic.lean:331–334, 414–415`),
  so every μ in a coherence proof is at `(L').obj Xᵢ` and all μ-pairs are token-identical by
  construction. Mathlib NEVER tensors two ambiguous-instance objects inside a μ object-arg.
- **Project path**: a second instance term `pshModMonoidal` on the bare form coexists with Mathlib's
  `PresheafOfModules.monoidalCategory` on the synonym; both appear in μ object-args. Classic parallel
  /duplicate-instance fragmentation.
- **Gap**: divergent-with-cost (now load-bearing in the stuck proof).
- **Cost**: every μ-pair that mixes a keystone-introduced μ (synonym instance) with a
  statement-introduced μ (bare instance) is uncancellable; reconciliation bombs `isDefEq`. Has
  churned `hK_lhs` for 5 iters.
- **Verdict**: ALIGN_WITH_MATHLIB (durable) / NEEDS structural re-route (immediate).

## Recommendation
Stop hunting a μ-cancel lemma and stop the Subsingleton-witness route — both are dead ends (no
witness exists; the cancel lemma exists but needs token-identical μ). **Re-shape the route so both
μ object-args are built with ONE instance term, at STATEMENT level (never in-proof).** Two tiers:

1. **Immediate (prover-fireable this iter)** — pin the inner presheaf tensor to a single instance
   end-to-end. Concretely, ascribe `(C := MonoidalPresheaf X)` to EVERY inner tensor `A♭ ⊗ B♭` that
   ends up inside a μ object-argument, in the *statements/`show`s* of `assocCommonForm`,
   `tensorObjAssoc_hK_lhs_head`, `tensorObjAssoc_eq_localizedAssociator_hK_lhs`, and anything feeding
   them (so they match the keystone `_eq_mu'`). Then both μ become the SAME term and the residual
   cancel is the pure-syntactic `rw [Iso.hom_inv_id_assoc]` (no defeq, no whnf, no bomb), after which
   the already-GREEN whisker-merge + `left_triangle_components` tail closes it. Do the pinning in the
   STATEMENT, not via a `show`/`rw … from rfl` over the existing bare-instance goal — that path
   isDefEq-bombs (validated @1975).
2. **Durable (must-fix to stop recurrence)** — eliminate the dual instance: do not register
   `pshModMonoidal`/`pshModBraided`/`pshModSymmetric` as separate instance terms colliding with
   Mathlib's; instead route all tensor positions through one form so synthesis always returns one
   constant. Then defeq between the two forms never arises anywhere and this whole class of
   μ-token-identity stalls disappears.
