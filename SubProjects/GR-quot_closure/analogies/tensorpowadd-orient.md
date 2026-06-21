# Analogy: orientation of the tensor-power additivity comparison `tensorPowAdd`

## Mode
api-alignment

## Slug
tensorpowadd-orient

## Iteration
023

## Question
Re-define `tensorPowAdd L m m' : L^⊗m ⊗ L^⊗m' ≅ L^⊗(m+m')` by recursion on the SECOND
index `m'` (right-unitor base + assoc⁻¹∘right-whisker succ) instead of the FIRST index `m`
(left-unitor base + braiding + two `eqToIso` reindexers succ). Is 2nd-index the canonical
Mathlib orientation for tensor-power additivity, and does removing the braiding let a Mathlib
coherence tactic close `tensorPowAdd_assoc`? Is there any braided-coherence tactic that could
close the CURRENT residual without refactoring?

## Project artifact(s)
- `SectionGradedRing.lean`:2202-2216 — `tensorPowAdd`, CURRENT 1st-index recursion (base = left
  unitor `tensorObjUnitIso ≪≫ eqToIso (Nat.zero_add)`; succ = `α ≪≫ (L^k ◁ β_{L,L^m'}) ≪≫ α⁻¹
  ≪≫ (μ_{k,m'} ▷ L) ≪≫ eqToIso (Nat.succ_add)`). Threads a braiding + 2 non-rfl reindexers.
- `SectionGradedRing.lean`:3193-3394 — `tensorPowAdd_assoc`, succ case STUCK 6 iters on the
  braided residual (1 `β`, hexagon+pentagon); inline `sorry` @3394.
- `SectionGradedRing.lean`:109-113 — `tensorPow` (right growth: `tensorPow L (n+1) = tensorPow L n ⊗ L`).

## Decisions identified

### Decision: recursion orientation (1st index vs 2nd index)
- **Mathlib idiom**: recurse on the SECOND argument, matching `Nat.add`'s own recursion and the
  right-growth of the power. Canonical precedent — monoid powers:
  - `npowRec` (`Mathlib.Algebra.Group.Defs`): `npowRec (n+1) a = npowRec n a * a` — RIGHT growth,
    the exact shape of the project's `tensorPow`.
  - `pow_succ` (`Mathlib.Algebra.Group.Defs`): `a ^ (n+1) = a ^ n * a`.
  - `pow_add` (`Mathlib.Algebra.Group.Defs`): `a ^ (m+n) = a^m * a^n`, PROVEN by `induction n`
    (the SECOND arg) with `pow_succ` + `mul_assoc` ONLY — no commutativity. Reproduced green:
    `| zero => rw [Nat.add_zero, pow_zero, mul_one] | succ n ih => rw [pow_succ, ← mul_assoc,
    ← ih, ← pow_succ, Nat.add_succ]`. This is the proposed refactor, one categorification up
    (`*`→`⊗`, `mul_assoc`→`α_`/pentagon, `mul_one`→`ρ_`).
  - `Mathlib.LinearAlgebra.TensorPower.Basic` (`TensorPower.gMul`, `TensorPower.cast`,
    `PiTensorProduct.tmulEquiv`) does additivity via the index-type equiv `Fin m ⊕ Fin n ≃ Fin (m+n)`
    (NON-recursive), so it doesn't dictate a recursion side — but it too is associativity-only
    (`cast` + reindex, no braiding). No general CATEGORICAL tensor-power additivity iso exists in
    Mathlib (this is the project's genuine gap).
- **Project's current path**: recursion on the FIRST index. Because BOTH `tensorPow` and `Nat.add`
  grow/recurse on the right, recursing on the LEFT forces the freshly-added `L` (right edge of
  `tensorPow L (k+1)`) to be transported across `tensorPow L m'` — manufacturing a BRAIDING
  `tensorBraiding L (tensorPow L m')` and two non-rfl `eqToIso`s (`Nat.zero_add`, `Nat.succ_add`).
- **Gap**: divergent-and-wrong. The braiding is an ARTIFACT of mis-orienting the recursion, not
  intrinsic to additivity (`pow_add` needs none). It converts a SOUND pentagon into a braided
  hexagon, and — per Q3 below — Mathlib has NO tactic to discharge the hexagon.
- **Cost of divergence**: 6 stuck iters; the entire iter-018→022 helper tower
  (`tensorObjWhiskerRightIso_tensorBraiding_natural` @3348, the σ-naturality "diamond solve") exists
  ONLY to push the spurious braiding through the bridges. All of it evaporates under the refactor.
- **Verdict**: ALIGN_WITH_MATHLIB → refactor to 2nd-index recursion.

### Decision: closing tactic once the braiding is gone
- **Mathlib idiom**: `monoidal` (`Mathlib.Tactic.CategoryTheory.Monoidal.Basic`) — the successor to
  `coherence` (`coherence` warns "use `monoidal` instead"). Closes any equality of morphisms built
  from `α_`/`λ_`/`ρ_`/`◁`/`▷`/`𝟙` (pentagon, triangle). VERIFIED green on the 4-object pentagon and
  on the refactored `tensorPowAdd_assoc` BASE case (`m''=0`, right-unitor triangle) after a one-line
  `simp only [tpowAdd, Iso.trans_hom, whiskerRightIso_hom, whiskerLeftIso_hom, eqToIso_refl,
  Iso.trans_refl]; monoidal`.
- **Localized `X.Modules` caveat**: `monoidal` runs against ANY `MonoidalCategory` instance, so it
  fires on the inherited `X.Modules` monoidal AFTER the project's `_eq` canonical bridges
  (`tensorObjWhiskerRightIso_eq`/`_eq`/`tensorObjAssoc`, route-(b) of `analogies/whisker-synonym.md`)
  have rewritten the hand-built isos to canonical `α_`/`▷`/`◁`. The succ case still needs `ih`
  (a non-structural atom) folded in first; `monoidal` is the FINISHER for the structural glue, not a
  one-shot. Pattern: peel succ clauses → bridge `f ▷ (A⊗B)` to `(f ▷ A) ▷ B` via
  `associator_inv_naturality_left_assoc` (pure associator, NOT braiding) → `rw [ihR]` (ih whiskered
  `▷ L`) → `monoidal`. The `eqToHom (add_assoc …)` reindex bookkeeping is dispatched by the project's
  EXISTING helpers (`tensorObjWhiskerRightIso_eqToIso`, `eqToIso_trans`,
  `tensorObjIso_tensorPowAdd_reindex`-style `subst`) — and is present in the FROZEN assoc statement
  REGARDLESS of orientation, so it is not a new cost.
- **Verdict**: PROCEED with `monoidal` as finisher (+ one `associator_inv_naturality_left_assoc`
  bridge per succ step). Import `Mathlib.Tactic.CategoryTheory.Monoidal.Basic` (already transitively
  present via `import Mathlib`).

### Decision: is the refactor NECESSARY or merely convenient? (no braided-coherence escape hatch)
- **Mathlib idiom**: there is NO braided/symmetric coherence DECISION tactic. `monoidal`/`coherence`
  handle associators+unitors ONLY. VERIFIED: `monoidal` on the braided hexagon
  `α ≫ β_ X (Y⊗Z) ≫ α = (β_ X Y ▷ Z) ≫ α ≫ (Y ◁ β_ X Z)` STRIPS the structural isos but leaves the
  raw `β`'s → "unsolved goals". Braided coherence in Mathlib is discharged only by invoking the
  axioms by hand (`BraidedCategory.hexagon_forward`/`hexagon_reverse`, `SymmetricCategory.symmetry`,
  `whisker_exchange`). So the CURRENT braided residual genuinely has no push-button closer.
- **Verdict**: refactor is NECESSARY, not just convenient — there is no tactic that would close the
  current hexagon residual in place.

## Recommendation
PROCEED with the proposed 2nd-index refactor — it is the canonical orientation (`npowRec`/`pow_add`,
`Mathlib.Algebra.Group.Defs`), and it is mathematically forced: with `tensorPow` and `Nat.add` both
right-growing, only 2nd-index recursion keeps the new `L` at the right edge of source AND target, so
NO braiding and NO `eqToIso` appear in the BODY. Verified facts (generic `MonoidalCategory` mock,
`lean_run_code`): (1) the refactored `def` elaborates with no `eqToIso`, no braiding, and does NOT
even require `[BraidedCategory C]`/`[SymmetricCategory C]`; (2) `tensorPowAdd_assoc` base case closes
by `monoidal`; (3) the succ case goal contains ONLY `α_`/`▷`/`◁` + folded atoms — ZERO braidings —
and reduces to pentagon (`monoidal`) after folding `ih` (whisker `ih` by `▷ L`, bridge the one
`f ▷ (A⊗B)` via `associator_inv_naturality_left_assoc`). Refactored body:
```lean
noncomputable def tensorPowAdd (L : X.Modules) (m m' : ℕ) :
    tensorObj (tensorPow L m) (tensorPow L m') ≅ tensorPow L (m + m') :=
  match m' with
  | 0      => tensorObjRightUnitor (tensorPow L m)                         -- m+0 = m  (rfl)
  | (c+1)  => (tensorObjAssoc (tensorPow L m) (tensorPow L c) L).symm
                ≪≫ tensorObjWhiskerRightIso (tensorPowAdd L m c) L          -- m+(c+1)=(m+c)+1 (rfl)
```
Signature is unchanged (frozen). Downstream: the `m''`-induction of `tensorPowAdd_assoc` becomes
pure pentagon; the entire braiding-bridge tower (`tensorObjWhiskerRightIso_tensorBraiding_natural`
and the 018–022 σ-naturality machinery) is no longer needed for assoc. Keep `tensorBraiding`/`_eq`
only if the deferred commutativity lemmas still want them. NOTE: `tensorPowAdd_zero_right`
(`μ_{n,0} = ρ`) becomes `rfl`/`tensorPowAdd_zero`, and `tensorPowAdd_succ` flips to the 2nd-index
succ clause — both consumers (`gMul`, `sectionsMul_mul_assoc`) only use `tensorPowAdd` through its
hom, so they are insulated, but their helper rewrites that name `tensorPowAdd_succ`/`_zero_right`
must be re-derived (cheap, both `rfl`).
