# Analogy: does the scheme Picard group law need a coherent monoidal category, or only existence-of-isos?

## Mode
api-alignment

## Slug
ts-picard-direct-216

## Iteration
216

## Question
Does the commutative-group structure on locally-trivial iso-classes genuinely
require only existence-of-associativity-iso (NOT a coherent natural associator,
NO pentagon, NO localizer monoidality)? Is the locally-trivial associator
buildable directly (à la the in-file `tensorObj_isLocallyTrivial`) from
`tensorObj_restrict_iso`, making the general-site whiskering apparatus
(`isLocallyInjective_whiskerLeft_of_W`, `(J.W).IsMonoidal`, d.1/d.2 stalk-⊗)
vestigial dead code?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:775-787` — §2 docstring: full `MonoidalCategory (X.Modules)` deliberately NOT built; group law from 4 existence-of-iso lemmas "mirroring Mathlib's `CommRing.Pic`".
- `…:903-946` — `tensorObj_assoc_iso`, built via ROUTE (d) whiskering (Steps 1/3 = `W_whiskerRight/Left_of_W`, Step 2 = `a.mapIso α`).
- `…:301-601` — the whiskering apparatus: `isLocallyInjective_whiskerLeft_of_W` (**open sorry, L546**, the 6-iter blocker), `W_whiskerLeft/Right_of_W`, `isIso_sheafification_map_of_W`, the stalk-linear d.1 section.
- `…:1004-1108` — `tensorObj_restrict_iso` (sorry L1082, the H1 funnel) + `tensorObj_isLocallyTrivial` (GREEN modulo restrict_iso) — the gluing template the planner cites.

## Decisions identified

### Decision 1: group-law substrate — coherent monoidal category vs. existence-of-iso

- **Mathlib idiom**: `CommRing.Pic R := Shrink (Skeleton (SemimoduleCat R))ˣ`
  (`Mathlib/RingTheory/PicardGroup.lean:407-412`). The `CommGroup` comes from
  `(…)ˣ` (units) of `Skeleton.instCommMonoid`, which is
  `commMonoidOfSkeletalBraided` over `monoidOfSkeletalMonoidal`
  (`Mathlib/CategoryTheory/Monoidal/Skeleton.lean:38-47, 80-81`). **The monoid
  laws are literally:**
  ```
  one_mul  X     := hC ⟨λ_ X⟩
  mul_one  X     := hC ⟨ρ_ X⟩
  mul_assoc X Y Z := hC ⟨α_ X Y Z⟩      -- hC : Skeletal C, i.e. (X ≅ Y) → X = Y
  mul_comm  X Y  := hC ⟨β_ X Y⟩
  ```
  Each axiom is discharged by feeding ONE iso (`⟨α_ X Y Z⟩`, a `Nonempty`) to
  `Skeletal`. The pentagon/triangle/hexagon coherence carried by the
  `MonoidalCategory` typeclass is **never invoked** in any monoid-law proof.
  So Mathlib's *own* Picard-group construction logically consumes only the
  existence of the associator/unitor/braiding isos. (It gets them "for free"
  from the bundled `MonoidalCategory ModuleCat` instance, but the laws don't
  touch coherence.)
- **Project's current path**: builds the group law directly on iso-classes of
  locally-trivial modules from four existence-of-iso lemmas (`tensorObj_assoc_iso`,
  `tensorObj_left/right_unitor`, `tensorObj_braiding`, `exists_tensorObj_inverse`),
  with no `MonoidalCategory (X.Modules)` instance.
- **Gap**: identical-in-substance. The project re-derives exactly the proof
  obligations of `monoidOfSkeletalMonoidal` (one `Nonempty(≅)` per axiom). It
  cannot literally reuse `Skeleton.instMonoid` because that needs a full
  `MonoidalCategory (X.Modules)` instance — whose pentagon fields would require
  the natural coherent associator, i.e. strictly MORE than the blocked route
  already wants. Mathlib has no scheme-level Picard idiom (the file's own TODO
  L59-61 lists "connect to invertible sheaves on Spec R" as future work).
- **Cost of divergence**: none. Building a coherent `MonoidalCategory` to use
  `Skeleton` would be *more* expensive, not less.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** — scheme-level construction absent
  from Mathlib; the project's design is correctly aligned to the ring-level
  idiom's actual substrate (existence-of-iso, not coherence). Planner claim #1
  CONFIRMED.

### Decision 2: associator route — general-site whiskering vs. `tensorObj_restrict_iso`

- **Mathlib idiom**: the only thing `monoidOfSkeletalMonoidal` ever needs from
  the associator is `⟨α_ X Y Z⟩` — a single iso. It builds NO localizer
  monoidality, NO `(J.W).IsMonoidal`, NO stalkwise-tensor commutation. The
  whole `(J.W).IsMonoidal`/whiskering apparatus has no counterpart in the
  Mathlib Picard pipeline.
- **Project's current path**: `tensorObj_assoc_iso` is built via ROUTE (d):
  transport the global presheaf associator `α` through sheafification, using
  `W_whiskerLeft/Right_of_W` to pull the inner sheafification out of the nested
  `tensorObj (tensorObj M N) P`. Those bottom out in
  `isLocallyInjective_whiskerLeft_of_W` (open sorry), whose two residuals are
  the Mathlib-absent d.1/d.2 stalk-⊗-over-a-varying-ring machinery (~300 LOC of
  apparatus L301-601 hangs off this).
- **Gap**: divergent-with-cost. The whiskering route is an over-engineered way
  to obtain a datum (`Nonempty((M⊗N)⊗P ≅ M⊗(N⊗P))`) that a lighter route
  supplies. For **locally-trivial** M,N,P (the only case the group law touches)
  the associator is obtainable from `tensorObj_restrict_iso` alone — the same
  single ingredient `tensorObj_isLocallyTrivial`, the unitors, the inverse, and
  the bifunctor all already funnel through. Closing `tensorObj_restrict_iso`
  (H1: presheaf-level `pushforwardPushforwardAdj` / sectionwise extension of
  scalars) thus retires the *entire* whiskering+stalk apparatus as dead code.
- **Cost of divergence (current route)**: a 6-iter-stuck sorry plus ~300 LOC of
  whiskering/stalk scaffolding, whose terminal dependency (d.2 stalk-⊗ over the
  varying ring) is the project's own "genuinely Mathlib-absent (largest piece)"
  (L543-544). All of it avoidable.
- **CAVEAT the planner must budget (do not under-scope)**: "build the associator
  directly by gluing, mirroring `tensorObj_isLocallyTrivial`" understates the
  work. `tensorObj_isLocallyTrivial` proves a **Prop** — `∀ x, ∃ U, Nonempty(…≅𝒪_U)`
  — purely pointwise, with NO overlap compatibility. The associator is **global
  data**: a single iso of sheaves on all of X. You cannot assemble it from
  pointwise-chosen trivialization isos (arbitrary local isos do not agree on
  overlaps). The correct construction:
  on each open `Uᵢ` of a common trivialising cover, form the **canonical**
  ```
  ((M⊗N)⊗P)|Uᵢ ≅ (M|⊗N|)⊗P|  --[restrict_iso, twice]
              ≅ M|⊗(N|⊗P|)     --[canonical PRESHEAF associator on restrictions]
              ≅ (M⊗(N⊗P))|Uᵢ  --[restrict_iso, twice]
  ```
  Because `tensorObj_restrict_iso` is natural and the presheaf associator is
  natural/canonical, these local isos **do** agree on overlaps, so a
  "Hom-of-sheaves-is-a-sheaf" gluing assembles the global iso. This needs:
  (i) `tensorObj_restrict_iso` (the named funnel), (ii) the canonical presheaf
  associator (`PresheafOfModules.monoidalCategoryStruct.associator`, already
  available — it is Step 2 of the current route), and (iii) a gluing-of-isos
  lemma + the overlap-naturality proof. Item (iii) is a real, bounded cost — but
  it does NOT touch `(J.W).IsMonoidal`, d.1, or d.2. (One could even skip the
  cover entirely and glue the canonical local isos directly via the sheaf
  condition on internal Hom, but the cover form matches the in-file template.)
- **Verdict**: **ALIGN_WITH_MATHLIB** — drop the whiskering/`(J.W).IsMonoidal`/
  stalk route; build `tensorObj_assoc_iso` from `tensorObj_restrict_iso`
  + canonical presheaf associator + gluing. Planner claims #2/#3 CONFIRMED with
  the gluing caveat.

## Recommendation

The planner is right on all three counts, with one scoping correction. (1) The
group law needs only existence-of-iso, exactly as Mathlib's `Skeleton`
monoid-law proofs show (`mul_assoc := hC ⟨α⟩`); the project's no-`MonoidalCategory`
design is the *correct* alignment, and building a coherent monoidal category to
reuse `Skeleton` would be strictly harder. (2)+(3) The general-site whiskering
apparatus (`isLocallyInjective_whiskerLeft_of_W` and its `(J.W).IsMonoidal` /
d.1 / d.2 dependents, ~300 LOC + the 6-iter sorry) is **vestigial**: it exists
only to realise an associator datum that, for locally-trivial M,N,P, follows
from `tensorObj_restrict_iso` — the single ingredient through which
`tensorObj_isLocallyTrivial`, the unitors, and the inverse already pass. The
project is NOT condemned to build d.2 / `(J.W).IsMonoidal`. Refactor: re-route
`tensorObj_assoc_iso` through `tensorObj_restrict_iso` and delete the whiskering
section; concentrate all remaining effort on the **single** linchpin
`tensorObj_restrict_iso` (H1 presheaf `pushforwardPushforwardAdj`). Budget the
associator's gluing-of-compatible-local-isos step (the one piece "mirror
`tensorObj_isLocallyTrivial`" hides, because that lemma is a Prop and the
associator is global data) — a bounded cost, not a Mathlib gap.
