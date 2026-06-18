# Project Progress

## Current Stage

prover  (GR-seed cone DELIVERED iter-001; SNAP-S0 residue ACTIVE — approach pivoted iter-007 to
Mathlib monoidal-localization transport)

## Stages
- [x] init
- [x] autoformalize
- [ ] prover — GR-seed cone delivered (iter-001). SNAP-S0 residue (3 sorries in
      `SectionGradedRing.lean`) ACTIVE; iter-007 pivots to inheriting the monoidal coherence from a
      Mathlib `LocalizedMonoidal` structure on `X.Modules`. χ-blocked nodes remain DEFERRED.
- [ ] polish — after SNAP residue closes.

## End-state overview

**ACHIEVED (iter-001):** the goal seed `AlgebraicGeometry.Grassmannian.represents` is sorry-free
and axiom-clean (`#print axioms` = `[propext, Classical.choice, Quot.sound]`, NO `sorryAx`). The
GR-quot representability cone (Nitsure §1/§5; FGA Explained Ch. 5) is delivered and merge-ready.

**ACTIVE (iter-006→007):** the SNAP-S0 H⁰ section graded ring `Γ_*(X,L)=⊕_{n≥0}Γ(X,L^{⊗n})`
(Stacks 01CV) residue. iter-006 closed 6/9 sorries axiom-clean (cast machinery, graded `GMul`/`GOne`,
left-unit law). The 3 residual coherence laws (`tensorPowAdd_zero_right` succ,
`sectionsMul_mul_assoc`, `sectionsMul_mul_comm`) were stuck on hand-proving triangle/pentagon/hexagon
over the obfuscated double-braiding `tensorObjAssoc`.

**iter-007 PIVOT (mathlib-analogist ALIGN_WITH_MATHLIB, `analogies/tensorobjassoc.md`; blueprint
GATE CLEAR).** Stop hand-rolling coherence. Build the full `MonoidalCategory`/`SymmetricCategory`
on `X.Modules` via Mathlib monoidal localization, so assoc/pentagon/triangle/hexagon are INHERITED.
This dissolves the auditor's `tensorObjAssoc` non-canonicity flag by construction. The SNAP layer is
self-contained in `SectionGradedRing.lean` and used by no other file (disjoint from the delivered
`represents` seed cone — refactor is safe). `tensorObjAssoc` etc. are NOT protected.

## Current Objectives

1. **`AlgebraicJacobian/Picard/SectionGradedRing.lean`** — Build the Mathlib monoidal-localization
   infrastructure, axiom-clean (additive; do NOT touch the 3 existing coherence sorries this iter):
   - **Instance `(J.W.inverseImage (toPresheaf X.ringCatSheaf.obj)).IsMonoidal`** via
     `MorphismProperty.IsMonoidal.mk'` [verified, Mathlib rev b80f227]:
     - `whiskerRight` field ← the already-proven general whisker brick `ztensor_whisker_localIso`
       (L1416, arbitrary `f` with `(toPresheaf).map f ∈ J.W`), bridging `W' f ⟺ (toPresheaf).map f ∈ J.W`
       via `isIso_sheafification_map_iff` [expected name].
     - `whiskerLeft` field ← braiding-conjugate the above using `PresheafOfModules.symmetricCategory`
       (presheaves of modules are symmetric) — the trick Mathlib uses in the opposite direction at
       `Sites/Monoidal.lean:147`.
     - multiplicativity ← free for an `inverseImage`.
   - **`MonoidalCategory X.Modules` + `SymmetricCategory X.Modules`** via `LocalizedMonoidal`
     `sheafification W' ε` (ε picks unit `unitModule X`) [verified] + `Localization/Monoidal/Braided`.
   - Module sheafification IS the localization functor: `(sheafification α).IsLocalization
     (J.W.inverseImage (toPresheaf R₀))` — `Mathlib/Algebra/Category/ModuleCat/Sheaf/Localization.lean:48`
     [verified]; project `sheafification` = this at `α = 𝟙`.

   **Stop condition:** land the `IsMonoidal` instance + the inherited `MonoidalCategory`/
   `SymmetricCategory` axiom-clean (`mathlib-build` invariant: no sorry in the new infra). The 3
   pre-existing coherence sorries are NOT this iter's target — they are closed NEXT iter by rewiring
   `tensorObjAssoc`/the coherence laws onto the inherited structure. If genuinely blocked on a field,
   hand off a precise decomposition.

   Blueprint: `chapters/Picard_SectionGradedRing.tex` — `def:sheafModule_W_isMonoidal`,
   `def:sheafModule_monoidalStructure`, anchors `lem:monoidalLocalization_mathlib`,
   `lem:moduleSheafification_isLocalization_mathlib` (GATE CLEAR complete+correct, iter-007).
   Verbatim construction recipe + Mathlib file:line: `analogies/tensorobjassoc.md`.

   NOT free (do not attempt): `(J.W (A:=AddCommGrpCat)).IsMonoidal` (`Sites/Monoidal.lean:149`) does
   NOT transfer (abelian `⊗_ℤ`, not the relative module tensor); the inverseImage-along-monoidal-
   functor instance (`Localization/Monoidal/Basic.lean:71`) does NOT fire (`toPresheaf` is oplax,
   not strong monoidal). Build `W'.IsMonoidal` directly (two fields, one already done).

   Hazard (ARCHON_MEMORY): value-`ModuleCat` diamond — term-mode congruence (`congrArg`/`.trans`/
   `Iso.ext`), not positional `rw`/`simp`/`erw`. Carrier idioms (file head ~L66): `P ⊗ Q` =
   `MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q`; abelian-group cat = `AddCommGrpCat`.
   [prover-mode: mathlib-build]

## Deferred (NOT objectives this iter)

- **3 coherence sorries (`SectionGradedRing.lean`):** `tensorPowAdd_zero_right` succ (L2031),
  `sectionsMul_mul_assoc` (L2091), `sectionsMul_mul_comm` (L2107). Closed NEXT iter by rewiring onto
  the inherited monoidal/symmetric structure built this iter — NOT by hand-induction. Also: the
  iter-006 auditor flagged `sectionsMul_mul_one` (L2053) as transitively contaminated via the
  `tensorPowAdd_zero_right` succ sorry — same rewire resolves it.
- **χ-blocked (`QuotScheme.lean`, 4 sorries):** `hilbertPolynomial` (χ-semantic), `QuotFunctor`,
  `Grassmannian` functor. Need a higher-cohomology engine this i=0 leg lacks; filled from the
  cohomology leg at merge. Genuine gap; not blind-formalizable.
- **`RelativeSpec.lean`:** Route-A sibling chapter, no phase in this leg. Out of scope.
- **Out-of-cone debt:** weak `Scheme.Grassmannian.representable` skeleton; goal does not rely on it.

## Blueprint health (non-gating, deferred to merge-back)

blueprint-reviewer (iter-007) GATE CLEAR on the active SectionGradedRing chapter. Dangling refs
remain in DEFERRED chapters: `Cohomology_FlatBaseChange.tex` (covers 2 non-existent files + ~15
refs), `QuotScheme.tex` (~13 crefs), `GlueDescent.tex` (2 labels). All target labels outside the
active SNAP cone — extraction artifacts that resolve at merge-back. Do NOT edit (byte-identical-to-
parent discipline).

## Standing notes

- **Prover model:** `opus`.
- **Cold-build validation:** `lake build AlgebraicJacobian.Picard.SectionGradedRing` (LSP hides
  `(kernel) deterministic timeout`); do NOT add `maxHeartbeats 1e6`.
- **No LLM API key in env** — use blueprint + Mathlib search + the analogist subagent.
- **Merge-back discipline:** the iter-007 monoidal-localization pivot DIVERGES from the sibling
  `FBC-B_SNAP-chain` encoding by design (sibling stuck at 9 sorries on the same hand-rolled wall;
  standing directive sanctions refactoring out of dead-ends). Still never add `\leanok` by hand.
