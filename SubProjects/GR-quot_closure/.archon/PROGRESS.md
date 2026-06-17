# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

**Zero inline `sorry` in the dependency cone of the seeds + kernel-only axioms** — modulo the
two χ-blocked nodes and the shared SNAP nodes, which are sourced from sibling legs at merge
(see below). This is the **GR-quot closure** extracted from *Quot-Foundations*: the
representability of the relative Grassmannian (Nitsure §1/§5; FGA Explained Ch. 5). Full arc in
`.archon/STRATEGY.md`.

**Seeds:** `thm:grassmannian_representable`, `def:grassmannian_scheme`,
`lem:tautologicalQuotient_epi` (cone = 287 blueprint nodes, 9 sorries).

## The 9 cone sorries, by disposition

1. **GR-quot — closable here (3).** `def:grassmannian_scheme`, `lem:tautologicalQuotient_epi`,
   `thm:grassmannian_representable`. The rank-`d` Grassmannian is a χ-free construction
   (constant Hilbert polynomial `Φ=d`); its own Lean decls do not need higher cohomology.
2. **SNAP — shared with sibling `FBC-B_SNAP-chain` (4).** `def:sectionsCast`,
   `lem:sectionsCast_refl`, `lem:gradedMonoid_eq_of_cast`, `lem:sectionMul_coherent` (+ the
   `gcommSemiring`/`gmodule` graded-assembly lemmas). H⁰ graded ring `Γ_*(X,L)`,
   Čech-independent. **Per user hint: keep as sorry here OR import the sibling's finished
   proofs — do not diverge the encoding.**
3. **χ-blocked — fill from cohomology leg (2).** `def:quot_functor`, `def:hilbert_polynomial`.
   In-cone via `grassmannian_scheme \uses quot_functor \uses hilbert_polynomial`, but
   `Scheme.hilbertPolynomial` is **χ-semantic** (verified: `Φ(m)=χ=Σᵢ(-1)ⁱ dim Hⁱ`, body
   `sorry` needing graded-Euler-characteristic infra). This i=0 leg has no cohomology engine →
   **keep both as sorry; never fabricate an H⁰ `Φ_s` under the χ label.**

## Current Objectives

The closable frontier is GR-quot + SNAP (SNAP only if not importing the sibling's proofs).
**NEVER positional `rw`/`simp`/`erw` under the `X.Modules`/Scheme-cat diamond**; use term-mode
(`.trans`/`congrArg`/applied `map_smul`) + the `change`-to-nested-application lever.

1. **`AlgebraicJacobian/Picard/GrassmannianQuot.lean`** — GR-quot endgame.
   - `tautologicalQuotient_epi` (`lem:tautologicalQuotient_epi`): epi of the tautological
     quotient via joint reflection across the chart cover; precondition
     `isIso_glueRestrictionHom` is sorry-free. Closing this → GrassmannianQuot route complete
     (`represents` already done).
   - Blueprint: `chapters/Picard_GrassmannianQuot.tex`. [prover-mode: prove]

2. **`AlgebraicJacobian/Picard/SectionGradedRing.lean`** — SNAP graded assembly (ONLY if not
   importing sibling proofs; coordinate with `FBC-B_SNAP-chain` first).
   - Fill bottom-up: `sectionsCast`, `sectionsCast_refl`, `gradedMonoid_eq_of_cast`, then the 4
     cast-mediated coherence Eqs `sectionsMul_{one_mul,mul_one,mul_assoc,mul_comm}` =
     `lem:sectionMul_coherent`; then the `GCommSemiring`/`Gmodule` instances mirroring
     `Mathlib.LinearAlgebra.TensorPower.Basic` field-for-field.
   - Recipe: `analogies/snap-gcomm.md`, `analogies/snap-assoc.md`, blueprint proofs.
   - Blueprint: `chapters/Picard_SectionGradedRing.tex`. [prover-mode: prove]

## Blocked / merge-sourced (do not dispatch a prover)

- **`def:quot_functor`, `def:hilbert_polynomial`** — χ-blocked (see above). Fill from the
  cohomology leg at merge-back; keep the `sorry` bodies here.
- **SNAP nodes** — if the decision is to import the sibling's proofs, treat these as
  merge-sourced too rather than re-proving.

## Tracked (non-blocking blueprint debt)

- `Picard_QuotScheme.tex` `\lean{Grassmannian.representable}` UNDER-DELIVERS (weakened existence
  skeleton, omits smoothness/properness/rel-dim/tautological-quotient); strengthen or split the
  label before claiming the full representability statement.
- `Picard_QuotScheme.tex` `def:hilbert_polynomial` ENCODING comment claims an **H⁰** encoding;
  this is inconsistent with the actual **χ** Lean decl (`QuotScheme.lean` docstring). The Lean
  source governs — do not act on the H⁰ comment.

## Standing notes

- **Prover model:** `opus`.
- **Import architecture:** root `AlgebraicJacobian.lean` imports each leaf; provers add decls to
  EXISTING files. `GrassmannianQuot` imports `GrassmannianCells` + `QuotScheme` + `GlueDescent`.
- **Cold-build validation:** `lake build AlgebraicJacobian.Picard.GrassmannianQuot` /
  `…SectionGradedRing` (LSP hides `(kernel) deterministic timeout`); do NOT add `maxHeartbeats 1e6`.
- **No LLM API key in env** — use blueprint + Mathlib search + the analogist subagent.
- **GR-quot do-not-retry:** `(unit R).sections` has NO AddCommGroup/Module instance — use
  biproducts. Value-ModuleCat diamond: `comp_apply`/`hom_comp` spellings ALL fail asymmetrically
  → `change`-to-nested-application; spell `@CategoryTheory.inv _ _ _ _ (...) hinst`; build
  composites with `IsIso.comp_isIso'`.
- **SNAP do-not-retry:** full `MonoidalCategory (SheafOfModules)` / strong-monoidal
  sheafification NOT needed; the crux is CLOSED. Stalkwise + "presheaf+Γ-at-end" routes are DEAD.
  Carrier: `AddCommGrpCat` NOT `AddCommGrp`; `P ⊗ Q` must spell
  `MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q`. `sectionMul_coherent` = FOUR
  cast-mediated component Eqs (NOT one GradedMonoid Eq, NOT a raw HEq).
- **Merge-back discipline:** never rename kept decls/labels/paths; never add `\leanok` by hand.
