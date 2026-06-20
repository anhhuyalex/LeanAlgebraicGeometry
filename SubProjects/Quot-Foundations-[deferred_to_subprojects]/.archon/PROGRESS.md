# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

**Zero inline `sorry` in the dependency cone of the seed declarations + kernel-only axioms.**
Čech-independent (i=0) leg of the parent's `thm:fga_pic_representability` cone: flat base change,
generic flatness, and the Quot/Grassmannian foundations. Full arc in STRATEGY.md.

## Iter-081 disposition

Iter-080 closed 3 sorries (global 12→9): GlueDescent 1→0 (KEYSTONE `isIso_glueRestrictionHom` closed),
GrassmannianQuot 3→1 (both `represents` inverse halves + `universalQuotient_isLocallyFreeOfRank`). FBC-B
NOOPED (planValidate dropped the 0-sorry file before any scaffold landed).

**This iter dispatches THREE real prover lanes — all now backed by landed sorry stubs.** Subagents this
phase: blueprint-reviewer (all 9 chapters complete+correct; 3 active lanes GATE CLEAR), strategy-critic
(2 CHALLENGEs — both addressed in STRATEGY.md, see below), progress-critic (GR-quot CONVERGING; FBC-B +
SNAP UNCLEAR/recovering, both must land a prover this iter), mathlib-analogist `fbcb-sig` (resolved the
FBC-B capstone signature — `restrictScalars` along `B → groundRing X'`; VERIFIED to elaborate), and two
lean-scaffolders (SNAP 9 stubs + the FBC-B verified stub).

**Strategy-critic CHALLENGEs — both addressed:**
- **H⁰-vs-χ merge-back (VERIFIED, was the critic's key must-fix).** Read the parent
  `def:hilbert_polynomial` = `Scheme.hilbertPolynomial`: it is **χ-semantic** (`Φ(m)=χ(F(m))`). An H⁰
  encoding under that label would silently change the theorem. Decision (STRATEGY Q1): this i=0 leg does
  NOT close `def:hilbert_polynomial`/`def:quot_functor` (χ → sibling cohomology leg); it keeps the
  χ-independent QUOT core (`grassmannian_scheme`/representability via rank-d locally-free quotients).
  SNAP-S0 `Γ_*(X,L)` is still required (Plücker/projective coordinate ring), χ-independent. No active lane
  affected.
- **RelativeSpec parallelism.** Promoted to its own NEXT row in STRATEGY (independent of GR-quot/SNAP);
  gated on Q4 reference retrieval (01LM/01LP/01LT). Not dispatched this iter (needs the Q4 fence first).
- (The critic's "stale `## Routes` preamble" quote was not present in the current STRATEGY.md — it read a
  stale copy — but the preamble + per-iter prose + long Risks cells were trimmed regardless.)

## Current Objectives

THREE independent frontier lanes (different files, no edit race). **NEVER positional `rw`/`simp`/`erw`
under the `X.Modules`/Scheme-cat diamond**; use term-mode (`.trans`/`congrArg`/applied `map_smul`) + the
`change`-to-nested-application lever for the value-ModuleCat diamond.

1. **`AlgebraicJacobian/Picard/GrassmannianQuot.lean`** — GR-quot endgame, **1 sorry** (GATE CLEAR;
   CONVERGING per progress-critic).
   - **L2470** `tautologicalQuotient_epi` (`lem:tautologicalQuotient_epi`) — NOW UNBLOCKED: the
     joint-reflection precondition `isIso_glueRestrictionHom` is sorry-free as of iter-080. Epi of the
     tautological quotient via joint reflection across the chart cover. Closing this → GrassmannianQuot
     0-sorry, GR-quot route complete (`represents` already DONE iter-080).
   - Blueprint: `chapters/Picard_GrassmannianQuot.tex` (`lem:tautologicalQuotient_epi`, full proof
     present; GATE CLEAR). [prover-mode: prove]

2. **`AlgebraicJacobian/Picard/SectionGradedRing.lean`** — SNAP-S0 graded assembly, **9 scaffolded
   sorries** (L1843–1901; GATE CLEAR — chapter rewritten + analogist-corrected, scaffolder landed the
   brick structure this phase).
   - Fill the bricks bottom-up: `sectionsCast` (L1843), `sectionsCast_refl` (L1849),
     `gradedMonoid_eq_of_cast` (L1856), the `GradedMonoid.GMul`/`GOne` instance bodies (L1862/L1867),
     then the 4 cast-mediated coherence Eqs `sectionsMul_one_mul`/`_mul_one`/`_mul_assoc`/`_mul_comm`
     (L1874/1882/1892/1901) = `lem:sectionMul_coherent`.
   - THEN build (new decls, not yet scaffolded) the `GMonoid`/`GSemiring`/`GCommSemiring`/`Gmodule`
     assembly instances mirroring `TensorPower.Basic` field-for-field (`gnpow` defaulted; bilinearity
     FREE), per `analogies/snap-gcomm.md` + the scaffolder handoff notes in-file (L1807–1830).
   - Recipe: `analogies/snap-gcomm.md`, `analogies/snap-assoc.md`, blueprint proofs.
   - Blueprint: `chapters/Picard_SectionGradedRing.tex` (`def:sectionsCast`, `lem:sectionsCast_refl`,
     `lem:gradedMonoid_eq_of_cast`, `lem:sectionMul_coherent`, `lem:sectionGradedRing_gcommSemiring`,
     `lem:sectionGradedModule_gmodule`; GATE CLEAR). [prover-mode: prove]

3. **`AlgebraicJacobian/Cohomology/FlatBaseChangeGlobal.lean`** — FBC-B DIRECT capstone, **1 sorry**
   (L274; GATE GREEN; stub landed this phase from the analogist-verified signature).
   - **L274** `Modules.baseChangeGammaPullbackEquiv` (`thm:fbcb_global_direct`):
     `Γ(X,F)⊗_A B ≃ₗ[B] Γ(X', F')`. Proof per blueprint 3-step: LHS is LITERALLY
     `baseChangeGammaEquiv F U hU B`'s domain (start there) → transport the RHS eqLocus to `gammaModA F' ⊤`
     via `gammaTopEquivEqLocus` applied to `F' = (Scheme.Modules.pullback g').obj F` and the base-changed
     cover `{(U_i)_B}`, identifying base-changed legs with `F'`'s restriction legs via
     `pullback_spec_tilde_iso` (01I9) + `affine_base_change_pushforward` [both DONE in FlatBaseChange.lean].
     RHS `B`-module is `restrictScalars` along `pullbackGroundRingAlg B : B → groundRing X'` (no
     `Algebra B (groundRing X')` instance needed). Full design: `analogies/fbcb-pullback-equiv-sig.md`.
   - Do NOT touch FlatBaseChange.lean (the 2 frozen named legs are a next-iter discharge — see Queued).
   - Blueprint: `chapters/Cohomology_FlatBaseChange.tex` (`thm:fbcb_global_direct`; gate GREEN).
     [prover-mode: prove]

## Queued — NEXT iters

- **FBC-B reduction lemma + named-leg discharge.** (a) Scaffold `flatBaseChange_isIso_iff_gammaTensorComparison`
  (`lem:flat_base_change_reduce_global_sections`) — left as TODO this iter; needs a follow-up analogist
  pass reconciling the abstract pullback-square parametrization of `pushforwardBaseChangeMap` with the
  direct-`B` parametrization. (b) Move/fill the 2 frozen named legs `affineBaseChange_pushforward_iso` /
  `flatBaseChange_pushforward_isIso` from `baseChangeGammaPullbackEquiv` (signatures movable between
  files), then delete the dead `base_change_mate_*` apparatus (4 sorries) — P2 cleanup lane.
- **RelativeSpec `RepresentableBy` upgrade** (own lane): first reference-retrieve Q4 Stacks tags
  01LM/01LP/01LT, then upgrade `thm:relative_spec_univ` from `IsAffineHom` to a `RepresentableBy` witness.
  Independent of GR-quot/SNAP.
- **QUOT-repr core** (after SNAP-S0 + RelativeSpec): `grassmannian_scheme` + `thm:grassmannian_representable`
  via rank-d locally-free quotients (χ-independent core only — see Q1). The χ Hilbert-poly / Quot-functor
  nodes are OUT of this leg (sibling cohomology leg).

## Tracked (non-blocking blueprint debt)

- `Picard_QuotScheme.tex` `\lean{Grassmannian.representable}` UNDER-DELIVERS (weakened existence skeleton,
  omits smoothness/properness/rel-dim/tautological-quotient); strengthen or split the label before the
  QUOT-repr core lane.
- `Cohomology_FlatBaseChange.tex`: `thm:flat_base_change_pushforward` is `\leanok` but its `\uses{}` lists
  the non-`\leanok` MV-route helpers; repoint to the DIRECT route once `baseChangeGammaPullbackEquiv` lands.
  The 3 MV-route helpers (`base_changed_equalizer_diagram`/`flat_base_change_separated`/`_mayer_vietoris`)
  are legacy docs, not on the DIRECT route — mark `% NOTE: MV route only` or prune.
- 2 false-isolated DAG nodes wired up this iter (`gr_exists_isUnit_submatrix` → `chartLocus_isOpenCover`;
  `isLocalizedModule_powers_restrictScalars` → `generic_flatness`).

## Standing notes

- **Prover model:** `opus`. Re-pin a `fable` lane only with valid creds.
- **Import architecture:** root `AlgebraicJacobian.lean` imports each leaf; provers add decls to EXISTING
  files. GrassmannianQuot imports GlueDescent + GrassmannianCells + QuotScheme; FlatBaseChangeGlobal
  imports FlatBaseChange (one-way — drives the named-leg deferral).
- **GR cold-build:** validate with real `lake build AlgebraicJacobian.Picard.GrassmannianQuot` /
  `...SectionGradedRing` / `AlgebraicJacobian.Cohomology.FlatBaseChangeGlobal` (LSP hides `(kernel)
  deterministic timeout`); do NOT reintroduce `maxHeartbeats 1e6`.
- **Cross-lane import transient:** a `lake build` while a sibling's imported file is mid-edit can delete the
  import's olean on a failed rebuild — provers with cross-lane imports RETRY, don't hard-fail.
- **No LLM API key in env** — `archon-informal-agent.py` unavailable; use blueprint + Mathlib search + the
  analogist subagent.
- **GR-quot do-not-retry:** `(unit R).sections` has NO AddCommGroup/Module instance — use biproducts. C2
  naive `eqToHom` transport ill-typed — the DONE `pullbackBaseChangeTransport`+`glueData_bridge_*` are the
  transport. Value-ModuleCat diamond: `comp_apply`/`hom_comp` spellings ALL fail asymmetrically →
  `change`-to-nested-application. Bare `inv`/`infer_instance` unreliable under the diamond → spell
  `@CategoryTheory.inv _ _ _ _ (...) hinst`; build composites with `IsIso.comp_isIso'`.
- **SNAP do-not-retry:** full `MonoidalCategory (SheafOfModules)` / strong-monoidal sheafification NOT
  needed; the crux is CLOSED. Stalkwise + "presheaf+Γ-at-end" routes are DEAD. Carrier: `AddCommGrpCat`
  NOT `AddCommGrp`; a `have` mentioning `P ⊗ Q` must spell
  `MonoidalCategory.tensorObj (C := MonoidalPresheaf X) P Q`. `sectionsMul_assoc_unit` = FOUR
  cast-mediated component Eqs (NOT one GradedMonoid Eq, NOT a raw HEq).
- **FBC do-not-retry:** the mate keystone `_legs_conj` (+`_gstar_transpose`) is ABANDONED — do NOT
  re-attempt it. Named legs route via FBC-B direct (`baseChangeGammaPullbackEquiv`). RHS `B`-module is
  `restrictScalars` along `B → groundRing X'`; do NOT chase `groundRing X' = B` (that is the theorem at
  `F = O_X`, a consequence not a hypothesis).
- **Hilbert polynomial is χ, not H⁰** — the parent `def:hilbert_polynomial` is Euler-characteristic; this
  leg does NOT formalize it (sibling cohomology leg owns it). Do not build an H⁰ `Φ_s` and label it the
  Hilbert polynomial. See STRATEGY Q1.
- **Merge-back discipline:** never rename kept decls/labels/paths; never add `\leanok` by hand. Advisory
  freeze (`genericFlatness`, `affineBaseChange_pushforward_iso`, `flatBaseChange_pushforward_isIso`,
  `QuotFunctor`): keep SIGNATURES stable, fill BODIES freely (movable between files preserving signature).
