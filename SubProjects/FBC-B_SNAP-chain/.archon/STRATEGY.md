# Strategy

## Goal

Close the `sorry`-bearing nodes of two Čech-independent (i=0) legs extracted from the parent
*Quot-Foundations* `thm:fga_pic_representability` cone, then merge back:

- **FBC-B** — `thm:flat_base_change_pushforward` + `thm:fbcb_global_direct` (the i=0 base-change map
  `g^* f_* F ⟶ f'_* g'^* F` is an isomorphism). The abstract affine lemma
  `affineBaseChange_pushforward_iso` is NOT a deliverable: its `\uses`-closure is disjoint from the
  goal's (leandag: goal closure = 22 nodes, all `[leanok]`/`[mathlib]` + 4 concrete scaffold targets,
  no mate/affine riders); it is recoverable later as a downstream corollary of the goal if ever needed.
- **SNAP** — `lem:sectionGradedRing_gcommSemiring` + `lem:sectionGradedModule_gmodule`: the H⁰
  graded ring `Γ_*(X,L) = ⊕_{n≥0} Γ(X, L^{⊗n})`.

End-state: zero project `sorry` in the 71-node closure, zero project axioms, kernel-only axioms.
Names/labels are the parent's so finished work merges back unchanged.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---|---|---|---|
| FBC-B i=0 — concrete-tilde equalizer (Stacks 02KH) | ACTIVE | 2–4 | ~250–450 | `tensorEqLocusEquiv`; tensor⊗ preserves finite products; qcqs-pushforward-qcoh (likely project-build) | heaviest node = MV qcqs gluing (effort 1737); glue residual = restriction-naturality of the concrete tilde iso (≠ off-path abstract mate); qcqs-pushforward-qcoh absent from Mathlib |
| SNAP — section graded ring | ACTIVE | 2–4 | ~120–300 (net DELETION ~900L bridge) | `MonoidalCategory (LocalizedMonoidal)` pentagon/triangle/hexagon; `Functor.Monoidal (L')` | Option-A LANDING (4 failed iters = MECHANISM not math): land via SKELETON refactor (re-base 5 defs + `sorry` broken coherences, single agent, NO concurrent writers) + prover fill — NOT monolithic; RISK = μ-boundary re-summoned in re-proofs (Open Q) → single-global-instance fallback |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|---|---|---|---|---|---|---|
| FBC RegroupHelper | inherited (parent) | ~120 | `Cohomology_RegroupHelper` | `regroupEquiv` `(A⊗_R R')⊗_A M ≅ R'⊗_R M` | `eT` identity-bridge + `TensorProduct.induction_on` beats transparent diamonds | `erw [TensorProduct.zero_tmul]` for zero-branch |
| FBC affine lemma + global infra | inherited (parent) | ~? | `FlatBaseChange.lean`, `FlatBaseChangeGlobal.lean` | `pullback_spec_tilde_iso` (01I9); `eqLocus` H⁰-equalizer; `baseChangeGammaEquiv`; element-level `gammaResA`/`leftRes`/`rightRes`/`gammaTopEquivEqLocus` | element-level equalizer presentation | A-linear "build-ahead" pins retired (phantom nodes) |
| SNAP tensor crux + chain | inherited (parent) | ~? | `SectionGradedRing.lean` | `isIso_sheafification_whiskerRight_unit`; `tensorObjAssoc`; `tensorPowAdd` axiom-clean | `W.whiskerRight`@`ModuleCat (ULift ℤ)` + `modToAb` + coequalizer descent (NOT stalks) | instance synth flaky in long `≪≫` — pass `@asIso _ _ _ _ f h`; `whiskerRightIso` iso-arg breaks `(C:=MonoidalPresheaf X)` |

## Routes

The two legs run in parallel (independent files: `Cohomology/*` vs `Picard/SectionGradedRing.lean`).

**FBC route — CONCRETE-tilde equalizer (mate + abstract `affineBaseChange` both off-path).** The
abstract `affineBaseChange_pushforward_iso` is mate-stuck (no working section-level route) and is NOT
on the goal's critical path. The per-affine-piece identification needs only the concrete module tilde
`Γ((U_i)_B,F')≅Γ(U_i,F)⊗_A B` = `pullback_spec_tilde_iso` (01I9, DONE), on charts AND (separated case)
affine overlaps. Critical path, all leaves `[leanok]`/`[mathlib]`:
`pullback_spec_tilde_iso`+`gamma_finite_equalizer`+`flat_preserves_equalizer` →
`baseChange_sheafConditionFork_tensorIso` → `flatBaseChange_..._of_isSeparated` →
`flatBaseChange_..._mayerVietoris` (qcqs; t=1 base case = affine tilde; separatedness used only on the
provably-separated cover intersections) → bridge `flatBaseChange_isIso_iff_gammaTensorComparison`
(`\uses` only `def_map` + qcqs-pushforward-qcoh; residual = a naturality square, NOT the mate) →
`flatBaseChange_pushforward_isIso` (goal). The concrete capstone `baseChangeGammaPullbackEquiv`
(`Γ(X,F)⊗_A B≃ₗ Γ(X',F')`) is the separated-case module equiv (helper
`baseChangeEqLocusToPullbackGamma`, overlaps via `pullback_spec_tilde_iso`). The `base_change_mate_*` +
`affineBaseChange_pushforward_iso` decls are dead off-path **riders** (proved Lean legs reference their
signatures); do NOT re-attempt the mate. Excision step: delete the riders the iter the goal lands.

**SNAP route — Option A alignment.** The hand-built `tensorObj F G :=
(F♭⊗_p G♭)^#` + a parallel `MonoidalCategory` proof of its associator coherence
(`tensorObjAssoc_eq_localizedAssociator`) is a PARALLEL-API anti-pattern: it forced a 10-iter
dual-`MonoidalCategory`-instance μ-token-divergence wall (analogist `snap-instance-design`,
verdict ALIGN_WITH_MATHLIB). Pivot: route the 5 structural defs (`tensorObj`, `tensorObjAssoc`,
`tensorBraiding`, `tensorObjUnitIso`, `tensorObjRightUnitor`) through the single canonical localized
product `⊗_loc` of `modulesLocalizedMonoidal X` (= Mathlib's `LocalizedMonoidal L W ε`). Then
`tensorObjAssoc_eq_localizedAssociator` is `rfl` (the open crux is DELETED, not proved), the ~900L
bridge machinery (`:hK_*`/seam/head lemmas) is deleted, and the ~10 downstream coherences
(`tensorPowAdd_assoc`, the 3 section cores, `sectionsMul_*`, `sectionMul_coherent`) re-prove cheaply
via Mathlib pentagon/triangle/hexagon + `Functor.Monoidal (L')` lax-coherences. KEEP the
localization-precondition machinery (`Wsheaf`/`W_isMonoidal`/`isIso_sheafification_whiskerRight_unit`)
and BOTH monoidal instances — dual-instance DELETION is REFUTED (load-bearing). Then graded assembly
(`gcommSemiring`/`gmodule`) → the H⁰ graded ring `Γ_*(X,L)`. Stalkwise / "presheaf+Γ-at-end" routes DEAD.
**LANDING MECHANISM (the 4-iter failure was mechanism, not math).** A monolithic refactor (re-base +
re-prove in one agent) times out and gets killed; iter-025's 3 concurrent writers raced into a broken
half-migration. Land as TWO steps: (1) ONE refactor agent (no concurrency), green-preserving: re-base
the 5 defs onto `⊗_loc` and `sorry` every coherence proof that breaks → commit GREEN-WITH-SORRIES
(`tensorObjAssoc_eq_localizedAssociator` becomes `rfl`, wall sorry DELETED); (2) a PROVER lane fills the
now-easy coherence sorries. Never >1 agent on the file at once; cold-build file AND root after step (1).

## Open key strategic questions
- **SNAP μ-boundary one layer down (sc022 CHALLENGE).** Under Option A, do the ~10 re-proved coherences
  stay entirely inside the single `⊗_loc` structure, or do any re-summon the localized↔presheaf-instance
  μ-boundary (the original wall)? Analogist `snap-instance-design` "μ-placement asymmetry" argues NO:
  μ is spent ONCE, opaque, inside the `sectionsMul`/`tensorObjLocalizedIso` defs; the coherences are pure
  `⊗_loc` pentagon/triangle/hexagon + `Γ∘L'` lax — neither reconciles two associators. UNVERIFIED until
  the prover re-proves them. REVERSAL: if ≥2 coherences cold-bomb on the μ-boundary, Option A merely moved
  the wall → escalate to single-global-instance (give `X.Modules` the localized instance directly).
- **FBC glue = ABSTRACT mate cocycle (iter-026 pivot; supersedes the 6-sub-lemma natTrans telescope).**
  The ON-PATH glue `..._ring_square_mate_glue` is the restriction-NATURALITY of the concrete tilde iso
  `pullback_spec_tilde_iso` (NOT the dead OFF-PATH `affineBaseChange_pushforward_iso`/`base_change_mate_*`).
  The concrete-whisker natTrans telescope (`ring_square_glue_natTrans`) is OVER-BUDGET (elaborates @800k-hb,
  kernel-bombs @200k whnf'ing the `tilde`/`extendScalars` carrier at statement-seam AND `.app M` fold).
  Replaced (mathlib-analogist `analogies/fbc-glue-carrier-whnf.md`) by an ABSTRACT carrier-free
  `ring_square_cocycle` (no `tilde`/`pullback`/`extendScalars` in statement or proof → no whnf can fire),
  proved by pure mate calculus, closing the heavy glue goal with ONE `exact` (carriers → metavars).
  The 4 leg facts are already-closed concrete lemmas (geom/alg leg-nat + unit-triangle + comp-coherence).
- **qcqs-pushforward-qcoh (Stacks 01XJ) absent from Mathlib (sc022).** Verified MISSING this iter. Required
  by the DOWNSTREAM bridge `flatBaseChange_isIso_iff_gammaTensorComparison` (not the glue). Plan: build
  project-side via `[prover-mode: mathlib-build]` when the bridge is reached; budget +1–2 iters / ~80–150 LOC.

## Mathlib gaps & new material

Gaps to fill:
- FBC-B concrete chain: scaffold `baseChange_sheafConditionFork_tensorIso`, `flatBaseChange_pushforward_isIso_of_isSeparated`, `flatBaseChange_pushforward_mayerVietoris`, `flatBaseChange_isIso_iff_gammaTensorComparison` (none exist in Lean yet — blueprint blocks present). Mathlib needs (verify each iter): `tensorEqLocusEquiv` (flat∘equalizer), tensor⊗ preserves finite products. **`qcqs-pushforward-is-qcoh` (Stacks 01XJ): confirmed ABSENT from Mathlib (sc022) → build project-side, `mathlib-build` mode, when the downstream bridge is reached (own scaffold node, +1–2 iters).**

New project material:
- `FlatBaseChangeGlobal.lean` element-level equalizer presentation (`baseChangeGammaEquiv`; capstone
  `baseChangeGammaPullbackEquiv` via `restrictScalars` along `B → groundRing X'`).
- `SectionGradedRing.lean` graded comm-semiring + module assembly for `Γ_*(X,L)`.
