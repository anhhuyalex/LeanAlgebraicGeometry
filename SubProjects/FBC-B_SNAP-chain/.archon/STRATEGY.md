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
| FBC-B i=0 — concrete-tilde equalizer (Stacks 02KH) | ACTIVE‖ | 2–4 | ~250–450 | `tensorEqLocusEquiv`; tensor⊗ preserves finite products; qcqs-pushforward-qcoh | heaviest node = MV qcqs gluing (effort 1737); bridge residual = naturality square; verify qcqs-pushforward-qcoh exists else project material |
| SNAP — section graded ring | ACTIVE‖ | 1–3 | ~120–300 | `DirectSum.Ring` assembly | builds the H⁰ object `Γ_*(X,L)`; residue = cast-coherence + graded assembly |

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

**SNAP route.** Crux `IsIso(sheafification.map(η_P ▷ Q))`, associator, `tensorPowAdd` all CLOSED
axiom-clean. Remaining: cast-coherence (`sectionMul_coherent`) → graded assembly
(`gcommSemiring`/`gmodule`). Produces the H⁰ graded ring `Γ_*(X,L)`. Full `MonoidalCategory
(SheafOfModules)` NOT needed; stalkwise / "presheaf+Γ-at-end" routes are DEAD.

## Mathlib gaps & new material

Gaps to fill:
- FBC-B concrete chain: scaffold `baseChange_sheafConditionFork_tensorIso`, `flatBaseChange_pushforward_isIso_of_isSeparated`, `flatBaseChange_pushforward_mayerVietoris`, `flatBaseChange_isIso_iff_gammaTensorComparison` (none exist in Lean yet — blueprint blocks present). Mathlib needs (verify each iter): `tensorEqLocusEquiv` (flat∘equalizer), tensor⊗ preserves finite products, qcqs-pushforward-is-qcoh.

New project material:
- `FlatBaseChangeGlobal.lean` element-level equalizer presentation (`baseChangeGammaEquiv`; capstone
  `baseChangeGammaPullbackEquiv` via `restrictScalars` along `B → groundRing X'`).
- `SectionGradedRing.lean` graded comm-semiring + module assembly for `Γ_*(X,L)`.
