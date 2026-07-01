# Strategy

## Goal

Close the `sorry`-bearing nodes of the **Grassmannian-quotient representability** cone (the
Čech-independent / H⁰ leg of the parent's `thm:fga_pic_representability` cone; Nitsure §1/§5,
FGA Explained Ch. 5), then merge back into *Quot-Foundations*:

- **GR-quot core** — `def:grassmannian_scheme`, `thm:grassmannian_representable`,
  `lem:tautologicalQuotient_epi`: the rank-`d` Grassmannian as a scheme glued from affine
  charts via the `GL_d` cocycle, representing the rank-`d`-quotient functor. χ-free (the
  Hilbert condition is constant rank `d`).
- **SNAP-S0** — `def:sectionsCast`, `lem:sectionsCast_refl`, `lem:gradedMonoid_eq_of_cast`,
  `lem:sectionMul_coherent` (+ graded assembly): the H⁰ section graded ring `Γ_*(X,L)`,
  Čech-independent. **Shared with the sibling `FBC-B_SNAP-chain`** — keep as sorry here or
  import the sibling's proofs (user hint).
- **χ-blocked** — `def:quot_functor`, `def:hilbert_polynomial`: in-cone via the blueprint
  `\uses` wiring, but χ-semantic (need higher cohomology this leg lacks). Sourced from the
  cohomology leg at merge; kept as `sorry` here.

End-state: zero project `sorry` in the closable part of the 287-node cone, zero project axioms,
kernel-only axioms. Names/labels/paths are the parent's so finished work merges back cleanly.

## Phases & estimations

**Leg closable scope COMPLETE.** GR functor-representability (`represents`) + section graded ring
`Γ_*(X,L)` (through invertible-`L` `GCommSemiring`) + the capped SNAP-S1 module stretch are ALL
delivered 0-sorry, axiom-clean. No live prover frontier remains. The leg is in a delivered /
awaiting-merge terminal state; the only open phases below are intentional out-of-leg deferrals. (Goal
boundary: the goal-named `thm:grassmannian_representable` = smooth-PROJECTIVE representability is delivered
only as a weak skeleton — the substantive content is `represents`/`grassmannian_universal_property`; the
smooth+projective+`relative_spec_*` residue is out-of-cone, parent-owned. See Open questions.)

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|---|---|---|---|---|---|
| χ-blocked nodes (`hilbert_polynomial`/`quot_functor`; downstream `sectionGradedModule_fg`, `hilbertPoly_of_sectionModule`) | DEFERRED — out of this i=0 leg | — | — | higher-cohomology / Euler-char engine (absent here) | `_fg` = Serre-finiteness/cohomology node (its blueprint needs properness+ampleness+coherence, cites Hartshorne II.5); `hilbertPoly` = Euler-char extraction; neither is a project sorry (blueprint pin only, no Lean decl) — both closable only in the cohomology leg, filled at merge |
| Blueprint marker/pin reconciliation + 356 `lean_aux` coverage debt + dormant broken refs | MERGE-BACK | — | — | — | extraction artifacts; labels owned by parent; resolve at merge, do NOT edit in-leg |

## Completed

`Iters (done@ · used)` = the iter the phase finished and how many iters it took. `inherited` =
delivered in the parent before this leg branched (no this-leg iter cost); this-leg phases carry
their actual iter span.

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|---|---|---|---|---|---|---|
| GR-cells/glue/sep/proper | inherited | ~1310 | `GrassmannianCells.lean`, `GlueDescent.lean` | charts, cocycle, `Grassmannian.scheme`, `isSeparated`, `isProper`, keystone `isIso_glueRestrictionHom` (0-sorry) | `IsLocalization.Away.lift`; `ValuativeCriterion`; cocycle telescopes via rotMid; effective descent NOT stalks | `Matrix.det_updateColumn` absent; `Spec.map_comp` rw fails on Scheme-cat diamond |
| GR-quot inverse | inherited | ~? | `GrassmannianQuot.lean` | `grPointOfRankQuotient` (Nitsure §5 inverse) | equivalence-transport; joint reflection across chart cover | value-ModuleCat diamond: never positional rw |
| GR-seed `represents` (goal) | 001 · 1 | ~? | `GrassmannianQuot.lean` | `represents` sorry-free + axiom-clean (goal seed DELIVERED) | equivalence-transport across chart cover | disjoint from SNAP/χ — SNAP shape cannot disturb it |
| GR-quot / repr — tautological quotient epi (closable GR cone) | ≤031 · — | ~? | `GrassmannianQuot.lean`, `GlueDescent.lean` | `tautologicalQuotient_epi` PROVED (last GR sorry); `universalQuotient_isLocallyFreeOfRank` — closable GR cone now 0-sorry | chart-local epi via `pullback_map_tautologicalQuotient` + surjectivity of chart immersions | `representable` weak-skeleton tracked-debt is OUT of the closable cone |
| SNAP-S0 phase (ii) GCommSemiring (invertible `L`) | 031 · 4 (028→031) | ~? | `SectionGradedRing.lean` | `sectionGradedRing_gcommSemiring` (Stacks 01CR/01CV); brick 1′ `tensorPowAdd_succ_left_braided`; `tensorBraiding_{self_eq_id,hexagon_forward,symm}`; `braiding_canonical_self_eq_id`; `tensorPowAdd_comm`; `sectionsMul_mul_comm` (auto) — `Γ_*(X,L)` is a graded CommSemiring for invertible `L` | generic-`M` braided core (mirror B6 `_assoc_succ_core`, pin `M:=LocalizedMonoidal`, maxRecDepth 4000); hand-built-first β-split via brick 2; β∘β=refl telescoping (`reassoc_of% hsymm`, no `monoidal`); basis-local descent for `β_{L,L}=𝟙` | canonical-first β-split DEAD (`braiding_tensor_right_hom` won't fire on hand-built `tensorObj`); order-PRESERVING `tensorPowAdd_succ_left` = WRONG glue (use order-reversing brick 1′); `Scheme.Modules.hom_ext`=⊤-trap (use `TopCat.Sheaf.hom_ext` on basis) |
| SNAP-S2 Hilbert–Serre engine | inherited | ~1470 | `QuotScheme.lean`, `GradedHilbertSerre.lean` | `IsRatHilb.ofDiffEq`; `gradedModule_hilbertSeries_rational` (00K1) | Route-2 ambient-subquotient pairs sidestep quotient gradings | bundled `IsInternal` over quotient carrier = hard `isDefEq` dead end |
| QUOT P1+gap1+gap2 | inherited | ~990 | `QuotScheme.lean` | schematic/proper support; `isIso_fromTildeΓ`; `isLocalizedModule_basicOpen` | equivalence-transport beats `IsContinuous`; open-imm pullback-unit IS Final | general-U `_of_cover` unprovable (basic-open only) |
| SNAP-S0 foundation → B1–B7 assoc → ∀L GSemiring | 007–027 · ~14 | ~? | `SectionGradedRing.lean` | crux `isIso_sheafification_whiskerRight_unit`; `tensorObjAssoc`; `tensorPowAdd` def; ★ `tensorObjAssoc_eta_factor_sheaf`; entire B1–B7 `tensorPowAdd_assoc`/`sectionsMul_mul_assoc` (∀L); `sectionGradedRing_gsemiring` (01CV) — all axiom-clean | Mathlib monoidal-localization + bridge `tensorObjIso`; coequalizer descent (NOT stalks); pin generic `M` to `LocalizedMonoidal` synonym + `maxRecDepth 4000` + comp-bridge `hc`; 2nd-index re-orient kills braided residual; element-level `congrArg` dissolves diamond (B7); `gradedMonoid_eq_of_cast` + `erw` bilinearity; `⨁`=`DirectSum ℕ` | `exact` default head ⇒ heartbeat blowup; `repeat erw` timeout; `monoidal` stalls on opaque iso pairs; `example` Semiring triggers codegen → `Nonempty` thm |
| SNAP-S0 phase (ii) PRIMARY braiding=id | 028 · 1 | ~? | `SectionGradedRing.lean` | `tensorBraiding_self_eq_id_of_isInvertible` (Stacks 01CR), axiom-clean; `IsInvertible` re-signed to carry trivializing basis as data | basis-local sheafification descent (Route A): presheaf β=`TensorProduct.comm`=id per open; descend via `TopCat.Sheaf.hom_ext` (basis) + unit injectivity; ring-diamond dissolved by explicit `Module.Invertible` arg (defeq) | `Scheme.Modules.hom_ext`=⊤-TRAP (use underlying `TopCat.Sheaf Ab`); `rw`/`simp` fail on `𝟙` after adjunction-unit step → `erw [Functor.map_id, comp_id]` |
| SNAP-S1 ℕ-graded ∀L graded MODULE `M(X,L,F)=⊕Γ(F⊗L^{⊗m})` (capped STRETCH) | 036 · 5 (032→036, 3 real-attempt) | ~? | `SectionGradedRing.lean` | (A) `moduleTensorPowAdd_assoc` (load-bearing distinct-object hexagon `β_{L^i,F}`); (B) `moduleSectionAction_{mul_smul,one_smul}`; base `moduleTensorPowAdd_zero_left`; (C) `sectionGradedModule_gmodule` = the deliverable `DirectSum.Gmodule` ∀L,F — all axiom-clean, file SORRY-FREE | keep `tensorPowAdd`/`moduleTensorPowAdd` `.hom` OPAQUE ⇒ NO comp-instance diamond ⇒ plain `rw`, NO generic-`M` `_core` (cheaper than B6/comm); (A) needs TWO `whisker_exchange` interchanges (`monoidal`≠interchange); unit friction `unitModule X`≠`𝟙_` → state over `𝟙_`+defeq-transport; `(1:sectionDeg L 0)` spelled (bare `GOne.one`=whnf bomb) | canonical-first β-split DEAD; `tensorBraiding_naturality_{left,right}` were dead code (deleted); prep/dispatch-bug iters 032/033 cost 2 iters (scaffold keyword must sit on the filename line) |

## Routes

**GR-quot route (closable cone DONE).** Glue `SheafOfModules` over `Scheme.GlueData` → effective-descent
iso `isIso_glueRestrictionHom` (DONE keystone) → Nitsure §5 inverse `grPointOfRankQuotient` (DONE) →
`represents` (DONE, goal seed) → `tautologicalQuotient_epi` (DONE, last GR sorry). The closable GR cone is
0-sorry. Faithful Lean image of Nitsure §5 cell-gluing + `GL_d` cocycle; inverse/representability is
Archon-original (Nitsure leaves it as §5 exercise). Tracked-debt `representable` (weak skeleton) is OUT of
the closable cone (its `\lean{}` under-delivers the prose: omits smoothness/properness/Plücker).

**SNAP-S0 route (DONE axiom-clean).** Crux `IsIso(sheafification.map(η_P ▷ Q))`, associator,
`tensorPowAdd`, the entire B1–B7 assoc chain, and both ring layers are closed. RE-ANCHOR (decisive): the
section ring `⊕ₘΓ(L^{⊗m})` is the FREE TENSOR ALGEBRA on Γ(L) — `sectionsMul_mul_comm` is FALSE for
general `L` (triple-verified; counterexample `L=𝒪²`). Per Stacks §17.25 `Γ_*` is defined for INVERTIBLE
sheaves; commutativity holds iff `L` invertible (`β_{L,L}=𝟙`). So the general deliverable is a
NON-commutative `DirectSum.GSemiring` (`sectionGradedRing_gsemiring`, Stacks 01CV, ∀L); `GCommSemiring`
(`sectionGradedRing_gcommSemiring`) is the upgrade under a project-local `IsInvertible L`
(locally-free-rank-1, Stacks 01CR), gated on `β_{L,L}=𝟙` (Mathlib
`Module.Invertible.tensorProductComm_eq_refl`, basis-local descent) → brick 2 hexagon →
`tensorBraiding_symm` → brick 1′ (order-REVERSING recursion) → `tensorPowAdd_comm` → `sectionsMul_mul_comm`
→ `sectionGradedRing_gcommSemiring`. `Γ_*(X,L)` is a graded CommSemiring for invertible `L`;
`sectionsMul_mul_comm` is correctly `[IsInvertible L]`-gated.

**SNAP-S1 module sub-route (COMPLETE, capped stretch).** `M(X,L,F) = ⊕_{m≥0} Γ(X, F⊗L^{⊗m})` is a
graded `DirectSum.Gmodule` over `Γ_*(X,L)` for ANY `F` — the ℕ-graded ∀L analog of Stacks 01CV (literal
01CV is Z-graded over an INVERTIBLE `L` using `L^∨`; we built the n≥0 truncation, general `L`). Delivered
axiom-clean: (A) `moduleTensorPowAdd_assoc` (distinct-object braided hexagon `β_{L^i,F}`, no invertibility)
→ (B) `moduleSectionAction_{mul_smul,one_smul}` → base `moduleTensorPowAdd_zero_left` → (C)
`sectionGradedModule_gmodule`. Route detail + pitfalls in the `## Completed` row. Downstream nodes
`sectionGradedModule_fg` and `hilbertPoly_of_sectionModule` are NOT pursued in-leg — and are neither
project sorries (blueprint `\lean{}` pins only, no Lean decl) nor closable in this H⁰ leg: `_fg` is a
Serre-finiteness/cohomology node (its blueprint statement needs `X_s` proper, `L_s` ample, `F_s` coherent
and cites Hartshorne II.5), `hilbertPoly` is the Euler-characteristic extraction. Both belong to the
cohomology leg, filled at merge. **Shared with sibling — finished proofs mergeable as-is.**

**χ-blocked route — none here.** `quot_functor`/`hilbert_polynomial` need the χ
(Euler-characteristic) engine; this i=0 leg does not build it. They remain `sorry` and are
filled from the cohomology leg at merge.

## Open strategic questions

- **SNAP-S1 module (RESOLVED: DELIVERED, capped stretch closed).** Pursued as a capped stretch after the
  mandated goal landed; closed axiom-clean. Leg's closable scope is now fully delivered — finalize / await
  merge. Downstream `_fg`/`hilbertPoly` deliberately NOT pursued (Serre-finiteness/cohomology nodes, not
  closable in the H⁰ leg).
- **SNAP coordination with `FBC-B_SNAP-chain`.** Decide per-iteration whether to prove SNAP here
  or import the sibling's finished proofs (Lean names identical). See manifest `overlaps` and
  `.archon/USER_HINTS.md`.
- **χ encoding consistency.** The blueprint `def:hilbert_polynomial` ENCODING comment claims an
  H⁰ encoding that contradicts the χ Lean decl. The Lean source governs; flag for the parent to
  reconcile the comment, but do NOT change the Lean to H⁰ in this leg.
- **Goal-label boundary `thm:grassmannian_representable` vs `represents` (state crisply, do NOT bury).**
  The goal para names `thm:grassmannian_representable` (smooth-PROJECTIVE representability, `\uses`
  `relative_spec_*`). The leg delivers the substantive functor-representability heart as
  `thm:grassmannian_universal_property` = `Grassmannian.represents` (`RepresentableBy (scheme d r)`,
  sorry-free + axiom-clean) — a DIFFERENT blueprint label. The goal-named node's residue (smooth +
  projective geometric upgrade + its out-of-cone `relative_spec_*` dependency) is delivered only as a weak
  skeleton and is parent-owned. This is a legitimate scope boundary, not a gap: deliverable (1)'s
  functor-moduli content is closed; the smooth/projective upgrade is out-of-cone. Strengthen/split the
  `thm:grassmannian_representable` label at merge in the parent.

## Mathlib gaps & new material

- GR-quot: effective descent for `SheafOfModules` over `Scheme.GlueData` (project-built).
- SNAP-S0: H⁰ section graded ring `Γ_*(X,L)` (project-built, `TensorPower.Basic` idiom: free tensor
  algebra ⇒ general `GSemiring`, `GCommSemiring` under invertibility).
- SNAP-S0: `IsInvertible (L : X.Modules)` (locally-free-rank-1, Stacks 01CR) + `β_{L,L}=𝟙` for
  invertible `L` (`braiding_eq_id_of_invertible`, via `Module.Invertible.tensorProductComm_eq_refl`).
- SNAP-S1: ℕ-graded ∀L module `M(X,L,F)=⊕_{m≥0}Γ(F⊗L^{⊗m})` over `Γ_*(X,L)` (project-built; `DirectSum.Gmodule`
  via the new module hexagon `moduleTensorPowAdd_assoc` — distinct-object braiding, no invertibility).
- `Grassmannian` (rank-`d` locally-free quotients) + representability as `IsRepresentable`.
