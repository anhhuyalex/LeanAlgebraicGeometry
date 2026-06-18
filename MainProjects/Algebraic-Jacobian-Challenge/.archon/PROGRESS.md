# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

**Zero inline `sorry` in the dependency cone of each protected declaration
+ kernel-only axioms** for Christian Merten's Jacobian challenge. Spine =
**pointed vs. unpointed**. 0 project axioms. Operative posture: option (c)
under the USER ROUTE C PAUSE. Full framing in STRATEGY.md.

## Merge note — 2026-06-18 (Cech-Cohomology enrich merge)

The **A.2.c-engine `Rⁱf_*` Čech lane** (previously the dominant open pole; the
target's `Cohomology/CechHigherDirectImage.lean` was an *orphaned*, un-imported
roadmap file with a `sorry` `CechNerve`) now carries the **Čech-cohomology
development imported from the `Cech-Cohomology` subproject** (21 Lean files,
~600 declarations, wired into the aggregator). `CechNerve` is genuinely closed
(via `pushPullFunctor` + `pushPullMap_comp`), and the bulk of the development —
including all of `CechSectionIdentification`, `CechAugmentedResolution`, and the
relative Čech complex machinery — is now **kernel-verified by `lake build`**.

**Honest build state (2026-06-18): `lake build` is green, with 8 documented
`sorry`s.** Crucially, the source `Cech-Cohomology` project's *own* `lake build`
never produced oleans for the `CechSectionIdentificationLeg → … →
CechToHigherDirectImage` chain — its `\leanok` marks came from Archon's LSP check,
which is weaker than the kernel. The merge surfaced this: the headline
`cech_computes_higherDirectImage` is **not** kernel-verified end-to-end. The
unverifiable proofs are `sorry`-ed (full proofs preserved in `MERGE-STUB-PROOF` /
`MERGE NOTE` comments), namely:
- `pushPull_interLegHom_sections` — kernel deterministic timeout (tested to 64M heartbeats).
- `coreIso_comm_leg/coface/sum/comm` — stubbed as a group (≥1 is a blow-up; not individually isolated).
- `isoOfComponents` naturality (CechToHigherDirectImage) — `rfl` genuinely fails (incomplete proof).
- `cechAugmented_to_acyclicResolutionInput` — whnf blow-up (tested to 1.6M heartbeats).
- `cech_flatBaseChange` — the target-local roadmap node reinstated in `CechHigherDirectImageUnconditional.lean`.

These are genuine defects inherited from the source, not merge artifacts. Fixing
them needs term-shrinking proof rewrites (e.g. replacing defeq/`rfl` on giant
`eqToHom` coherence terms with explicit rewrite lemmas), not more `maxHeartbeats`.
DAG: blueprint nodes 932→1235, proved 622→738, 0 broken `\uses`.

## Iter-303 — RESUME prover after the iter-272–302 DAG/blueprint pass · 4 lanes

**Context.** Iters 272–302 ran NO prover phase — they fleshed out and fully connected the
blueprint (iter-302: lean-aux 54→0, ∞-nodes 2→0, components 20→1, 932-node single cone;
blueprint-reviewer iter302 HARD GATE CLEARS, 0 must-fix). Last actual proving was iter-271.
Build is **green** (`lake build` exit 0 this phase). The two formerly-∞ nodes
(`sheafificationCompPullback_comp_tail`, `sliceDualTransportInv`) now carry **full, reviewer-certified
informal proofs** in the blueprint — they are honest finite roadmap nodes whose Lean `sorry` is this
lane's job.

**This iter executes the iter-271 correctives for the first time.** pc271 verdicts were DUAL=CHURNING,
D3′=STUCK; the iter-271 plan devised concrete correctives (the `sliceDualTransportInv` top-level
extraction; the analogist `conjugateEquiv_whiskerLeft` route for the D3′ tail) but the prover round that
would execute them never happened — the loop diverted to 31 DAG iters. So dispatching these lanes now is
**the first execution of those correctives**, not "another helper round on a churning lane." The
extraction is already in Lean (`DualInverse.lean:273`, typechecks per ts271); the recipe lives in
`analogies/d3-mate271.md`; both targets now have full blueprint proofs.

### Subagent summary (plan-phase)
| Subagent | Decision |
|---|---|
| blueprint-reviewer | SKIPPED — iter302 whole-blueprint review (this same calendar pass) HARD-GATE-CLEARS all 4 target chapters, 0 must-fix; no chapter edited since. |
| progress-critic | SKIPPED — prior 31 iters ran no prover phase ⇒ no new trajectory data (dispatcher skip condition). iter-271 CHURNING/STUCK addressed by first-time corrective execution + full blueprint proofs (rationale in sidecar). |
| strategy-critic | SKIPPED — STRATEGY.md SHA-unchanged since iter-272; prior verdict SOUND; sole caveat (Pic≅Cl theorem-level recheck) is a future-deferred A.4 note, not a live challenge. |

### USER standing directives (active — all honored)
1. **AUTONOMOUS (2026-05-31)**: all lane/skip decisions made by the loop; no user escalation.
2. **PARALLELISM (2026-05-31)**: 4 concurrent file lanes; engine lane import-independent of the Picard substrate.
3. **ROUTE C PAUSE (permanent)**: no RR/Genus0 lanes. `QuotScheme.smooth_proper_curve_projective` deliberately
   NOT dispatched — classically RR-dependent (high-degree-divisor embedding), would risk pulling paused RR.
4. **ROUTE A BOTTOM-UP**: lanes 1–2 = A.1.c.sub (deepest open sub-root); lane 3 = A.2.c-engine `Rⁱf_*`;
   lane 4 = A.2.c-engine generic flatness. No A.3+ dispatched.
5. **REFERENCE-DRIVEN**: each objective cites its blueprint label + reference anchor (Stacks/Mates.lean/Kleiman-Nitsure).
6. **PRIMARY GOAL (Pic_{C/k} representability, A.2.c)**: substrate (lanes 1–2) unblocks the RPF group inverse +
   comparison iso; engine lanes (3–4) advance the dominant A.2.c pole bottom-up.

## Current Objectives

1. **`Picard/TensorObjSubstrate/DualInverse.lean`** — **CRITICAL PATH (A.1.c.sub dual route-2). Close the
   `sliceDualTransport` ≃ₗ: finish `invFun` + `left_inv`/`right_inv`, attempt `naturality`.**
   **[prover-mode: fine-grained]** Blueprint: `chapters/Picard_TensorObjSubstrate.tex`
   (`lem:slice_dual_transport`, `lem:slice_dual_transport_inv` — the latter's full informal proof was
   reviewer-certified iter-302: component formula, additivity/linearity, and the naturality split
   (thin-poset base-uniqueness via `Subsingleton.elim` vs genuine module-map naturality via
   `PresheafOfModules.restrictScalarsLaxε`)). ~11 real sorries in the dual cluster.
   - **Done already (ts271):** `sliceDualTransportInv` extracted top-level (`DualInverse.lean:273`,
     typechecks; binder-metavar gone), `invFun` wired (holes 4→3). Leg-B `.hom`-direction infra
     (`dualUnitRingSwapHom`/`dualUnitRingSwapInv` + cancellation pair, `isIso_ε_restrictScalars_appIso_hom`)
     all axiom-clean iter-265.
   - **`invFun` finish:** component over `Over fV`, `W'' ≤ fV`, `P := f⁻¹ᵁ W''.left`; X-slice mirror of `toFun`
     with the `eqToHom` conjugation (à la `homLocalSection`, since `f.opensFunctor.obj P = W''.left` only
     propositionally via `image_preimage_of_le`). Codomain swap is `dualUnitRingSwapHom` (the `.hom`-dir
     `inv ε`), per the corrected blueprint. `map_add'`/`map_smul'` mirror the closed forward proofs.
   - **`left_inv`/`right_inv`:** `Iso.inv_hom_id`/`hom_inv_id` of `f.appIso` + the down-set bijection
     cancellation (`image_preimage_of_le`), consuming the iter-265 `@[simp]` cancellation lemmas.
   - **`naturality` (attempt, do not gate on it):** ε-naturality square via
     `PresheafOfModules.restrictScalarsLaxε` [verified, `Picard/TensorObjSubstrate/PresheafInternalHom.lean:290`],
     `NatTrans.naturality` field. Get an early read; if it stalls, commit `invFun`+round-trips first.
   - **RACE MITIGATION (MANDATORY):** this file imports `TensorObjSubstrate.lean` (lane 2). Keep the file
     compilable; commit only compiling states; retain typed sorries for fields that don't close.
   - **Bar:** close `invFun` + both round-trips axiom-clean (dual cluster holes ≤ 1, ideally close
     `lem:slice_dual_transport`). Partial real progress + precise blocker report beats a clean re-pin.

2. **`Picard/TensorObjSubstrate.lean`** — **CRITICAL PATH (A.1.c.sub, D3′) + ready tensor-iso cluster.**
   **[prover-mode: fine-grained]** Blueprint: `chapters/Picard_TensorObjSubstrate.tex`
   (`lem:sheafificationcomppullback_comp_tail` — full reviewer-certified informal proof iter-302; plus the
   frontier-ready nodes `lem:jw_ismonoidal`, `lem:pullback0_tensor_iso`, `lem:pullback_tensor_iso_loctriv`,
   `lem:pullback_compatible_with_tensorobj`, `lem:stalk_tensor_commutation_naturality_right`).
   ~14 real sorries. **Recipe: `analogies/d3-mate271.md` (READ FIRST).**
   - **Primary (deep): close `sheafificationCompPullback_comp_tail` (`TensorObjSubstrate.lean:2536`).** The
     5-step argument the blueprint certifies: strip identity wrapper → distribute `forget` → recover
     sub-comparison units → slide `pushforwardComp` by naturality → reassemble composite unit. The stuck
     factor `forget.map ((pullback h).map ((sheafCompPb f).hom.app P))` gets a transposable head via
     `CategoryTheory.Adjunction.conjugateEquiv_whiskerLeft` (`Mathlib/CategoryTheory/Adjunction/Mates.lean:525`),
     then `leftAdjointUniqUnitEta_app` (axiom-clean brick, in-file) recovers R1/R5 as `B_f.unit`/`B_h.unit`.
     The sheaf↔presheaf wrap is crossed by the landed `forget_map_pushforward_map` (iter-265). Assemble
     (a)–(e) per `analogies/d3-mate271.md` (use `erw`, not `rw` — `SheafOfModules` comps are defeq-not-syntactic).
   - **Also attempt the mechanical-ish ready nodes** in the same lane (`jw_ismonoidal`, `pullback0_tensor_iso`,
     `pullback_tensor_iso_loctriv`, `pullback_compatible_with_tensorobj`,
     `stalk_tensor_commutation_naturality_right`) — each has a blueprint block; close whichever land.
   - **Non-circular FALLBACK** (if the `conjugateEquiv_whiskerLeft` `have` is fiddly): re-prove
     `sheafificationCompPullback_comp` wholesale via `obtain ⟨τ,rfl⟩ := (conjugateEquiv …).surjective` +
     `apply (conjugateEquiv …).injective` + whisker/comp simp reduction of `leftAdjointCompNatTrans_assoc`
     (CompositionIso.lean:130–164) — the route Mathlib itself uses for `SheafOfModules.pullback_assoc`.
   - **Do NOT touch** `pullbackTensorMap_restrict` or `exists_tensorObj_inverse` (gated, D4′/downstream).
   - **RACE MITIGATION (MANDATORY):** lanes 1 and 4 import this file. Do NOT change any exported signature;
     close sorries only; commit only compiling states.
   - **Bar:** close `sheafificationCompPullback_comp_tail` axiom-clean + as many ready tensor-iso nodes as
     land. If the analogist route's `have` lands but assembly stalls, report which of (a)–(e) failed.

3. **`Cohomology/CechHigherDirectImage.lean`** — **A.2.c-ENGINE (DOMINANT POLE, de-coupled): build the
   generalized kernel-cheap `eqToHom`-transport cancellation lemma, then close `pushPullMap_comp`.**
   **[prover-mode: mathlib-build]** Blueprint: `chapters/Cohomology_CechHigherDirectImage.tex`
   (`lem:push_pull_functor`; complete+correct iter-302). Import-independent of the Picard lanes.
   `pushPullMap_id` + `pushPull_unit_mate` LANDED axiom-clean (iter-264/265); 4 sorries remain.
   - **The blocker (iter-265):** `pushPullMap_comp` is blocked NOT by the mate calculus
     (`pushPull_unit_mate` makes it a one-liner) but by a KERNEL whnf blow-up cancelling the
     `eqToHom (congrArg (fun q => (pushforward q).obj …) (Over.w g))` over-triangle transports baked into
     `pushPullMap`'s definition (`CechHigherDirectImage.lean:175–187`).
   - **Build (option b):** state a **generalized** cancellation lemma with the over-triangle equality as a
     **free hypothesis** `(h : g.left ≫ Y₁.hom = Y₂.hom)` (NOT the specific `Over.w` instance), proven by
     `subst h` (transports become `eqToHom rfl = 𝟙` and vanish — kernel-cheap), `@[simp]`/applied by `rw`.
     Abstracting the pushforward objects means `rw` does NOT force the kernel to whnf them (the failure mode
     of the iter-265 concrete `exact`). Then close `pushPullMap_comp` with it + `pushPull_unit_mate` +
     `pseudofunctor_associativity` + the `hpf`-style sectionwise pushforward-coercion collapse (mirrors
     `pushPullMap_id`).
   - **Reverse signal (option a escalation):** if the generalized lemma ALSO hits the kernel whnf wall (the
     blow-up survives `subst`), report precisely — next iter dispatches the refactor subagent to make
     `pushPullMap` transport-light.
   - **Do NOT attempt** the 3 infra-gated downstream sorries (`CechAcyclic.affine`,
     `cech_computes_higherDirectImage`, `cech_flatBaseChange`) or the `CechNerve` hole (gated on comp).
   - **Bar (mathlib-build):** land the generalized cancellation lemma axiom-clean (no sorry); if budget
     remains, close `pushPullMap_comp`. Precise kernel-wall report deciding option-b-vs-a is acceptable.

4. **`Picard/FlatteningStratification.lean`** — **A.2.c-ENGINE (generic flatness root, RR-free, now
   blueprinted + frontier-ready). Build `genericFlatness` first, then the flat-locus chain.**
   **[prover-mode: mathlib-build]** Blueprint: `chapters/Picard_FlatteningStratification.tex`
   (complete+correct iter-302; frontier nodes `thm:generic_flatness_algebraic`, `lem:flat_locus_open`,
   `lem:nonflat_locus_proper`, `lem:flat_locus_stratification_lean`, `lem:flat_locus_reduction_lean`).
   7 typed sorries (`genericFlatness` L208, `flatLocusStratification` L252, `flatLocusReduction` L280,
   `flatLocusAssembly` L310, `flatteningStratification` L358, `flatteningStratification_universal` L399,
   `flatteningStratification.ofCurve` L438).
   - **Reference anchor:** the scheme-level `AlgebraicGeometry.genericFlatness` (Lean decl, blueprint block
     L163) reduces to the **algebraic** generic-flatness lemma `thm:generic_flatness_algebraic` =
     **[Nitsure] §4 "Lemma on Generic Flatness"** (`A` noetherian domain, `B` finite-type `A`-algebra, `M`
     finite `B`-module ⇒ ∃ `f≠0` with `M_f` free over `A_f`) — its full induction proof (prime filtration +
     Noether normalisation) is transcribed in the blueprint from
     `references/nitsure-hilbert-quot-src/nitsure-hilbert-quot.tex` L1711–1772. Read that before building.
   - **Build bottom-up (mathlib-build, Mathlib-gradient):** the algebraic ingredient
     `thm:generic_flatness_algebraic` is pinned to a TODO Lean name (`…TODO.genericFlatnessAlgebraic`) — i.e.
     not yet formalized. Build it FIRST as a project-side axiom-clean lemma (Mathlib HAS module/algebra-level
     generic-flatness pieces — search `Module.Flat`, generic-flatness / Noether-normalisation lemmas), then
     reduce the scheme-level `genericFlatness` (L208) to it. Stop when genuinely blocked and hand off a
     precise decomposition.
   - **Do NOT** weaken any signature or introduce an axiom; mathlib-build's no-sorry invariant holds (each
     step fully proved or absent).
   - **Bar (mathlib-build):** real axiom-clean progress on `genericFlatness` (one or more sub-lemmas landed)
     + a precise decomposition of the remainder. If Mathlib genuinely lacks the module-level core, name it
     exactly (the Mathlib-gradient next target) — do not leave a bare "waiting for Mathlib" sorry.

**Gate judgment:** all 4 chapters HARD-GATE-CLEARED by the iter-302 whole-blueprint review (`correct: true`,
0 must-fix; `complete: partial` on the substrate chapters reflects exactly the open sorry bodies these lanes
fill). 4 files within the 10 cap. Build green this phase, so the blocked-deps filter exempts the
substrate-importing lanes (1, 4) co-assigned with their upstream (2).

## Held lanes (explicit rationale)

- **`Picard/QuotScheme.lean`** — `quot_reduction_to_pi_star_W` is frontier-ready but
  `smooth_proper_curve_projective` is classically RR-dependent (high-degree-divisor embedding) ⇒ deferred to
  avoid pulling the paused Route C; re-open after a theorem-level RR-disjointness check at A.2.c entry.
- **`Picard/RelPicFunctor.lean`** — `rel_pic_etale_sheaf_unit_canonical` frontier-ready, but the functor's
  `addCommGroup`/`functorial` bodies are gated cross-file on D4′ + the dual chain (lanes 1–2). Re-opens once
  the substrate closes.
- **`Picard/LineBundleCoherence.lean` + `Picard/SheafOverEquivalence.lean` — DONE** (locally sorry-free; the
  engine coherence shared root `chartOverIso` closed iter-258/259). No lane needed.
- **A.2.c engine `Cohomology/FlatBaseChange.lean`** (HELD, defeq wall: `base_change_map_affine_local` +
  `pushforward_base_change_mate_cancelBaseChange`, Mathlib-scale per iter-243) + `HigherDirectImage.lean` DEFERRED.
- **Route-1 Albanese cone** (`Albanese/*`, `AbelianVarietyRigidity.lean`) — A.4 RR-free PRIMARY; gated A.2.c.
- **Route 2 Albanese (`Albanese/AlbaneseUP.lean`)** — gated A.2.c; CONTINGENT (Milne §III.6 check at A.2.c entry).
- **Lane WD / Lane RCI (`RiemannRoch/*`)** — HELD; Route C PAUSED (USER).
- **A.3.* lanes** — NOT dispatched (USER directive #6).

## Standing deferrals (unchanged unless noted)

- **Import architecture:** `LineBundlePullback → TensorObjSubstrate → {DualInverse, RelPicFunctor, FlatteningStratification?}`
  (cycle broken iter-247). `CechHigherDirectImage → HigherDirectImage → Mathlib` (acyclic, Picard-independent).
- **Dual bridge directions:** FORWARD `IsInvertible⟹IsLocallyTrivial` (`lem:isinvertible_implies_locallytrivial`)
  is Mathlib-scale + off-path — do NOT build (frontier lists it but it is the avoided direction). REVERSE
  `IsLocallyTrivial⟹IsInvertible` (`exists_tensorObj_inverse`) closes via the dual chain (DualInverse.lean).
- **Blueprint:** DECLARED COMPLETE + FULLY CONNECTED iter-302 (932-node single cone, 0 isolated, 0 ∞-nodes,
  0 broken `\uses`). 44 unmatched `\lean{}` hints are expected forward references to not-yet-formalized targets.
- **`set_option backward.isDefEq.respectTransparency false`** + **`Sheaf.val → ObjectProperty.obj` deprecation**
  — deferred polish pass (non-blocking).

**USER FYI (loop proceeds autonomously per the 2026-05-31 directive; override via USER_HINTS.md):**
- **Prover work resumes at iter-303 after 31 DAG/blueprint iters (272–302).** The blueprint is now complete
  and fully connected; the two formerly-∞ substrate nodes have full informal proofs. The 4 lanes execute the
  iter-271 correctives (devised but never run) for the first time, now backed by certified blueprint proofs.
- **The A.2.c-engine `Rⁱf_*` lane (CechHigherDirectImage) + generic flatness (FlatteningStratification)** are
  the dominant rate-limiter, DE-COUPLED from the Picard substrate, running concurrently. `pushPullMap_comp`'s
  blocker is DEFINITIONAL (kernel whnf on `eqToHom`), with a clear option-b→option-a escalation ladder.
