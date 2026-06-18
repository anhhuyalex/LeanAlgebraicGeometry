# Strategy

## Goal

Build the **comparison-isomorphism substrate on line bundles** — the A.1.c.sub
work package carved from Christian Merten's Jacobian challenge
(`references/challenge.lean.ref`). Final deliverables = three seed nodes + their
108-node cone, with zero inline `sorry` in each seed's cone and kernel-only axioms:

- `lem:pullback_tensor_iso_loctriv` — `Modules.pullbackTensorIsoOfLocallyTrivial`:
  loc-triv comparison iso `f^*(M⊗N) ≅ f^*M ⊗ f^*N` (D4′ chart-chase over the D3′ substrate).
- `lem:dual_isLocallyTrivial` — `Modules.dual_isLocallyTrivial`: dual of a
  loc-triv module is loc-triv (DUAL route).
- `thm:rel_pic_addcommgroup_via_tensorobj` — `PicSharp.addCommGroup_via_tensorObj`:
  assembles these into the `AddCommGroup` on the relative Picard sheaf `Pic♯_{C/k}`.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|-------------------|-------|
| D4′ seed-1 `pullbackTensorIsoOfLocallyTrivial` (`TensorObjSubstrate.lean`) | **ACTIVE** | ~1–2 | ~30–60 | K1 presheaf-δ iso (in-proof) | Chart-chase closed; sole residual = brick K1 (`pullbackTensorMap` iso for open immersion, arbitrary M,N). Route in `### D4′` below. Risk: mate calculus; partial committable. |
| Terminal `exists_tensorObj_inverse` close (architectural) | NEXT | ~2–3 | ~30–80 | `homOfLocalCompat` (A-bridge) | The project's SOLE bare `sorry`. Import-cycle-gated in `TensorObjSubstrate.lean` (needs `dual_isLocallyTrivial` from DualInverse, which imports TOS). RESOLUTION: refactor-MOVE the decl to a file downstream of DualInverse (only consumer is RelPicFunctor `neg`/`neg_add_cancel` → repoint its import), then close the gluing proof (bridges C+B done, A = SheafOfModules morphism descent). Standing directive lists this as one of the six required closures. |
| Consumer seed-3 (`RelPicFunctor.lean`) | BLOCKED | ~1–2 | ~30–80 | — | `addCommGroup_via_tensorObj`; gated on seed-1 (map_add ← comparison iso) + `exists_tensorObj_inverse` (group inverse). |
| Coverage + file-split cleanup | DEFERRED | ~1–2 | ~0 (tex/private) | — | bulk ~99 `lean_aux` isolated nodes + `TensorObjSubstrate.lean` (>3600 LOC) split; defer until active seed-1 lane lands. |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|-------|----------------------|-----|-------|-------------|---------------------|----------|
| DUAL dual-inverse | 015 · ~6 | ~250 | `DualInverse/SliceTransport.lean`, `DualInverse.lean` | `sliceDualTransport` (+`Inv`) sorry-free; seed `dual_isLocallyTrivial` delivered | leg-B `inv ε` rotated morphism-level (`IsIso.inv_comp_eq`), never pointwise (whnf timeout); `appIso_inv/hom_naturality_apply` ring-level pastes; `set_option maxHeartbeats 1600000` for inline 6-field `≃ₗ` | pointwise `inv ε` heartbeat-bombs; `rw [ModuleCat.restrictScalars.map_apply]` no-match — use defeq `erw [hφ]`; import-race green→red when sibling lane edits the shared dep (isolate via HEAD worktree) |
| D3′ base-change substrate (`pullbackTensorMap_restrict`) | 019 · ~9 (005–019) | ~600 | `TensorObjSubstrate.lean` | full base-change cone sorry-free, axiom-clean; substrate for seed-1 | generic single-`[Category C]` lemmas applied by `exact` cross the `SheafOfModules`↔`Scheme.Modules` defeq-but-not-syntactic instance wall (`comp_cancel_mid` family); `conjugateEquiv_comp` for Sq1 cocycle at NatTrans level; **unit-naturality factor-out** collapses the Sq4 leaf to a sheaf-level cocycle | `rw/erw [Category.assoc]` whnf-bombs on the carrier; top-level extraction of monoidal-carried content fails (`MonoidalCategoryStruct` not synthesizable) — keep IN-PROOF; metavar `reassoc_of% δ_natural` whnf-times-out → concrete fully-applied `have` |

## Routes

The relative Picard substrate needs two isomorphisms on locally trivial line
bundles. Completed routes (D3′ base-change substrate, DUAL dual-inverse) are recorded in
`## Completed`; the live routes are below.

### D4′ — seed-1 `pullbackTensorIsoOfLocallyTrivial` (the comparison ISO) — ACTIVE
The chart-chase is assembled and sorry-free: promote δ_sheaf=`pullbackTensorMap` to an iso via
`isIso_of_isIso_restrict` over `{f⁻¹Uᵢ}`; on each chart the two `pullbackTensorMap_restrict`
(base-change) splits of `j' ; f = g ; j` isolate the comparison, closed by the trivial-base case K2
(`pullbackTensorMap_natural` + `pullbackTensorMap_unit_isIso`). Isolating the restriction factor from
the four-fold base-change composite needs the FLANKING open-immersion comparisons `δ^{j'}, δ^{j}`
invertible — the sole residual brick **K1** (`lem:pullback_tensor_map_isiso_open_immersion`):
`pullbackTensorMap` iso for an OPEN immersion, arbitrary M,N. Route for K1: the functor-level
`Functor.Monoidal.transport` is blocked by the non-synthesizable monoidal-carrier (see Pitfalls).
Instead enter via `isIso_pullbackTensorMap_of_isIso_sheafifyDelta`, reduce to the presheaf
`IsIso (δ (pullback φ'))`, and close it IN-PROOF mirroring the CLOSED `tensorObj_restrict_iso` (H1 =
`pushforward β ≅ pullback φ'` via `leftAdjointUniq`; H2 = `restrictScalarsMonoidalOfBijective`) plus the
adjunction-mate compatibility `Adjunction.IsMonoidal` (its `leftAdjoint_μ` field expresses the right
adjoint's `μ` through the left adjoint's oplax `δ`). Reference: Stacks `lemma-tensor-product-pullback`.
The OnProduct-specialisation `pullback_tensorObj_iso` (`lem:pullback_compatible_with_tensorobj`) lands
downstream once seed-1 closes.

### Terminal `exists_tensorObj_inverse` — architectural close — NEXT
The project's last bare `sorry` and one of the six standing-directive closures. It needs
`dual_isLocallyTrivial` (C-bridge, DONE in DualInverse.lean) but DualInverse imports
TensorObjSubstrate, so the decl cannot close where it sits. PLAN: dispatch the `refactor` subagent
to MOVE `exists_tensorObj_inverse` (not protected) to a file downstream of DualInverse (a new
`TensorObjInverse.lean`, or into DualInverse), and repoint `RelPicFunctor.lean` — verified the SOLE
code consumer (`neg`/`neg_add_cancel`, lines 357–447) — to import that file (chain stays acyclic:
RelPicFunctor → {new file} → DualInverse → SliceTransport → TensorObjSubstrate). Then a prover closes
the gluing proof: bridges B (`isIso_of_isIso_restrict`, done) + C (`dual_isLocallyTrivial`, done) +
A (`homOfLocalCompat`, SheafOfModules morphism descent gluing the local `(L⊗dual L)|_{Uᵢ}≅𝒪_{Uᵢ}`).
Decomposition in `informal/exists_tensorObj_inverse.md` + `analogies/ts226descent.md`. Do this AFTER
seed-1 lands to keep the warm file stable (both touch TensorObjSubstrate.lean).

### Consumer seed-3 `PicSharp.addCommGroup_via_tensorObj` (`RelPicFunctor.lean`) — BLOCKED
Builds the group on loc-triv iso-classes: `map_add` ← seed-1 comparison iso; `map_zero` ←
`pullbackUnitIso`; inverse ← `exists_tensorObj_inverse`. Carrier = `IsLocallyTrivial`; `map_add`
consumes the comparison ISO (not just additivity-of-pullback). Gated on seed-1 + the terminal close.

## Open strategic questions

- Completeness vs AJC parent: RESOLVED — the 3-seed cone is complete
  (108/108 nodes, cone sizes 52/36/32 match exactly, `DualInverse` decls complete). Only diffs
  are AJC dead code (Lan block) + out-of-scope Route-A. Nothing required is missing; the open
  `sorry`s are frontier math AJC itself has not closed.
- Coverage debt: ~97 Lean decls (prover-created helpers) have no blueprint entry
  (`leandag unmatched`); dispositioned non-blocking. Scheduled as
  the `Coverage + file-split cleanup` phase: author blueprint blocks for load-bearing helpers, mark
  genuine internals `private`. User policy: no isolated/∞ blueprint nodes; split `.lean` files >1000/1500 LOC —
  `DualInverse.lean` split done; `TensorObjSubstrate.lean` (3152 LOC) split is the next refactor.
- Sq1 cocycle: now framed at the NatTrans level via `conjugateEquiv_comp` (Mates.lean) with the
  working template `pullbackObjUnitToUnit_comp` (`analogies/d3cocycle006.md`); the older
  whiskerLeft/`d3-mate271.md` component approach is superseded (it kept hitting the dependent δ-splice).
- Consumer (when unblocked): blueprint should make explicit which group axioms ride
  the monoidal associator vs. the comparison iso, so the consumer doesn't assume the
  iso discharges more than additivity-of-pullback.
- **Out of scope** (sibling extracts): A.2.c representability + Quot/Cartier engine →
  Quot-Foundations; Čech higher direct image → Cech-Cohomology; A.3 tangent/Pic⁰-AV,
  A.4 Albanese UP, Route-C Riemann–Roch, genus-0 arm → parent-scope. Cones disjoint
  (0 overlap with both siblings).

## Mathlib gaps & new material

Gaps to fill:
- DUAL route-2 `sliceDualTransport` — built by hand (leg-A slice-Hom base-change ∘
  leg-B unit ε-iso); ε-naturality via morphism-level `IsIso.inv_comp_eq` rotation (`analogies/dualnat006.md`).
- A-bridge `homOfLocalCompat` — glues compatible local `𝒪_X`-module morphisms to a
  global morphism via `homLocalSection`, `topSectionToHom`, and `homMk`.
- D3′ — upgrade δ (`pullbackTensorMap`) to iso via `isIso_of_isIso_restrict`.
- K1 (seed-1 residual) — presheaf-level `IsIso (δ (pullback φ'))` for an open immersion: build in-proof from
  the closed `tensorObj_restrict_iso` H1∘H2 model + the leftAdjointUniq monoidal-mate compatibility
  (`Adjunction.IsMonoidal`). NOT the functor-level `Functor.Monoidal.transport` (carrier diamond).

New project material:
- By-hand `AddCommGroup` on loc-triv iso-classes (Mathlib `Sheaf.monoidalCategory`
  needs a FIXED `MonoidalCategory A`; varying-ring tensor on `X.Modules` has none).
  Modeled on Mathlib `CommRing.Pic.mapAlgebra`.
- `IsInvertible M := ∃N, M⊗N≅𝒪` carrier for `Pic X` (Stacks 0B8K/01CX);
  `picCommGroup` axiom-clean.
