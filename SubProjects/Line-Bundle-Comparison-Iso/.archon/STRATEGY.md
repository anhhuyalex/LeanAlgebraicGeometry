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
| D4′ seed-1 `pullbackTensorIsoOfLocallyTrivial` (`TensorObjSubstrate.lean`) | ACTIVE | ~2 (over budget: 7 elapsed) | ~150–300 | direct sectionwise tensorator comparison; reuse D3′ `pushforwardComp_lax_μ` machinery | Carrier diamond RESOLVED (023). `hmon` DECOMPOSED (025) into `pushforward_{eta,mu}_appIso_collapse`. η nearly closed (1 ring identity, iter-027 lane). μ-collapse RE-DECOMPOSED iter-027: mate route is CIRCULAR (consumes `hmon`); genuine residual extracted as `pushforward_lax_mu_comparison` (bare 2-lax-structure comparison, direct, NO `IsMonoidal`), mirror of proved `pushforwardComp_lax_μ`. Route in `### D4′`. |
| Terminal `exists_tensorObj_inverse` close (`TensorObjInverse.lean`) | ACTIVE (STUCK — effort-break) | ~3–4 | ~150–350 | 5 per-constituent restriction-naturality squares (composite pullback+sheafification isos) | Sole residual = `trivialisation_restrict_compat`: STUCK 3 iters (1st green window iter-032 closed only S1=chart morphism+reindex). pc032 reversal LIVE → blueprint effort-break iter-033 (split into 5 squares incl. blueprint-OMITTED `uι` + telescope). Then prove S2 `tensorObj_restrict_iso` square first as template. `tensorObj_unit_self_duality_collapse` CLOSED (029); cocycle hedge gated. Real formalization sub-project, not a one-tactic gap. |
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
`pullbackTensorMap` iso for an OPEN immersion, arbitrary M,N. The carrier diamond that stalled K1 for
iters 018–022 is RESOLVED (iter-023): the bad `MonoidalCategory` carrier is normalized away via the
defeq composite `Gβ := pushforward₀OfCommRingCat … ⋙ restrictScalars β'` (`δ Gβ = μIsoβ.inv` by `rfl`)
plus `hadj'`/`H1'` re-ascriptions onto the good `presheaf ⋙ forget₂` carrier, closing the full mate
calculus (`hd`/`hU`/`hUinv`/`hstar`/`he` + `simp(zeta:=false)`/`erw` assembly). Recipe in
`analogies/recon023.md`.

**K1 residual `hmon : hadj'.IsMonoidal` — DECOMPOSED (iter-025), μ-side RE-DECOMPOSED (iter-027).** The
`IsMonoidal` instance itself stays IN-PROOF (built on the re-ascribed `Gβ` carrier; not synthesizable
top-level — Completed/Pitfalls). Its two pure-tensor-collapse obligations are named TOP-LEVEL lemmas:
`lem:pushforward_eta_appiso_collapse` (η, thin twin of proved `presheafUnit_comp_map_eta` D2′; iter-027
nearly closed — one sectionwise ring identity left, needs a presheaf-level `pushforwardPushforwardAdj.unit`
value lemma) and `lem:pushforward_mu_appiso_collapse` (δ/μ-side).
- **μ-side mate route is CIRCULAR (empirically confirmed iter-026):** reducing it via
  `unit_app_tensor_comp_map_δ hadj'` needs `hadj'.IsMonoidal` = `hmon`, which CONSUMES this lemma. So the
  μ-collapse is NOT closed through the adjunction's monoidal-mate machinery.
- **iter-027 fix:** effort-break extracted the genuine non-circular residual as a standalone key lemma
  `lem:pushforward_lax_mu_comparison` — the bare comparison of the two lax tensorators on `pushforward φ'`
  (`μ(rightAdjointLaxMonoidal hadj') = μ(presheafPushforwardLaxMonoidal)` on `Gβ A, Gβ B`), with NO
  `IsMonoidal` dependency. The collapse lemma's proof is now a 4-step mate reduction onto it. The comparison
  is the open-immersion analogue of the PROVED in-project `pushforwardComp_lax_μ` (L2197) — prove by
  mirroring it one-to-one (sectionwise pure tensors through `pushforward₀OfCommRingCat`, D3′ μ-helper
  family, `erw` no-whnf; `Gβ.obj(A⊗B)` is a pushforward of a tensor so `tensor_ext` does not fire).
Blueprint chain in chapter §"K1 monoidal-mate bridge". The OnProduct-specialisation `pullback_tensorObj_iso`
(`lem:pullback_compatible_with_tensorobj`) lands downstream once seed-1 closes.

### Terminal `exists_tensorObj_inverse` — decoupled parallel lane (`TensorObjInverse.lean`) — ACTIVE
One of the six standing-directive closures. It needs `dual_isLocallyTrivial` (C) + `homOfLocalCompat`
(A) — both BUILT in DualInverse.lean — but DualInverse imports TensorObjSubstrate, so the decl cannot
close where it sits (import-cycle). RESOLUTION: the unprotected decl lives in a new `TensorObjInverse.lean`
downstream of DualInverse; `RelPicFunctor.lean` (SOLE code consumer — `neg`/`neg_add_cancel`, L357–447;
all other refs are docstrings) imports it. Chain stays acyclic: RelPicFunctor → TensorObjInverse →
DualInverse → SliceTransport → TensorObjSubstrate. This decouples the terminal from the K1 brick — a
prover lane on a DIFFERENT file, runnable in parallel with K1 (it does NOT unblock K1: this is a
non-critical branch, seed-3's `map_add` still rides seed-1→K1). Gluing recipe (`rem:dual_discharges_inverse`):
`L⁻¹ := dual L` (line bundle by C); glue the local left-unitor contractions `(L⊗dual L)|_U ≅ 𝒪_U` via
A (`homOfLocalCompat`) + `tensorObj_restrict_iso`; upgrade to a global iso via B (`isIso_of_isIso_restrict`).
iter-023 built the full descent skeleton (object + C closed; cover/`eM`/`eN`/local contraction/glued ε
all compile). **Residual B CLOSED (iter-026):** the connector `homOfLocalCompat_restrictFunctor_map`
(`lem:hom_of_local_compat_restrict`) landed in DualInverse.lean (now sorry-free), closing
`IsIso ((restrictFunctor (U x).ι).map ε)` one-line. **Residual A (open):** the overlap cocycle `hf`
(canonical-evaluation transition-unit cancellation — section maps are real ab-group homs, `subsingleton`
WRONG). iter-027 pinned + analogist-specified its two closing helpers: (A) `trivialisation_restrict_compat`
— restriction-functor naturality of the trivialisation iso-chain (idiom = `restrictFunctorComp`/
`restrictFunctorCongr` NatIsos, already used in `restrictIsoUnitOfLE`); (B) `tensorObj_unit_self_duality_collapse`
— eval-at-1 cancellation, orientation `(dualIsoOfIso t)⁻¹` on the N-leg with explicit `dual_unit_iso`
conjugation (split B1/B2). Precise signatures in `analogies/cocycle-a.md`; scaffold+prove iter-028. Rigid
`ExactPairing` idiom is off-path (needs `MonoidalCategory (X.Modules)`, absent) — bespoke is correct.

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
  global morphism via `homLocalSection`, `topSectionToHom`, and `homMk`. Companion gluing-value
  connector `homOfLocalCompat_restrictFunctor_map` (restriction recovers the local datum) — built
  project-side from the internal `IsGluing` spec; unblocks terminal residual B.
- D3′ — upgrade δ (`pullbackTensorMap`) to iso via `isIso_of_isIso_restrict`.
- K1 residual `hmon : hadj'.IsMonoidal` — NOT a Mathlib gap; genuine sectionwise monoidal-mate
  compatibility (δ/μ twin of `presheafUnit_comp_map_eta`). Carrier diamond RESOLVED (iter-023, `Gβ`
  composite re-ascription). Prove in-proof via D3′ `pushforwardComp_lax_μ` machinery.

New project material:
- By-hand `AddCommGroup` on loc-triv iso-classes (Mathlib `Sheaf.monoidalCategory`
  needs a FIXED `MonoidalCategory A`; varying-ring tensor on `X.Modules` has none).
  Modeled on Mathlib `CommRing.Pic.mapAlgebra`.
- `IsInvertible M := ∃N, M⊗N≅𝒪` carrier for `Pic X` (Stacks 0B8K/01CX);
  `picCommGroup` axiom-clean.
