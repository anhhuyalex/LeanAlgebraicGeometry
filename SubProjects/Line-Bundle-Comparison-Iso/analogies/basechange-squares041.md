# Analogy: can S2–S4c be derived from the project's own base-change composition substrate?

## Mode
api-alignment

## Slug
basechange041

## Iteration
041

## Question
Can the 5 restriction-naturality squares S2–S4c (residual of `trivialisation_restrict_compat`,
`TensorObjInverse.lean` L191–282) be DERIVED from the project's OWN existing base-change composition
substrate, rather than from new per-leg immersion-naturality lemmas? iter-040 prover concluded the
squares are "not free" / "genuinely deep per-leg immersion-naturality". Is that correct?

## Headline finding (corrects iter-040)
**iter-040's "genuinely deep per-leg immersion-naturality, not free" is WRONG for S2 and S4c.**
The deep per-leg immersion-naturality content the prover feared IS exactly the project's already-proven
composition laws:
- `pullbackTensorMap_restrict` (D3′, `TensorObjSubstrate.lean` L3451) — **axiom-clean** (verified:
  `propext/Classical.choice/Quot.sound` only). The L3480/L3541 "typed sorry retained" comments are
  **STALE**; the proof closes via `pullbackValIso_comp_leg` (L3984/85). Header doc L60 confirms "FULLY
  CLOSED (iter-019+)".
- `pullbackObjUnitToUnit_comp` (unit composition law, L884) — **axiom-clean** (verified).
- `dual_restrict_iso` (`DualInverse.lean` L166) — **axiom-clean** (verified; Step-4 closes by
  `subsingleton`/thin-poset, the L364/366 "PARTIAL Step-4 sorry" comment is STALE).
- `pullbackTensorMap_isIso_of_isOpenImmersion` (L4751) — **axiom-clean** (verified). Its internal
  `hcompat` (L4812) IS bridge B1's deep content (see below).

The squares therefore do NOT need new deep math; they need cheap *bridges* between two views of the
same comparison (`tensorObj_restrict_iso` the iso vs `pullbackTensorMap` the map) and a reindex
coherence. One genuine residual remains: the **dual side has no composition law** (S3/S4a).

## Architecture (verified from defs)
`tensorObj_restrict_iso f M N` (L477): `(M⊗N).restrict f ≅ (M.restrict f)⊗(N.restrict f)`, built as
  `(restrictFunctorIsoPullback f).app(M⊗N) ≪≫ sheafCompPb ≪≫ a.mapIso(H1.symm ≪≫ H2.symm)`
  where `H1 = hadj.leftAdjointUniq(pullbackPushforwardAdj)`, `H2 = μIsoβ` (strong-monoidal tensorator
  of `pushforward β`, β = open-immersion structure ring iso). Call the tail (everything after
  `restrictFunctorIsoPullback`) `T_f : (pullback f).obj(M⊗N) ≅ (M.restrict f)⊗(N.restrict f)`.

`pullbackTensorMap f M N` (L1182): `(pullback f).obj(M⊗N) ⟶ (pullback f).obj M ⊗ (pullback f).obj N`,
  `sheafCompPb.hom ≫ a.map δ ≫ sheafifyTensorUnitIso.hom ≫ a.map(forget(pullbackValIso M)⊗forget(pullbackValIso N))`.
  Iso for open immersions (`pullbackTensorMap_isIso_of_isOpenImmersion`).

The two have **different codomains** (`restrict` factors vs `pullback` factors), differing by
`restrictFunctorIsoPullback` on each tensor leg.

The proven composition law has **exactly S2's RHS shape** (h=j, f=U.ι):
`pullbackTensorMap (h≫f) = (pullbackComp h f).inv.app ≫ (pullback h).map(pullbackTensorMap f)
   ≫ pullbackTensorMap h ≫ (tensorObjIsoOfIso (pullbackComp h f)).hom`
— but in the `pullback` world with `pullbackComp` reindex, not the `restrict` world with
`restrictCompReindex` (= `restrictFunctorComp`).

## The two bridges S2 needs

### Bridge B1 — iso↔map promotion (the DEEP part is ALREADY PROVEN)
Target: for open immersion f,
`tensorObj_restrict_iso f M N
   = (restrictFunctorIsoPullback f).app(M⊗N) ≪≫ asIso(pullbackTensorMap f M N)
       ≪≫ tensorObjIsoOfIso ((restrictFunctorIsoPullback f).app M).symm ((…).app N).symm`.

Why it nearly falls out: `hcompat` (inside `pullbackTensorMap_isIso_of_isOpenImmersion`, L4812) proves
`δ (pullback φ') M.val N.val = e.hom` with `e = (H1.app(M⊗N)).symm ≪≫ μIsoβ.symm ≪≫ tensorIso (H1 M)(H1 N)`.
Note H1, μIsoβ(=H2) are the **same** isos that build `tensorObj_restrict_iso`'s tail `T_f`. Hence
`a.map δ = a.map(H1.symm ≫ H2.symm) ≫ a.map(H1⊗H1) = (a.mapIso(H1.symm≪≫H2.symm)).hom ≫ a.map(H1⊗H1)`,
so `pullbackTensorMap f = T_f.hom ≫ [a.map(H1⊗H1) ≫ sheafifyTensorUnitIso ≫ a.map(pullbackValIso⊗)]`.
The bracket is exactly the per-leg `restrictFunctorIsoPullback` reindex. ⇒ B1.

Cost: the **deep mate-calculus is done** (hcompat, axiom-clean). Work = (i) expose `hcompat`/`δ=e.hom`
as a standalone lemma (currently locked in a private proof), (ii) assemble the
sheafification/sheafifyTensorUnitIso/pullbackValIso bookkeeping. **SMALL–MEDIUM.**

### Bridge B2 — reindex coherence (shared by ALL squares)
`restrictFunctorIsoPullback` is a Mathlib NatIso `restrictFunctor f ≅ pullback f`. Need its
pseudonaturality across the composite `j ≫ U.ι`: that `restrictCompReindex j hjι` (=
`restrictFunctorComp j U.ι` + `restrictFunctorCongr hjι`) matches `pullbackComp j U.ι` conjugated by
`restrictFunctorIsoPullback`. Plus the `hjι : j≫U.ι = V.ι` eqToHom threading (restrict side already in
`restrictCompReindex`; pullback side needs a `pullbackCongr`/eqToHom). **Does NOT exist** (grep: only
comment mentions). General category coherence, ~40–80 LOC, **MEDIUM**, reusable across S2–S4c.

Then S2 = `pullbackTensorMap_restrict j U.ι` (PROVEN) re-wrapped by B1 (×3, at V.ι/U.ι/j) + B2.

## Per-square verdicts (ranked cheapest first)

### S4c `trivialisation_uIota_restrict_compat`  — DERIVABLE-from-existing. LOW.
`unitRestrictIso f = (restrictFunctorIsoPullback f).app 𝒪 ≪≫ pullbackUnitIso f`, and
`pullbackUnitIso = pullbackObjUnitToUnitIso`. The composition law `pullbackObjUnitToUnit_comp` (L884)
is PROVEN axiom-clean. ⇒ S4c = `pullbackObjUnitToUnit_comp` re-wrapped via B2 (+ unit-iso packaging).
No new deep content. Verdict: **DERIVABLE-from-existing (needs B2 only).**

### S2 `tensorObj_restrict_iso_restrict_compat`  — NEEDS-SMALL-NEW-LEMMA. LOW–MEDIUM.
= `pullbackTensorMap_restrict` (PROVEN, the hard 4-square coherence) + B1 (deep part = proven hcompat)
+ B2. NOT genuinely deep. Verdict: **NEEDS-SMALL-NEW-LEMMA (B1 extract + B2).**

### S4b `tensorObj_unit_iso_restrict_compat`  — NEEDS-SMALL-NEW-LEMMA (after S2). MEDIUM.
`tensorObj_unit_iso = a.mapIso(λ_ 𝟙) ≪≫ counit`. Reduces to S2 + unit identification (S4c/`pullbackUnitIso`)
+ left-unitor naturality. Derivable once S2 + S4c land. Verdict: **NEEDS-SMALL-NEW-LEMMA, depends on S2/S4c.**

### S3 `dual_restrict_iso_restrict_compat`  — NEEDS-MEDIUM-NEW-LEMMA (route b) / GENUINELY-DEEP (route a). MEDIUM(-HIGH).
**No dual composition law exists** (no `pullbackDualMap`, no `pullbackDualMap_restrict`; grep confirms).
Two routes:
- (a, fallback) Mirror S2: build `pullbackDualMap f M : (pullback f).obj(dual M) ⟶ dual((pullback f).obj M)`
  + `pullbackDualMap_restrict` (the entire dual D3′ cone) + B1-dual + B2. ~150–250 LOC. GENUINELY-DEEP.
- (b, recommended) Exploit thin-poset structure. `dual_restrict_iso = restrictFunctorIsoPullback ≪≫
  sheafCompPb ≪≫ a.mapIso(H1.symm ≪≫ isoMk sliceDualTransport)`; its Step-4 closes by `subsingleton`.
  S3 then strips via B2 (restrictFunctorIsoPullback) + `sheafificationCompPullback_comp` (PROVEN, L2788)
  + the H1-`leftAdjointUniq` composition coherence + a presheaf isoMk-composition square over the thin
  poset Opens that should close by `subsingleton`. The only genuinely-new ingredient is the
  H1-composition coherence (on S2's side this was subsumed into `pullbackTensorMap_restrict`; here it is
  a cleaner standalone). Verdict: **NEEDS-MEDIUM-NEW-LEMMA via (b); (a) is the deep fallback.**
  CAVEAT: route (b)'s "subsingleton closes the isoMk-composition square" is plausible (mirrors Step-4)
  but UNVERIFIED — confirm before committing.

### S4a `dual_unit_iso_restrict_compat`  — depends on S3. MEDIUM–HIGH.
`dual_unit_iso = a.mapIso presheafDualUnitIso ≪≫ counit`; uses `dual_restrict_iso`. As deep as S3's
chosen route + the `presheafDualUnitIso` composition coherence (cf. proven `presheafDualUnitIso_naturality`,
which is naturality in the unit automorphism, not the immersion — so a small new immersion-side variant,
likely also thin-poset/subsingleton). Verdict: **depends on S3; NEEDS-MEDIUM-NEW-LEMMA after S3.**

## Decisions identified

### Decision: should S2/S4c be proved directly (4-leg chart-chase) or via the existing composition laws?
- **Mathlib/project idiom**: base-change squares are proved once as a *composition coherence* of the
  comparison map (`pullbackTensorMap_restrict`, `pullbackObjUnitToUnit_comp`) in the `pullback` world,
  then transported to the `restrict` world via the `restrictFunctorIsoPullback` NatIso. The project
  ALREADY does this at the IsIso level in `chart_isIso` (L4988: `NatIso.isIso_map_iff
  (restrictFunctorIsoPullback j') ≫ pullbackTensorMap_restrict`).
- **Project's current path (S2–S4c stubs)**: re-derive each square directly by immersion-naturality of
  the 4-leg `restrictFunctorIsoPullback ≫ sheafCompPb ≫ leftAdjointUniq ≫ δ` chart-chase. iter-040
  found this "explodes". It re-proves content already in `pullbackTensorMap_restrict`.
- **Gap**: divergent-with-cost. Proving directly duplicates the proven D3′/unit composition laws and
  hits the explosion the project already paid to resolve once.
- **Cost of divergence**: re-deriving `pullbackTensorMap_restrict`'s 4-square mate calculus (the
  iter-019..-256 effort) per square × 5. The aligned path reuses it.
- **Verdict**: ALIGN — route S2/S4b/S4c (and S3/S4a as far as the dual side allows) through the existing
  composition laws + bridges B1/B2, do NOT re-derive the chart-chase.

### Decision: does the dual side need its own composition law?
- **Idiom**: yes, the tensor side has `pullbackTensorMap_restrict`; the dual side has nothing analogous.
- **Project path**: `dual_restrict_iso` exists but no `pullbackDualMap`/`pullbackDualMap_restrict`.
- **Gap**: NEEDS_MATHLIB_GAP_FILL (project-local) — but the thin-poset route (b) may sidestep building
  the full cone.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL for S3/S4a; try route (b) first (cheaper), (a) as fallback.

## Recommendation
Stop treating S2–S4c as deep immersion-naturality. Build two reusable bridges:
**B2** (`restrictFunctorIsoPullback` pseudonaturality vs `restrictFunctorComp`/`pullbackComp` —
shared prerequisite) and **B1** (`tensorObj_restrict_iso = restrictFunctorIsoPullback ≪≫
asIso pullbackTensorMap ≪≫ reindex`, whose deep content is the already-proven `hcompat`/`δ=e.hom` at
L4812 — extract it). Then land in order: **S4c** (just B2 + proven `pullbackObjUnitToUnit_comp`) →
**S2** (B1+B2 + proven `pullbackTensorMap_restrict`) → **S4b** (S2+S4c) → **S3** via thin-poset route
(b) (B2 + proven `sheafificationCompPullback_comp` + H1-comp coherence + subsingleton) → **S4a**
(after S3). The only genuine new deep work is the dual-side H1/sliceDualTransport composition coherence
(S3), and even that is bounded by the thin-poset `subsingleton` device that already closed
`dual_restrict_iso` Step-4.
