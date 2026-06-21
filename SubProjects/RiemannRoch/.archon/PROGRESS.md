# Project Progress

## Current Stage

prover

## Stages
- [x] init
- [x] autoformalize
- [ ] prover
- [ ] polish

## End-state overview

**Zero inline `sorry` in the dependency cone of the two genus-0 Riemann–Roch headline targets,
0 project axioms (kernel-only).** Full arc in STRATEGY.md.

Headline targets (both protected):
1. `Scheme.WeilDivisor.l_eq_degree_plus_one_of_genus_zero` — `ℓ(D)=deg(D)+1` (genus 0).
2. `genusZero_curve_iso_P1` — genus-0 smooth proper geom. irred. curve over `k̄` ≅ `ℙ¹`.

**iter-017 plan — close the now-unblocked S3 cokernel leaves (G2/G3).** iter-016 closed the ENTIRE
carrier-stalk chain (binding leaf `carrierSheaf_stalk_eq` axiom-clean), which was the sole deep dependency
of the G2/G3 cokernel leaves. progress-critic iter-017: S3 **CONVERGING** (dispatch OK). blueprint-reviewer
iter-017: **HARD GATE CLEARED** for G2/G3 on OcOfD (3 blocks complete+correct, deps closed). The deep
independent bridge `carrierSheaf_zero_iso_toModuleKSheaf` (Hartshorne II.6.3A) was DECOMPOSED in the
blueprint this iter (Mathlib anchor `mem_integers_of_valuation_le_one` [verified] → section-wise lemma →
assembly) for a dedicated lane next iter — it is NOT a prover target this iter (same file as the G2/G3 lane).

## Current Objectives

One `prove` lane on `OcOfD.lean` — the three cokernel-iso leaves (G2 + G3), now unblocked by the
closed binding leaf. Blueprint: `chapters/RiemannRoch_OcOfD.tex`.

1. **`RiemannRoch/OcOfD.lean`** — fill these three `sorry`s, in order. Blueprint:
   `chapters/RiemannRoch_OcOfD.tex`. [prover-mode: prove]

   - `sheafOf.cokernel_stalk_at_iso_kbar` (G2, decl **L1420**, sorry **L1427**) — at `P.point` the
     stalk of `𝒪_C(D) ↪ 𝒪_C([P]+D)` is the fractional-ideal inclusion `π^{-n}𝒪_{C,P} ⊆ π^{-(n+1)}𝒪_{C,P}`
     (both stalks via the closed `carrierSheaf_stalk_eq`). Multiply by `π^{n+1}` (a `k̄`-linear automorphism
     of `K(C)`) to carry it onto `𝔪_P = π𝒪_{C,P} ⊆ 𝒪_{C,P}`; the cokernel quotient is the residue field
     `𝒪_{C,P}/𝔪_P = k̄` (codim-one point, `codimOne_point_residueField_eq_kbar`). Uses
     `stalk_isDVR_of_smooth` (DVR uniformiser `π_P`). Blueprint `lem:cokernel_sheafOf_single_add_stalkAtP_iso_kbar`.
   - `sheafOf.cokernel_skyscraper_hom` (G3 def, decl **L1437**, sorry **L1444**) — the residue-evaluation
     comparison morphism `coker f ⟶ skyscraperSheaf P.point k̄`: zero on opens avoiding `P.point`; on a
     small `U ∋ P.point` sends the class of `g` to its leading Laurent coefficient `(π^{n+1}·g) mod 𝔪_P ∈ k̄`,
     well-defined mod `𝒪_C(D)(U)` and natural in `U`. Blueprint `def:cokernel_skyscraper_hom`.
   - `sheafOf.cokernel_skyscraper_hom_isIso` (G3, decl **L1457**, sorry **L1461**) — that morphism is a
     stalkwise iso: zero-to-zero away from `P.point` (use `carrierPresheaf_le_hom_app_isIso_of_not_mem` ⇒
     coker stalk 0 there + terminal skyscraper stalk), and the residue iso `= k̄` at `P.point` (G2). A
     stalkwise iso of sheaves is an iso: `isIso_of_stalkFunctor_map_iso` [verified]. Blueprint
     `lem:cokernel_skyscraper_hom_isIso`. (Closing this also makes the iso assembly
     `cokernel_carrierSheafHom_iso_skyscraper` fully sorry-free transitively.)

   **Opportunistic comment cleanup (auditor iter-015/016, no proof impact — fix if cheap while in file):**
   stale `sheafOf`/`sheafOf_zero` docstrings + module-header status block still claim closed decls are
   "Tier-3 honest typed sorry"; dual iter-numbering; `open scoped Classical` (L88) lint; dead `hW` param in B0.

   **Do NOT touch this iter:** `carrierSheaf_zero_iso_toModuleKSheaf` (bridge, L1557 — decomposed in blueprint,
   needs scaffolding of its new sub-lemmas next iter); the two `sheafOf_ses_single_add` corners (L1701/L1707,
   bridge-gated); L771 `sheafOf_singlePoint_iso` (off-cone, OCofP-private blocker).

## Deferred this iter (not prover objectives)

- **Bridge `carrierSheaf_zero_iso_toModuleKSheaf`** — DECOMPOSED in blueprint this iter into:
  `\mathlibok` anchor `IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one` [verified],
  project lemma `carrierSheaf_zero_sections_eq_structureSheaf` (section-wise = 𝒪_C via Dedekind-per-chart),
  and the iso assembly. NEXT iter: scaffold the new sub-lemma Lean stubs into OcOfD, then prove (same file
  as the G2/G3 lane → cannot run concurrently this iter). Once landed, the 2 ses corners close by transport.
- **S2 base finiteness** (`Cohomology/SerreFiniteness.lean`) — NEXT after S3. GATE (blueprint-reviewer
  iter-016/017): pin shared H²/Ext²-vanishing lemma for `lem:grothendieck_vanishing_curve` (no `\lean`,
  used-by 4) = same fact as RRFormula.lean:469; do at S2 activation. See STRATEGY + task_pending M3.
- **M3-close (`RRFormula.lean`) / HEADLINE #1** — BLOCKED on S3 + S2. Owes `_hH1`/fallacious-step prose fix
  in `thm:riemannRoch_genus_zero` (Lean closed; writer-fix at S2 activation).
- **S4 (narrow) + M5 (`RationalCurveIso.lean` + `AbelianVarietyRigidity.lean`)** — HEADLINE #2 arm.
  Before dispatch: add `% archon:covers AbelianVarietyRigidity.lean` to RationalCurveIso.tex.
- **S5 `injective_flasque` (`j_!`)** — out of headline cone; leave.

## Notes

- **prove mode**: the G2/G3 leaves are scaffolded typed `sorry`s with detailed blueprint proofs; the prover
  fills them. G2 is the one deep sorry (residue computation); the G3 def + isIso are assembly.
- **No import changes** needed (OcOfD already imports CurveKrullDim/SmoothStalkDVR/WeilDivisor/ResidueFieldKbar).
- `\leanok` markers recomputed deterministically by `sync_leanok` post-prover.
- "Route C PAUSE" / "Pic representability" / "Route A" standing hints are stale parent-Jacobian
  carryovers (this subproject IS the former Route-C RR work); AUTONOMOUS directive governs.
