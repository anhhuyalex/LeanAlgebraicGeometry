# AlgebraicJacobian/Picard/TensorObjSubstrate.lean

## `pullbackTensorMap_isIso_of_isOpenImmersion` (K1, L4139) — seed-1 D4′ brick

### Attempt 1 (iter-021) — presheaf-δ route (planner REDIRECT, NOT functor-level transport)
- **Approach:** Followed the planner's designed entry `isIso_pullbackTensorMap_of_isIso_sheafifyDelta`,
  then mirrored the CLOSED `tensorObj_restrict_iso` (H1 + strong-monoidal `pushforward β`) and reduced
  the residual via the adjunction-mate calculus, exactly as directed.
- **Result:** PARTIAL — K1's bare `sorry` (was L4172) is replaced by a multi-step proof whose **sole**
  residual is one clean presheaf-level mate-compatibility equation (L4219). Whole file compiles, zero
  errors, zero new axioms, no new top-level declarations.

#### What is now proved (verified, committed)
1. **STEP A (sheafification preserves isos).** `apply isIso_pullbackTensorMap_of_isIso_sheafifyDelta`
   reduces to `IsIso (a_Y.map δ)`; reduced further to the PRESHEAF-level
   `IsIso (Functor.OplaxMonoidal.δ (PresheafOfModules.pullback φ') M.val N.val)` and closed the wrapper
   with `Functor.map_isIso _ (…δ…)`.
   - **Gotcha:** needed `haveI hRA : (pushforward φ').IsRightAdjoint := (pullbackPushforwardAdjunction φ').isRightAdjoint`
     in scope (else the `presheafPullbackOplaxMonoidal` instance leaves metavars in `δ`).
   - **Gotcha:** `infer_instance`/`Functor.map_isIso _ _` FAIL (the `[IsIso f]` arg becomes a metavar);
     must pass the `δ` term **explicitly**: `exact Functor.map_isIso _ (Functor.OplaxMonoidal.δ … )`.
   - **Gotcha:** `δ` only elaborates with a fully type-annotated `letI φ' : … := (f.toRingCatSheafHom).hom`
     (fixes the monoidal-category args); but the instance for the OUTER goal must be registered against
     the LITERAL `(f.toRingCatSheafHom).hom`, not the let-var (zeta mismatch in instance search).
2. **STEP B (strong-monoidal witness `e`).** Built, in-proof and mirroring `tensorObj_restrict_iso`:
   `α`, `β` (sectionwise `f.appIso⁻¹`), `hadj : pushforward β ⊣ pushforward φ'`
   (`pushforwardPushforwardAdj`), `H1 : pushforward β ≅ pullback φ'` (`leftAdjointUniq`),
   `hβ`/`β'`/`hMonβ` (`restrictScalarsMonoidalOfBijective`), the object-level tensorator
   `μIsoβ := Functor.Monoidal.μIso (pushforward₀OfCommRingCat … ⋙ restrictScalars β') M.val N.val`,
   and the candidate iso `e` of the **same type as `δ`**:
   `e := (H1.app (M⊗N)).symm ≪≫ μIsoβ.symm ≪≫ (H1.app M ⊗ᵢ H1.app N)`.
   Then `rw [hcompat]; exact e.isIso_hom`. All of this typechecks.
3. **hcompat reduction (verified).** `hcompat : δ (pullback φ') M.val N.val = e.hom` is reduced by
   `rw [Adjunction.leftAdjointOplaxMonoidal_δ, Equiv.symm_apply_eq, Adjunction.homEquiv_unit]`
   to the **sheafification-free, δ-free** presheaf equation (**):
   ```
   (adj.unit M ⊗ₘ adj.unit N) ≫ μ(pushforward φ') (FM) (FN)
     = adj.unit (M ⊗ N) ≫ (pushforward φ').map e.hom         (adj := pullbackPushforwardAdjunction φ')
   ```
   Confirmed (multi_attempt) that the next step also fires:
   `rw [← Adjunction.unit_leftAdjointUniq_hom_app hadj (pullbackPushforwardAdjunction φ') M.val]`
   substitutes `adj.unit = hadj.unit ≫ (pushforward φ').map H1.hom`.

#### The SOLE residual `sorry` (L4219) — precise mathematical content
After substituting the units (`unit_leftAdjointUniq_hom_app`) and `μ`-naturality, (**) reduces to:

> the **strong-monoidal tensorator** `μIsoβ.inv` of `pushforward β` equals the **`hadj`-mate** of the
> project lax tensorator `μ (pushforward φ')` — equivalently, the project lax structure
> `presheafPushforwardLaxMonoidal φ'` on `pushforward φ'` coincides with `rightAdjointLaxMonoidal hadj`
> (the mate of `pushforward β`'s `restrictScalarsMonoidalOfBijective` strong structure).

Equivalently: `(Adjunction.leftAdjointOplaxMonoidal hadj).δ M.val N.val = μIsoβ.inv`. By the uniqueness
`laxMonoidalEquivOplaxMonoidal`, this would follow from `hadj.IsMonoidal` w.r.t. **both** the project lax
structure on `pushforward φ'` AND `pushforward β`'s strong structure — but `instIsMonoidal hadj` only
yields `hadj.IsMonoidal` w.r.t. the **mate** lax structure (`rightAdjointLaxMonoidal hadj`), which is a
**different construction** of the lax structure than the project's explicit composite
`presheafPushforwardLaxMonoidal`. Reconciling the two (their `μ`/`ε` components agree) is the residual.

This is the δ-side analogue of the unit-side `presheafUnit_comp_map_eta` (D2′) and the open-immersion
analogue of the D3′ base-change mate calculus. It is a `mathlib-build`-scale reconciliation of two
monoidal structures on the same functor `pushforward φ'` — exactly the "functor-level strong-monoidal
pullback model" that ARCHON_MEMORY flags as not globally synthesizable.

#### Key Mathlib facts located (for the next iteration)
- `Adjunction.leftAdjointOplaxMonoidal_δ`: `δ X Y = (adj.homEquiv).symm ((unit X ⊗ₘ unit Y) ≫ μ G _ _)`.
- `Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2 x : adj1.unit.app x ≫ G.map((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x` (Adjunction/Unique.lean).
- `Adjunction.IsMonoidal.leftAdjoint_μ` / `leftAdjoint_ε`, `instIsMonoidal`/`instIsMonoidal_1`,
  `Adjunction.laxMonoidalEquivOplaxMonoidal` (uniqueness of the mate oplax/lax structure),
  `CategoryTheory.Functor.Monoidal.natTransIsMonoidal_of_transport` (Monoidal/NaturalTransformation.lean).
- `Functor.OplaxMonoidal.δ` of a strong (`Monoidal`) functor is iso (used via `e.isIso_hom`).

#### Dead ends (do NOT retry)
- Functor-level `Functor.Monoidal.transport H1` / `(pullback φ').Monoidal` — the monoidal-carrier diamond
  (already documented; superseded by the in-proof δ route above).
- `infer_instance` / `Functor.map_isIso _ _` for the sheafification wrapper (metavar in `[IsIso f]`).
- `Adjunction.IsMonoidal.leftAdjoint_μ` alone does NOT close it: it expresses `μ` only at
  pushed-forward objects `G X, G Y`, not at arbitrary `M.val, N.val`, so it cannot give `IsIso (δ … M.val N.val)`
  directly. The route MUST go through the explicit `H1`/`μIsoβ` witness + the (**) reconciliation.

## Needs blueprint entry
None — all new content is in-proof (`let`/`have` inside `pullbackTensorMap_isIso_of_isOpenImmersion`,
whose signature is unchanged). No new top-level declarations.

## Summary
- **sorry count (this file): before 2 → after 2.** No bare sorry CLOSED, but the K1 sorry was
  transformed from a bare top-level `sorry` (old L4172) into the residual of a substantial, fully-typechecked
  proof scaffold (Steps A+B + the verified `hcompat` transposition), leaving a single clean presheaf-level
  mate-compatibility equation (**) at L4219.
- **Still open:** `pullbackTensorMap_isIso_of_isOpenImmersion` residual (**) (L4219) — mate reconciliation,
  see above. `exists_tensorObj_inverse` (L734) — import-cycle-deferred per standing deferral (untouched).
- **Adjacent sorries:** L734 is the only other; it is the standing import-cycle deferral (NOT to be closed
  in this file), so not attempted.

## Why I stopped
**Partial progress.** Concrete, verified Lean advances (all compile, file is error-free, no new axioms):
1. Reduced K1 to the presheaf-level `IsIso δ` (Step A), with the two non-obvious elaboration gotchas solved.
2. Constructed the explicit strong-monoidal witness iso `e` (Step B), of the exact type of `δ`.
3. Reduced the compatibility `δ = e.hom` (`hcompat`) by adjunction transposition to a clean,
   sheafification-free, δ-free unit/μ equation (**), and verified the subsequent unit-substitution step fires.

The remaining residual (**) is the strong-monoidal/mate reconciliation between the project's explicit lax
structure on `pushforward φ'` and the `hadj`-mate of `pushforward β`'s strong structure. This is a genuine
`mathlib-build`-scale obstacle (the same functor-level strong-monoidal-pullback content ARCHON_MEMORY/
the planner flagged), not a difficulty I can paper over: I confirmed `Adjunction.IsMonoidal.leftAdjoint_μ`
cannot fire directly (wrong objects), and `instIsMonoidal` only gives the mate lax structure, not the
project one. The planner's directive explicitly authorized stopping here ("If the mate-compatibility does
NOT fire on this concrete adjunction … STOP, report the exact unprovable `have` + its goal state, and name
the missing reconciliation lemma — next iter switches to `mathlib-build`"). The missing ingredient is:
**a lemma identifying `presheafPushforwardLaxMonoidal φ'` with `Adjunction.rightAdjointLaxMonoidal hadj`**
(equivalently `(Adjunction.leftAdjointOplaxMonoidal hadj).δ = μIsoβ.inv`), for the open-immersion
pushforward-pushforward adjunction `hadj`.
