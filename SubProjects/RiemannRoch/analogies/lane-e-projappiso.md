# Analogy: Mathlib path for `r_1.appTop isLocElem = 1` in Lane E

## Mode
api-alignment

## Slug
lane-e-projappiso

## Iteration
189

## Question

Does Mathlib at b80f227 expose `(Proj.awayι _).appIso ⊤` as a usable
identity, and if not, what is the cleanest Mathlib-aligned recipe for
computing `r_1.appTop ((ΓSpecIso _).inv isLocElem) = (ΓSpecIso k̄).inv 1`
where `r_1 ≫ Proj.awayι (X 1) = onePt.left` with `onePt.left =
Proj.fromOfGlobalSections 𝒜 (evalIntoGlobal v=(1,1)) hφ`?

## Project artifact(s)

- `AlgebraicJacobian/AbelianVarietyRigidity.lean:106-163` — `iotaGm_onePt_chart1_factor` (constructs `r_1` via `IsOpenImmersion.lift` but packs it in an `∃`).
- `AlgebraicJacobian/AbelianVarietyRigidity.lean:252-439` — `iotaGm_chart1_composition_isOpenImmersion` (the blocker; ends with a residual `r_1.appTop(isLocElem) = 1` sorry at L439).
- `AlgebraicJacobian/Genus0BaseObjects/Points.lean:51-128` — `evalIntoGlobal`, `pointOfVec`, `onePt = pointOfVec (fun _ => 1) 0`.

## Decisions identified

### Decision: `IsOpenImmersion.lift_app` vs. `appTop`-of-composition for evaluating `r_1.appTop`

- **Mathlib idiom**: `IsOpenImmersion.lift_app` at
  `Mathlib/AlgebraicGeometry/OpenImmersion.lean:696`:
  ```
  (lift f g H).app V = (f.appIso V).inv ≫ g.app (f ''ᵁ V) ≫
      X.presheaf.map (eqToHom (app_eq_invApp_app_of_comp_eq_aux _ _ _ (lift_fac ..).symm V).op
  ```
  Combined with `lift_uniq` (line 643), this is the canonical idiom for
  evaluating `r_1.app U` whenever `r_1 ≫ f = g` for an open immersion
  `f`. The `appIso` direction (`Γ(Y, f ''ᵁ U) ≅ Γ(X, U)`, line 190) is
  the right thing to use for the inverse "lift" direction; the `appTop`
  direction goes the wrong way (image-mismatch on degree-0 part, as the
  directive observed).
- **Project's current path**: iter-186 documented a 6-step recipe using
  `cancel_mono` to derive `r_1 = lift _ _ h_range` from `h_r_1`. This is
  structurally correct. Iter-188 attempted it but ran into reconstruction
  of `h_range` (already proven in `iotaGm_onePt_chart1_factor`, but
  unavailable because `r_1` is hidden inside an `∃`).
- **Gap**: divergent-with-cost. The `∃`-packaging of `r_1` forces the
  consumer to re-derive `h_range` via `cancel_mono`. Refactoring
  `iotaGm_onePt_chart1_factor` to expose `r_1` as a `noncomputable def`
  (with the lift body inline) and `h_r_1`, `h_range` as separate lemmas
  removes the re-derivation cost.
- **Cost of divergence**: ~30-50 LOC of `cancel_mono` plumbing in every
  consumer (currently just one: `iotaGm_chart1_composition_isOpenImmersion`),
  plus the structural confusion (iter-186 to iter-188, 3 iters lost to
  recipe rediscovery).
- **Verdict**: ALIGN_WITH_MATHLIB — refactor `iotaGm_onePt_chart1_factor`
  to a `def` + lemma pair.

### Decision: `(Proj.awayι _).appIso ⊤` direct simp lemma vs. manual chain

- **Mathlib idiom**: There is NO direct simp lemma identifying
  `(Proj.awayι _).appIso ⊤` with `basicOpenIsoAway.symm ≪≫ (topIso etc.)`
  in Mathlib at b80f227. The available identifications:
  - `Proj.basicOpenIsoAway` (`Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Basic.lean:179`):
    `Away 𝒜 f ≅ Γ(Proj 𝒜, basicOpen 𝒜 f)` via `awayToSection`.
  - `Proj.basicOpenToSpec_app_top` (line 143):
    `(basicOpenToSpec 𝒜 f).app ⊤ = (ΓSpecIso _).hom ≫ awayToSection ≫ basicOpen.topIso.inv`.
  - `Proj.opensRange_awayι` (line 199):
    `(Proj.awayι _).opensRange = Proj.basicOpen 𝒜 f`.

  The consumer must wire these together: `awayι = basicOpenIsoSpec.inv ≫ basicOpen.ι`
  (line 190) ⟹ `awayι.app U = basicOpen.ι.app U ≫ basicOpenIsoSpec.inv.app (basicOpen.ι ⁻¹ᵁ U)`;
  for `U = basicOpen 𝒜 f`, this collapses via `basicOpenToSpec_app_top`.
- **Project's current path**: iter-188 attempted `simp` default and got
  stuck. No explicit manual wiring through `basicOpenIsoAway` was tried.
- **Gap**: NEEDS_MATHLIB_GAP_FILL (partial). The connecting lemma
  ```
  (Proj.awayι 𝒜 f f_deg hm).app (Proj.basicOpen 𝒜 f) ≫ basicOpenIsoAway.hom
    = (ΓSpecIso _).inv ≫ ... (topIso shuffle) ...
  ```
  is implicit in `basicOpenToSpec_app_top` + the definition of `awayι`,
  but no single simp lemma packages it. A 5-10 LOC Mathlib PR adding
  `Proj.awayι_app_basicOpen` or `Proj.awayι_appIso_top` would close the gap.
- **Cost of divergence**: ~30-40 LOC of manual `basicOpenIsoSpec.inv`
  unwinding per consumer. For just one consumer (this file), absorbable
  inline; if more Proj-of-graded-ring computations land downstream
  (Picard / etc.), upstream the PR.
- **Verdict**: PROCEED (project-side helper) + flag for Mathlib PR.

### Decision: Compute `r_1.appTop` via `lift_app` vs. via `morphismRestrict`

- **Mathlib idiom**: For `r_1 = lift (awayι 𝒜 (X 1)) onePt.left h_range`,
  the `lift_app` direction is more directly tied to the open-immersion
  universal property. The `morphismRestrict` direction (via
  `fromOfGlobalSections_morphismRestrict` line 493 +
  `fromOfGlobalSections_resLE` line 502) is more directly tied to the
  specific shape of `onePt.left = fromOfGlobalSections`.
  Both reach the same answer; `morphismRestrict` may be cleaner here
  because `fromOfGlobalSections_morphismRestrict` already says:
  ```
  (fromOfGlobalSections 𝒜 f hf) ∣_ (basicOpen 𝒜 r) =
    (Scheme.isoOfEq _).hom ≫ toBasicOpenOfGlobalSections 𝒜 f rfl hn hr
  ```
  This identifies the restriction of `onePt.left` to `basicOpen 𝒜 (X 1)`
  with the explicit `toBasicOpenOfGlobalSections` morphism — whose
  underlying ring map is `IsLocalization.map _ (evalIntoGlobal v)`.
- **Project's current path**: iter-186 recipe is via `lift_app`.
- **Gap**: divergent-equivalent (both work; `morphismRestrict` may be
  ~10-15 LOC shorter).
- **Verdict**: DIVERGE_INTENTIONALLY if the project prefers the `lift_app`
  recipe (it's a cleaner conceptual statement), but mention
  `morphismRestrict` as the structural alternative.

## Recommendation

**Primary path (recommended)**: refactor `iotaGm_onePt_chart1_factor` to
expose `r_1` as a `noncomputable def` plus a separate `lift_fac`-style
lemma. The current `∃`-packaging hides the `IsOpenImmersion.lift`
internals that the consumer needs. Once exposed, the iter-188 6-step
recipe collapses to:

1. `unfold r_1_def` (now exposed) ⟹ `r_1 := IsOpenImmersion.lift (awayι _) onePt.left h_range`.
2. `rw [IsOpenImmersion.lift_app]` at `V = ⊤` ⟹ `appIso.inv ≫ onePt.left.app (basicOpen 𝒜 (X 1)) ≫ presheaf.map`.
3. Use `Proj.opensRange_awayι` to rewrite `awayι ''ᵁ ⊤ = basicOpen 𝒜 (X 1)`.
4. For `appIso ⊤ .inv (isLocElem)`: use `awayι = basicOpenIsoSpec.inv ≫ basicOpen.ι`, then `basicOpenToSpec_app_top` + `basicOpenIsoAway.hom = awayToSection` to identify the image as `basicOpenIsoAway.hom isLocElem ∈ Γ(Proj 𝒜, basicOpen)`.
5. Use `fromOfGlobalSections_morphismRestrict` (or `_resLE`) on `onePt.left` restricted to `basicOpen 𝒜 (X 1)` ⟹ `toBasicOpenOfGlobalSections`-shape morphism whose ring map is `IsLocalization.map _ (evalIntoGlobal (1,1))`.
6. Evaluate on `isLocElem = X_0 / X_1`: `IsLocalization.map _ (evalIntoGlobal v) sends [X_0 / X_1] ↦ (evalIntoGlobal v X_0) / (evalIntoGlobal v X_1) = 1 / 1 = 1` (in `Localization.Away 1 = k̄`).

Realistic budget: **~60-80 LOC**, not 30-50. The directive's 30-50 LOC
target underestimates the appIso plumbing.

**Secondary observation**: if the project envisions more
`Proj.fromOfGlobalSections` ↔ chart calculations downstream (e.g. in
Picard / FGA layer), a small Mathlib PR adding a direct
`Proj.awayι_appIso_top` simp lemma (5-10 LOC, derived from
`basicOpenToSpec_app_top`) would generalize this work and remove the
chase across all consumers. Not blocking iter-190.
