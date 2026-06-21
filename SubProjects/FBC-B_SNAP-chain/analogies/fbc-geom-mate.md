# Analogy: per-factor mate coherence for the geometric leg `chartBaseChangeGeometricComparison_mate`

## Mode
api-alignment

## Slug
fbc-geom-mate

## Iteration
018

## Question
(1) Does Mathlib have a per-factor unit-transpose / mate coherence for `Scheme.Modules.pullbackComp` /
`pushforwardComp` — the geometric analogue of `ModuleCat.homEquiv_extendScalarsComp`? (2) If absent,
what idiom makes `conjugateEquiv` over a COMPOSITE `pullbackPushforwardAdjunction` elaborate cheaply
(the `refine natTrans_ext_of_unit … (fun c => unit_conjugateEquiv …) ?_` route whnf-bombs at 200k hb)?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:1590-1619` — `chartBaseChangeGeometricComparison_mate`, the open `sorry`; its comment (L1615) asserts `conjugateEquiv_pullbackComp_inv` is "comment-fiction".
- `…:1524-1549` — `chartBaseChangeGeometricComparisonNat`, `.hom = (pullbackComp ρB inclR).hom ≫ (pullbackCongr hsq).hom ≫ (pullbackComp inclR' ρ).inv`.
- `…:1556-1582` — `chartBaseChangePushforwardNat`, `.hom = (pushforwardComp inclR' ρ).hom ≫ (pushforwardCongr hsq).hom ≫ (pushforwardComp ρB inclR).inv`.
- `…:1450-1471` — `conjugateEquiv_extendScalarsComp` (the algebraic per-factor mate, the template to mirror).
- prior `analogies/fbc-mate-reencode.md` (iter-034) and `analogies/fbc-composite-mate-recognition.md` (iter-044) — already cite `conjugateEquiv_pullbackComp_inv` as REAL and lay out this exact idiom for the bigger `_legs` crux.

## Decisions identified

### Decision: does the geometric per-factor mate coherence exist in Mathlib? (Q1)

- **Mathlib idiom — IT EXISTS, the directive premise is FALSE.** `conjugateEquiv_pullbackComp_inv` is a
  real, `@[simp]`-tagged Mathlib lemma, in TWO layers reachable from the project (it already imports
  `Scheme.Modules.pullbackComp`, so this is in scope):
  - `AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv`
    (`Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:238-242`):
    ```
    conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
        (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv = (pushforwardComp f g).hom
    ```
  - backed by `SheafOfModules.conjugateEquiv_pullbackComp_inv`
    (`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:176-181`),
  - whose engine is the generic `Adjunction.conjugateEquiv_leftAdjointCompIso_inv`
    (`Mathlib/CategoryTheory/Adjunction/CompositionIso.lean:82-86`).
  - Identity-side sibling: `Scheme.Modules.conjugateEquiv_pullbackId_hom` (`Sheaf.lean:203-206`,
    `conjugateEquiv .id (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom = (pushforwardId X).inv`).
  This is EXACTLY the geometric analogue of `ModuleCat.homEquiv_extendScalarsComp`/`conjugateEquiv_extendScalarsComp`.
  Mathlib in fact gives MORE than the algebraic side has: the geometric per-factor fact is fully proven
  in Mathlib, whereas the algebraic `chartBaseChangeModuleReassoc_extendScalarsComp` is still a project `sorry`.

- **Project's current path**: comment L1615 claims the lemma is fictional and proposes a bespoke
  `homEquiv_pullbackComp` or banned `set_option maxHeartbeats`. Both are unnecessary.
- **Gap**: divergent-and-wrong (the premise that no coherence exists is factually false; the project's
  own later iters 034/044 already use the real lemma elsewhere — the L1615 comment is stale).
- **Verdict**: **ALIGN_WITH_MATHLIB.** Use `conjugateEquiv_pullbackComp_inv`; delete the false comment.

### Decision: how to make the composite-adjunction conjugate elaborate cheaply? (Q2)

- **Root cause of the 200k-hb bomb**: `refine natTrans_ext_of_unit … (fun c => unit_conjugateEquiv _ _ _ c) ?_`
  forces, at every component `c`, the composite unit `((a_ρ).comp (a_ι')).unit.app c` to whnf-reduce in
  the `(Spec _).Modules` value-`ModuleCat` category. That component reduction is the expensive thing.
- **Mathlib idiom — never reduce to components.** Drive the proof entirely through CLOSED coherence
  lemmas (`conjugateEquiv_pullbackComp_inv`, `conjugateEquiv_comp`, a tiny `conjugateEquiv_pullbackCongr`
  helper). `rw`/`exact` against a closed `@[simp]` lemma only unifies the adjunction/iso ARGUMENTS
  (defeq on already-built terms) — it never normalises `unit_conjugateEquiv` to component form, so the
  diamond never forms. This is the same "lock-prone object stays a metavariable" principle the prior
  analogies used (`surjective`/`injective`), specialised here to the much simpler 3-factor target.
  `natTrans_ext_of_unit` and `unit_conjugateEquiv`-over-the-composite are BANNED for this leg.
- **Verdict**: **PROCEED** on the coherence-driven route; no `def`-wrap and no bespoke `homEquiv_pullbackComp` needed.

## Buildable skeleton

Abbreviations (use the file's `set` names): `a_ρ, a_ι', a_ι, a_ρB := pullbackPushforwardAdjunction (Spec.map …)`;
`adjA := a_ρ.comp a_ι'` (left = `pb(Spec ρ) ⋙ pb(Spec inclR')` = `geomNat`'s `L₁`);
`adjB := a_ι.comp a_ρB` (left = `pb(Spec inclR) ⋙ pb(Spec ρB)` = `L₂`);
`adjMid1 := pullbackPushforwardAdjunction (Spec.map ρB ≫ Spec.map inclR)`;
`adjMid2 := pullbackPushforwardAdjunction (Spec.map inclR' ≫ Spec.map ρ)`.

**Step 0 — one helper lemma (the only genuine residual; congr piece, NOT a composite, so no bomb):**
```lean
lemma conjugateEquiv_pullbackCongr {X Y : Scheme} {f g : X ⟶ Y} (hf : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackCongr hf).hom = (Scheme.Modules.pushforwardCongr hf).hom := by
  subst hf            -- f,g free ⇒ substitutable; both congrs collapse to the identity nat-iso
  -- pullbackCongr rfl = eqToIso rfl = Iso.refl; pushforwardCongr rfl ≅ 𝟭 (app = 𝟙 by *_app_app)
  ext : 2; simp [Scheme.Modules.pullbackCongr, conjugateEquiv_id]   -- close to `conjugateEquiv_id`
```
(`subst` works because `f g` are universally quantified vars; in the call site `hf = hsq` is an equality
of fixed composites, but the helper is applied as a closed lemma, so no `subst` happens there.)

**Step 1 — reduce to `.hom` and split the composite via `conjugateEquiv_comp` (closed `@[reassoc(attr:=simp)]`):**
```lean
theorem chartBaseChangeGeometricComparison_mate … := by
  -- (introduce letI/set exactly as in the two Nat defs so the adjunction/iso names match syntactically)
  apply Iso.ext
  rw [conjugateIsoEquiv_apply_hom]            -- L1498 uses this; auto-simp of `@[simps] conjugateIsoEquiv`
  -- unfold geomNat.hom and chartBaseChangePushforwardNat.hom to their 3 coherence factors
  show conjugateEquiv adjA adjB
        ((pullbackComp (Spec.map ρB) (Spec.map inclR)).hom ≫
         (pullbackCongr hsq).hom ≫ (pullbackComp (Spec.map inclR') (Spec.map ρ)).inv)
      = (pushforwardComp (Spec.map inclR') (Spec.map ρ)).hom ≫
        (pushforwardCongr hsq).hom ≫ (pushforwardComp (Spec.map ρB) (Spec.map inclR)).inv
  -- regroup left-assoc, then split twice with conjugateEquiv_comp (←) supplying the midpoint adjunctions:
  rw [show (p3 ≫ p2 ≫ p1) = (p3 ≫ p2) ≫ p1 from (Category.assoc _ _ _).symm,
      ← conjugateEquiv_comp adjA adjMid2 adjB,           -- α=p1, β=p3≫p2
      ← conjugateEquiv_comp adjMid2 adjMid1 adjB]        -- inner split: α=p2, β=p3
```
(Supply `adjMid1/adjMid2` explicitly — `rw ←` cannot synthesise the midpoint adjunction. Use explicit
`have` regroupings rather than letting higher-order unification guess the associativity split.)

**Step 2 — discharge each of the three single-pair conjugate factors by a closed lemma:**
- `conjugateEquiv adjA adjMid2 (pullbackComp (Spec inclR')(Spec ρ)).inv = (pushforwardComp (Spec inclR')(Spec ρ)).hom`
  — **directly `conjugateEquiv_pullbackComp_inv`** (`f=Spec inclR', g=Spec ρ`; `a_ρ.comp a_ι' = adjA` ✓).
- `conjugateEquiv adjMid2 adjMid1 (pullbackCongr hsq).hom = (pushforwardCongr hsq).hom`
  — **`conjugateEquiv_pullbackCongr hsq`** (Step 0). [adjMid2/adjMid1 are the `pullbackPushforwardAdjunction`
  of the two sides of `hsq`; the helper's `f,g` instantiate to those composites.]
- `conjugateEquiv adjMid1 adjB (pullbackComp (Spec ρB)(Spec inclR)).hom = (pushforwardComp (Spec ρB)(Spec inclR)).inv`
  — the `.hom`/reverse direction. Get it from `conjugateEquiv_pullbackComp_inv` (`f=Spec ρB, g=Spec inclR`:
  `conjugateEquiv adjB adjMid1 (pullbackComp ρB inclR).inv = (pushforwardComp ρB inclR).hom`) by inverting:
  `conjugateIsoEquiv adjMid1 adjB (pullbackComp ρB inclR)` has `.inv = (pushforwardComp ρB inclR).hom`, so
  its `.hom` (= our term) `= (pushforwardComp ρB inclR).hom⁻¹ = (pushforwardComp ρB inclR).inv`. Mechanise
  with `Iso.inv_eq_inv` / `conjugateIsoEquiv` or a 3-line `have`.

After the three rewrites both sides are the identical 3-term pushforward composite; close by `rfl`.

## Recommendation
**ALIGN_WITH_MATHLIB.** The geometric leg is in BETTER shape than the algebraic leg: Mathlib already
proves the per-factor mate coherence (`conjugateEquiv_pullbackComp_inv`, `conjugateEquiv_pullbackId_hom`).
Do NOT build `homEquiv_pullbackComp`, do NOT use `set_option maxHeartbeats`, and ABANDON the
`natTrans_ext_of_unit` + `unit_conjugateEquiv`-over-the-composite route (that component reduction is the
200k-hb bomb). Instead: (a) add the small `conjugateEquiv_pullbackCongr` helper (`subst`→`conjugateEquiv_id`);
(b) `apply Iso.ext; rw [conjugateIsoEquiv_apply_hom]`; (c) split the 3-factor conjugate with explicit
`conjugateEquiv_comp` over named midpoint adjunctions `adjMid1/adjMid2`; (d) discharge the three factors by
`conjugateEquiv_pullbackComp_inv` (×2, one inverted) + `conjugateEquiv_pullbackCongr`. Every step is a `rw`
against a closed `@[simp]` lemma, so the composite unit is never whnf-reduced and the diamond never bites.
Delete the stale "comment-fiction" note at L1615. This mirrors the live `analogies/fbc-mate-reencode.md` /
`fbc-composite-mate-recognition.md` idiom, scaled down to this 3-factor target.
