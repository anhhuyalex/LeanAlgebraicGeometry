# Analogy: is `SheafOfModules.pullbackObjUnitToUnit`'s instance shape canonical, and what is the canonical idiom for transporting `IsIso` across its composition-coherence equation?

## Mode
api-alignment

## Slug
pbu-canon

## Iteration
241

## Question
(1) Is `SheafOfModules.pullbackObjUnitToUnit`'s instance-shape canonical, or is the
project fighting a design mismatch? (2) What is the canonical Mathlib idiom for
transporting `IsIso` across a coherence equation `pbu(h;f) = … ; … ; …` without
re-triggering instance synthesis on the components? (3) Will this instance-canonicity
issue RECUR in Phase 2/3?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:923-1009` — `pullbackObjUnitToUnit_comp`
  (landed, axiom-clean): the pullback-side composition coherence
  `pbu(h≫f) = (pullbackComp h f).inv.app _ ≫ (pullback h).map (pbu f) ≫ pbu h`.
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1011-1049` — HANDOFF block: the
  per-chart lemma `isIso_restrict_pullbackObjUnitToUnit` + globalizer recipe is fully
  worked out but blocked because, inside the multi-hypothesis chart context,
  `infer_instance` fails to synthesize `IsIso (pbu U.ι)`, `IsIso (pbu g)`, and even
  `IsIso ((pullbackComp g U.ι).inv.app _)` — all of which synthesize FINE standalone.

## Decisions identified

### Decision: Is the comparison-map / IsIso-instance signature canonical?

- **Mathlib idiom**: The comparison map and its iso fact are *Mathlib's own*, defined in
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree` (`.lake/.../PullbackFree.lean`):
  - `pullbackObjUnitToUnit φ := ((pullbackPushforwardAdjunction φ).homEquiv _ _).symm
    (unitToPushforwardObjUnit φ)` — i.e. it IS the adjunction-mate (conjugate) of the
    concrete pushforward-side map `unitToPushforwardObjUnit`. (PullbackFree.lean, the
    `noncomputable def pullbackObjUnitToUnit` block.)
  - `instance [F.Final] : IsIso (pullbackObjUnitToUnit φ)` — proved via
    `isIso_iff_coyoneda_map_bijective` + `bijective_pushforwardSections` (finality ⇒
    sections bijective). Its full instance-arg list, from the hover, is
    `[Functor.IsContinuous F J K] [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [K.HasSheafCompose (forget₂ RingCat AddCommGrpCat)] [(pushforward φ).IsRightAdjoint]
    [F.Final]`.
  These are NOT design noise: `IsContinuous`/`HasSheafCompose`/`IsRightAdjoint` are exactly
  the data needed to *define* `pushforward`/`pullback`/the adjunction in the first place,
  and `F.Final` is the genuine mathematical hypothesis. This is the standard Mathlib shape
  for an adjunction-mate comparison that becomes iso under a hypothesis. The closest direct
  precedents:
  - `CategoryTheory.Functor.Monoidal.μIso` (`Mathlib.CategoryTheory.Monoidal.Functor`):
    the monoidal-functor lax-comparison `μ : F X ⊗ F Y ⟶ F (X ⊗ Y)` (itself an
    adjunction/coherence-mate) is exposed as a **bundled `Iso`** `μIso F X Y` keyed on the
    hypothesis `[F.Monoidal]`, with `μIso_hom : (μIso F X Y).hom = LaxMonoidal.μ F X Y`.
    Mathlib does NOT publish a bare `instance : IsIso (LaxMonoidal.μ …)` and reason about it
    on composites — it hands out the `Iso`.
  - In the SAME file as `pullbackObjUnitToUnit`, `pullbackObjFreeIso` builds
    `(asIso (sigmaComparison _ _)).symm ≪≫ Sigma.mapIso (fun _ ↦ asIso (pullbackObjUnitToUnit φ))`
    — Mathlib wraps `pullbackObjUnitToUnit` in `asIso` and composes at the `Iso` level,
    rather than synthesizing `IsIso` of a `rw`-produced composite.
- **Project's current path**: Uses Mathlib's `pullbackObjUnitToUnit` + the `OfFinal`
  instance verbatim (correct), then tries to close `IsIso` of the *rewritten composite*
  (`rw [pullbackObjUnitToUnit_comp …]; infer_instance`) inside a context cluttered with
  `haveI : IsIso (pbu …)` / `(Opens.map _).Final` hypotheses.
- **Gap**: identical on the signature (the project uses Mathlib's exact API). The friction is
  NOT a signature mismatch — it is Lean's typeclass-resolution behavior on the rewritten
  composite. So: **divergent-equivalent at worst**, and only at the proof-tactic level.
- **Cost of divergence (if any)**: none structural. The "buried implicits" the prover
  flagged are canonical; refactoring them is impossible (upstream Mathlib) and unnecessary.
- **Verdict**: PROCEED. The signature is canonical; the project is NOT fighting a design
  mismatch. The wall is a proof-context TC accident, addressed by Decision 2.

### Decision: canonical idiom for transporting `IsIso` across the coherence equation

- **Mathlib idiom**: *Bundle the comparison as an `Iso` (`asIso`) at a clean construction
  site, then do ALL downstream reasoning at the `Iso` level* — never re-synthesize the
  `F.Final`-keyed `IsIso` instance on a `rw`-produced composite. This is precisely what
  `μIso` (hand out the iso, expose `μIso_hom`) and `pullbackObjFreeIso`
  (`asIso (pullbackObjUnitToUnit φ)` + `Sigma.mapIso`/`≪≫`) do. Concretely, for the project's
  cancellation goal "given `IsIso (A ≫ B ≫ C)` with `A`, `C` iso, deduce `IsIso B`":
  1. Build the two outer legs as named `Iso`s where their instances are clean:
     `iA := (Scheme.Modules.pullbackComp V.ι f).symm.app _` (a `NatIso` component — its
     `.hom`/`.inv` are iso UNCONDITIONALLY via `Iso.isIso_hom`/`Iso.isIso_inv`, no `Final`),
     and `iC := asIso (pullbackObjUnitToUnit V.ι.toRingCatSheafHom)` (built ONCE in a local
     `have`, freezing the `IsRightAdjoint`/`Final` implicits into the term).
  2. Reason with `iA.hom`, `iC.hom`, and `(Scheme.Modules.pullback V.ι).mapIso _` whose
     `IsIso` instances are the global, unconditional `CategoryTheory.Iso.isIso_hom` /
     `Functor.mapIso`-based ones — TC never re-enters `pullbackObjUnitToUnit`'s implicit
     args.
  3. Cancel with `CategoryTheory.IsIso.of_isIso_comp_left`
     (`[IsIso f] [IsIso (f ≫ g)] ⊢ IsIso g`, `Mathlib.CategoryTheory.Iso`) for the left leg
     then `IsIso.of_isIso_comp_right` for the right leg.
  The point: `asIso e` requires `[IsIso e]` only at the moment of construction (a single,
  clean local goal whose only relevant in-scope instance is the matching `(Opens.map _).Final`),
  and thereafter `(asIso e).hom`'s iso-ness comes from `Iso.isIso_hom`, which is a global
  instance with no `Final`/`IsRightAdjoint` implicit to clash with a stale local `haveI`.
- **Why the project's current `rw + infer_instance` fails**: `pullbackObjUnitToUnit φ`'s
  instance args include the `Prop`-valued `[(pushforward φ).IsRightAdjoint]` and the
  `[F.Final]` proof. A pre-established `haveI : IsIso (pbu g)` head-matches the goal's
  `IsIso (pbu ?)`, so Lean's resolution *picks the local hypothesis first*, then fails to
  unify the buried implicit instance terms (defeq but not syntactically equal at reducible
  transparency), and — because local instances are tried with priority and limited
  backtracking — resolution aborts rather than falling through to the global `OfFinal`
  instance. Bundling into `asIso`/`Iso` removes every such `IsIso (pbu ?)` synthesis goal
  downstream, so the clash can never arise.
- **Gap**: divergent-with-(small)-cost. The project should adopt the bundled-iso idiom; the
  cost of NOT doing so is the current hard block (the math is complete, the proof can't close).
- **Verdict**: ALIGN_WITH_MATHLIB (proof-tactic alignment, not a signature refactor).

### Decision: recurrence in Phase 2/3

- **Mathlib idiom**: same `asIso`/bundled-`Iso` discipline applies to every adjunction-mate
  comparison. `μIso` is the template for *all* of monoidal-functor comparison reasoning in
  Mathlib; the project's Phase-2 `pullbackObjTensorToTensor` is the direct analogue of
  `μ`/`μIso` for the `f^*` pseudofunctor.
- **Project's current path**: Phase 2 plans to prove `pullbackObjTensorToTensor` iso by the
  same finality chart-chase; Phase 3 composes `pullbackTensorIso⁻¹ ≫ f^*e ≫ pullbackUnitIso`.
- **Gap**: Phase 2 will hit the SAME wall *iff* it again routes through
  `rw [coherence]; infer_instance`. Phase 3 will NOT — it composes already-bundled `Iso`s
  (`pullbackTensorIso`, `pullbackUnitIso`), which is iso-level reasoning by construction.
- **Cost of divergence (if any)**: if the project treats Decision 2 as a one-off
  type-ascription hack rather than adopting the bundled-iso idiom as the *standard pattern*,
  Phase 2 re-pays the same debugging cost. Adopting it once (a `pullbackObjUnitToUnitIso`
  thin wrapper mirroring `μIso`, plus an `Iso`-level coherence mirroring `μIso_hom`) makes
  Phase 2 mechanical.
- **Verdict**: PROCEED — the *shape* (signature) is NOT the bottleneck, so there is nothing
  to refactor upstream; the recurrence is real but is fully absorbed by the Decision-2 idiom
  applied uniformly.

## Recommendation
The signature is Mathlib's and is canonical (it mirrors `Functor.Monoidal.μIso`); do not
attempt to refactor the comparison-map API. The block is a Lean typeclass-resolution accident
on `rw`-produced composites, triggered by stale local `haveI : IsIso (pbu …)` hypotheses whose
buried `IsRightAdjoint`/`Final` implicits fail to unify. Fix it the way Mathlib does in this
very file: introduce a thin bundled wrapper `pullbackObjUnitToUnitIso φ [F.Final] := asIso
(pullbackObjUnitToUnit φ)` (the analogue of `μIso`), build each leg of the coherence as a named
`Iso` at a clean site, and do all `IsIso` cancellation through `Iso.isIso_hom`/`Functor.mapIso`/
`IsIso.of_isIso_comp_left`/`of_isIso_comp_right` — never via `infer_instance` on a `pbu`
composite. Apply the same discipline to Phase 2's `pullbackObjTensorToTensor`; Phase 3 is
already iso-level and unaffected. This is a uniform proof idiom, not a one-time workaround and
not a signature change.
