# Analogy: assembling a mate/pseudofunctor coherence square over heavy carriers without forcing a carrier whnf

## Mode
cross-domain-inspiration

## Slug
fbc-glue-carrier-whnf

## Iteration
025

## Structural problem (abstracted)
Prove one equation of natural isomorphisms (equivalently of their `M`-components) between two
composite functors `C ⥤ D`, where both sides are pasted from per-leg comparison isos. Each leg is the
conjugate/iterated mate of a base coherence (`gammaPushforwardNatIso`). The per-leg facts and the
composition coherence are ALL closed; only the ASSEMBLY remains. The carriers (`tilde` =
sheafification, `pullback (Spec φ)`, `ModuleCat.extendScalars`) are kernel-heavy: any tactic that
forces a defeq/whnf ACROSS a carrier (`.obj (tilde M)`, the `extendScalars`/`ModuleCat` diamond, a
whisker seam matching `extendScalars`'s codomain against `tilde`'s source) triggers a kernel
`(deterministic) timeout @200000hb`. The term is well-typed (elaborates at 800000hb); it is merely
over the kernel budget, and `maxHeartbeats` is forbidden.

## Failed approaches (from directive)
- M-component iterated-mate transpose (`.app M`/`.mapIso` over `pullback.obj (tilde M)`): whnf-bombs.
- Functor-level natTrans `≪≫`-chain (`ring_square_glue_natTrans`): the STATEMENT bombs at
  `isoWhiskerRight (chartBaseChangeModuleReassocNat) (tilde.functor _)` (whisker-seam type-match
  whnf's the `extendScalars` diamond); the FOLD `congrArg (Iso.app · M)` bombs distributing `.app M`
  over the legs (re-crossing `.obj (tilde M)`).
- Partial mitigation: re-basing one leg's def so its `.app (tilde M)` is syntactic removed exactly 1
  of 4 crossings; did not fix the statement-seam bomb nor the other 3 legs.

## Key project evidence that makes the analogues viable
The project's own iter-021/024 kernel probes establish the decisive lever:
- A DIRECT `exact <closed-lemma> ψ φ ρ M` whose type mentions `.obj (tilde M)` is **kernel-light** —
  unification BINDS the heavy carrier to a metavariable rather than reducing it.
- `simp`/`rw`/`congr`/`rfl`/`congrArg(Iso.app ·)` over a `.obj (tilde M)` type are **kernel-heavy** —
  they emit `Eq.mpr`/motive-recheck obligations that force the kernel to whnf the carrier.
So the universal escape is: **do all reasoning over ABSTRACT carriers (where no whnf is possible),
then instantiate the concrete heavy goal by a single `exact`/`apply`.** Every analogue below is an
instance of exactly that discipline, and Mathlib uses it pervasively.

## Analogues found (ranked by porting cost)

### Analogue: `Mathlib.CategoryTheory.CatCommSq` (`CatCommSq`, `.hComp`/`.vComp`, `hComp_iso_hom_app`)
- **Domain**: 2-categorical / `Cat`-level square algebra (one shelf over the project).
- **Same structural problem there**: a commutative square of functors `T ⋙ R ≅ L ⋙ B` is **bundled
  as a typeclass** `CatCommSq T L R B` carrying the iso (`CatCommSq.iso : T.comp R ≅ L.comp B`,
  built by `CatCommSq.mk iso`). Pasting two squares is `CatCommSq.hComp`/`vComp`, which produces
  `CatCommSq (T₁.comp T₂) V₁ V₃ (B₁.comp B₂)` **structurally** — it composes the two bundled isos; no
  component is touched. The component formula `hComp_iso_hom_app`
  (`.iso (T₁⋙T₂) …).hom.app X = (.iso T₂ …).hom.app (T₁.obj X) ≫ B₂.map ((.iso T₁ …).hom.app X)`) is a
  proved `@[simp]` lemma — it crosses the carrier ONCE, generically over abstract `Tᵢ,Vᵢ,Bᵢ`, so when
  instantiated it binds the heavy carrier (light), it does not re-derive it.
- **Technique**: assemble the whole square by `hComp`/`vComp` of leg-squares (carrier-free), prove the
  two routings equal by **uniqueness of the bundled iso** (equate `.iso` of the two pastes via the
  mate cocycle below), and extract `.app M` only at the very end through `hComp_iso_hom_app` or a
  single `exact`. The bulk of the proof never names a component.
- **Mapping to project**: register each of the 4 `pullbackSpecTildeNatIso φ` dictionary legs and the 2
  comparison legs (`chartBaseChangeGeometricComparisonNat`, `chartBaseChangeModuleReassocNat`) as
  `CatCommSq` instances via `CatCommSq.mk`; build the LHS and RHS routings of the ring square by
  `CatCommSq.hComp`/`vComp`; the glue equation becomes equality of the two pastes' `.iso`. Fold to the
  `pullback_spec_tilde_iso_ring_square_mate_glue` goal by a final `exact` (carrier bound, not reduced).
- **Porting cost**: low–medium — wrap existing nat-isos in `CatCommSq.mk` (mechanical); the genuine
  content is the iso-equality of the two pastes, which is the mate cocycle (next analogue). Replaces
  the bombing `isoWhiskerLeft/Right` `≪≫`-chain with `.hComp`/`.vComp` whose composition is structural.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Mathlib.CategoryTheory.Adjunction.Mates` (`mateEquiv_vcomp`, `mateEquiv_hcomp`, `iterated_mateEquiv_conjugateEquiv`)
- **Domain**: Beck–Chevalley / adjoint-mate calculus (the project is already partly on it).
- **Same structural problem there**: `mateEquiv_vcomp adj₁ adj₂ adj₃ (α) (β)` etc. equate the mate of
  a pasted TwoSquare with the paste of the mates — **stated and proved entirely over abstract
  functors/adjunctions** (`G₁ G₂ H₁ H₂ L₁ L₂ L₃ R₁ R₂ R₃` are free; `TwoSquare`-valued). The Beck–
  Chevalley cocycle never instantiates a concrete heavy carrier in its proof.
- **Technique**: keep the four-leg telescope in the `TwoSquare`/`mateEquiv` algebra. The cocycle
  `mateEquiv_vcomp`/`hcomp` + `iterated_mateEquiv_conjugateEquiv` + the project's two closed leg-nat
  lemmas + `gammaPushforwardNatIso_comp` is the FULL content. Crucially, prove it as a GENERIC lemma
  whose statement contains NONE of `tilde`/`pullback`/`extendScalars` — only abstract adjunctions and
  the TwoSquares satisfying the unit-triangle/mate/comp hypotheses — then instantiate by one `exact`.
- **Mapping to project**: the project's `ring_square_glue_natTrans` failed *because its statement is
  concrete* (it whiskers over `tilde.functor`/`extendScalars`, which is what whnf-bombs). Re-cast it as
  `ring_square_cocycle (abstract adjs) (hUnitTri) (hGeomLeg) (hAlgLeg) (hComp) : <abstract ≪≫ eqn>`,
  proved by `conjugateEquiv_symm_comp` + `mateEquiv_vcomp`/`hcomp` + the hyps; then
  `pullback_spec_tilde_iso_ring_square_mate_glue` is `exact ring_square_cocycle … (pullback_spec_tilde_iso_inv_unit_triangle …) (ring_square_glue_geom_leg_nat …) (ring_square_glue_alg_leg_nat …) (gammaPushforwardNatIso_comp …)`. The `exact` binds `tilde M` etc. to metavars (iter-021: light).
- **Porting cost**: medium — `mateEquiv_vcomp`/`_hcomp` confirmed present and abstract; the project
  already has `pst_iterated_mate`, both leg-nat lemmas, and `gammaPushforwardNatIso_comp` closed. The
  new work is the abstract `ring_square_cocycle` statement + its TwoSquare-algebra proof. No carrier
  appears in it, so no whnf bomb is possible during its proof.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `Mathlib.CategoryTheory.Bicategory.Strict.Pseudofunctor` (`mapComp'₀₁₃`, `mapComp'₀₂₃`, `map₂_associator`)
- **Domain**: bicategory / pseudofunctor coherence.
- **Same structural problem there**: the depth-3 composition coherence of a pseudofunctor `F : B ⥤ C`
  is `mapComp'₀₁₃_hom`, which takes the intermediate composites as EXPLICIT 1-cells with equality
  hypotheses `h₀₂ : f₀₁ ≫ f₁₂ = f₀₂`, `h₁₃ : f₁₂ ≫ f₂₃ = f₁₃`, `hf : f₀₁ ≫ f₁₃ = f`, and proves the
  telescoped coherence in the ABSTRACT 2-cell algebra of `F`. The heavy target bicategory `C` (here
  `Cat`) carriers are bound by the statement, never whnf'd in the proof.
- **Technique**: model the dictionary `φ ↦ (tilde ⋙ pullback(Spec φ) ≅ extendScalars φ ⋙ tilde)` as an
  actual `Pseudofunctor` (objects = `CommRingCat`, 1-cells = ring maps, the comparison = `mapComp`),
  so the ring-square coherence IS `mapComp'₀₁₃ = mapComp'₀₂₃` instantiated at the ring square
  `inclR ≫ ρB = ρ ≫ inclR'`. The `mapComp'` `h…` equality hyps are exactly `chartBaseChange_ring_square`.
- **Mapping to project**: the highest-fidelity match (the pst dictionary already is morally a
  pseudofunctor — see `analogies/fbc-pst-pseudofunctor.md`). Packaging it as a `Pseudofunctor` makes
  the ring square a single Mathlib coherence lemma. But it requires building the pseudofunctor
  instance (`mapId`/`mapComp` + the pentagon/triangle fields) — substantial.
- **Porting cost**: medium–high — full `Pseudofunctor` packaging is multi-lemma; pays off only if the
  dictionary is reused for higher coherences. The `mapComp'`-with-equality-hyps PATTERN, however, can
  be borrowed cheaply inside analogue 2's `ring_square_cocycle` (pass the ring-square equality as a hyp).
- **Verdict**: PARTIAL_ANALOGUE.

### Analogue: `Mathlib.CategoryTheory.Limits.IsLimit.hom_ext` / `IsLimit.uniq` / `limit.hom_ext` (opacity discipline)
- **Domain**: limits/colimits — the canonical Mathlib heavy-opaque-carrier.
- **Same structural problem there**: `limit F` is `Classical.choice`-opaque and never unfolded;
  ALL coherence among limit morphisms is proved through the universal-property API (`limit.hom_ext`,
  `IsLimit.uniq`, `limit.lift_π`, `limit.w`). Two morphisms into a limit are equal iff equal after the
  cone legs — uniqueness, not carrier reduction.
- **Technique**: NEVER force a defeq through the heavy carrier; reason only through the bundled
  universal-property lemmas, which were each proved once generically.
- **Mapping to project**: the META-PRINCIPLE behind analogues 1–3. Treat `tilde M`, `pullback.obj`,
  `extendScalars` as opaque; reason only through the bundled `pullback_spec_tilde_iso` /
  `CatCommSq.iso` API and term-mode `exact`; never `simp`/`rw`/`congr` at a `.obj (tilde M)` type.
  This is precisely the project's iter-021 empirical finding, restated as Mathlib's standing discipline.
- **Porting cost**: n/a (principle, not a port).
- **Verdict**: PARTIAL_ANALOGUE (guiding principle).

## Discarded
- `Mathlib.Tactic.CategoryTheory.Coherence` / `monoidal_coherence` / `Monoidal.monoidal`: reflect
  coherence into a free monoidal structure (carrier-free) — right SPIRIT (discharge in a syntactic
  structure, never the concrete carrier) but the square has genuine mate content, not pure monoidal
  coherence; the tactic won't fire on it. Mentioned only as design confirmation, not a port.
- `CategoricalPullback`/`CatCommSqOver`/`mkNatIso` (`…Limits.Shapes.Pullback.Categorical.Basic`):
  builds nat-isos into a 2-pullback from component+coherence data — adjacent, but the glue isn't a map
  into a categorical pullback; `CatCommSq` (analogue 1) is the directly-applicable subset.

## Top suggestion
Take **analogue 2 (the abstract `mateEquiv`/conjugate cocycle as a GENERIC lemma + one `exact`)**,
optionally packaged with **analogue 1 (`CatCommSq.hComp`/`vComp`)** for the structural pasting. The
project's blocker is self-inflicted: `ring_square_glue_natTrans` is stated *concretely* (whiskers over
`tilde.functor`/`extendScalars`), so both its statement-seam and its `.app M` fold whnf the carrier.
Mathlib's `mateEquiv_vcomp`/`hcomp` (`Mathlib.CategoryTheory.Adjunction.Mates`) and `CatCommSq.hComp`
(`Mathlib.CategoryTheory.CatCommSq`) show the discipline: the cocycle is proved over ABSTRACT
adjunctions/squares, and the heavy instance enters by a single `exact`/`apply` that BINDS the carrier
to a metavariable (exactly the project's own iter-021 "direct `exact` is kernel-light" finding).
Concretely, in `AlgebraicJacobian/Cohomology/FlatBaseChange.lean`: state a new
`ring_square_cocycle {abstract cats/functors/adjunctions} (hUnitTri) (hGeomLeg) (hAlgLeg) (hComp) :
<the ≪≫/⊗-component equation over the abstract objects>`, prove it with
`conjugateEquiv_symm_comp` + `mateEquiv_vcomp`/`mateEquiv_hcomp` + the four hypotheses (NO `tilde`/
`pullback`/`extendScalars` anywhere — so no whnf can occur), then close
`pullback_spec_tilde_iso_ring_square_mate_glue` by the single line
`exact ring_square_cocycle … (pullback_spec_tilde_iso_inv_unit_triangle …)
(ring_square_glue_geom_leg_nat …) (ring_square_glue_alg_leg_nat …) (gammaPushforwardNatIso_comp …)`.
Delete `ring_square_glue_natTrans` (its concrete whisker statement is the over-budget artifact). First
files/lemmas to read: `Mathlib.CategoryTheory.Adjunction.Mates` (`mateEquiv_vcomp`/`_hcomp`,
`iterated_mateEquiv_conjugateEquiv`) and `Mathlib.CategoryTheory.CatCommSq` (`hComp`,
`hComp_iso_hom_app`).
