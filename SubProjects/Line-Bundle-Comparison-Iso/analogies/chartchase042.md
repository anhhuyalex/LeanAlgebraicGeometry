# Analogy: naturality-under-composition of a comparison iso built from pseudofunctor structure cells

## Mode
cross-domain-inspiration

## Slug
chartchase042

## Iteration
042

## Structural problem (abstracted)
For a pseudofunctor `f ↦ P_f` (here `P_f = Scheme.Modules.pullback f`, with structure cells
`pullbackComp`, `restrictFunctorIsoPullback`) where each `P_f` carries a (strong) monoidal
structure, the comparison `c_f : P_f(M⊗N) ≅ P_f M ⊗ P_f N` is the tensorator `μ`. We need that
`f ↦ c_f` is **compatible with composition of the base 1-morphism** `j ≫ U.ι = V.ι`: the four
blueprint squares S2/S3/S4a/S4b. Equivalently, the structure iso `pullbackComp` (resp.
`restrictFunctorComp`) is a **monoidal natural isomorphism** between the two strong-monoidal
functors `P_{j∘U.ι}` and `P_{U.ι} ⋙ P_j`. The same shape recurs for the dual / internal-Hom and
the unit.

## Failed approaches (from directive)
- `restrictFunctorComp.hom.naturality φ`: naturality in a MORPHISM φ of X-modules, not in the immersion.
- B1/B2 routing through pullback-composition laws: B1 (`tensorObj_restrict_iso = restrictFunctorIsoPullback ≫ asIso(pullbackTensorMap) ≫ reindex`) becomes a >100-LOC bespoke mate calculus relating two differently-shaped composites.
- `apply Iso.ext; simp [tensorObj_restrict_iso]` on S2 → full 4-leg chase explosion.

## Analogues found

### Analogue: `CategoryTheory.Functor.Monoidal.natTransIsMonoidal_of_transport` + `NatTrans.IsMonoidal` (`Mathlib/CategoryTheory/Monoidal/NaturalTransformation.lean:233`, class at `:48`)
- **Domain**: category theory / monoidal coherence (same shelf).
- **Same structural problem there**: given `[F.Monoidal]` and an iso `e : F ≅ G`, `e.hom` is a
  monoidal natural transformation — its `tensor` field is exactly
  `μ F X Y ≫ e.app (X⊗Y) = (e.app X ⊗ₘ e.app Y) ≫ μ G X Y`, i.e. the square S2 verbatim.
  Proof is `refine ⟨rfl, fun X Y ↦ ?_⟩; simp [transport_μ, tensorHom_comp_tensorHom_assoc]` — ONE line.
- **Technique**: don't chase the 4 legs. Register a `Functor.Monoidal` instance on `pullback f`
  (open immersion) with `μIso = asIso (pullbackTensorMap f)` (project already proves IsIso at
  `TensorObjSubstrate.lean:1271`); transport along `restrictFunctorIsoPullback f`
  (`= leftAdjointUniq`, `Sheaf.lean:371`) via `Functor.Monoidal.transport` (`Monoidal/Functor.lean`)
  to get `(restrictFunctor f).Monoidal` with `μIso = tensorObj_restrict_iso f`. Then S2 is the
  `.tensor` field of `NatTrans.IsMonoidal (restrictFunctorComp j U.ι).hom`, supplied by
  `natTransIsMonoidal_of_transport`.
- **Mapping to project**: `F := restrict V.ι`, `G := restrict U.ι ⋙ restrict j`,
  `e := restrictFunctorComp j U.ι` (Mathlib, `Sheaf.lean:392`), both `Monoidal`; the
  `tensor`/`unit` fields ARE S2 / S4b. `restrictCompReindex` is `e` up to `restrictFunctorCongr`.
- **Porting cost**: medium. One-time: register `(pullback f).Monoidal` (μ data exists) and lift to
  `(restrictFunctor f).Monoidal`; then B1, S2, S4b all fall out of instances. Replaces 4×>100-LOC.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `CategoryTheory.Functor.Monoidal.transport_μ` (`Mathlib/CategoryTheory/Monoidal/Functor.lean`)
- **Domain**: category theory / monoidal.
- **Same problem**: `μ G X Y = (i.inv.app X ⊗ₘ i.inv.app Y) ≫ μ F X Y ≫ i.hom.app (X⊗Y)`.
- **Technique**: this is EXACTLY the project's hand-written B1 shape
  `restrictFunctorIsoPullback ≫ asIso(pullbackTensorMap) ≫ tensorObjIsoOfIso(inv)(inv)`
  (`TensorObjInverse.lean:238`). Once `tensorObj_restrict_iso f` is *defined as* / proven `= μIso`
  of the transported instance, B1 becomes the simp-lemma `transport_μ` — the 100-LOC mate calculus
  evaporates (it was re-deriving a Mathlib `@[simp]` equation by hand).
- **Mapping**: `F := pullback f`, `G := restrict f`, `i := (restrictFunctorIsoPullback f).symm`.
- **Porting cost**: low (rides on Analogue 1's instance).
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `CategoryTheory.Functor.LaxMonoidal.comp_μ` / `comp_ε` (`Mathlib/CategoryTheory/Monoidal/Functor.lean`)
- **Domain**: category theory / monoidal.
- **Same problem**: `μ (F⋙G) X Y = μ G (F.obj X) (F.obj Y) ≫ G.map (μ F X Y)` — μ of a composite
  functor as the canonical two-step whisker.
- **Technique**: rewrites the RHS composite `restrict U.ι ⋙ restrict j` tensorator into the
  two-step form, so the S2 RHS is `comp_μ` not a 4-leg chase. Used jointly with Analogue 1.
- **Mapping**: `F := restrict U.ι`, `G := restrict j`.
- **Porting cost**: low.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: mate-compositionality — `mateEquiv_vcomp`, `conjugateEquiv_mateEquiv_vcomp`, `Adjunction.leftAdjointUniq_trans` (`Mathlib/CategoryTheory/Adjunction/Mates.lean`, `.../Unique.lean`)
- **Domain**: category theory / adjunction mates.
- **Same problem (= B2)**: the comparison of left adjoints (`leftAdjointUniq`) is compatible with
  composition of adjunctions. `leftAdjointUniq_trans`:
  `(adj1.leftAdjointUniq adj2).hom ≫ (adj2.leftAdjointUniq adj3).hom = (adj1.leftAdjointUniq adj3).hom`.
  `mateEquiv_vcomp`: mate of a horizontal composite = vertical composite of mates.
- **Technique**: B2 (`restrictFunctorIsoPullback_comp_compat`) is `restrictFunctorIsoPullback =
  leftAdjointUniq`; its pseudonaturality is `leftAdjointUniq_trans` threaded against `pullbackComp`
  /`restrictFunctorComp`, replacing the deferred ~40-60 LOC unit chase with a closed-form
  transitivity + `mateEquiv_vcomp`.
- **Mapping**: `adj1 := restrictAdjunction V.ι`, `adj2 := pullbackPushforwardAdjunction V.ι` (etc.);
  the mate of the `pullbackComp` 2-square equals the vcomp of the per-leg mates.
- **Porting cost**: medium (still some eqToHom/`pullbackCongr hjι` threading from `hjι`).
- **Verdict**: PARTIAL_ANALOGUE.

### Analogue: `CategoryTheory.Adjunction.IsMonoidal` + `isMonoidal_comp` (`Mathlib/CategoryTheory/Monoidal/Functor.lean`)
- **Domain**: category theory / monoidal adjunctions (the deep abstraction).
- **Same problem**: the 2-functor `f ↦ (pullback f ⊣ pushforward f)` lands in *monoidal*
  adjunctions, and monoidal adjunctions compose (`isMonoidal_comp`). This encodes ALL four squares
  + dual/internal-Hom (S3/S4a via closed-monoidal mates) at one stroke.
- **Technique**: `instIsMonoidal` makes a left adjoint of a lax-monoidal right adjoint
  oplax-monoidal; `isMonoidal_comp` composes. The project is ALREADY inside this doctrine at the
  PRESHEAF level (`presheafPullbackOplaxMonoidal` = `leftAdjointOplaxMonoidal`,
  `TensorObjSubstrate.lean:1115`; `Functor.OplaxMonoidal.comp`/`pullbackComp` refs at `:2275`,`:2331`).
  The gap is lifting to SHEAF level + exposing `μIso = tensorObj_restrict_iso`.
- **Mapping**: register `(SheafOfModules.pullback f).OplaxMonoidal`/`.Monoidal` and
  `(restrictAdjunction f).IsMonoidal`; the squares become `isMonoidal_comp` consequences.
- **Porting cost**: high (build sheaf-level OplaxMonoidal pushforward + adj.IsMonoidal instances)
  but it is the canonical idiom and also discharges S3/S4a.
- **Verdict**: ANALOGUE_FOUND (strategic).

## Top suggestion
Try Analogue 1 first: read `Mathlib/CategoryTheory/Monoidal/NaturalTransformation.lean:48,233`
(`NatTrans.IsMonoidal` class + `natTransIsMonoidal_of_transport`) and `Monoidal/Functor.lean`
(`Functor.Monoidal.transport`, `transport_μ`, `comp_μ`). Port by registering a `Functor.Monoidal`
instance on `Scheme.Modules.pullback f` (open immersion; μ = `asIso (pullbackTensorMap f)`, IsIso
already at `TensorObjSubstrate.lean:1271`) and transporting it onto `restrictFunctor f` along the
Mathlib `restrictFunctorIsoPullback f`. Then `tensorObj_restrict_iso_eq_pullbackTensorMap` (B1,
`TensorObjInverse.lean:238`) is `transport_μ`, and `tensorObj_restrict_iso_restrict_compat` (S2,
`:254`) and `tensorObj_unit_iso_restrict_compat` (S4b) are the `.tensor`/`.unit` fields of
`NatTrans.IsMonoidal (restrictFunctorComp j U.ι).hom`, obtained from
`natTransIsMonoidal_of_transport` (one line each), with `comp_μ` expanding the composite leg. First
file to touch: `AlgebraicJacobian/Picard/TensorObjInverse.lean`. This dissolves the exact B1
bottleneck (it is a hand re-derivation of the `@[simp]` `transport_μ`) rather than moving it.
