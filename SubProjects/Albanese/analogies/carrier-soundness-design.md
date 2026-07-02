# Analogy: Carrier shape for `Pic0Scheme / PicScheme / QuotScheme / picSharp / ...`

## Mode
api-alignment

## Slug
carrier-soundness-design

## Iteration
195

## Question

The project has 7+ load-bearing typed `:= sorry` definition carriers
(`PicScheme`, `Pic0Scheme`, `QuotScheme`, `picSharp`, `divFunctor`,
`abelMap`, `PicSharp / presheaf / etSheaf`, `addCommGroup`) whose
sorries propagate silently through typeclass synthesis. Which of the
three proposed carrier shapes — A (existential + `Classical.choose`),
B (opaque + axiom), or C (structure-of-data) — is the Mathlib idiom,
and which actually delivers kernel-only-axiom downstream consumers?

## Project artifact(s)

- `AlgebraicJacobian/Picard/FGAPicRepresentability.lean:132` — `picSharp := sorry`
  (forward-reference functor stub).
- `AlgebraicJacobian/Picard/FGAPicRepresentability.lean:147` — `divFunctor := sorry`
  (same).
- `AlgebraicJacobian/Picard/FGAPicRepresentability.lean:187` — `PicScheme := sorry`
  (carrier of the FGA representability theorem).
- `AlgebraicJacobian/Picard/FGAPicRepresentability.lean:226` — `abelMap := sorry`
  (natural transformation stub).
- `AlgebraicJacobian/Picard/FGAPicRepresentability.lean:324` — `representable := sorry`
  (the `RepresentableBy` witness).
- `AlgebraicJacobian/Picard/IdentityComponent.lean:738` — `Pic0Scheme := sorry`
  (the identity component, body intended to be
  `GroupScheme.IdentityComponent (PicScheme C)`).
- `AlgebraicJacobian/Picard/QuotScheme.lean:326` — `QuotScheme := sorry`
  (theorem-shaped: `∃ Q, Nonempty (RepresentableBy Q)`).
- `AlgebraicJacobian/Picard/RelPicFunctor.lean:205, 284, 323, 370, 429, 478` —
  `addCommGroup`, `PicSharp`, `PicSharp.functorial`, `presheaf`,
  `etSheaf`, `etSheafUnit` (functor / instance / sheaf assembly stubs).

## Decisions identified

### Decision: How to encode a carrier whose existence is proved by a
deep theorem (FGA / Kleiman §4) but whose body must be available NOW
for downstream typeclass synthesis

- **Mathlib idiom**: a Prop-valued typeclass packaging the existence
  claim, plus a `noncomputable def` extracting the carrier via
  `Classical.choose` of the typeclass instance. Concretely
  `CategoryTheory.Functor.IsRepresentable` + `Functor.reprX`:

  ```lean
  -- Mathlib.CategoryTheory.Yoneda
  class Functor.IsRepresentable (F : Cᵒᵖ ⥤ Type v) : Prop where
    has_representation : ∃ Y, Nonempty (F.RepresentableBy Y)

  noncomputable def Functor.reprX (F : Cᵒᵖ ⥤ Type v) [hF : F.IsRepresentable] : C :=
    hF.has_representation.choose
  ```

  Empirically `#print axioms Functor.reprX` reports
  `[propext, Classical.choice, Quot.sound]` — exactly the kernel-only
  axiom set the project targets.

  Why Mathlib chose this: separating *existence* (a `Prop` typeclass,
  proved separately and possibly conditionally) from *extraction*
  (`Classical.choose` is kernel-only) lets downstream lemmas take the
  typeclass as a parameter and remain kernel-clean. The Mathlib
  source for `Functor.RepresentableBy` keeps the data structure
  separate from the existence claim — that is the load-bearing split.

- **Project's current path**: `PicScheme C := sorry` (a typed
  carrier-level sorry) plus a separate `representable C : ... := sorry`
  theorem. Downstream lemmas reference `PicScheme C` directly, so
  every instance / theorem about `PicScheme C` transitively depends on
  `sorryAx` through the carrier.

- **Gap**: divergent-and-wrong (in the kernel-axiom-soundness sense).
  Mathlib never writes `def MyType := sorry` for a carrier; it always
  either (a) constructs concretely (`SplittingField`,
  `AlgebraicClosure`, `Localization`, `UniformSpace.Completion`,
  `presheafToSheaf`), or (b) parameterizes by an existence typeclass
  and extracts via `Classical.choose` (`Functor.reprX`,
  `Limits.getColimitCocone`).

- **Cost of divergence**: silent `sorryAx` propagation through every
  typeclass synthesis touching `PicScheme C` / `Pic0Scheme C` /
  `QuotScheme`. `lean_verify` on the protected `AlgebraicGeometry.Jacobian`
  declarations will fail the kernel-only-axiom check whenever Route A
  consumers compile, even if the consumer's own proof body is sorry-free
  at the source level. Bridge / fix-up lemmas: every downstream theorem
  becomes implicitly conditional on the FGA existence, but the
  conditionality is *invisible* in the type signature.

- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision: How to encode a carrier whose construction is a piece of
infrastructure NOT yet built (e.g. `picSharp`, `divFunctor`, `abelMap`,
`addCommGroup`, `PicSharp.functorial`, `PicSharp.presheaf`)

- **Mathlib idiom**: build concretely from the substrate. Mathlib has
  no precedent for `noncomputable def MyFunctor ... := sorry` as a
  forward-reference stub. `presheafToSheaf` (Mathlib's sheafification
  functor) is built explicitly from the plus-construction, even though
  the plus-construction itself takes several files. Concrete
  precedents:

  - `CategoryTheory.GrothendieckTopology.sheafify`
    (`Mathlib.CategoryTheory.Sites.ConcreteSheafification`): concrete
    multiequalizer construction.
  - `PresheafOfModules.sheafification`
    (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`):
    concrete.
  - `UniformSpace.Completion`
    (`Mathlib.Topology.UniformSpace.Completion`): concrete via Cauchy
    filters; the *abstract* shape lives separately as
    `AbstractCompletion` (a structure of data — Option C — for when
    consumers want to receive *any* completion, not the canonical one).

  When the substrate genuinely is not buildable yet, Mathlib's pattern
  is to parameterize: a function takes its dependency as an argument
  rather than referring to a global stub. The `[HasColimit F]` typeclass
  is the parametric form of "this colimit exists"; `colimit F` extracts
  via `Classical.choice`.

- **Project's current path**: each forward-reference carrier is a
  typed sorry at top-level, so downstream files import the stub
  directly. The stubs' bodies are intended to land in iter-177+ but
  meanwhile the sorries silently flow through every typeclass
  synthesis.

- **Gap**: divergent-with-cost. For `picSharp / divFunctor / abelMap`
  the *intended* body is "re-export of the sibling chapter's pinned
  decl", so once the sibling file lands these collapse to one-line
  re-exports — but the current stubs propagate `sorryAx` until that
  happens. For `addCommGroup / PicSharp.functorial / PicSharp.presheaf
  / etSheaf` the stubs are genuine pre-construction, and Mathlib's
  idiom is to introduce a `[HasFoo]` typeclass and parameterize.

- **Cost of divergence**: same kernel-axiom-soundness cost as
  Decision 1, plus an *additional* fragmentation cost: when the
  sibling chapter (`Picard/RelPicFunctor.lean`) ships its own
  `PicSharp`, the project ends up with two parallel `PicSharp`-shaped
  carriers (the local stub and the canonical one) until the merge.

- **Verdict**: ALIGN_WITH_MATHLIB. For forward-reference re-exports:
  delete the local stubs once the sibling file lands (already the
  iter-177+ plan). For pre-construction assemblies: introduce a
  `Prop`-valued existence typeclass + `Classical.choose` extraction,
  same as Decision 1.

### Decision: A vs B vs C — which of the three proposed carrier shapes
is the Mathlib idiom

- **Option A (Mathlib `Functor.IsRepresentable` form)**: Prop-valued
  existence typeclass, carrier extracted via `Classical.choose`.
  Axioms: `[propext, Classical.choice, Quot.sound]` (kernel-only) **on
  any consumer that takes the typeclass as a parameter without
  supplying its body**. The instance-construction site is the
  exclusive location where `sorryAx` can enter. — This is the Mathlib
  idiom. **VERDICT: ALIGN_WITH_MATHLIB.**

- **Option B (`opaque T : Type` + `axiom T_isAbelianVariety`)**:
  empirical test (`opaque myType : Type := Unit` and
  `opaque myTypeNoBody : Type`) confirms `opaque` itself adds no new
  axioms. **However**, the property bundle `axiom T_isAbelianVariety :
  IsAbelianVariety (Pic0Scheme C)` introduces a user-declared `axiom`
  token, which IS a kernel axiom outside
  `{propext, Classical.choice, Quot.sound}`. This DIRECTLY violates the
  end-state contract. Even the body-less form
  `opaque myAbelianVariety : { S : Type // IsAbelianVariety S }`
  needs `Inhabited`/`Nonempty` of the subtype, and providing that
  Nonempty *is* the existence proof — equivalent to Option A but
  routed via opaque instead of `Classical.choose`. — **VERDICT:
  DIVERGE_INTENTIONALLY (REJECT). Option B can never deliver
  kernel-only axioms unless the `axiom` token is replaced by a typed
  hypothesis, at which point it collapses to Option A.**

- **Option C (structure-of-data, e.g. `AbstractCompletion`)**:
  Mathlib precedent is `AbstractCompletion α` (carries `space : Type
  v`, `coe : α → space`, `uniformStruct`, `CompleteSpace`, `T0Space`,
  `IsUniformInducing`, `DenseRange`). Used as the **destination of a
  universal property**: a function takes `cpl : AbstractCompletion α`
  as an argument and operates on `cpl.space`. The canonical
  `UniformSpace.Completion α` is then a *concrete* construction
  wrapped as `cPkg : AbstractCompletion α`. This is the right pattern
  when consumers want to *receive* the carrier as data (e.g. the
  divisor-map Albanese UP wants any abelian variety satisfying the UP,
  not specifically `Pic0Scheme C`). For `Pic0Scheme` the consumer
  expectation is a canonical scheme, not "any abelian variety
  satisfying the UP", so Option C is structurally available but
  heavier than needed. — **VERDICT: DIVERGE_INTENTIONALLY (RESERVE).
  Keep C in reserve for places where the Albanese UP genuinely
  benefits from a bundle (e.g. `AbelianVarietyOfCurve C` as a single
  Σ' carrying `J + isAbelianVariety + isAlbaneseFor`), but Option A is
  the right default for the seven listed carriers.**

### Decision: Does Option A *eliminate* silent `sorryAx` propagation,
or merely *isolate* it?

- **Mathlib idiom**: isolates, but does not eliminate. Empirical test
  with a sorry-d existence:

  ```lean
  theorem fake_exists : ∃ x : Nat, x > 5 := sorry
  noncomputable def via_choose_sorry : Nat := fake_exists.choose
  -- #print axioms via_choose_sorry → [sorryAx, Classical.choice]
  ```

  So `via_choose_sorry` still depends on `sorryAx`. The benefit is
  that any consumer of `via_choose_sorry` that takes a *parameter* of
  the form "Nat with property" and uses it without computing
  `via_choose_sorry` is kernel-clean — the sorry stays at the instance
  site.

  Concretely, for the project:

  ```lean
  class HasPic0Scheme (C : ...) : Prop where
    exists_repr : ∃ J : ..., IsProper J.hom ∧ Smooth J.hom ∧ ...

  noncomputable def Pic0Scheme (C : ...) [hC : HasPic0Scheme C] :
      Over (Spec (.of k)) := hC.exists_repr.choose

  -- An UNRESOLVED instance, the only sorry site:
  instance HasPic0Scheme_of_curve (C : ...) [SmoothOfRelativeDimension 1 C.hom]
      [IsProper C.hom] [GeometricallyIntegral C.hom] : HasPic0Scheme C := sorry

  -- A downstream consumer, KERNEL-CLEAN if instance is not in scope:
  theorem Pic0_finrank_eq_genus (C : ...) [HasPic0Scheme C] :
      topologicalKrullDim (Pic0Scheme C).left = (genus C : WithBot ℕ∞) := ...
  ```

  `#print axioms Pic0_finrank_eq_genus` returns kernel-only as long as
  the instance `HasPic0Scheme_of_curve` is not used in the proof. The
  protected declaration `AlgebraicGeometry.Jacobian` would then carry
  the `[HasPic0Scheme C]` hypothesis explicitly — making the gap
  visible at the type level, not hidden in typeclass synthesis.

- **Project's current path**: silent. `Pic0Scheme C := sorry` makes
  every downstream instance / theorem depend on `sorryAx` without any
  type-level signal.

- **Gap**: divergent-and-wrong. The project's claim "downstream lemmas
  consume `[AddCommGroup Pic0Scheme]` and silently inherit sorryAx"
  is exactly the failure mode the Mathlib idiom is designed to
  prevent.

- **Verdict**: ALIGN_WITH_MATHLIB. Option A delivers what the project
  needs — the sorry stays at one named, type-level-visible boundary
  rather than propagating invisibly.

## Recommendation

**Refactor under Option A (Mathlib `Functor.IsRepresentable` pattern),
NOT Option B (kernel-axiom-unsafe) or Option C (heavier than needed
for these carriers).** The recommended target shape:

1. Introduce a `Prop`-valued typeclass for each existence claim. The
   exact Mathlib decl to emulate is
   `CategoryTheory.Functor.IsRepresentable` (`Mathlib.CategoryTheory.Yoneda`).

2. Define the carrier via `Classical.choose` of the typeclass
   instance, exactly like `Functor.reprX`. `noncomputable` is required
   (the project already uses `noncomputable def` for all the listed
   carriers, so this is a no-op change for the keyword).

3. Add typeclass arguments `[HasPic0Scheme C]` etc. to every
   downstream consumer that previously referenced `Pic0Scheme C`. The
   protected declarations `AlgebraicGeometry.Jacobian` / `Jacobian.
   nonempty_jacobianWitness` would then explicitly carry these typeclass
   args (the existence gap becomes type-level visible).

4. Put the `sorry` in the *instance constructor*:

   ```lean
   instance (C) [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
       [GeometricallyIntegral C.hom] : HasPic0Scheme C := ⟨sorry⟩
   ```

   This is the SINGLE site where `sorryAx` enters. `lean_verify` on a
   downstream theorem will show `sorryAx` only if it actually USES
   this instance (i.e. constructs `Pic0Scheme C`). Theorems that
   merely *quantify* over `HasPic0Scheme C` are kernel-clean.

5. For `picSharp / divFunctor / abelMap` (forward-reference stubs):
   collapse to one-line re-exports when the sibling file lands (the
   iter-177+ plan already accommodates this). No refactor needed
   beyond the import wire-up.

6. For `addCommGroup / PicSharp.functorial / PicSharp.presheaf /
   etSheaf / etSheafUnit` (pre-construction assemblies): same
   treatment as (1)–(4) — `HasPicSharp` typeclass, extraction via
   `Classical.choose`, sorry isolated to the instance.

**Effort estimate**:

- FGAPicRepresentability refactor (5 forward-ref defs + representable
  theorem): 2-3 iters, ~200-300 LOC affected.
- Pic0AbelianVariety + IdentityComponent (Pic0Scheme): 1-2 iters,
  ~100-150 LOC.
- RelPicFunctor (PicSharp/presheaf/etSheaf/addCommGroup): 2-3 iters,
  ~200-300 LOC.
- Cross-file downstream-consumer typeclass-arg wiring:
  1-2 iters, ~100-200 LOC.
- **Total: 6-10 iters, ~600-950 LOC.** The planner's 2-4 iter
  estimate is light; the cross-file blast radius (~5-6 files +
  consumer code) bumps it.

**Iter-slot recommendation**: the verdict is concrete and actionable
THIS iter (option C of the directive's pull-forward options would be
the right call). Suggest:

- Pull forward to iter-196 the FGAPicRepresentability slice (the
  cleanest Mathlib alignment, lowest risk, ~2-3 iters).
- Iter-197–199: Pic0AbelianVariety + IdentityComponent +
  RelPicFunctor slices.
- Keep iter-200 mathlib-analogist sweep separately scheduled (the
  sweep catches fresh Mathlib landings, distinct concern from this
  refactor).

**Reversal trigger**: if iter-196 hits a typeclass-synthesis cycle
(e.g. `[HasPicSharp C]` is needed to state `[HasPic0Scheme C]`, but
the project's typeclass resolver can't break the cycle), fall back to
Option C bundles (`AbelianVarietyOfCurve C` Σ'-carrier) for the
specific cycle-breaking carrier.
