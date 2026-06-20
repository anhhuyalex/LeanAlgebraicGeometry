# Analogy: installing `GrpObj Gm` via `GrpObj.ofRepresentableBy`

## Mode
api-alignment

## Slug
gm-grpobj-representable

## Iteration
179

## Question

What is the canonical Mathlib idiom for installing the `GrpObj` instance on
`𝔾_m = Spec (k̄[t, t⁻¹])` via the representable-by-units functor
construction? The project's
`AlgebraicJacobian/Genus0BaseObjects/Points.lean:251` has had this as
bare `sorry` for 11+ iterations (iter-167 escalation watch). It is
load-bearing for `gm_smooth` (L255), the Route C base case
`morphism_P1_to_grpScheme_const_aux` chain, and `iotaGm_isDominant`
(`AbelianVarietyRigidity.lean:86`).

## Project artifact(s)

- `AlgebraicJacobian/Genus0BaseObjects/Points.lean:240-251` — declaration
  + docstring; body bare `sorry`.
- `AlgebraicJacobian/Genus0BaseObjects/Points.lean:253-258` — downstream
  `gm_smooth` instance consuming `gm_grpObj`.
- `analogies/gm-grpobj-and-friends.md` (iter-167) — prior analogy with
  the same recipe sketched but not landed.

## Mathlib state (verified iter-179)

- **`GrpObj.ofRepresentableBy`** lives at
  `Mathlib/CategoryTheory/Monoidal/Cartesian/Grp_.lean:35`.
  Signature (verbatim):

  ```lean
  def GrpObj.ofRepresentableBy
      (F : Cᵒᵖ ⥤ GrpCat.{w}) (α : (F ⋙ forget _).RepresentableBy X) :
      GrpObj X where
    __ := MonObj.ofRepresentableBy X (F ⋙ forget₂ GrpCat MonCat) α
    inv := α.homEquiv'.symm (α.homEquiv (𝟙 _))⁻¹
    left_inv := …  -- discharged by Mathlib
    right_inv := … -- discharged by Mathlib
  ```

  All five group-object axioms are handled inside `ofRepresentableBy` (the
  monoid axioms come from `MonObj.ofRepresentableBy` at
  `Cartesian/Mon_.lean:157`; only `left_inv`/`right_inv` need to be added
  in `ofRepresentableBy` itself, and those are also discharged by the
  Mathlib body). The caller's only obligation is to supply `F` and `α`.

- **`Functor.RepresentableBy`** lives at `Mathlib/CategoryTheory/Yoneda.lean:285`:

  ```lean
  structure RepresentableBy (F : Cᵒᵖ ⥤ Type v) (Y : C) where
    homEquiv {X : C} : (X ⟶ Y) ≃ F.obj (op X)
    homEquiv_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
      homEquiv (f ≫ g) = F.map f.op (homEquiv g) := by cat_disch
  ```

  So the project must build a per-`T` equiv `(T ⟶ Gm) ≃ Γ(T.left, ⊤)ˣ`
  plus naturality, where `T` ranges over `(Over (Spec (.of kbar)))ᵒᵖ`.

- **No concrete-scheme uses of `GrpObj.ofRepresentableBy` in Mathlib.**
  A grep across `Mathlib/AlgebraicGeometry/` finds zero callers. The
  uses in Mathlib are abstract (the round-trip lemma
  `ofRepresentableBy_yonedaGrpObjRepresentableBy` at
  `Cartesian/Grp_.lean:90` and three internal hooks). No
  `Mathlib.AlgebraicGeometry.Group.Gm`, no `GroupScheme.Gm` namespace.

- **`Mathlib.AlgebraicGeometry.AffineSpace.homOverEquiv`** (the
  affine-space analogue at `AffineSpace.lean:155`):

  ```lean
  def homOverEquiv : { f : X ⟶ 𝔸(n; S) // f.IsOver S } ≃ (n → Γ(X, ⊤))
  ```

  This is the closed form of the bijection chain for `Ga`. For `Gm`,
  Mathlib does NOT ship a parallel `Spec(Localization.Away t).homOverEquiv`,
  so the project must compose the chain by hand from primitives
  (`ΓSpec.adjunction.homEquiv` + `IsLocalization.Away.lift`).

- **`ΓSpec.adjunction.homEquiv`** at `GammaSpecAdjunction.lean:494/500`:
  `(X ⟶ Spec R) ≃ (R ⟶ Γ(X, ⊤))` (the global-sections / Spec adjunction)
  with the over-`Spec k̄` condition automatic from the Spec-of-algebra-map
  structure.

- **`IsLocalization.Away.lift`** at `Mathlib/RingTheory/Localization/Away/Basic.lean`:

  ```lean
  lemma IsLocalization.Away.lift (x : R) [IsLocalization.Away x S] {g : R →+* P}
      (hg : IsUnit (g x)) : S →+* P
  ```

  with companion `IsLocalization.Away.algebraMap_isUnit` (algebraMap x is
  a unit in S) and `IsLocalization.Away.lift_comp` (lift composed with
  algebraMap equals g). These three lemmas together give the bijection
  `(k̄[t,t⁻¹] →ₐ[k̄] R) ≃ {u : R // IsUnit u}` (forward: send `φ` to
  `φ(t)` which is forced to be a unit by
  `IsLocalization.Away.algebraMap_isUnit`; backward: apply
  `IsLocalization.Away.lift` to the polynomial ring map `t ↦ u`).

## Decisions identified

### Decision 1: Is `GrpObj.ofRepresentableBy` the right Mathlib idiom?

- **Mathlib idiom**: YES. `GrpObj.ofRepresentableBy` is THE canonical
  Yoneda installer for `GrpObj` on a representable presheaf of groups.
  Cite: `Mathlib/CategoryTheory/Monoidal/Cartesian/Grp_.lean:35`. Why
  Mathlib chose it: this is the categorical formulation of "to give a
  group structure on an object `X`, exhibit `Hom(-, X)` as a presheaf of
  groups". It is strictly more powerful than `GrpObj.mk` (the explicit
  μ/η/ι path) because it automates all five axioms via the Equiv's
  injectivity (see the inv-axiom proofs at L39-L54). The downstream
  Mathlib API (`Hom.group`, `yonedaGrp`, the FullyFaithful embedding)
  composes naturally with `ofRepresentableBy`-installed instances.

- **Project's current path**: planned to use `ofRepresentableBy`; body is
  `sorry`. The docstring at L240-L251 names the idiom explicitly. Aligned.

- **Gap**: identical. The project's planned path IS the Mathlib idiom.

- **Verdict**: **PROCEED with `GrpObj.ofRepresentableBy`**. No parallel
  API risk.

### Decision 2: Is there a Mathlib analogue for `𝔾_m`'s `GrpObj` instance already?

- **Mathlib state**: NO. Searched all of `Mathlib/AlgebraicGeometry/` for
  any instance of `GrpObj` on a `Spec`-of-units construction, on
  `Spec (Localization.Away _)`, on `Spec (FractionRing _)`, or in any
  `Mathlib.AlgebraicGeometry.Group/*.lean` file. The Group folder ships
  only `Smooth.lean` (smoothness from `GrpObj`) and `Abelian.lean`
  (commutativity from properness + group-object). Both CONSUME an
  arbitrary `GrpObj`; neither produces one for a concrete scheme.

- **Project's current path**: build the instance from scratch using
  `ofRepresentableBy` + the 3-step bijection chain. NOT a parallel API —
  this is a genuine Mathlib gap.

- **Gap**: NEEDS_MATHLIB_GAP_FILL. The project is FIRST in Mathlib
  ecosystem to install a concrete-scheme `GrpObj` via `ofRepresentableBy`.
  Future upstream candidate: `Mathlib.AlgebraicGeometry.Group.Gm` (single
  file, ~100 LOC).

- **Verdict**: **PROCEED** with the from-scratch build. Reusable as an
  upstream contribution post-formalization.

### Decision 3: What's the closed body's shape?

The 8-step recipe (each line a single Mathlib idiom):

1. Open `letI := Spec (.of kbar)`, then build `F : (Over (Spec (.of kbar)))ᵒᵖ ⥤ GrpCat.{u}`
   with `obj T := GrpCat.of Γ(T.unop.left, ⊤)ˣ`. Use `Scheme.Hom.appTop` for
   the map: a morphism `φ : T → T'` in `Over (Spec k̄)` gives
   `(φ.unop.left).appTop : Γ(T'.unop.left, ⊤) ⟶ Γ(T.unop.left, ⊤)`, which
   restricts to a group hom on units via `Units.map`.

2. Build the per-`T` equiv `homEquiv : (T ⟶ Gm kbar) ≃ Γ(T.unop.left, ⊤)ˣ`
   as a 3-step composition of equivs:

   - **Step 2a** (over-category unfold): `(T ⟶ Gm)` in `Over (Spec k̄)` ≃
     `{f : T.unop.left ⟶ Spec(k̄[t,t⁻¹]) // f ≫ struct = T.unop.hom}`.
     Use `Over.homMk` / `Over.Hom.left` pair to assemble/destructure.

   - **Step 2b** (Spec adjunction): the underlying scheme morphism
     `f : T.unop.left ⟶ Spec(k̄[t,t⁻¹])` corresponds via
     `ΓSpec.adjunction.homEquiv` to a ring map `k̄[t,t⁻¹] →+* Γ(T.unop.left, ⊤)`,
     and the "over `Spec k̄`" commutativity turns it into a `k̄`-algebra map
     (the structure map's image of `algebraMap k̄ (k̄[t,t⁻¹])` is forced).

   - **Step 2c** (universal property of the Away localisation): a
     `k̄`-algebra map `k̄[t,t⁻¹] →ₐ[k̄] Γ(T.unop.left, ⊤)` is the choice of
     a unit. Forward: take the image of `t = X ()` (it is a unit by
     `IsLocalization.Away.algebraMap_isUnit`'s functorial transfer:
     algebraMap of t in k̄[t,t⁻¹] is a unit, hence so is its image). Backward:
     given a unit `u : Γ(T.unop.left, ⊤)ˣ`, build the polynomial ring map
     `MvPolynomial.aeval (Unit.elim u) : MvPolynomial Unit k̄ →ₐ[k̄] Γ(T.unop.left, ⊤)`,
     then factor through `Localization.Away (X ()) = k̄[t,t⁻¹]` via
     `IsLocalization.Away.lift`. `MvPolynomial.aeval_unique` discharges
     well-definedness.

3. Build `homEquiv_comp` (naturality): the three component equivs are
   each natural (the over-cat unfold is structurally natural; the Spec
   adjunction is the unit/counit of an adjunction; the Localization.Away
   step is natural by `IsLocalization.Away.lift_comp`). Discharge
   via `Equiv.trans` composition; `cat_disch` should close most of it.

4. Apply `GrpObj.ofRepresentableBy (Gm kbar) F ⟨homEquiv, homEquiv_comp⟩`.

### Decision 4: Cross-domain comparison

- **Searched in `Mathlib/Algebra/Category/Grp/`**: no `Spec`-based
  `GrpObj` constructions.
- **Searched in `Mathlib/CategoryTheory/Monoidal/`**: only the abstract
  `ofRepresentableBy` idioms (Grp_, CommGrp_, Mon_, CommMon_); no concrete
  builders.
- **Searched in `Mathlib/AlgebraicGeometry/`**: no concrete `MonObj`
  or `GrpObj` on `Spec (Localization.Away _)` or
  `Spec (FractionRing _)`.

Conclusion: the project's path is the FIRST concrete-scheme instance
of `GrpObj.ofRepresentableBy` in the Mathlib ecosystem. No prior art to
mimic; the recipe in Decision 3 is the canonical synthesis from
Mathlib's primitives.

## LOC estimate

- Functor `F : (Over (Spec (.of kbar)))ᵒᵖ ⥤ GrpCat.{u}` definition: **20-30 LOC**.
- The per-`T` `homEquiv` (3-step composition): **40-60 LOC**.
- The `homEquiv_comp` naturality field: **15-25 LOC** (mostly `cat_disch`
  + one or two explicit rewrites).
- Total: **75-115 LOC** for a clean closed body.

## Recommendation

Use `GrpObj.ofRepresentableBy` with the 3-step bijection chain in
Decision 3. The skeleton:

```lean
instance gm_grpObj (kbar : Type u) [Field kbar] : GrpObj (Gm kbar) := by
  refine GrpObj.ofRepresentableBy (Gm kbar)
    { obj := fun T => GrpCat.of (Γ(T.unop.left, ⊤))ˣ
      map := fun {T T'} φ =>
        GrpCat.ofHom (Units.map (φ.unop.left.appTop).hom.toMonoidHom)
      map_id := by intro T; ext u; simp [Scheme.Hom.id_appTop]
      map_comp := by intros T T' T'' φ ψ; ext u; simp [Scheme.Hom.comp_appTop] }
    ?_
  refine
    { homEquiv := fun {T} => ?_
      homEquiv_comp := ?_ }
  · -- Step 2a-2c composed:
    -- (T ⟶ Gm) in Over (Spec k̄)
    --   ≃ {f : T.unop.left ⟶ Spec(k̄[t,t⁻¹]) // IsOver Spec k̄}   -- over-cat unfold
    --   ≃ {φ : k̄[t,t⁻¹] →ₐ[k̄] Γ(T.unop.left, ⊤)}                 -- ΓSpec.adjunction
    --   ≃ {u : Γ(T.unop.left, ⊤) // IsUnit u}                     -- IsLocalization.Away.lift
    --   = Γ(T.unop.left, ⊤)ˣ
    sorry  -- the 3-step Equiv composition (recipe per Decision 3, 40-60 LOC)
  · sorry  -- naturality via cat_disch + Spec.map / Units.map naturality
```

The dispatching prover should split the `homEquiv` body into three
named helper lemmas (one per step in Decision 3), each ~15-20 LOC,
so the assembly is just `Equiv.trans ∘ Equiv.trans`. The `homEquiv_comp`
field reduces to checking that pre-composing `T ⟶ Gm` with
`φ : T' → T` produces the comap of the unit on the `Γ`-side; this is
`Scheme.Hom.appTop` naturality + `Units.map` functoriality.

**Bonus parallel — `ga_grpObj`:** the same `ofRepresentableBy` idiom with
`AffineSpace.homOverEquiv` (a single Mathlib lemma at `AffineSpace.lean:155`)
discharging the 3-step chain in one step closes `ga_grpObj` in 2-3 lines.
The asymmetry: `Ga = 𝔸(Fin 1, Spec k̄)` is exactly the affine space
`AffineSpace.homOverEquiv` is built for; `Gm` is not, because Mathlib
does NOT ship a "homOverEquiv for `Spec (Localization.Away t)`" lemma.
This is the missing Mathlib gap-fill that would unify the two
constructions; for now, the project owes ~100 LOC for `gm_grpObj`
versus ~3 LOC for `ga_grpObj`.

## Reversal trigger

If the 3-step bijection composition encounters:

- **Universe issues** in `GrpCat.{w}` vs the project's `.{u}` (the
  `homEquiv` value must live in `Type u`; if the unit-group at level `u`
  can't be coerced to level `w` of `F`, redefine `F` with explicit
  universe annotation `F : (Over (Spec (.of kbar)))ᵒᵖ ⥤ GrpCat.{u}`);
- **Definitional-eq issues** with the `IsOver` predicate (the
  over-category unfold may need `Over.homMk`-η-expansion via `Over.hom_ext`);
- **`IsScalarTower kbar (MvPolynomial Unit kbar) (k̄[t,t⁻¹])` synthesis
  failures** in step 2c (mitigated by the iter-170
  `Algebra.compHom`-style fix from `route-c-option-c-committed-iter170.md`
  — instantiate with the same `Algebra.compHom kbar (algebraMap kbar (MvPolynomial Unit kbar))`
  pattern that unblocked `Algebra kbar (HomogeneousLocalization.Away _ _)`);

then **fall back to direct `GrpObj.mk`**: hand-define `μ`, `η`, `ι` as
`Spec.map` of explicit ring maps —

- `μ := Spec.map ofHom (k̄[t,t⁻¹] → k̄[t,t⁻¹] ⊗_{k̄} k̄[t,t⁻¹], t ↦ t ⊗ t)`,
- `η := Spec.map ofHom (k̄[t,t⁻¹] → k̄, t ↦ 1)`,
- `ι := Spec.map ofHom (k̄[t,t⁻¹] → k̄[t,t⁻¹], t ↦ t⁻¹)`,

and prove the five group-object axioms by `Spec.map_comp` +
`CommRingCat.hom_ext` + ring-level computation. More wiring
(~150-200 LOC) but uses only `Spec.map`, `pullbackSpecIso`, and
`IsLocalization.Away.lift` — no over-category Yoneda, no Functor
build, no naturality. This fallback is the iter-167 escalation-watch
backup and was deliberately deferred in favor of the `ofRepresentableBy`
path because the latter is API-aligned. Fall back only if the
Yoneda path stalls for ≥2 iters with the same root cause.
