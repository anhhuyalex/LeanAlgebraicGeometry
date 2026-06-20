# Analogy: structure shape for `Scheme.QcohAlgebra`

## Mode
api-alignment

## Slug
qcohalgebra-structure

## Iteration
174

## Question

What is the right Mathlib-aligned structure shape for
`AlgebraicGeometry.Scheme.QcohAlgebra X` (a quasi-coherent sheaf of
`O_X`-algebras)? Three candidates were proposed:

- (A) `SheafOfModules X.ringCatSheaf` + `QuasiCoherent` predicate
      + `Mon_Class` monoid + commutativity.
- (B) Functorial form: `X.openSets^op ⥤ CommAlgCat (Γ(X, O_X))`
      + qcoh predicate.
- (C) Typeclass form `[QcohAlgebraStr X 𝒜]`.

## Project artifact(s)

- `AlgebraicJacobian/Picard/RelativeSpec.lean:98` — `QcohAlgebra X : Type (u+1) := sorry`
  (must-fix type-level placeholder flagged by lean-auditor `iter173`).
- `AlgebraicJacobian/Picard/RelativeSpec.lean:123,134,169,193,223,251` — the 6 pinned
  declarations and the `structureMorphism` helper, every one quantifying over
  `X.QcohAlgebra`.
- `blueprint/src/chapters/Picard_RelativeSpec.tex:39-59` — informal definition
  `def:qc_sheaf_of_algebras` (Stacks 01LL).

## Mathlib status at pinned commit `b80f227`

Surveyed `Mathlib.AlgebraicGeometry`, `Mathlib.Algebra.Category.ModuleCat.Sheaf`,
`Mathlib.CategoryTheory.Monoidal`, `Mathlib.CategoryTheory.Sheaf`.

| Looked-for | Present? | Reference |
|---|---|---|
| `QcohAlgebra` / `Scheme.algebraSheaf` / `RelativeSpec` | NO | (project must build it) |
| `SheafOfModules R` (over a sheaf of rings) | YES | `Mathlib/Algebra/Category/ModuleCat/Sheaf.lean:32` |
| `SheafOfModules.IsQuasicoherent` predicate | YES | `Mathlib/Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean:249` |
| `Scheme.Modules X := SheafOfModules X.ringCatSheaf` | YES | `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:37` |
| `MonObj` typeclass (monoid object in monoidal cat) | YES | `Mathlib/CategoryTheory/Monoidal/Mon_.lean:74` |
| `IsCommMonObj` (commutativity overlay) | YES | `Mathlib/CategoryTheory/Monoidal/CommMon_.lean` |
| `Mon_Class` typeclass | NO (renamed → `MonObj` at this commit) | — |
| `Mon (ModuleCat R) ≌ AlgCat R` equivalence | YES | `Mathlib/CategoryTheory/Monoidal/Internal/Module.lean:14` |
| `CommAlgCat R` (bundled commutative `R`-algebras) | YES | `Mathlib/Algebra/Category/CommAlgCat/Basic.lean:31` |
| `Under R` in `CommRingCat` ≃ commutative `R`-algebras | YES | `Mathlib/Algebra/Category/Ring/Under/Basic.lean:13-18` (explicit "Under R is (equivalent to) the category of commutative R-algebras") |
| `PresheafOfModules` monoidal structure | YES | `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean:13-23` |
| `SheafOfModules` monoidal structure (sheafified tensor) | **NO** | (no `Sheaf/Monoidal.lean`; only the presheaf version exists) |
| `TopCat.Sheaf CommRingCat X` (structure sheaf type) | YES | `X.sheaf : Scheme → TopCat.Sheaf CommRingCat X`, `Mathlib/AlgebraicGeometry/Scheme.lean:152` |
| `Functor.RepresentableBy` (for the Yoneda statement) | YES | `Mathlib/CategoryTheory/Yoneda.lean` |

## Decisions identified

### Decision 1: choice of *carrier* (module-with-algebra-overlay vs. under-object in sheaves of CommRings)

- **Mathlib idiom**: there are **two** valid Mathlib idioms for "commutative `R`-algebra"
  and they cohabit:
  1. `CommAlgCat R` — bundled `(carrier, CommRing, Algebra R)` structure
     (`Mathlib/Algebra/Category/CommAlgCat/Basic.lean:31`).
  2. `Under (R : CommRingCat)` — under-category form. Mathlib's
     `Mathlib/Algebra/Category/Ring/Under/Basic.lean` opens with
     *"`Under R` is (equivalent to) the category of commutative `R`-algebras"*,
     and provides `toAlgHom`, `mkUnder R A` translating each direction
     (`:35-67`). For *non-commutative* algebras the file says use `AlgCat R`.
  3. `Mon_ ModuleCat R ≌ AlgCat R` is the *categorical* form; only relevant
     when the project also needs the monoidal structure machinery.

  The right Mathlib precedent for *sheaves* of commutative algebras over a
  *sheaf* of commutative rings is the **sheafified under-object form**: an
  object of `Sheaf J CommRingCat` together with a unit morphism from
  `X.sheaf`. This is the direct upgrade of `Under R` to the relative setting.

- **Project's current path**: typed-`sorry` placeholder. The docstring at
  `RelativeSpec.lean:90-96` sketches Encoding II (monoid-in-modules):
  ```
  structure QcohAlgebra (X : Scheme.{u}) where
    module : X.Modules
    algStr : Mon_Class module
    isCommutative : ...
  ```
- **Gap**: divergent-with-cost. Encoding II needs the monoidal structure on
  `SheafOfModules R` **which is missing from Mathlib at `b80f227`** — only
  `PresheafOfModules` has tensor (cf. `Mathlib/Algebra/Category/ModuleCat/Presheaf/Monoidal.lean`).
  Sheafifying the tensor product (so `M₁ ⊗ M₂` is again a sheaf, not just a
  presheaf) is genuine new infrastructure (~200-500 LOC; needs
  `HasSheafify J ModuleCat` and a sheaf-of-modules tensor-product lemma pile).
  Until that lands upstream, Encoding II is **stuck behind a Mathlib gap**.

- **Cost of divergence (if any)**: building Encoding II inside this project
  would (i) duplicate a piece of upstream infrastructure that is a known
  Mathlib direction, (ii) add 200-500 LOC of orthogonal categorical scaffolding
  unrelated to the Jacobian proof, (iii) leave the project unable to consume
  an eventual upstream monoidal-SheafOfModules without renaming. Encoding I
  (under-object), by contrast, is a 20-30 LOC carrier that re-uses
  `TopCat.Sheaf CommRingCat`, `X.sheaf`, and `SheafOfModules.IsQuasicoherent`
  unchanged.

- **Verdict**: NEEDS_MATHLIB_GAP_FILL (the *idiomatic* form is Encoding II
  but its prerequisite is upstream). **Interim choice for iter-174+**:
  Encoding I — `Under`-style in `TopCat.Sheaf CommRingCat X`. Encoding I
  is itself a Mathlib idiom (the relative version of `Under R`), so this
  is not project drift — it's the Mathlib-aligned choice given the available
  upstream infrastructure.

### Decision 2: bundled structure vs. predicate-on-existing-object

- **Mathlib idiom**: bundled. Both `CommAlgCat R` and `Under R` are bundled
  structures, not predicates. The `Mon_ C` / `Mon` / `CommMon C` lineage
  (`Mathlib/CategoryTheory/Monoidal/Mon_.lean:258`,
  `Mathlib/CategoryTheory/Monoidal/CommMon_.lean:27`) is also bundled with
  field-accessors and `[instance]` projections, not a `Prop`-valued predicate
  on an existing object.

- **Project's current path**: the docstring at `RelativeSpec.lean:90-96`
  proposes a bundled `structure`. ALIGN.

- **Gap**: identical.

- **Verdict**: ALIGN_WITH_MATHLIB — keep it a `structure`, not a `class`
  on top of `SheafOfModules`.

### Decision 3: typeclass vs. plain structure for the algebra/commutativity overlay

- **Mathlib idiom**: in `Mon_ ModuleCat` style, the monoid structure is a
  typeclass `[MonObj M]` (and commutativity is `[IsCommMonObj M]`)
  attached to the underlying object (`Mathlib/CategoryTheory/Monoidal/Mon_.lean:73-85`).
  In `CommAlgCat` style, the `CommRing` and `Algebra` instances are
  *bracketed fields* of the bundled structure
  (`Mathlib/Algebra/Category/CommAlgCat/Basic.lean:35-36`):
  ```
  structure CommAlgCat where
    private mk ::
    carrier : Type v
    [commRing : CommRing carrier]
    [algebra : Algebra R carrier]
  ```
  Both styles coexist; the bracketed-field form is preferred when downstream
  code wants to manipulate the bundled object directly (which is the
  RelativeSpec case — we always have a specific `𝒜 : X.QcohAlgebra` and we
  want `Γ(𝒜, U)` to *automatically* carry `CommRing` / `Algebra Γ(X, U)`
  instances).

- **Project's current path**: docstring uses `Mon_Class module` (positional
  field). Once the carrier swaps to "under-object in `Sheaf CommRingCat`",
  the algebra/CommRing structure is *induced* by `RingHom.toAlgebra` on each
  section (cf. `Mathlib/Algebra/Category/Ring/Under/Basic.lean:35`,
  `instance (A : Under R) : Algebra R A := RingHom.toAlgebra A.hom.hom`),
  so no explicit overlay is needed.

- **Verdict**: ALIGN_WITH_MATHLIB — use the bracketed-field pattern of
  `CommAlgCat`, but at the *sheaf* level: bracket-field a `CommRing`
  instance for each section, with restriction-as-`RingHom`. The induced
  algebra structure comes automatically from the unit `X.sheaf ⟶ 𝒜`.

### Decision 4: Yoneda Hom-set for `UniversalProperty`

- **Mathlib idiom**: `CategoryTheory.Functor.RepresentableBy`
  (`Mathlib/CategoryTheory/Yoneda.lean`). The natural-bijection statement
  `Hom_X(T, Spec_X(𝒜)) ≅ Hom_{O_X-alg}(𝒜, g_* O_T)` is a
  `RepresentableBy` witness for the functor `F : Schᵒᵖ ⥤ Type` of pairs
  `(g, φ : g^* 𝒜 → O_T)`.

  The RHS `Hom_{O_X-alg}(𝒜, g_* O_T)` is the morphism-set in the under-category
  `Under (X.sheaf)` of `TopCat.Sheaf CommRingCat X`:
  given `g : T → X`, `g_* O_T : TopCat.Sheaf CommRingCat X` (pushforward of
  the structure sheaf), the unit `X.sheaf → g_* O_T` is `g.c`, and a Hom of
  `O_X`-algebras `𝒜 → g_* O_T` is exactly a morphism in
  `Under X.sheaf` (i.e. a Hom in `TopCat.Sheaf CommRingCat X` commuting with
  the units from `X.sheaf`).

- **Project's current path**: iter-173 file-skeleton encodes
  `UniversalProperty` as `IsAffineHom (structureMorphism 𝒜)` (a
  type-dodging consequence). Blueprint review (`Picard_RelativeSpec.tex:145-149`)
  explicitly flags this as a must-upgrade for iter-174+.

- **Gap**: divergent-with-cost (the placeholder is non-tautological but
  not the universal property). Iter-174+ refines to a
  `CategoryTheory.Functor.RepresentableBy` witness.

- **Verdict**: ALIGN_WITH_MATHLIB — upgrade the signature to
  `Functor.RepresentableBy F (X.RelativeSpec 𝒜)` where `F` is the
  Stacks 01LQ functor of pairs, expressible directly with the
  under-object encoding.

## Recommendation

**Use Encoding I (the relative `Under` form) for iter-174+.** Concretely:

```lean
/-- A quasi-coherent sheaf of O_X-algebras: a sheaf of commutative rings
    on X equipped with a unit from the structure sheaf, whose underlying
    O_X-module is quasi-coherent. -/
structure Scheme.QcohAlgebra (X : Scheme.{u}) where
  /-- The underlying sheaf of commutative rings on X. -/
  sheaf : TopCat.Sheaf CommRingCat.{u} X
  /-- The O_X-algebra unit `𝒪_X ⟶ 𝒜`. -/
  unit : X.sheaf ⟶ sheaf
  /-- The underlying O_X-module (via `forget₂ CommRingCat RingCat` + the
      unit) is quasi-coherent. -/
  isQcoh : (toQcohModule sheaf unit).IsQuasicoherent  -- helper to define
```

Helper `toQcohModule : ∀ (𝒮 : TopCat.Sheaf CommRingCat X) (u : X.sheaf ⟶ 𝒮),
SheafOfModules X.ringCatSheaf` extracts the `O_X`-module structure from the
unit (~15 LOC: forget to `RingCat`, then use `u` to get the module action
via `Algebra.toModule` at each section + sheaf-of-modules glue —
specifically via `SheafOfModules` constructor with `R := X.ringCatSheaf`,
the underlying `Sheaf J Ab` from forget₂, and the section-level smul
`r • a := u(r) * a`).

**Recipe for the Yoneda Hom-set required by `UniversalProperty`**:

```lean
/-- The functor `F : Schᵒᵖ ⥤ Type` from Stacks 01LQ: an X-scheme `g : T → X`
    together with an `O_T`-algebra map `g^* 𝒜 → O_T`. Via push-pull
    adjunction this is equivalently an `O_X`-algebra map `𝒜 → g_* O_T`. -/
def UniversalFunctor (X : Scheme.{u}) (𝒜 : X.QcohAlgebra) :
    Scheme.{u}ᵒᵖ ⥤ Type u := ...

theorem UniversalProperty {X : Scheme.{u}} (𝒜 : X.QcohAlgebra) :
    (UniversalFunctor X 𝒜).RepresentableBy (X.RelativeSpec 𝒜) := ...
```

The morphism set `Hom_{O_X-alg}(𝒜, g_* O_T)` is concretely
`{ φ : 𝒜.sheaf ⟶ (g.pushforward).obj T.sheaf //
   𝒜.unit ≫ φ = X.sheaf-to-g_*O_T-unit }`, which is exactly a Hom in
`Under X.sheaf` over `TopCat.Sheaf CommRingCat X`.

**Cost of Encoding I**:

- Carrier `structure`: ~25 LOC.
- `toQcohModule` helper + `IsQuasicoherent` plumbing: ~30 LOC.
- Section-level `CommRing`/`Algebra` instances (derived): ~25 LOC.
- `UniversalFunctor` definition: ~40 LOC.
- `RelativeSpec` body via gluing (uses `Scheme.GlueData` +
  `AffineScheme.glueOpens`): ~200 LOC.
- `UniversalProperty` as `RepresentableBy`: ~120 LOC.
- `affine_base_iff` (Stacks 01LO, reduces to `Spec(Γ(X, 𝒜))`): ~70 LOC.
- `base_change` (Stacks 01LS): ~120 LOC.
- `functor` (object + map action): ~50 LOC.

**Total iter-175+ body-lane estimate: ~680 LOC.** (Higher than the
file-skeleton's 56-LOC plan because the file-skeleton numbers assumed
the carrier was already a typed `sorry`.)

**Encoding II remains the long-term Mathlib-aligned form** and Encoding I
is upgradable to it: when monoidal `SheafOfModules` lands upstream, replace
the `sheaf : TopCat.Sheaf CommRingCat X` field with `module : X.Modules`
+ `[MonObj module]` + `[IsCommMonObj module]`, and the rest of the API
(unit, Yoneda, base change) transports via the equivalence
`Mon_(SheafOfModules X.ringCatSheaf) ≃ Under X.sheaf in Sheaf CommRingCat`
(the sheaf-of-rings analogue of `Mon_ ModuleCat R ≌ AlgCat R`).

## Hard-NO on candidate (B) and (C)

- **(B) Functorial form** `X.openSets^op ⥤ CommAlgCat (Γ(X, O_X))` is
  **wrong**: `CommAlgCat R` requires a fixed base ring, but on each open
  `U` the natural base is `Γ(U, O_X)`, not `Γ(X, O_X)`. The functor lands
  in `CommRingCat` (not a fixed `CommAlgCat R`), with restriction maps
  that are *not* `Γ(X, O_X)`-algebra homomorphisms in general. Treating
  it as a functor to `CommAlgCat (Γ(X, O_X))` either (i) loses the
  open-local information or (ii) needs a varying `R` per open which is
  not what `CommAlgCat R` expresses. The sheaf-of-CommRings-under-X.sheaf
  form (Encoding I) is the correct generalization.

- **(C) Typeclass form** `[QcohAlgebraStr X 𝒜]` is over-engineered: there
  is no `𝒜 : Type` to attach the instance to (an O_X-algebra isn't a type,
  it's a sheaf-valued object). Mathlib reserves typeclass overlays for
  *operations on types* (e.g. `[Mul R]` on a type), not for sheaves of
  rings. The bundled-structure form is what Mathlib uses for analogous
  notions like `CommAlgCat` and `Mon_ C`.
