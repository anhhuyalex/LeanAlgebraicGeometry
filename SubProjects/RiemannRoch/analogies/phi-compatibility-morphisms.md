# Analogy: φ-compatibility morphisms for `PresheafOfModules.pullback`

## Slug

phi-compatibility-morphisms-iter135

## Iteration

135

## Question

For each of the four scheme morphisms in piece (i.b) of
`AlgebraicJacobian/Cotangent/GrpObj.lean`
(`π_G = G.hom`, `η_G.left`, `pr_2 = (snd G G).left`,
`s.left = (lift (𝟙 G) (toUnit G ≫ η[G])).left`), what is the
canonical Mathlib idiom for the compatibility morphism `φ` that
`PresheafOfModules.pullback` consumes? And do the iter-134 placeholder
theorems' intended types elaborate against that idiom?

## Project artifact(s)

- `AlgebraicJacobian/Cotangent/GrpObj.lean:417–419` —
  `schemeHomRingCompatibility` helper (iter-134 packaging around
  `((adj).homEquiv _ _).symm f.c` for CommRingCat-valued presheaves).
- `AlgebraicJacobian/Cotangent/GrpObj.lean:476–514, 566–572` — the three
  iter-134 placeholder theorems (`Iso.refl`-wrapped) whose intended
  `PresheafOfModules.pullback`-based shapes this analogist call settles.
- `AlgebraicJacobian/Differentials.lean:51–54` —
  `relativeDifferentialsPresheaf`, the parent definition whose φ-shape
  convention (`relativeDifferentials'` consumes the adjunction transpose
  on the X side) `schemeHomRingCompatibility` was packaging.

## Decisions identified

### Decision 1: Shape of the φ-compatibility morphism for `PresheafOfModules.pullback`

- **Mathlib idiom**: The signature of `PresheafOfModules.pullback`
  (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback:38–45`) is
  ```
  variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {F : C ⥤ D} {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}}
    (φ : S ⟶ F.op ⋙ R) [(pushforward.{v} φ).IsRightAdjoint]
  noncomputable def pullback : PresheafOfModules.{v} S ⥤ PresheafOfModules.{v} R
  ```
  i.e. φ is a morphism from the **base-side** presheaf of rings `S` to
  the pushforward `F.op ⋙ R` of the **total-side** presheaf of rings `R`.
  For a scheme morphism `f : X ⟶ Y`, this is exactly the structure-sheaf
  comorphism `f.c : Y.presheaf ⟶ f.base _* X.presheaf`, whiskered with
  `forget₂ CommRingCat RingCat`. Mathlib **already packages this** as
  `Scheme.Hom.toRingCatSheafHom`
  (`Mathlib.AlgebraicGeometry.Modules.Presheaf:42–45`):
  ```
  def Hom.toRingCatSheafHom (f : X ⟶ Y) :
      Y.ringCatSheaf ⟶ ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
        _ _ _).obj X.ringCatSheaf where
    hom := Functor.whiskerRight f.c _
  ```
  The `.hom` field projects the underlying nat trans of presheaves
  of rings (since `TopCat.Sheaf` is an `ObjectProperty.FullSubcategory`,
  the hom-extractor is `.hom` not `.val`). So
  `(Scheme.Hom.toRingCatSheafHom f).hom :
    Y.ringCatSheaf.obj ⟶ (Opens.map f.base).op ⋙ X.ringCatSheaf.obj`
  is exactly the φ consumed by `PresheafOfModules.pullback`.

- **Project's current path**: `schemeHomRingCompatibility`
  (`Cotangent/GrpObj.lean:417–419`) returns the **adjunction transpose**
  `((adj).homEquiv _ _).symm f.c :
   (TopCat.Presheaf.pullback f.base).obj Y.presheaf ⟶ X.presheaf`,
  which is a morphism of presheaves on `X` (not on `Y`). This is the
  correct shape for the project's `relativeDifferentialsPresheaf`
  (which calls `PresheafOfModules.DifferentialsConstruction.relativeDifferentials'`
  in the `F = 𝟭 D` special case, taking `φ' : S' ⟶ R`), but it is the
  **wrong direction** for `PresheafOfModules.pullback` (whose `φ`
  uses the general `S ⟶ F.op ⋙ R` shape with C = base side, D = total side).

- **Gap**: divergent-and-wrong — `schemeHomRingCompatibility` cannot be
  reused for `PresheafOfModules.pullback`; the two helpers consume
  different morphisms (adjunction transpose vs. raw comorphism). Both
  are needed in the project but for distinct purposes.

- **Cost of divergence (if any)**: zero — the project does not need
  to *replace* `schemeHomRingCompatibility`; it just needs to *not
  reuse* it for the piece (i.b) φ_* morphisms, and instead use the
  Mathlib helper `(Scheme.Hom.toRingCatSheafHom f).hom` (or
  equivalently `Functor.whiskerRight f.c (forget₂ CommRingCat RingCat)`)
  for those.

- **Verdict**: **ALIGN_WITH_MATHLIB** — use `(Scheme.Hom.toRingCatSheafHom f).hom`
  (the Mathlib idiom) for all four `φ_*` morphisms. Keep
  `schemeHomRingCompatibility` for its existing
  `relativeDifferentialsPresheaf`-internal use.

### Decision 2: Direction of `f.c` for `PresheafOfModules.pullback`

- **Mathlib idiom**: The iter-134 prover lane's task-result handoff
  asked whether `f.c : Z.presheaf ⟶ f.base _* Y.presheaf` is the
  `C → D op` shape expected by `PresheafOfModules.pullback`. **Yes,
  it is**: with `C = Opens Z.top`, `D = Opens Y.top`,
  `F = Opens.map f.base : Opens Z.top ⥤ Opens Y.top` (the preimage
  functor), we have `F.op ⋙ Y.presheaf = (Opens.map f.base).op ⋙ Y.presheaf
   = f.base _* Y.presheaf`. So `f.c` matches `S ⟶ F.op ⋙ R` modulo the
   `forget₂ CommRingCat RingCat` whiskering.

- **Project's current path**: The iter-134 placeholder bodies are
  `Iso.refl`-wrapped reflexive isos; the iter-134 prover did not commit
  to a direction. The handoff note ("`f.c` itself with `forget₂`
  conversion should be usable as φ") is the right intuition.

- **Gap**: identical (the handoff note is correct).

- **Cost of divergence (if any)**: zero — the handoff intuition is
  the right one.

- **Verdict**: **PROCEED** — the directional claim is correct. The
  iter-135 refactor can use `(Scheme.Hom.toRingCatSheafHom f).hom`
  uniformly.

### Decision 3: Home file for the 4 `φ_*` morphisms

- **Mathlib idiom**: Mathlib places `Scheme.Hom.toRingCatSheafHom` in
  `AlgebraicGeometry/Modules/Presheaf.lean`, in the
  `AlgebraicGeometry.Scheme` namespace, as a re-usable scheme-side
  helper. No project-side wrapper is needed.

- **Project's current path**: The directive lists three candidate homes
  for new project-side `φ_str / φ_η / φ_pr_two / φ_section` definitions:
  (i) in-file helpers in `Cotangent/GrpObj.lean`,
  (ii) utilities in `Differentials.lean` (where `schemeHomRingCompatibility`
   already lives), or
  (iii) Mathlib PR.

- **Gap**: divergent-with-trivial-cost — the project does not need any
  new helper because Mathlib already provides `Scheme.Hom.toRingCatSheafHom`.
  The 4 `φ_*` symbols should be **inline applications**
  `(Scheme.Hom.toRingCatSheafHom <morphism>).hom`, not new project
  definitions. Optionally, the prover can introduce them as local
  `let`-bindings inside the statements for readability:
  ```
  let φ_str := (Scheme.Hom.toRingCatSheafHom G.hom).hom
  let φ_η := (Scheme.Hom.toRingCatSheafHom (CommaMorphism.left η[G])).hom
  let φ_pr_two := (Scheme.Hom.toRingCatSheafHom (CartesianMonoidalCategory.snd G G).left).hom
  let φ_section := (Scheme.Hom.toRingCatSheafHom (lift (𝟙 G) (toUnit G ≫ η[G])).left).hom
  ```
  but no `def` is justified.

- **Cost of divergence (if any)**: NONE for the inline approach.
  Defining new project helpers would create gratuitous indirection
  on top of `toRingCatSheafHom`; the only justification would be
  ergonomics (4-character abbreviations vs. 30-character calls), which
  is better served by `let`-bindings local to each statement.

- **Verdict**: **ALIGN_WITH_MATHLIB** — no new project helpers; inline
  `(Scheme.Hom.toRingCatSheafHom <morphism>).hom` (or local `let`-bind
  them) at the 3 use sites in `Cotangent/GrpObj.lean`. Keep
  `schemeHomRingCompatibility` for its existing `relativeDifferentialsPresheaf`
  use; it serves a different purpose.

### Decision 4: Elaboration sanity check of the intended types

- **Mathlib idiom**: N/A (this is a project-side validation).

- **Project's current path**: The iter-134 placeholders use
  `Nonempty (... ≅ ...)` with `Iso.refl _` to record the eventual
  conclusion shape but not the load-bearing type.

- **Gap**: TBD — verified by `lean_run_code` (see report).

- **Cost of divergence (if any)**: zero — the intended types elaborate
  cleanly without any universe / typeclass / `forget₂` workaround.

- **Verdict**: **PROCEED** — the iter-135 refactor of the 3 placeholder
  theorems to intended-type + `sorry` will succeed at the
  type-elaboration level. The remaining work is the proof bodies, which
  is the next mathlib-analogist call's scope (for Step 2) and iter-136+
  prover lane work (for Step 3 + composition).

## Recommendation

Iter-135 should refactor the 3 placeholder theorems in
`AlgebraicJacobian/Cotangent/GrpObj.lean` (lines 476, 508, 566) to
their intended `PresheafOfModules.pullback`-based signatures, using
`(Scheme.Hom.toRingCatSheafHom <morphism>).hom` for each `φ_*`. The
literal Lean text for the 3 intended types appears in the iter-135
report (`mathlib-analogist-phi-compatibility-morphisms-iter135.md` §
"Intended types"). No new project-side `φ_*` definitions are needed
— inline the Mathlib helper or use local `let`-bindings for legibility.
`schemeHomRingCompatibility` (line 417) should remain in place; it is
used by `relativeDifferentialsPresheaf` for a different purpose (the
adjunction transpose used by `relativeDifferentials'` in the `F = 𝟭 D`
case) and should not be repurposed for `PresheafOfModules.pullback`.

The Mathlib precedent `Scheme.Hom.toRingCatSheafHom` at
`Mathlib/AlgebraicGeometry/Modules/Presheaf.lean:42–45` is the
authoritative wrapper; no Mathlib PR is needed.
