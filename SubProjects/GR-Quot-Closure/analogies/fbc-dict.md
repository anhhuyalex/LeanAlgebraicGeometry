# Analogy: affine tilde pushforward/pullback dictionary for flat base change (i=0)

## Mode
api-alignment

## Slug
fbc-dict

## Iteration
235

## Question
For the affine reduction of `affineBaseChange_pushforward_iso`, what is the Mathlib
idiom for (Q1) an element-free Γ-fragment iso `restrictScalars φ (Γ (tilde M)) ≅
Γ (pushforward (Spec.map φ) (tilde M))` — including the accessor for the ring map
underlying `SheafOfModules.pushforward` — and a direct affine-pushforward-of-tilde
iso if one exists; and (Q2) is "pushforward preserves quasi-coherent" genuinely
Mathlib-absent, and if so what is the cheapest project-side build path?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:207-237` — `affineBaseChange_pushforward_iso` (sorry).
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean:168-205` — the iter-234 Γ-fragment doc block + instance-wall report.
- `blueprint/src/chapters/Cohomology_FlatBaseChange.tex:1,18,229` — chapter is explicitly about a **quasi-coherent** F; affine-local statement is `F = tilde M`.

## Decisions identified

### Decision: missing `[IsQuasicoherent F]` hypothesis on `affineBaseChange_pushforward_iso`

- **Mathlib idiom**: the whole affine dictionary only exists for QC sheaves. Mathlib's
  affine module API is built around `tilde` (`Mathlib/AlgebraicGeometry/Modules/Tilde.lean`),
  and the *only* characterisation of "a `(Spec R).Modules` is `tilde` of something" is
  quasi-coherence: `isIso_fromTildeΓ_iff` (`Tilde.lean:340`) says `IsIso M.fromTildeΓ ↔
  (tilde.functor R).essImage M`, and `(tilde N).IsQuasicoherent` is an instance
  (`Tilde.lean:394`). There is no notion of "restriction of `f_*F` to scalars" for a
  non-QC `F`.
- **Project's current path**: `affineBaseChange_pushforward_iso (h) [IsAffineHom f] (F : X.Modules)`
  — no QC hypothesis. The proof sketch (file comment + blueprint:229) nonetheless assumes
  `F|affine = tilde M`, i.e. uses quasi-coherence.
- **Gap**: divergent-and-wrong. Without `[IsQuasicoherent F]` the statement is *false*
  (Stacks "affine base change" / 02KH requires F quasi-coherent) and the intended proof
  route is impossible — over an affine open a general `F` is not `tilde M`, so neither
  the Γ-fragment iso nor `cancelBaseChange` applies.
- **Cost of divergence**: the entire iter-234 instance-wall effort is spent on a lemma
  (`Γ(pushforward (Spec.map φ)(tilde M)) ≅ restrictScalars φ M`) that can only feed a
  theorem whose hypotheses don't currently license `F = tilde M`. The signature is **not**
  in `archon-protected.yaml`, so it is freely editable.
- **Verdict**: ALIGN_WITH_MATHLIB. Add `[IsQuasicoherent F]` (or `[F.IsQuasicoherent]`)
  to both `affineBaseChange_pushforward_iso` and `flatBaseChange_pushforward_isIso`.

### Decision: direct affine-pushforward-of-tilde iso (Q1 highest-value find)

- **Mathlib idiom**: ABSENT. Grep of all of Mathlib for any `pushforward … tilde` /
  `tilde … restrictScalars` lemma returns nothing; `leansearch` for "pushforward of
  quasicoherent is quasicoherent" returns only the structural `pushforward` definitions.
  There is no `tilde.functor R' ⋙ pushforward (Spec.map φ) ≅ restrictScalars φ ⋙
  tilde.functor R` (the Beck–Chevalley/affine-pushforward = restriction-of-scalars iso).
- **Project's current path**: building the Γ-fragment by hand at the section level.
- **Gap**: NEEDS_MATHLIB_GAP_FILL.
- **Cheapest build path**: produce the object iso
  `pushforward (Spec.map φ) (tilde M) ≅ tilde (restrictScalars φ.hom M)` once, then
  everything downstream (QC of the pushforward, the Γ-fragment) is a corollary:
  `(isQuasicoherent R).IsClosedUnderIsomorphisms` (`Quasicoherent.lean:330`) +
  `(tilde N).IsQuasicoherent` (`Tilde.lean:394`) give QC for free; `moduleSpecΓFunctor`
  applied to the iso + `tilde.toTildeΓNatIso` (`Tilde.lean:273`, an iso) give the
  Γ-fragment for free. Build the object iso via the conservativity route below rather
  than the section-smul route.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL.

### Decision: hand-built section smul-dictionary vs Mathlib conservativity reduction

- **Mathlib idiom**: `tilde.functor R` is fully faithful (`Tilde.fullyFaithfulFunctor`,
  `Full`, `Faithful` instances, `Tilde.lean:312-316`) with essential image = QC
  (`isIso_fromTildeΓ_iff`, `Tilde.lean:340`). A fully faithful functor reflects isos
  (`CategoryTheory.Functor` `Full`+`Faithful ⇒ ReflectsIsomorphisms` instance). So for a
  map `α : N₁ ⟶ N₂` between **QC** `(Spec R)`-modules, the counit naturality
  `fromTildeΓNatTrans` (`Tilde.lean:248`) gives, with both `fromTildeΓ`s iso,
  `IsIso α ↔ IsIso (tilde.functor.map (moduleSpecΓFunctor.map α)) ↔
  IsIso (moduleSpecΓFunctor.map α)`. This reduces `IsIso (base-change map)` to `IsIso`
  of a concrete `ModuleCat R` map — no section-level `Module`/`SMul` instances are ever
  named.
- **Project's current path (iter-234)**: hand-build a `LinearEquiv` on the common carrier
  `Γ(M^~,⊤)` and discharge its `map_smul'` goal — which hits the instance wall (the
  intermediate `Γ(Spec R,⊤)`/`Γ(Spec R',⊤)`-actions buried in `Module.compHom` /
  `restrictScalars` are not synthesizable as named instances on the final carrier).
- **Gap**: divergent-with-cost. The section-smul route fights the API at the wrong
  altitude; the conservativity route sidesteps it structurally.
- **Cost of divergence**: the `backward.isDefEq.respectTransparency false` + bespoke
  `@`-explicit smul threading is fragile and route-specific; it produces a Γ-fragment iso
  that still has to be glued to QC-of-pushforward, QC-of-pullback, and `cancelBaseChange`
  by hand. The conservativity route collapses "iso of sheaves" to "iso of `ModuleCat`
  maps" in one step using infra Mathlib already ships.
- **Verdict**: ALIGN_WITH_MATHLIB (reframe the affine reduction around
  `tilde`-full-faithfulness; keep section-level smul work confined to identifying the
  resulting `ModuleCat` map with `cancelBaseChange`, where Mathlib's own
  `IsScalarTower`/`CompatibleSMul` idiom applies — see next decision).

### Decision: the `map_smul'` smul-compatibility idiom (if section-level work is unavoidable)

- **Mathlib idiom**: Tilde.lean itself closes the *identical* shape of goal twice.
  `modulesSpecToSheafIso` (`Tilde.lean:100-104`) discharges `map_smul'` by
  `IsScalarTower.algebraMap_smul`. `SpecModulesToSheafFullyFaithful` (`Tilde.lean:71-79`)
  *materialises* the intermediate action by hand:
  `letI := Module.compHom … (algebraMap …)`,
  `haveI : IsScalarTower R _ _ := .of_algebraMap_smul fun _ _ ↦ rfl`, then
  `IsLocalization.linearMap_compatibleSMul … |>.map_smul`. This directly refutes the
  iter-234 claim that "the action can't be named": Mathlib names it with `letI`/`haveI`.
- **Project's current path**: tried `change`/`rw`/`rfl`/`IsScalarTower.algebraMap_smul`
  *without* first introducing the `Module.compHom` `letI`, so the action stayed implicit.
- **Gap**: divergent-with-cost (recoverable by adopting the idiom).
- **Verdict**: PROCEED — if a `ModuleCat`-level smul identity is still needed at the end,
  use the `letI Module.compHom` + `IsScalarTower.of_algebraMap_smul` + `algebraMap_smul`
  pattern verbatim from Tilde.lean rather than expecting the instance to be synthesized.

### Decision: accessor for the ring map underlying `SheafOfModules.pushforward` (Q1 blocker)

- **Mathlib idiom**: `f.toRingCatSheafHom` (`Modules/Presheaf.lean:42`) is built
  `where hom := Functor.whiskerRight f.c _`. In current Mathlib `Sheaf J A` is an
  `ObjectProperty.FullSubcategory` of presheaves (`Sheaf.Hom.mk := ObjectProperty.homMk`,
  `Sites/Sheaf.lean:315`), so a sheaf-of-rings morphism projects through `.hom` (a
  presheaf `NatTrans`), **not** `.val` — this is exactly why the prover's `.val.app`
  failed ("InducedCategory.Hom"). The RingCat map at `⊤` is
  `f.toRingCatSheafHom.hom.app (op ⊤)`, definitionally
  `(forget₂ CommRingCat RingCat).map (f.c.app (op ⊤))`. Even simpler: don't dig through
  the module pushforward at all — the comparison ring map at `⊤` is `f.appTop`
  (`Γ(Y,⊤) ⟶ Γ(X,⊤)` as `CommRingCat`), available directly on the scheme morphism, and
  for `f = Spec.map φ` it is conjugate to `φ` by `Scheme.ΓSpecIso_inv_naturality`
  (`Scheme.lean:619`).
- **`(Spec.map φ) ⁻¹ᵁ ⊤ = ⊤`**: `Scheme.preimage_top` (`Scheme.lean:259`) is **`rfl`**.
  So `Γ((pushforward f).obj M, ⊤) = Γ(M, f⁻¹ᵁ ⊤) = Γ(M, ⊤)` needs no transport
  (`pushforward_obj_obj` is rfl; `preimage_top` is rfl). Where Mathlib does want to align
  a `homOfLE le_top`/`eqToHom` it uses the `(ΓSpecIso R).inv ≫ presheaf.map (homOfLE
  le_top).op` idiom (`Scheme.lean:627`), but here it is unnecessary.
- **Verdict**: PROCEED with the corrected accessor (`.hom.app (op ⊤)` / `f.appTop`).

### Decision: QC-of-pushforward (Q2)

- **Mathlib idiom**: ABSENT. `IsQuasicoherent` appears in exactly two files
  (`Modules/Tilde.lean`, `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean`); there is
  no `AlgebraicGeometry/Morphisms/QuasiCoherent.lean`. No "pushforward/closed-immersion/
  finite/affine morphism preserves `IsQuasicoherent`" lemma exists. What Mathlib *does*
  ship: `IsQuasicoherent.of_coversTop` (`Quasicoherent.lean:377`, locality),
  `(isQuasicoherent R).IsClosedUnderIsomorphisms` (`:330`), `(tilde N).IsQuasicoherent`
  (`Tilde.lean:394`).
- **Cheapest build path**: do NOT prove the general theorem. For this lane the pushforward
  is of a concrete `tilde M`, so `IsQuasicoherent (pushforward (Spec.map φ)(tilde M))`
  follows from the object iso `pushforward (Spec.map φ)(tilde M) ≅ tilde (restrictScalars
  φ.hom M)` via `IsClosedUnderIsomorphisms` + the `tilde` instance — i.e. it is *the same*
  brick as the Q1 object iso, not an independent obligation.
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (absent; built as a corollary of the Q1 object iso).

## Recommendation

Two moves, in order. **(1) Fix the signature**: add `[IsQuasicoherent F]` to
`affineBaseChange_pushforward_iso` (and `flatBaseChange_pushforward_isIso`) — the theorem
is false and unprovable without it, the blueprint already says "quasi-coherent", and the
declaration is not protected. **(2) Reframe the affine reduction around `tilde`
full-faithfulness instead of a hand-built section smul-dictionary**: over an affine open,
source and target of the base-change map are QC `(Spec R)`-modules; use
`isIso_fromTildeΓ_iff` + `fromTildeΓNatTrans` naturality + `tilde.functor`'s
reflect-isos to reduce `IsIso (base-change map)` to `IsIso` of `moduleSpecΓFunctor.map`
of it, a concrete `ModuleCat R` map, which is `cancelBaseChange`. The single remaining
gap-fill brick is the object iso `pushforward (Spec.map φ)(tilde M) ≅ tilde
(restrictScalars φ.hom M)` (Q1 top find, Mathlib-absent); it simultaneously discharges
QC-of-pushforward (Q2). When a residual `ModuleCat`-level smul identity surfaces, copy the
`letI Module.compHom` + `IsScalarTower.of_algebraMap_smul` + `algebraMap_smul` idiom that
Tilde.lean uses for the same goal — the action is nameable, contrary to the iter-234
diagnosis. Accessor fixes: `f.toRingCatSheafHom.hom.app (op ⊤)` / `f.appTop` (not `.val`),
and `(Spec.map φ) ⁻¹ᵁ ⊤ = ⊤` is `rfl`.
