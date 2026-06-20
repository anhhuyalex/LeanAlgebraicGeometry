# Analogy: strong-monoidal tensorator for an abstract left-adjoint pullback of sheaves of modules

## Mode
cross-domain-inspiration

## Slug
pullback-tensor

## Iteration
242

## Structural problem (abstracted)
Given a monoidal adjunction-shaped situation `F ⊣ G` between two monoidal categories
(here `F = pullback`, `G = pushforward`, objects = sheaves of modules over a varying
structure ring, `⊗ = sheafify(presheaf-⊗)`), with `F` defined ONLY as the abstract
left adjoint `(pushforward).leftAdjoint` (no sectionwise/stalkwise value), produce a
strong-monoidal comparison `F(A ⊗ B) ≅ F A ⊗ F B` — at least enough to conclude
`IsInvertible M → IsInvertible (F M)`.

## Failed approaches (from directive)
- Sectionwise `extendScalars.Monoidal`: the abstract left adjoint has no sectionwise
  formula to apply it to.
- Generic `Adjunction.leftAdjointOplaxMonoidal` packager: *directive claimed absent* —
  **this is STALE (see below): it is present at the pin.**
- Filesystem grep: no tensor-pullback comparison, no `MonoidalCategory (SheafOfModules)`.

## KEY CORRECTION TO THE DIRECTIVE'S PREMISE
The pinned Mathlib (`b80f227`, 2026-04-20) **does** contain the full doctrinal-adjunction
tensorator machinery. PR #36599 ("the monoidal adjunction between the extension and the
restriction of scalars", merged 2026-03-20) added it; the pin postdates it. So Q1's
"has Mathlib built a tensorator from an adjoint?" = **YES**, and Q3's bump question is
moot — it is already in the tree.

Locations (all in `Mathlib/CategoryTheory/Monoidal/Functor.lean`):
- `Adjunction.rightAdjointLaxMonoidal` (line 897): `F ⊣ G`, `[F.OplaxMonoidal] ⊢ G.LaxMonoidal`.
- `Adjunction.leftAdjointOplaxMonoidal` (line 1009): `F ⊣ G`, `[G.LaxMonoidal] ⊢ F.OplaxMonoidal`.
  Explicit mate formula (line 1010-1011):
    `η := (adj.homEquiv _ _).symm (ε G)`
    `δ X Y := (adj.homEquiv _ _).symm ((adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _)`
- `Adjunction.IsMonoidal` (line 952): compatibility Prop; auto-instances `instIsMonoidal`,
  `instIsMonoidal_1` produce it for the mate structures.
- `Adjunction.laxMonoidalEquivOplaxMonoidal` (line 1070): `G.LaxMonoidal ≃ F.OplaxMonoidal`.

## Analogues found

### Analogue: `Adjunction.leftAdjointOplaxMonoidal` (doctrinal adjunction / mate)
- **Domain**: category theory — monoidal functors / mates.
- **Same structural problem there**: produce a (op)lax tensorator on a functor given only
  as one half of an adjunction, transporting structure across the adjunction by the mate
  correspondence (no value formula for the functor needed).
- **Technique**: the tensorator `δ_{X,Y} : F(X⊗Y) → FX⊗FY` is the *adjunct* of
  `(unit_X ⊗ unit_Y) ≫ μ_G : X⊗Y → G(FX) ⊗ G(FY) → G(FX⊗FY)`, i.e.
  `δ X Y := (adj.homEquiv _ _).symm ((adj.unit.app X ⊗ₘ adj.unit.app Y) ≫ μ G _ _)`.
  This needs ONLY the lax structure `μ_G` on the right adjoint + the adjunction unit; it is
  exactly "tensorator without a sectionwise value."
- **Mapping to project**: `F = Scheme.Modules.pullback f`, `G = Scheme.Modules.pushforward f`,
  `adj = Scheme.Modules.pullbackPushforwardAdjunction f` (this term EXISTS in Mathlib,
  `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:172`). `μ_G` = the lax comparison
  `f_*A ⊗ f_*B → f_*(A⊗B)` for pushforward.
- **Porting cost**: HIGH for the bundled API, MEDIUM for a hand-port. Blockers:
  1. The bundled API requires `MonoidalCategory (SheafOfModules 𝒪_X)` and
     `MonoidalCategory (SheafOfModules 𝒪_Y)` instances — **the project has none** (it
     carries `Scheme.Modules.tensorObj` as a bespoke sheafified-presheaf tensor with no
     bundled monoidal category, which is *why* the group law was built by hand on
     `IsInvertible`). So `[F.OplaxMonoidal]`/`[G.LaxMonoidal]` cannot even be stated as-is.
  2. Need `pushforward.LaxMonoidal` (the `μ_G` above) — **absent from Mathlib** (grep of
     `SheafOfModules.pushforward*` shows no monoidal structure).
  3. **Oplax gives only a MAP, not an iso.** `pullbackTensorIso` must be an iso; oplax `δ`
     is not automatically invertible. Strong monoidality (`F.Monoidal`, each `δ` iso) is
     genuine geometric content the adjunction alone does NOT supply.
  The hand-port: skip the `MonoidalCategory` instance, build the single comparison map
  `δ_{M,N}` for the specific `M,N` via the formula above (needs `μ` only for `f_*(f^*M), f_*(f^*N)`),
  then prove it is iso separately.
- **Verdict**: ANALOGUE_FOUND (precedent confirmed; the directive's "absent" was wrong),
  but NOT plug-and-play — see Analogue 2 for the route Mathlib itself actually uses.

### Analogue: `ModuleCat.extendScalars.Monoidal` + `Monoidal/Adjunction.lean` (the sectionwise model — and Mathlib's OWN recipe)
- **Domain**: commutative algebra / ModuleCat — base change of modules.
- **Same structural problem there**: extension of scalars `extendScalars f : Mod R → Mod S`
  along `f : R →+* S` (the LEFT adjoint of `restrictScalars`) is the affine, sectionwise
  model of pullback; it must be strong monoidal.
- **Technique — and the decisive observation**: Mathlib does **NOT** get the LEFT adjoint's
  monoidal structure from the adjunction. In `Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean`:
  - `instance : (extendScalars f).Monoidal` (line 42) is built **explicitly** via
    `Functor.CoreMonoidal.toMonoidal`, with the tensorator coming from the linear-algebra
    distributivity iso `TensorProduct.AlgebraTensorModule.distribBaseChange`
    (`S ⊗_R (M ⊗_R N) ≅ (S⊗_R M) ⊗_S (S⊗_R N)`). This is a genuine *iso*, hence STRONG.
  - `instance : (restrictScalars f).LaxMonoidal := (extendRestrictScalarsAdj f).rightAdjointLaxMonoidal`
    (line 102) — the RIGHT adjoint's lax structure is THEN derived from the adjunction.
  So the Mathlib-endorsed pattern is: **build the left adjoint's strong-monoidal structure
  concretely (CoreMonoidal + a distributivity iso), and derive the right adjoint's lax
  structure from the adjunction — not the other way round.**
- **Mapping to project**: build a *concrete* strong-monoidal pullback
  `P := sheafify ∘ (presheaf base-change)` (presheaf base change = sectionwise `extendScalars`,
  whose strong monoidal structure is the lemma above; sheafification is monoidal — the project
  already has the brick `sheafifyTensorUnitIso`), show `P ⊣ pushforward`, then transport the
  monoidal structure to the abstract `pullback` via uniqueness of left adjoints
  (`Adjunction.leftAdjointUniq` — the project already used this in iter-217 to close
  `tensorObj_restrict_iso`). The directive's "no sectionwise formula" obstacle is dissolved by
  `leftAdjointUniq`: the abstract adjoint is iso to any concrete one, and the monoidal
  structure transports along that iso.
- **Porting cost**: HIGH but this is the *honest* cost of strong-monoidality, which no route
  avoids. Ingredients mostly present: `distribBaseChange` ✓, sheafification-monoidal brick ✓,
  `leftAdjointUniq` ✓, `pullbackPushforwardAdjunction` ✓. Missing: the concrete presheaf
  base-change pullback as a monoidal functor + the monoidal transport along `leftAdjointUniq`.
- **Verdict**: ANALOGUE_FOUND — the route the project should actually follow.

### Analogue: `Module.Invertible` / `CommRing.Pic` localization-stability (Q2 locally-free route)
- **Domain**: commutative algebra — Picard group of a ring.
- **Same structural problem there**: invertibility of a module is stable under base change /
  localization: `Module.Invertible.instLocalizationLocalizedModule`
  (`Mathlib/RingTheory/PicardGroup.lean`) — `[Module.Invertible R M] ⊢
  Module.Invertible (Localization S) (LocalizedModule S M)`. Plus
  `Module.Invertible.free_iff_linearEquiv`, `mk_eq_one_iff_free` characterize invertible =
  locally-free-rank-1.
- **Technique**: stalk-/localization-local reasoning: invertibility checked after base change
  to local rings, where invertible ⇔ free of rank 1.
- **Mapping to project**: the project ALREADY has the "pullback preserves local triviality"
  half — `IsLocallyTrivial.pullback` (`LineBundlePullback.lean:156`, DONE). So the Q2 route
  reduces to the bridge `IsLocallyTrivial M → IsInvertible M` (build the tensor-inverse of a
  locally-trivial sheaf), which is the project's KNOWN-STUCK arc
  (`dual_restrict_iso`/`exists_tensorObj_inverse`, demoted per [[ts232-carrier-pivot]]).
- **Porting cost**: HIGH and OFF the project's chosen path. Mathlib's results are over a single
  ring, not sheaves; there is NO Mathlib "stalk of the *abstract* pullback ≅ tensor of stalks"
  (only `Scheme.Modules.restrictStalkNatIso` for OPEN IMMERSIONS, not general `f`). The
  locally-free⇒tensor-invertible gluing remains the gap.
- **Verdict**: PARTIAL_ANALOGUE — higher cost/risk than the monoidal route; do not prefer.

## Important negative result (kills a tempting shortcut)
"Oplax/lax monoidal functors preserve invertible objects automatically" is **FALSE**. Global
sections `Γ` is lax monoidal yet sends line bundles to modules that need not be invertible
(e.g. `Γ(P¹, O(1)) = 0`). So even after obtaining the oplax `δ` from `leftAdjointOplaxMonoidal`,
one cannot skip proving `δ` is an iso. Strong monoidality on the relevant objects is genuinely
required; there is no free preservation lemma to lean on.

## Top suggestion
Mirror Mathlib's own recipe from PR #36599 (Analogue 2). Read
`Mathlib/Algebra/Category/ModuleCat/Monoidal/Adjunction.lean` (especially the
`(extendScalars f).Monoidal` instance at line 42 and `restrictScalars.LaxMonoidal` at line 102)
together with `Adjunction.leftAdjointOplaxMonoidal` in
`Mathlib/CategoryTheory/Monoidal/Functor.lean:1009`. Then in the project: build a *concrete*
strong-monoidal presheaf-level pullback (sectionwise `extendScalars` via
`AlgebraTensorModule.distribBaseChange`, sheafified using the existing `sheafifyTensorUnitIso`
brick), prove it left-adjoint to `pushforward`, and transport its `Monoidal` structure to the
abstract `Scheme.Modules.pullback` along `Adjunction.leftAdjointUniq` (already used in iter-217).
That yields `pullbackTensorIso` as a genuine iso. Do NOT attempt to derive the left adjoint's
structure from a (still-unbuilt) lax pushforward — that is the wrong direction and Mathlib avoids
it. First project file to touch: a new monoidal-pullback file feeding
`AlgebraicJacobian/Picard/LineBundlePullback.lean`.
