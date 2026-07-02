# Analogy: how to get the tensor-inverse object `Linv` for a locally-trivial `X.Modules`

## Mode
api-alignment

## Slug
ts219dual

## Iteration
219

## Question

To prove `exists_tensorObj_inverse` (every locally-trivial `L : X.Modules` has a
locally-trivial `Linv` with `tensorObj L Linv ≅ 𝒪_X`), we must CONSTRUCT an inverse
object. (1) Does Mathlib provide an internal-hom/dual for `PresheafOfModules R` /
`SheafOfModules R` landing back in modules? (2) Is there a line-bundle-specific
shortcut for the inverse (how does `Module.Invertible`/`CommRing.Pic` get the inverse
over a fixed ring, and does its shape port sheaf-locally)? (3) Does Mathlib have
object-level descent/gluing for `SheafOfModules` or sheaves valued in a category?
(4) Verdict + concrete bounded recipe + cost.

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean:1390` — `exists_tensorObj_inverse` (the sorry).
- `…:991` — `tensorObj` (sheafification of presheaf tensor; the build the dual should mirror — and CAN'T).
- `…:1257` — `tensorObj_restrict_iso` (CLOSED iter-217; downstream local→global bookkeeping).
- `informal/exists_tensorObj_inverse.md` — iter-218 blocker report.

## Decisions identified

### Decision 1: internal-hom / dual object for `PresheafOfModules` / `SheafOfModules`

- **Mathlib idiom (fixed ring only)**: over a FIXED ring `R`, the internal hom of
  `ModuleCat R` IS built: `instance : MonoidalClosed (ModuleCat.{u} R)` with
  `ihom M = linearCoyoneda … (op M)`, i.e. `ihom M N = (M ⟶ N)` as an `R`-module, and
  `ihom M 𝟙_ = Module.Dual R M = M →ₗ[R] R`. Cite:
  `Mathlib/Algebra/Category/ModuleCat/Monoidal/Closed.lean:39` (instance), `:52` (`ihom_map_apply`).
- **For the VARYING-ring case (what the project needs)**: ABSENT at EVERY level.
  - No `MonoidalClosed (PresheafOfModules R)`, no `MonoidalClosed (SheafOfModules R)`
    (re-confirmed: `loogle PresheafOfModules.internalHom` → 0 results; the
    `…/ModuleCat/Presheaf/` directory has `Monoidal.lean` (the tensor) but NO
    `Closed`/`InternalHom`/`Dual` file; same for `…/ModuleCat/Sheaf/`).
  - There is no presheaf-level dual to sheafify either, so this is **NOT** a
    "build-presheaf-then-sheafify" mirror of `tensorObj`. `tensorObj` sheafifies cleanly
    because the presheaf tensor `PresheafOfModules.Monoidal.tensorObj` is COVARIANT in
    the restriction maps. The dual/internal-hom is CONTRAVARIANT in the restriction
    (`U ↦ Hom_{R(U)}(M(U),R(U))` is not a presheaf in the covariant direction); the
    correct object is the slice/end formula `ℋom(M,N)(U) = (M|_U ⟶ N|_U)`, whose
    construction IS the hard part. So the iter-217 H1 precedent ("de-sheafify an existing
    sheaf-level decl") does NOT apply — there is no parallel API at any level to mirror.
- **Gap**: divergent-and-absent (Mathlib has the fixed-ring idiom but nothing for the
  varying structure sheaf).
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL**.

### Decision 2: line-bundle-specific inverse — port the `Module.Dual` shape sheaf-locally?

- **Mathlib idiom (fixed ring)**: the inverse of an invertible `R`-module `M` IS its
  linear dual. `Module.Invertible R M : Prop := Function.Bijective (contractLeft R M)`
  (`Mathlib/RingTheory/PicardGroup.lean:78`); the contraction
  `Module.Dual R M ⊗[R] M ≃ₗ[R] R` is `Module.Invertible.linearEquiv` (`:84`); the dual
  is itself invertible: `instance : Module.Invertible R (Dual R M)` (`:169`). So Mathlib's
  fixed-ring inverse object is **`Module.Dual R M = M →ₗ[R] R = ihom M 𝟙_`** — i.e. the
  SAME internal hom as Decision 1, specialised to target `R`.
- **Does the shape port?** Sheaf-locally `L|_{U_i} ≅ 𝒪_{U_i}`, and the dual of the
  trivial module is trivial, so each LOCAL inverse is just `𝒪_{U_i}`. But ASSEMBLING a
  global `Linv` from the local `𝒪_{U_i}` along the inverse-transpose transitions
  `g_{ij}⁻ᵀ` is exactly object-level descent (Decision 3). The only way to get a global
  inverse WITHOUT descent is a global dual formula — which is the internal hom
  (Decision 1). So Decision 2 is not an independent cheaper route: it collapses into
  Decision 1 (global formula) or Decision 3 (local-then-glue). The predicate being purely
  existential (`∃ Linv, …`) does NOT help — you must still construct at least one object.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (same gap as Decision 1; no fixed-ring shortcut
  evades the object-construction problem).

### Decision 3: object-level descent / gluing for `SheafOfModules`

- **Mathlib idiom (NEW, 2025, Riou–Merten)**: there IS now an abstract effective-descent
  framework. `CategoryTheory.Pseudofunctor.DescentData F f` is the category of objects
  over a cover `{X i ⟶ S}` with cocycle descent data
  (`Mathlib/CategoryTheory/Sites/Descent/DescentData.lean:57`); the typeclass
  `Pseudofunctor.IsStack F J` says the descent functors are essentially surjective
  (`…/Descent/IsStack.lean:49`), and `isEquivalence_toDescentData` (`IsStack.lean:70`)
  gives effectivity: descent data ⇒ a global object with prescribed restrictions. This is
  precisely the route-(II) primitive in the blocker report — assemble a global object from
  a cover + cocycle.
- **BUT the connection to modules is ABSENT**: there is NO `IsStack` instance for the
  module-sheaf pseudofunctor — `grep IsStack` across Mathlib finds it ONLY inside
  `Sites/Descent/*`; nothing for `SheafOfModules` / `QuasiCoherent` / `Scheme.Modules`.
  There is no constructed pseudofunctor `LocallyDiscrete (Opens X)ᵒᵖ ⥤ᵖ Cat`,
  `U ↦ modules on U`, to feed it. The one module-flavoured descent file,
  `Mathlib/Algebra/Category/ModuleCat/Descent.lean`, is FIXED-ring faithfully-flat
  comonadic descent (extension of scalars), and even there effectivity is an explicit
  `TODO` — it is not Zariski-local object gluing on `Opens X`.
- **Gap**: framework present, instance absent. Building the restriction pseudofunctor +
  proving `IsStack` for the small Zariski site is a large multi-file effort (the
  `DescentData` structure carries `hom`/`pullHom_hom`/`hom_self`/`hom_comp` cocycle fields;
  the pseudofunctor needs coherent restriction-of-restriction isos).
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (principled long-term route; heavier than a
  bounded build).

## Recommendation

All three faces are the SAME missing object and all render **NEEDS_MATHLIB_GAP_FILL**.
The fixed-ring shape is fully known (`Module.Dual` = `ihom M 𝟙_`), and porting it needs
EITHER a sheaf internal-hom of modules (Decision 1/2) OR connecting `SheafOfModules` to
the new `Pseudofunctor.IsStack` framework (Decision 3). Neither is a bounded
iter-217-style `mathlib-build`: the iter-217 H1 was bounded only because the sheaf-level
pushforward adjunction already existed and was de-sheafified — here the internal hom is
absent at presheaf, sheaf, AND general-categorical level, so there is no parallel API to
mirror, and the dual is contravariant so it is not even a "sheafify the presheaf" job.
This is a genuinely LARGE multi-iter swath (comparable to / larger than the abandoned d.2
stalk-⊗ effort). The realistic call is to NOT fund the dual build on Lane TS as a bounded
objective: either (a) commit to a multi-iter infrastructure block (recommend Decision 1:
build the presheaf/sheaf internal-hom of modules, ~several hundred LOC across iters), or
(b) escalate to USER for a strategic re-route that does not need the abstract tensor-inverse
object (e.g. the divisor-class `Pic⁰` route noted in project memory). Decision 3 (stack
framework) is the most principled and reusable if a heavy build is funded, but is the
largest.
