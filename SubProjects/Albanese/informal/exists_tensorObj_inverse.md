# Blocker report: `AlgebraicGeometry.Scheme.Modules.exists_tensorObj_inverse`

**File:** `AlgebraicJacobian/Picard/TensorObjSubstrate.lean` (L1375)
**Iter:** 218 (PRIMARY critical-path objective)
**Verdict:** INFRASTRUCTURE MISSING — the INCOMPLETE gate of PROGRESS.md fired.
The informal agent was called (`--provider auto`, MOONSHOT key set) but returned
HTTP 401 *Invalid Authentication*, so no external sketch is available; the
analysis below is derived from the on-disk Mathlib API.

## Goal

```lean
lemma exists_tensorObj_inverse {X : Scheme.{u}} {L : X.Modules}
    (hL : LineBundle.IsLocallyTrivial L) :
    ∃ Linv : X.Modules, LineBundle.IsLocallyTrivial Linv ∧
      Nonempty (tensorObj L Linv ≅ SheafOfModules.unit X.ringCatSheaf)
```

`X.Modules = SheafOfModules X.ringCatSheaf`; `tensorObj` is the substrate tensor
(sheafification of `PresheafOfModules.Monoidal.tensorObj`); the unit is
`SheafOfModules.unit X.ringCatSheaf = 𝒪_X`. `IsLocallyTrivial M` = for every
`x` an affine open `U ∋ x` with `M.restrict U.ι ≅ 𝒪_U`.

## Blueprint route (`lem:tensorobj_inverse_invertible`) and where it bottoms out

The blueprint sets `Linv := ℋom_{𝒪_X}(L, 𝒪_X)` (the internal hom / dual),
shows it is locally trivial, and produces the contraction/evaluation
`ε_L : L ⊗_X Linv → 𝒪_X`, `s ⊗ φ ↦ φ(s)`, which is a local iso (= left unitor on
the trivialising cover) and hence a global iso since "is-an-iso" is local.

**The construction is blocked at its FIRST step**, before any tactic state can be
advanced (one cannot even `refine ⟨Linv, ?_, ?_⟩` because `Linv` cannot be named):

1. **Missing primitive A — the internal hom object `ℋom_{𝒪_X}(L, 𝒪_X)` as a
   `SheafOfModules`.** Mathlib at `b80f227` has
   - NO `MonoidalClosed (SheafOfModules R)` instance,
   - NO `MonoidalClosed (PresheafOfModules R)` instance (verified absent: `loogle`
     `MonoidalClosed (PresheafOfModules ?R)` → no results; the file's §2 comment
     records the same "verified-absent `MonoidalClosed (PresheafOfModules R₀)`
     wall"),
   - NO `SheafOfModules`-level internal-hom / dual / `ihom` construction
     (`CategoryTheory.sheafHom` produces a `Sheaf J (Type …)`, NOT a
     `SheafOfModules`; it carries no `𝒪_X`-module structure).

   So the dual object `Linv` has no `Scheme.Modules`-level construction.

2. **Missing primitive B — the evaluation/contraction morphism**
   `L ⊗_X ℋom(L,𝒪_X) → 𝒪_X` is the counit of the (absent) internal-hom
   adjunction; it has no construction either.

3. **No monoidal-category escape hatch.** The standard categorical route
   ("an invertible object of a monoidal category has a two-sided inverse",
   e.g. dualizable/rigid-object API) is unavailable *by design*: the project
   deliberately does **not** build `MonoidalCategory (X.Modules)` for the varying
   structure sheaf (see `rem:scheme_modules_monoidal_off_path` and memory
   `commring-pic-is-skeleton-route`). So there is no monoidal structure to read an
   inverse off of.

4. **No object-gluing/descent fallback.** The alternative — glue a global `Linv`
   from local `𝒪_{U_i}` pieces along transition functions `g_{ij}^{-1}` — needs
   *object-level descent* for `SheafOfModules` (build a global object from a cover +
   cocycle). Mathlib has section-level gluing (`TopCat.Sheaf.existsUnique_gluing`)
   and the "iso is local" fact (`MorphismProperty.isomorphisms.IsLocalAtTarget` for
   subcanonical `J`, `Sheaf.isLocallyBijective_iff_isIso`), but **no construction
   that assembles a global `SheafOfModules` object from local objects + transition
   isos**. So the gluing route is also Mathlib-absent.

## Exact missing ingredient (for `mathlib-build` / `mathlib-analogist`)

Either of the following would unblock the PRIMARY; **(I) is the blueprint's route**:

- **(I) Internal hom / dual for `SheafOfModules R`** (or for `PresheafOfModules R`
  then sheafify, mirroring how `tensorObj` sheafifies the presheaf tensor):
  a functor `ℋom : (SheafOfModules R)ᵒᵖ × SheafOfModules R ⥤ SheafOfModules R`
  (at least its action `M ↦ ℋom(M, 𝒪_X)` and the evaluation
  `M ⊗ ℋom(M,𝒪_X) → 𝒪_X`), i.e. a `MonoidalClosed` structure or a bespoke dual.
  Statement of the precise object needed:
  ```
  def AlgebraicGeometry.Scheme.Modules.dual {X : Scheme.{u}} (M : X.Modules) :
      X.Modules                                   -- ℋom_{𝒪_X}(M, 𝒪_X)
  def AlgebraicGeometry.Scheme.Modules.eval {X : Scheme.{u}} (M : X.Modules) :
      tensorObj M (dual M) ⟶ SheafOfModules.unit X.ringCatSheaf   -- s ⊗ φ ↦ φ(s)
  ```
  Then: `dual` of a locally-trivial `M` is locally trivial (internal hom commutes
  with open-immersion restriction + dual of free rank-one is free rank-one), and
  `eval` is a local iso (= contraction `𝒪_U ⊗ 𝒪_U ≅ 𝒪_U`, the left unitor) hence
  a global iso by `tensorObj_restrict_iso` (CLOSED) + "iso is local".

- **(II) Object-level descent for `SheafOfModules`:** a construction taking an open
  cover `{U_i}` of `X`, objects `M_i : (U_i).Modules`, and transition isomorphisms
  `M_i|_{U_i ∩ U_j} ≅ M_j|_{U_i ∩ U_j}` satisfying the cocycle condition, and
  producing a global `M : X.Modules` with `M|_{U_i} ≅ M_i`. With `M_i = 𝒪_{U_i}`
  and `g_{ij}^{-1}` transitions this builds `Linv` directly.

## Downstream steps that ARE available once `Linv`/`eval` exist

`tensorObj_restrict_iso` (CLOSED, iter-217), `tensorObj_unit_iso`,
`restrictIsoUnitOfLE`, and `tensorObj_isLocallyTrivial` (CLOSED) already supply the
local-triviality of `Linv` and the local-iso-⟹-global-iso bookkeeping (mirror the
existing `tensorObj_isLocallyTrivial` proof at L1349). The ONLY genuinely absent
pieces are A and B (the dual object and its evaluation).

## Recommendation

Assign primitive (I) [`SheafOfModules` internal-hom/dual + evaluation] in
`mathlib-build` mode (it is the blueprint's route and the smaller of the two; the
presheaf-level internal hom + sheafification mirrors the existing `tensorObj`
build). Per the progress-critic ts218 PRE-CAUTION, this is the mathlib-analogist
trigger to run before iter-220 — do NOT push a `dual`-shaped helper-sorry into
`exists_tensorObj_inverse` (the iter-214 d.1 anti-pattern).
