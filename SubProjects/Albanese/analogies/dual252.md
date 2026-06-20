# Analogy: pushforward-along-a-ring-iso commutes with the presheaf dual `ℋom(–,𝟙_)`

## Mode
api-alignment

## Slug
dual252

## Iteration
252

## Question
For the Step-4 residual of `dual_restrict_iso` (`AlgebraicJacobian/Picard/TensorObjSubstrate/DualInverse.lean:254`):
```
(pushforward β).obj (PresheafOfModules.dual M.val) ≅ PresheafOfModules.dual ((pushforward β).obj M.val)
```
(`β` sectionwise the open-immersion ring iso `𝒪_Y(V) ≅ 𝒪_X(fV)`):
1. Does Mathlib have an idiom for "pushforward along a sectionwise ring iso commutes with the internal-hom dual" for `PresheafOfModules`?
2. What is the precise `isoMk` skeleton, mirroring the closed H2 step of `tensorObj_restrict_iso`?
3. Is `InternalHom.restrictScalarsRingIsoDualEquiv` the right ingredient, or is there a more direct `restrictScalars`-vs-`dual` commutation in Mathlib?

## Project artifact(s)
- `DualInverse.lean:228-254` — `dual_restrict_iso`; one `sorry` at the Step-4 presheaf residual.
- `PresheafInternalHom.lean:234-266` — `restrictScalarsRingIsoDualEquiv` (the proposed atom; CLOSED, axiom-clean).
- `PresheafInternalHom.lean:893-896` — `PresheafOfModules.dual M = internalHom M 𝟙_` (slice internal hom).
- `PresheafInternalHom.lean:628-674` — `homModule`/`internalHomObjModule`: dual section value `(dual M).obj (op U) = (restr U M ⟶ restr U 𝟙_)`, a **slice Hom over `Over U`**, NOT a single linear dual.
- `PresheafInternalHom.lean:504-513` — `restrictScalarsMonoidalOfBijective` (the H2 atom of the *tensor* lane, for comparison).

## Decisions identified

### Decision 1: Does Mathlib supply the pushforward-vs-dual idiom for `PresheafOfModules`?

- **Mathlib idiom**: NONE. Mathlib has `PresheafOfModules.pushforward₀` / `pushforward`
  (`Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward`) and the sheaf-level
  `SheafOfModules.pushforward*`, but **no internal hom, no dual, and no `MonoidalClosed`
  instance for `PresheafOfModules`** — verified: `loogle "MonoidalClosed (PresheafOfModules ?R)"`
  returns no results. The entire `PresheafOfModules.dual = ℋom(–,𝟙_)` slice construction
  (`internalHom`, `homModule`, `restr`) is project-local. So there is *nothing upstream to
  commute pushforward against*.
- **Project's path**: build the iso by hand sectionwise.
- **Gap**: divergent-and-necessary (the upstream object does not exist).
- **Verdict**: NEEDS_MATHLIB_GAP_FILL (expected; the gap is genuinely upstream).

### Decision 2: Is the prover's "close sectionwise via `restrictScalarsRingIsoDualEquiv`" faithful to the tensor lane's H2?

- **Mathlib idiom for the *shape***: the abstract route does exist —
  `CategoryTheory.Monoidal.Rigid.OfEquivalence.hasRightDualOfEquivalence`
  (`Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence`) transports a right dual along a
  strong-monoidal equivalence. But it requires the project's `dual` to *be* the rigid-category
  right dual of a registered `MonoidalCategory` + rigid structure on `PresheafOfModules`, which
  does not exist. Porting cost is prohibitive — not the path.
- **Why the tensor-lane analogy is NOT faithful**: the H2 step of `tensorObj_restrict_iso`
  worked because **Mathlib's `tensorObj` is sectionwise**: `(M ⊗ N)(X) = M(X) ⊗ N(X)`, so the
  presheaf tensorator of `restrictScalars β` reduces, section by section, to
  `ModuleCat.restrictScalars`'s tensorator (= `restrictScalarsRingIsoTensorEquiv`), packaged as
  `restrictScalarsMonoidalOfBijective`. **The project `dual` is NOT sectionwise**: its value
  `(dual M)(U) = (restr U M ⟶ restr U 𝟙_)` is a Hom of presheaves over the *whole down-set*
  `Over U`, not a fiber at `U`. So there is no clean sectionwise reduction of "pushforward
  commutes with dual" to a single `ModuleCat`-level fact.
- **The actual decomposition of the residual** (at section `V : (Opens Y)ᵒᵖ`):
  ```
  ((pushforward β).obj (dual M.val)).obj V
      = restrictScalars (β.app V) ( Hom_{Over fV}(restr fV M.val, restr fV 𝟙_X) )   -- 𝒪_X(fV)→𝒪_Y(V)
  (dual ((pushforward β).obj M.val)).obj V
      =                          Hom_{Over V} (restr V (pushβ M.val), restr V 𝟙_Y)    -- over 𝒪_Y(V)
  ```
  Going from the first to the second couples **two** transports that `tensorObj` never needed:
  - **(B) ring-iso reconciliation of the unit codomain** `𝒪_X(fV) ≅ 𝒪_Y(V)` — THIS is exactly
    what `restrictScalarsRingIsoDualEquiv` does (its codomain is hardcoded to the ground ring =
    the monoidal unit, matching `dual`'s `𝟙_`). ✓ right atom.
  - **(A) slice-site transport** of the *domain* presheaf: `restr V (pushβ M.val)` over
    `Over V` (in `Opens Y`) ↔ `restr fV M.val` over `Over fV` (in `Opens X`), under the
    fully-faithful `f.opensFunctor` restricted to the down-set of `fV`. This is a genuine,
    NON-sectionwise build. `restrictScalarsRingIsoDualEquiv` does NOT touch it; the directive's
    banned `overSliceSheafEquiv` was the natural-but-wrong-level tool for it (Sheaf cat / fixed
    value cat). The dual's slice-Hom is NOT a single linear dual (the `restr U M ⟶ restr U 𝟙_`
    carries down-set-wide compatibility data beyond the terminal-section functional
    `M(U) →ₗ 𝒪(U)`), so (A) cannot be elided.
- **Gap**: the prover's framing ("sectionwise via `restrictScalarsRingIsoDualEquiv`")
  **under-scopes** by omitting leg (A). `restrictScalarsRingIsoDualEquiv` is leg (B) only.
- **Verdict**: DIVERGE/GAP — the residual needs (A)+(B); the atom supplies (B).

### Decision 3: Is there a more direct `restrictScalars`-vs-`dual` `LinearEquiv` in Mathlib?

- **Mathlib idiom**: NO. `LinearMap.restrictScalars` / `LinearEquiv.restrictScalars`
  (`Mathlib.Algebra.Module.LinearMap.Defs`, `Mathlib.Algebra.Module.Equiv.Basic`) are gated on
  `LinearMap.CompatibleSMul M N R S` — a **scalar-tower** situation (`R → S`, *same* modules,
  codomain unchanged). The dual swap `(M →ₗ[S] S) → (M →ₗ[R] R)` changes the codomain `S ↝ R`,
  which is only possible via a ring *isomorphism* `e : R ≃+* S` carrying `S` back to `R` — not a
  `CompatibleSMul` instance. Mathlib has no `Module.Dual`-vs-`restrictScalars` commutation of
  this codomain-swapping kind.
- **Project's path**: `restrictScalarsRingIsoDualEquiv` (CLOSED, axiom-clean). It is the
  correct and necessary atom; keep it.
- **Verdict**: PROCEED (project lemma is the right primitive).

## Recommendation

`restrictScalarsRingIsoDualEquiv` **is** the correct ring-iso atom (leg B) — the faithful
`ModuleCat`-level dual analogue of `restrictScalarsRingIsoTensorEquiv`, NOT of the *presheaf*-level
`restrictScalarsMonoidalOfBijective`. But the Step-4 residual is **not** sectionwise-closable by it
alone: it additionally needs the **slice-site transport (leg A)** identifying `restr V (pushβ M.val)`
over `Over V ⊂ Opens Y` with `restr fV M.val` over `Over fV ⊂ Opens X` across the open immersion —
the part `tensorObj_restrict_iso` never needed because `tensorObj` is sectionwise and `dual` is not.

Concrete build (mirror of the H2 plumbing, swapping in the slice transport):
```
PresheafOfModules.isoMk
  (app := fun V => (sliceDualTransport f M V).toModuleIso)     -- 𝒪_Y(V)-LinearEquiv
  (naturality := fun {V W} g => /- thin poset Opens Y: Subsingleton.elim, as in dualUnitIsoGen -/)
```
where `sliceDualTransport f M V :`
```
  restrictScalars (β.app V) (restr fV M.val ⟶ restr fV 𝟙_X)
    ≃ₗ[𝒪_Y(V)] (restr V (pushβ M.val) ⟶ restr V 𝟙_Y)
```
is assembled as **(A) slice equivalence Hom-transport ≪ₗ (B) `restrictScalarsRingIsoDualEquiv`**.
The load-bearing field is the construction of `sliceDualTransport` (leg A), NOT the outer
`isoMk` naturality (which is thin-poset-trivial, exactly as in `dualUnitIsoGen` /`dualIsoOfIso`).

Leg (A) must be built at the **PresheafOfModules / varying-ring** level (the slice value of
`internalHom`), so it is a genuine new build — but it is a *down-set restriction of the open
immersion's fully-faithfulness*, not a missing Mathlib import. The planner should scope leg (A)
as a standalone verified lemma FIRST (a presheaf-level `restr`-vs-`f.opensFunctor` base-change /
Beck–Chevalley square over the slice), then compose with `restrictScalarsRingIsoDualEquiv`.

Alternative worth weighing before committing to (A): derive `dual_restrict_iso` from the already
-closed `tensorObj_restrict_iso` by **uniqueness of monoidal inverses** (dual = ⊗-inverse), using
the eval/coeval naturality — this sidesteps the slice transport entirely if the inverse-uniqueness
glue is cheaper than leg (A). Flagged, not verified.
