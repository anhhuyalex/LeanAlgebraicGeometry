# `chartOverIso` — the over↔restrict trivialisation bridge (LineBundleCoherence engine)

## Statement wanted

For `X : Scheme.{u}`, `U : X.Opens`, `M : X.Modules`, and a scheme-level
trivialisation
```
e : M.restrict U.ι ≅ SheafOfModules.unit (U : Scheme).ringCatSheaf
```
construct
```
chartOverIso M U e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U).
```

This is the **single** remaining `sorry` in
`AlgebraicJacobian/Picard/LineBundleCoherence.lean` (line ~178). Everything else
in the engine is closed and axiom-clean modulo it:
`chartPresentation = unitPresentation.ofIsIso chartOverIso.inv`, and the main
theorem `IsLocallyTrivial.isFinitePresentation` + corollary `isFiniteType` are
fully assembled on top (verified: they depend only on `sorryAx` via this one
bridge; the cover/universe/QuasicoherentData plumbing is all real).

## Why it is not a one-liner (type analysis, verified in Lean)

The two objects live in **different categories**:

* `M.restrict U.ι : (U : Scheme).Modules = SheafOfModules ((U:Scheme).ringCatSheaf)`
  — base site `Opens ↥(U:Scheme)` (the open subspace), ring sheaf
  `(U:Scheme).ringCatSheaf`. This is where `e` lives.
* `M.over U = (SheafOfModules.pushforward (𝟙 _)).obj M : SheafOfModules (X.ringCatSheaf.over U)`
  — base site `(Opens.grothendieckTopology X).over U`, base category `Over U`,
  ring sheaf `X.ringCatSheaf.over U`. This is what `QuasicoherentData.presentation`
  consumes.

So `e.hom` cannot be fed to `Presentation.ofIsIso` to land in `M.over U` (the
planner's iter-257 recipe "ofIsIso e.hom" is type-incorrect — confirmed by
`lean_goal`: goal is `(SheafOfModules.over M U).Presentation` while
`e.hom : M.restrict U.ι ⟶ SheafOfModules.unit (↑U).ringCatSheaf`).

## The genuine route (Mathlib-scale)

The base categories are equivalent via the **site** equivalence
```
Opens.overEquivalence U : Over U ≌ Opens ↥U      -- Mathlib.Topology.Sheaves.Over (line 41)
```
(both legs are continuous — that is the named TODO in `Over.lean:19-22`). What is
missing is the **lift to sheaves of modules**: an equivalence
```
Φ : SheafOfModules ((U:Scheme).ringCatSheaf) ≌ SheafOfModules (X.ringCatSheaf.over U)
```
induced by `overEquivalence U` together with the identification of the two
structure-ring-sheaves, under which
```
Φ (M.restrict U.ι) ≅ M.over U      and      Φ (unit _) ≅ unit _.
```
Then `chartOverIso := Φ(e) composed with the unit-matching iso` (transport `e`
across `Φ` and reconcile units).

Required Mathlib primitives (all exist individually; assembling them is the work):
* `Opens.overEquivalence` + the (TODO) continuity of its two legs.
* `Functor.sheafPushforwardContinuous` / `SheafOfModules.pushforward` along a
  continuous functor (`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`),
  and `pushforwardPushforwardEquivalence` (used by `QuasicoherentData.bind`,
  Quasicoherent.lean:370) — the closest existing "equivalence of module
  categories from a site equivalence + ring identification" primitive.
* A ring-sheaf iso `(U:Scheme).ringCatSheaf ≅ (overEquivalence-transport of) X.ringCatSheaf.over U`.
* `restrictScalars` reconciliation for the ring-sheaf identification.

## Estimate / status

~200–350 LOC, a standalone file (the modules-level shadow of the project's
`overSliceSheafEquiv`, which exists only at the `Sheaf`-of-`Ab` level and is
proven inapplicable here because the ring varies — same conclusion as the dual
lane, see `informal/dual_restrict_iso.md`). This is the **same wall** blocking
`exists_tensorObj_inverse` (DualInverse lane). Building it once, generally, would
unblock both the engine's finiteness theorem and the dual chain.

Recommended: a `mathlib-build` sub-step producing
`SheafOfModules.overEquivalence : SheafOfModules (R.over U) ≌ SheafOfModules (Y.ringCatSheaf)`
for an open immersion `Y.ι` (or directly the `restrict ↔ over` natural iso),
then `chartOverIso` and the dual bridge both become short consumers.

## Tooling note

The informal agent (`archon-informal-agent.py`) was unavailable this iter:
`kimi` → 401 Invalid Authentication, `kimi-anthropic` → 404 url.not_found
(consistent with the standing "informal agent DOWN" note). No external sketch
obtained; the above is derived from the Mathlib source and the in-Lean type
checks performed this iter.
