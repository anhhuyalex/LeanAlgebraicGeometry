# Analogy: the invertible-scoped associator for `Scheme.Modules.tensorObj` — which realization avoids the `MonoidalClosed` wall

## Mode
api-alignment

## Slug
ts-assoc-gate210

## Iteration
210

## Question
Scope the `⊗_X` associator `(M⊗N)⊗P ≅ M⊗(N⊗P)` to INVERTIBLE (locally-free rank-1,
hence flat) objects only — all the relative-Picard group law consumes. Under that
scope: (1) is the associator existence-iso buildable from PRESENT Mathlib WITHOUT
`MonoidalClosed (PresheafOfModules R₀)`? (2) which of three realizations —
(1) local-trivialization gluing, (2) flat-exactness whiskerLeft, (3) `J.W.IsMonoidal`
on the flat subcategory — should we formalize? (3) does realization (1) genuinely
avoid the absorption-iso wall, or does the global gluing secretly re-invoke it?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjSubstrate.lean`:199–202 — `tensorObj M N :=
  sheafification(PresheafOfModules.Monoidal.tensorObj M.val N.val)`.
- `TensorObjSubstrate.lean`:330–399 — `tensorObj_restrict_iso` (the restriction-
  compatibility iso) is a typed `sorry`; its residual (lines 357–398) is the
  H1/H2 decomposition: (H1) a presheaf-level `pushforward β ≅ pullback φ` adjunction,
  (H2) `restrictScalars` along a ring iso is strong monoidal — both absent from
  Mathlib, both flatness-INDEPENDENT.
- `TensorObjSubstrate.lean`:412–425 — `tensorObj_isLocallyTrivial` (blueprint
  `lem:tensorobj_preserves_locally_trivial`, the cited "already proven" precedent
  for realization (1)); its proof at L423 CALLS `tensorObj_restrict_iso`.
  **`lean_verify` reports `sorryAx` in its axiom set** — it is NOT actually proven.
- blueprint `Picard_TensorObjSubstrate.tex`:531–578 — `lem:tensorobj_assoc_iso`,
  currently ARBITRARY `M,N,P`, `% NOTE` admits the absorption-iso/`MonoidalClosed` route.
- blueprint L795 `def:scheme_modules_isinvertible`; L859 `lem:tensorobj_isoclass_commgroup`.

## Decisions identified

### Decision 1: which realization of the invertible-scoped associator

The associator nests an inner sheafification inside the presheaf tensor on both sides:
`(M⊗N)⊗P = a( a(M.val ⊗ᵖ N.val).val ⊗ᵖ P.val )` where `a = PresheafOfModules.sheafification`.
Transporting the presheaf associator `α` needs, besides `a.mapIso(α)`, the
**absorption iso** `a(a(A).val ⊗ᵖ B) ≅ a(A ⊗ᵖ B)` (and its mirror) = whiskering-stability
of the sheafification localizer `J.W`: `J.W g → J.W (B ◁ g)`.

- **Mathlib idiom**. Mathlib's general whiskering-stability of a sheafification localizer
  is `CategoryTheory.GrothendieckTopology.W.whiskerLeft`
  (`Mathlib.CategoryTheory.Sites.Monoidal`), whose signature **requires
  `[MonoidalClosed A]`** plus enriched-hom instances on `Cᵒᵖ ⥤ A`. For invertibility/Picard,
  Mathlib instead scopes to a *predicate on objects* — `Module.Invertible R M`
  (`Mathlib.RingTheory.PicardGroup`) — and derives `Module.Invertible.instFinite`,
  `Module.Invertible.instProjective`, hence `Module.Flat.of_projective` (all present), so the
  invertible/line-bundle objects are FLAT, and flat-exactness replaces the closed structure.
- **Realization (1) — local-trivialization gluing**. To build `(M⊗N)⊗P ≅ M⊗(N⊗P)` by gluing
  structure-sheaf associators on a trivialising cover, you must first identify
  `((M⊗N)⊗P).restrict W` with the affine triple tensor — i.e. invoke
  `tensorObj_restrict_iso`. That lemma is a `sorry`; its residual (H1/H2, file L357–398) is
  the strong-monoidal-pushforward / `restrictScalars`-along-ring-iso infrastructure,
  **absent from Mathlib and flatness-INDEPENDENT** (H2 is about the open-immersion ring iso
  `f.appIso`, not about M,N,P). So scoping M,N,P to invertible does **not** lighten it.
  The cited precedent `tensorObj_isLocallyTrivial` proves only EXISTENCE of local
  trivialisations yet still routes through the same `sorry` — `lean_verify` confirms
  `sorryAx` in its axioms. **Gap: divergent-and-wrong** (renamed wall).
- **Realization (3) — `J.W.IsMonoidal` on the flat subcategory**. Gating Mathlib's
  `CategoryTheory.Sheaf.monoidalCategory` needs a `MorphismProperty.IsMonoidal J.W` instance,
  whose `whiskerLeft` field is exactly `GrothendieckTopology.W.whiskerLeft` — **`MonoidalClosed`-
  gated**. Even restricted to flat objects, instantiating Mathlib's bundled `W.IsMonoidal`
  pulls in the closed structure for ALL objects. **Gap: divergent-with-cost** (the wall, packaged).
- **Realization (2) — flat-exactness whiskerLeft (RECOMMENDED)**. Do NOT instantiate the
  bundled `W.IsMonoidal`. Prove the two specific absorption-iso *instances* directly:
  `a(η_{M⊗N} ◁ P)` is iso (P invertible⇒flat) and the mirror `a(M ▷ η_{N⊗P})` is iso
  (M invertible⇒flat), where `η = toSheafify` is the sheafification unit (in `J.W` by
  `instIsLocallyInjectiveToSheafify`). The bridge `J.W g → J.W (P ◁ g)` for FLAT P is
  elementary: via the `J.WEqualsLocallyBijective` characterisation (`Presheaf.IsLocallyInjective`
  + `IsLocallySurjective`), `P ◁ g` stays locally injective by
  `Module.Flat.lTensor_preserves_injective_linearMap` (sectionwise) and locally surjective by
  right-exactness of `⊗`. **All named ingredients present in Mathlib.** Assemble:
  `(M⊗N)⊗P ≅[a(η◁P)] a((M⊗ᵖN)⊗ᵖP) ≅[a.mapIso α] a(M⊗ᵖ(N⊗ᵖP)) ≅[a(M▷η)] M⊗(N⊗P)`.
  **Gap: divergent-equivalent → ALIGN_WITH_MATHLIB** (this is the `Module.Invertible`+flat idiom).
- **Verdict**: realization (2) — **ALIGN_WITH_MATHLIB**; realizations (1) and (3) — reject
  (both bottom out in absent Mathlib: (1) in `tensorObj_restrict_iso`'s H1/H2, (3) in
  `MonoidalClosed`).

### Decision 2: re-scope `lem:tensorobj_assoc_iso` from arbitrary `M,N,P` to invertible/flat

- **Mathlib idiom**. `Module.Invertible` is a `Prop` object-predicate; the Picard arithmetic
  (`CommRing.Pic.mk_tensor`, `mk_dual`, …) are existence-of-iso facts scoped to invertibles,
  never coherence on all modules. The flatness the bridge "needs" is FREE on invertibles
  (`Module.Invertible.instProjective` → `Module.Flat.of_projective`).
- **Project's path**. Blueprint L536 states the associator for *arbitrary* `M,N,P` with "no
  line-bundle, local-freeness or flatness hypothesis required" — which is precisely what forces
  the arbitrary-`F` whiskering-stability = `MonoidalClosed` wall (its own `% NOTE` L549–562).
- **Gap**: divergent-with-cost. The arbitrary statement is unbuildable at the pinned commit; the
  consumer `lem:tensorobj_isoclass_commgroup`/`thm:rel_pic_addcommgroup_via_tensorobj` only ever
  associates INVERTIBLE objects.
- **Verdict**: **ALIGN_WITH_MATHLIB** — re-scope the hypothesis to `IsInvertible M/N/P` (or a
  `Module.Flat`-style predicate); drop the "no flatness required" clause.

## Recommendation

Re-scope `lem:tensorobj_assoc_iso` to invertible `M,N,P` and formalize it via **realization (2)**,
the flat-exactness whiskerLeft. The associator is built as a 3-step composite —
`a(η ◁ P)` absorption (P flat), `a.mapIso` of the presheaf associator `α`, mirror `a(M ▷ η)`
absorption (M flat) — whose only non-`mapIso` content is the bridge lemma
`J.W g → J.W (P ◁ g)` for flat `P`, assembled from `Module.Flat.lTensor_preserves_injective_linearMap`
+ right-exactness through the `J.WEqualsLocallyBijective` / `IsLocallyInjective`+`IsLocallySurjective`
API (all present Mathlib). This genuinely avoids `MonoidalClosed (PresheafOfModules R₀)`.

Do **NOT** take realization (1): it reduces to the sorry'd `tensorObj_restrict_iso`, whose
residual (H1 presheaf pushforward-adjunction, H2 strong-monoidal `restrictScalars`-along-ring-iso)
is absent from Mathlib AND flatness-independent, so the invertible scope does not unlock it — the
"already proven" precedent `tensorObj_isLocallyTrivial` is itself `sorryAx`-tainted via the same
hole. Do **NOT** take realization (3): instantiating Mathlib's bundled `W.IsMonoidal` is gated on
`GrothendieckTopology.W.whiskerLeft`'s `[MonoidalClosed A]` requirement — the wall, renamed.

**Reversal signal: NOT triggered globally.** Realization (2) is a genuine present-Mathlib escape,
so the lane is alive. But the directive's *favored* realization (1) IS a renamed wall — the bridge
to build is the flat-whiskering `J.W` stability, not the structure-sheaf gluing. The remaining
prover risk is bounded and elementary (the flat-whiskering bridge ≈ 30–80 LOC over the
locally-bijective API), NOT a multi-file `MonoidalClosed`/strong-monoidal-pushforward build.
