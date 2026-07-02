# Analogy: closing the `dual_restrict_iso` Step-4 residual — inverse-uniqueness vs. slice Beck–Chevalley

## Mode
api-alignment

## Slug
dualstep4-257

## Iteration
257

## Question
Two precise questions about the sole residual `sorry` of `dual_restrict_iso`
(`DualInverse.lean:259`), the PresheafOfModules-level iso
`(pushforward β).obj (dual M.val) ≅ dual ((pushforward β).obj M.val)`:

1. **Cheaper alternative** — can `dual_restrict_iso` be derived from the CLOSED
   `tensorObj_restrict_iso` via *uniqueness of monoidal inverses* (dual = ⊗-inverse), using a
   Mathlib "right duals are unique" / "strong monoidal functor preserves chosen right duals"
   idiom, WITHOUT a registered `MonoidalCategory` + rigid/`MonoidalClosed` structure on
   `PresheafOfModules`?
2. **If leg (A) is unavoidable** — the cleanest Mathlib idiom for the slice Beck–Chevalley
   `restr V ((pushforward β) M.val)` over `Over V ⊂ Opens Y` ↔ `restr fV M.val` over
   `Over fV ⊂ Opens X` transported across `f.opensFunctor`, and the minimal `sliceDualTransport`
   skeleton.

## Project artifact(s)
- `DualInverse.lean:233-259` — `dual_restrict_iso`; Steps 1–3 + H1 closed, one `sorry` at the Step-4 presheaf residual.
- `DualInverse.lean:358-407` — `homLocalSection`; the existing axiom-clean thin-poset `eqToHom`-conjugation slice transport (the structural template for leg A).
- `DualInverse.lean:439-442` — `image_preimage_of_le`; the down-set identity `W.ι ''ᵁ (W.ι ⁻¹ᵁ V) = V` powering the `eqToHom`-conjugations.
- `PresheafInternalHom.lean:234-266` — `restrictScalarsRingIsoDualEquiv` (the leg-B scalar atom; CLOSED).
- `PresheafInternalHom.lean:658-674` / `893-896` — `restr` (= `pushforward₀ (Over.forget U)`), `dual M = internalHom M 𝟙_`; the slice-Hom value is NOT a single linear dual.
- `Vestigial.lean:617-718` — `overSliceSheafEquiv = (Opens.overEquivalence U).sheafCongr A`; the Sheaf/fixed-value-cat version proven INAPPLICABLE here.

## Decisions identified

### Decision 1: Route (1) — derive `dual_restrict_iso` from `tensorObj_restrict_iso` by inverse-uniqueness

- **Mathlib idiom (the shape exists)**: `CategoryTheory.hasRightDualOfEquivalence`
  (`Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence`) — transports a right dual along a
  strong-monoidal equivalence; `CategoryTheory.rightDualIso`
  (`Mathlib.CategoryTheory.Monoidal.Rigid.Basic`) — `ExactPairing X Y₁ → ExactPairing X Y₂ → Y₁ ≅ Y₂`,
  the canonical uniqueness of right duals. Both are the *correct abstract statements* of
  "duals/inverses are unique and preserved".
- **Why it is NOT applicable** — `hasRightDualOfEquivalence`'s signature requires, simultaneously:
  1. `[MonoidalCategory C]` and `[MonoidalCategory D]`. **ABSENT**: `loogle "MonoidalCategory
     (PresheafOfModules ?R)"` → no results; `loogle "MonoidalClosed (PresheafOfModules ?R)"` →
     no results. The project carries its monoidal structure entirely by hand
     (`PresheafOfModules.Monoidal.tensorObj`, `Scheme.Modules.tensorObj`) precisely because
     no `MonoidalCategory` instance exists to register a `HasRightDual`/`ExactPairing` against.
  2. `[F.Monoidal]` — F (restriction along the open immersion) must be **strong** monoidal.
     The project only has it as **lax/oplax** (`restrictScalarsLaxMonoidal`, the oplax `δ` of
     `pullback`); the comparison `δ` is NOT an iso in general (this is the recurring wall of the
     whole tensor lane). Not strong.
  3. `[F.IsEquivalence]` — F must be an **equivalence**. Restriction along a non-surjective open
     immersion is a localization, **not** an equivalence of module categories. Fails outright.
  4. `HasRightDual X` / `ExactPairing M (dual M)` — `dual M = internalHom(M, 𝟙_)` is a
     categorical right dual only when `M` is **dualizable** (locally free of rank 1). It supplies
     an evaluation (`internalHomEval`) but **no coevaluation** `𝟙_ → dual M ⊗ M` and no zig-zag
     for general `M`. Crucially `dual_restrict_iso` is stated for **general `M`**, where the
     inverse-uniqueness argument is not even mathematically valid.
- **Even restricting to the consumer's invertible `L`** (`dual_isLocallyTrivial` uses
  `dual_restrict_iso U.ι L` on a line bundle): you would still have to *register* a
  `MonoidalCategory` instance, *build* the coevaluation, *verify* the two zig-zag identities to
  get `ExactPairing L (dual L)`, and *promote* restriction to a strong-monoidal equivalence —
  strictly **more** infrastructure than leg (A), not less.
- **Gap**: divergent-and-wrong as a shortcut — the rigid machinery needs four pieces of structure
  the project does not have and (for general M) cannot have.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (route 1 not viable — commit to leg A).

### Decision 2: Route (2) — the cleanest atom for the leg-(A) slice transport

- **Mathlib idiom (the engine)**: `CategoryTheory.Functor.FullyFaithful.homEquiv`
  (`Mathlib.CategoryTheory.Functor.FullyFaithful`): `F.FullyFaithful → ((X ⟶ Y) ≃ (F.obj X ⟶ F.obj Y))`.
  This is the categorical bijection-of-Hom-sets that underlies leg (A): the slice value
  `restr V P ⟶ restr V Q` over `Over V` corresponds to `restr fV P' ⟶ restr fV Q'` over
  `Over fV` once the slice categories are identified by the fully faithful `f.opensFunctor`.
- **Mathlib idiom (the off-the-shelf slice equivalence)**: `TopologicalSpace.Opens.overEquivalence`
  (`Mathlib.Topology.Sheaves.Over`): `Over U ≌ Opens ↥U`. The slice `Over V ⊂ Opens Y` is
  identified with `Over fV ⊂ Opens X` by composing two `overEquivalence`s through the
  open-immersion homeomorphism `↥V ≅ ↥(fV)`. **Caveat** (loogle): every structure map of
  `overEquivalence` (unit/counit components) is an `eqToHom` — so invoking the full equivalence
  drags in exactly the `eqToHom`-bookkeeping you would otherwise write directly.
- **The leg-(B) scalar atom**: `restrictScalarsRingIsoDualEquiv` (project, CLOSED) is the correct
  ring-iso reconciliation of the codomain unit `𝒪_X(fV) ↝ 𝒪_Y(V)` via `β_V = (f.appIso V).inv`
  — confirmed by dual252; it realizes the `𝒪_Y(V)`-linearity at the terminal slice section.
- **Project-aligned recommendation**: because `Opens X`/`Over V` are **thin posets**, leg (A)
  collapses to exactly the construction the project ALREADY ships axiom-clean in this very file —
  `homLocalSection` (`DualInverse.lean:358`): conjugate the slice-Hom components by `eqToHom`
  along the down-set identity `image_preimage_of_le` (`DualInverse.lean:439`), with **naturality
  by `Subsingleton.elim`**, wrapped in `PresheafOfModules.isoMk` (mirroring `dualUnitIsoGen` /
  `dualIsoOfIso`). `Functor.FullyFaithful.homEquiv` and `overEquivalence` are the conceptual
  atoms, but in the thin setting they reduce to the `eqToHom`-conjugation the project can already
  drive. Do NOT build a heavyweight `Over V ≌ Over fV` equivalence object.
- **Gap**: the leg-(A) `≃ₗ` (`sliceDualTransport`) is a genuine new build, but a *down-set
  restriction of the open immersion's order-embedding*, not a missing Mathlib import — and
  structurally a copy of `homLocalSection`.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (build `sliceDualTransport` à la `homLocalSection`,
  compose with `restrictScalarsRingIsoDualEquiv`).

## Recommendation

**Drop route (1) decisively.** `hasRightDualOfEquivalence` / `rightDualIso` are the right abstract
statements but require four structures the project lacks: a `MonoidalCategory` instance on
`PresheafOfModules` (absent), a *strong* (not lax/oplax) monoidal restriction functor, restriction
being an *equivalence* (false for a non-surjective open immersion), and an `ExactPairing M (dual M)`
(only for dualizable M, whereas the lemma is general). Even for the invertible-`L` consumer this is
strictly more work than leg (A). Commit to leg (A).

**Build leg (A) as `sliceDualTransport`, mirroring `homLocalSection`.** Minimal skeleton:

```
-- β_V : 𝒪_Y(V) ≃+* 𝒪_X(fV)  (the open-immersion structure ring iso, = (f.appIso V).inv as RingEquiv)
-- LHS module = restrictScalars β_V applied to the slice-Hom over Over fV
-- RHS module = the slice-Hom over Over V
noncomputable def sliceDualTransport {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]
    (M : X.Modules) (V : (Opens Y)ᵒᵖ) :
    (restr (f.opensFunctor.obj V.unop) M.val ⟶ restr (f.opensFunctor.obj V.unop) 𝟙_X)
      ≃ₗ[(𝒪_Y(V.unop) : Type u)]
    (restr V.unop ((pushforward β).obj M.val) ⟶ restr V.unop 𝟙_Y) :=
  -- (A) Hom-set transport along the slice order-iso induced by f.opensFunctor:
  --     realized by eqToHom-conjugation of the φ.app components along
  --     image_preimage_of_le (f reflects ≤ on the down-set of fV), naturality = Subsingleton.elim;
  -- (B) ∘ restrictScalarsRingIsoDualEquiv β_V  (the 𝒪_Y(V)-linear codomain-unit ring swap).
  ...

-- Step-4 residual then closes by:
PresheafOfModules.isoMk
  (fun V => (sliceDualTransport f M V).toModuleIso)
  (fun {V W} g => /- thin poset Opens Y: Subsingleton.elim, as in dualUnitIsoGen/dualIsoOfIso -/)
```

The load-bearing piece is `sliceDualTransport` itself (leg A); the outer `isoMk` naturality is
thin-poset-trivial. Build and verify `sliceDualTransport` as a standalone axiom-clean `def` FIRST
(it is a near-copy of `homLocalSection`'s `eqToHom`-conjugation pattern + `restrictScalarsRingIsoDualEquiv`),
then assemble the residual. Atoms to import/cite: `Functor.FullyFaithful.homEquiv`
(`Mathlib.CategoryTheory.Functor.FullyFaithful`), `image_preimage_of_le` (project, this file),
`restrictScalarsRingIsoDualEquiv` (project, CLOSED), `PresheafOfModules.isoMk`. Do NOT route through
`overSliceSheafEquiv` (Sheaf / fixed-value-cat — proven inapplicable) nor build a full
`Over V ≌ Over fV` equivalence object.
