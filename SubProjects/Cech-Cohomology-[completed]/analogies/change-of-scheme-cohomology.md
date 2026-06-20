# Analogy: transporting an Ext / right-derived cohomology computation across a scheme isomorphism

## Mode
api-alignment

## Slug
change-of-scheme-cohomology

## Iteration
056

## Question
Find Mathlib's idiom (decl names + imports) for transporting the right-derived / `Ext` cohomology
computation `Ext^q(jShriekOU V, H)` across the canonical iso of an affine scheme with `Spec` of its
global sections, so the ⊤-case Serre vanishing `affine_serre_vanishing` over `Spec R` discharges the
residual `IsZero ((preadditiveCoyoneda.obj (op (jShriekOU (j ⁻¹ᵁ W)))).rightDerived q).obj H)` for
`j⁻¹W` a *general affine open* of the affine scheme `U`. Is the transport route sound and cheaper
than building a `BasisCovSystem U` over arbitrary affine opens?

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/OpenImmersionPushforward.lean:296-306` — the residual `sorry`
  (`hSec` leaf inside `higherDirectImage_openImmersion_acyclic`); already reduced through
  `rightDerivedNatIso (sectionsFunctorCorepIso (j ⁻¹ᵁ W))` to
  `IsZero ((preadditiveCoyoneda.obj (op (jShriekOU (j ⁻¹ᵁ W)))).rightDerived q).obj H)`.
- `AlgebraicJacobian/Cohomology/AffineSerreVanishing.lean:521` — `affine_serre_vanishing`, the
  available ⊤-case (`Ext^p (jShriekOU ⊤) F = 0` over `Spec R`).
- `AlgebraicJacobian/Cohomology/CechToCohomology.lean:323,429` — `BasisCovSystem` and
  `cech_eq_cohomology_of_basis` (the comparison consuming a cover system on a basis `B`).
- `AlgebraicJacobian/Cohomology/AffineSerreVanishing.lean:373` — `affineCoverSystem R`
  (`BasisCovSystem (Spec R)` with `B = {D f}`).
- `analogies/restriction-preserves-injectives.md` (iter-026) — the project's recorded decision to
  adopt **Form B** *precisely to avoid* restriction-preserves-injectives (a 200–500 LOC Mathlib gap).

## Headline finding (read this first)

The directive's chosen route — **make `V = j⁻¹W` the whole space via `V ≅ Spec Γ(V,𝒪)`** — is a
**WALL, not a shortcut.** It secretly re-introduces **restriction-preserves-injectives**, the exact
Mathlib gap the project deliberately side-stepped in iter-026 by adopting Form B
(`H^q(V,−) := Ext^q_{U.Modules}(jShriekOU V, −)`, ambient, no restriction). The transport is *not*
circular, but its cost is the 200–500 LOC `j_!`/restriction-injectives infrastructure, with the same
risk profile that already forced a pivot once.

Reason (the crux): `jShriekOU_U V` and `H` both live in `U.Modules`, and the only available iso is
`V ≅ Spec Γ(V)` — an iso of the **open subscheme** `V`, **not** of `U`. To use it you must first
**restrict** `U.Modules → V.Modules` (`H ↦ H|_V`); the derived comparison
`Ext^q_{U.Modules}(j_!𝒪_V, H) ≅ H^q(V, H|_V)` *is* restriction-preserves-injectives (an injective
resolution in `U.Modules` must stay injective after `(−)|_V` to compute the intrinsic `H^q(V,−)`).
`V ↪ U` is an **open immersion, not an iso**, so there is no equivalence `U.Modules ≌ V.Modules` to
transport `Ext` along — only the non-exact-inverse restriction functor.

**Contrast:** `U ≅ Spec Γ(U)` (the *whole* affine `U`) IS a genuine iso, giving a genuine
equivalence `U.Modules ≌ (Spec ΓU).Modules`. That transport ("need #1", abstract-affine → `Spec`)
is sound. But it sends the proper open `V ⊆ U` to a **general (non-distinguished) affine open**
`φ(V) ⊆ Spec ΓU`, *not* to `⊤`. So even after the sound whole-affine transport, you still face
general-affine-open vanishing, which `affine_serre_vanishing` (⊤ only) does not cover.

**The general-affine-open gap is unavoidable** (no basis dodge): `Q.obj(op W) = H^q(j⁻¹W, H)` and any
affine open `W ⊆ X` straddling the boundary of `j(U)` forces `j⁻¹W = U ⊓ W` to be a general affine
open of `U`; points of `W` on the boundary of `j(U)` cannot be covered by opens whose `j`-preimage is
distinguished-or-empty. So the residual genuinely is "Serre vanishing for **every** affine open of an
affine scheme".

**The sound, Form-B-native discharge** is to stay ambient and get general-affine-open vanishing from
`cech_eq_cohomology_of_basis` by **enlarging the cover system's basis `B` from `{D f}` to all affine
opens** — `cech_eq_cohomology_of_basis s … V hV` already gives `Ext^q(jShriekOU V, H)=0` for *any*
`V ∈ s.B`, entirely inside `(Spec R).Modules`, with no restriction functor anywhere in its proof.

## Verified Lean names

### Q1 — affine scheme ≅ Spec(Γ)
- `AlgebraicGeometry.Scheme.isoSpec (X) [IsAffine X] : X ≅ Spec (X.presheaf.obj (op ⊤))`
  — `Mathlib.AlgebraicGeometry.AffineScheme`. **[verified]**
- `Scheme.isoSpec_hom : X.isoSpec.hom = X.toSpecΓ` **[verified]**;
  `Scheme.toSpecΓ_isoSpec_inv` **[verified]**;
  `IsAffineOpen.fromSpec_top : hV.fromSpec = X.isoSpec.inv` **[verified]**.
- `AlgebraicGeometry.IsAffineOpen.isCompact (hU : IsAffineOpen U) : IsCompact ↑U`
  — `Mathlib.AlgebraicGeometry.AffineScheme`. **[verified]** (this is what generalizes
  `standard_cover_cofinal` from `D f` to a general affine open).

### Q2 — module-category functoriality from a scheme morphism / iso
- `AlgebraicGeometry.Scheme.Modules.pushforward (f : X ⟶ Y) : X.Modules ⥤ Y.Modules`
  — `Mathlib.AlgebraicGeometry.Modules.Sheaf:151`. **[verified]**
- `Scheme.Modules.pushforwardId : pushforward (𝟙 X) ≅ 𝟭 _` (`:190`),
  `Scheme.Modules.pushforwardComp : pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g)` (`:210`),
  `Scheme.Modules.pushforwardCongr (hf : f = g) : pushforward f ≅ pushforward g` (`:224`),
  instance `(pushforward f).Additive` (`:182`),
  `Scheme.Modules.pullbackPushforwardAdjunction` (`:172`). **[verified, all in Modules/Sheaf.lean]**
- **[gap — assembly]** Mathlib has **no packaged** `Y.Modules ≌ Z.Modules` from a scheme iso. It is
  assembled from `pushforward φ.hom` / `pushforward φ.inv` + `pushforwardComp`/`pushforwardCongr`/
  `pushforwardId` (the unit/counit isos), ~30–60 LOC. Sound and Mathlib-aligned (a genuine
  equivalence because `φ` is an iso).

### Q3 — getting `Ext` to transport across the equivalence
- `CategoryTheory.Abelian.Ext.mapExactFunctor (F) [F exact] : Ext X Y n → Ext (F.obj X) (F.obj Y) n`
  — `Mathlib/Algebra/Homology/DerivedCategory/Ext/Map.lean:126`; with
  `Functor.mapExtAddHom` (`:169`), `Ext.mapExactFunctor_zero` (`:160`),
  `Ext.mapExactFunctor_comp`. **[verified]** An equivalence is exact, so `mapExactFunctor` of the
  equivalence (and of its inverse) gives the `Ext`-iso. This is a *cleaner* vehicle than
  `rightDerivedNatIso` for the whole-affine transport: `e : Ext_{U}(jShriekOU V, H) ↦
  e.mapExactFunctor Φ.functor` lands in the `Spec ΓU` `Ext`, which the enlarged cover system kills;
  injectivity of `mapExactFunctor` for an equivalence sends `e ↦ 0`.
- Already-built project vehicles (keep, reusable for either need): `rightDerivedNatIso`,
  `sectionsFunctorCorepIso` (`OpenImmersionPushforward.lean:156,174`). They connect
  `(preadditiveCoyoneda (op (jShriekOU V))).rightDerived q` ≅ `Ext^q(jShriekOU V, −)`. They are
  **not** the wall.

## Decisions identified

### Decision: route for *general-affine-open* `Ext`-vanishing (need #2) — isoSpec-of-`V` vs enlarge-`B`
- **Mathlib idiom**: for "cohomology of every member of a basis", build the basis into the comparison
  input. The project already has the right vehicle: `cech_eq_cohomology_of_basis (s) … V hV` gives
  `Ext^q(jShriekOU V, H)=0` for any `V ∈ s.B`. The Mathlib-idiomatic move is to make `B` the right
  set, not to change spaces. (`CechToCohomology.lean:429`.) **[verified]**
- **Project's proposed path (directive)**: transport the ⊤-case along `V ≅ Spec Γ(V)`.
- **Gap**: divergent-and-wrong (as a *cheaper* route). It forces restriction-preserves-injectives —
  a 200–500 LOC Mathlib gap-fill the project already rejected (`restriction-preserves-injectives.md`).
- **Cost of divergence**: build `j_!` functor / restriction-preserves-injectives (200–500+ LOC, HIGH
  risk; the project pivoted away from this once already). The ambient enlarge-`B` alternative is
  ~40–80 LOC.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** for the isoSpec-of-`V` route (do NOT take it). **ALIGN /
  PROCEED** on enlarging `B`.

### Decision: enlarge `affineCoverSystem` basis `B` from `{D f}` to all affine opens (the recommended need #2)
- **Mathlib idiom / mechanism**: `BasisCovSystem` is generic over `B`/`Cov`; `cech_eq_cohomology_of_basis`
  consumes any `V ∈ B`. Set `B := { affine opens }`, keep `Cov` = standard covers `i ↦ D(g i)` but
  let the covered set be any affine open `V = ⨆ D(g i)`.
- **What must be re-proved**:
  - `faces_mem`: faces `⨅ D(g_{σk}) = D(∏ g)` are distinguished ⊆ affine — **already covered**, even
    easier than before (`affine_faces_mem`).
  - `injective_acyclic`: cover-agnostic (`injective_cech_acyclicFam`) — **unchanged**.
  - `surj_of_vanishing`: now needed for every affine open `V ∈ B`. Generalize `affine_surj_of_vanishing`
    (`AffineSerreVanishing.lean:233`, currently `f : R`, `V = D f`) to a general affine open. Its proof
    uses only quasi-compactness of the target + the basic-open basis, via `standard_cover_cofinal`
    (`:167`); swap `PrimeSpectrum.isCompact_basicOpen f` for `hV.isCompact`
    (`IsAffineOpen.isCompact` **[verified]**). **This is the one genuine new piece.**
- **Cost**: ~40–80 LOC, low risk (mechanical reindex of two shipped lemmas + the structure literal).
- **Verdict**: **PROCEED** (recommended discharge of need #2; fully ambient, Form-B-native, zero new
  Mathlib gaps).

### Decision: abstract-affine `U` → `Spec Γ(U)` transport (need #1, UNAVOIDABLE)
- `U` is `[IsAffine U]`, not literally `Spec R`, while every affine-development decl is over `Spec R`.
  So a transport along `U.isoSpec : U ≅ Spec Γ(U)` is required no matter which need-#2 route is taken.
- **Mathlib idiom**: equivalence from `isoSpec` via `pushforward`/`pushforwardComp`/`pushforwardCongr`/
  `pushforwardId`; transport `Ext` via `Ext.mapExactFunctor`. Side obligations: `Φ.functor (jShriekOU_U V)
  ≅ jShriekOU (φ ''ᵁ V)` (jShriekOU is yoneda+sheafify on `Opens`, so an iso of schemes transports it),
  `φ ''ᵁ V` affine, `Φ.functor H` quasi-coherent. All standard, all sound (genuine equivalence).
- **Cost**: ~60–120 LOC, low–medium risk. Comparable to — but smaller and lower-risk than — the 01I8
  sheaf-infra route that overran (this is one equivalence + one `Ext`-functor, no cover-dense / site
  plumbing).
- **Verdict**: **PROCEED** (sound; the isoSpec tool genuinely belongs here, on the *whole* affine).

## Recommendation

**Split the residual into the two transports it actually needs and route each correctly:**

1. **need #2 — general-affine-open vanishing — do it AMBIENT, by enlarging `B`.** Generalize
   `standard_cover_cofinal` and `affine_surj_of_vanishing` from `D f` to a general affine open (swap in
   `IsAffineOpen.isCompact`), set `affineCoverSystem`'s `B := {affine opens}` (and `Cov`'s covered set
   to affine opens), then read off
   `affine_serre_vanishing_allAffineOpens : ∀ V affine, ∀ q≥1, Ext^q_{(Spec R).Modules}(jShriekOU V, H)=0`
   from `cech_eq_cohomology_of_basis (affineCoverSystem R) … V hV`. ~40–80 LOC, no new Mathlib gap.

2. **need #1 — abstract affine `U` → `Spec Γ(U)` — do it with `isoSpec` (the SOUND use of the tool).**
   Assemble `Φ : U.Modules ≌ (Spec Γ U).Modules` from `Scheme.Modules.pushforward U.isoSpec.hom/.inv`
   + `pushforwardComp`/`pushforwardId`/`pushforwardCongr`; transport the step-1 vanishing back to `U`
   and `V = j⁻¹W` via `Ext.mapExactFunctor` (+ `jShriekOU`/quasi-coherence naturality). ~60–120 LOC.

**Do NOT** transport along `j⁻¹W ≅ Spec Γ(j⁻¹W)` to make `V` the whole space — that is the
restriction-preserves-injectives wall the project already rejected. `isoSpec` is the right tool only
for the *whole* affine `U`, never for the proper open `V`.

The `rightDerivedNatIso`/`sectionsFunctorCorepIso` already in the file remain correct and reusable;
they are orthogonal to this choice.
