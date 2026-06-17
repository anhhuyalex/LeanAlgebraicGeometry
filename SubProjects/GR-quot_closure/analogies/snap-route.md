# Analogy: associative section graded ring `⊕ Γ(X, L^{⊗m})` without a monoidal `X.Modules`

## Mode
cross-domain-inspiration

## Slug
snap-route

## Iteration
050

## Structural problem (abstracted)
`C` monoidal (coherent), `L : C ⥤ D` a reflective localization (sheafification),
`D` NOT known monoidal. Build an associative graded monoid `(A_m, μ_{m,m'} : A_m ⊗ A_{m'}
→ A_{m+m'})` where `A_m = Φ(L(P^{⊗m}))` and `Φ` is a section/global-elements functor.
Concretely `C = X.PresheafOfModules`, `L = sheafification`, `D = X.Modules`,
`Φ = Γ(X,-)`, `A_m = Γ(X, L^{⊗m})`. The lax multiplication `Γ(F)⊗Γ(G) → Γ(F⊗G)`
(`sectionsMul`) is BUILT, associator-free. The open crux is the comparison family
`tensorPowAdd : L^{⊗m} ⊗ L^{⊗m'} ≅ L^{⊗(m+m')}` whose inductive step needs the
sheaf-level associator = strong monoidality of `L`, i.e. `IsIso (L.map (η_P ▷ Q))`.

## Failed approaches (from directive)
- snap-assoc Analogue-4 (local-freeness, no associator): INSUFFICIENT — the inductive
  step is irreducibly associativity (moving a factor across a bracket); unitor+braiding
  alone cannot.
- Stalkwise-iso ⟹ IsIso on `η_P ▷ Q`: tensor only right-exact ⇒ not locally injective;
  and no module-sheaf stalk infra in pinned Mathlib.
- `LocalizedMonoidal`: needs `W.IsMonoidal`, whose discharge wants
  `MonoidalClosed (PresheafOfModules R)` — ABSENT.

## KEY META-FINDING (negative): route (b) "build at presheaf, take Γ at end" is ILLUSORY
The directive's hoped dodge — live entirely in the coherent presheaf monoidal category
and apply Γ only at the end — does NOT avoid the crux. Reduction chain (each link forced):

1. **Wrong ring.** `Γ_sheaf(P) := Γ(X, sheafification P) ≠ Γ_pre(P) := P(⊤)`.
   Sheafification changes global sections (e.g. `O(1)⊗O(1)` presheaf-sections ≠ `O(2)`
   sections on ℙ¹). The presheaf section ring `⊕ P_L^{⊗m}(⊤) = T(Γ(L))` (tensor algebra
   on the module `Γ(L)`) is associative for free (eval@⊤ is STRICT monoidal on presheaves)
   — but it is the WRONG object. The map `η@⊤ : ⊕Γ(L)^{⊗m} → ⊕Γ(L^m)` is a ring hom into
   the desired ring, not onto/iso, so it does NOT transport associativity to the target.

2. **Defining the multiplication already needs the comparison.** The graded mult must land
   in degree `m+m'`: `sectionsMul` lands in `Γ(L^m ⊗_sheaf L^{m'})`; to reach `Γ(L^{m+m'})`
   one MUST have a morphism `L^m ⊗_sheaf L^{m'} → L^{m+m'}` (= `μ_{m,m'}`, even as a mere
   morphism, not iso). It is `rfl`/identity only for `m'=1`; general `m'` is inductive and
   the step needs the associator MAP `A⊗(B⊗C) → (A⊗B)⊗C`.

3. **The associator map itself needs the crux.** For `tensorObj = sh(⊗_pre)`,
   `(A⊗B)⊗C = sh(P_{sh(P_A⊗P_B)} ⊗ P_C)` has an INNER sheafification. The only canonical
   map relating `P_{sh P}` and `P` is the unit `η : P → P_{sh P}` (one direction). Bridging
   the inner sheafifications to build the associator (in either direction, lax or strong) is
   exactly "factor `η_{X⊗Y}` through `η_X ⊗ η_Y`", possible iff `η_X ⊗ η_Y ∈ W` — the crux.

4. **Lax-monoidality of `Γ_sheaf` / of `sheafification` also needs the crux.** Sending a
   presheaf monoid (the tensor algebra `⊕ P_L^{⊗m}`) to a sheaf monoid requires `sh` LAX
   monoidal: `sh X ⊗_sheaf sh Y → sh(X⊗Y)`, i.e. `P_{shX}⊗P_{shY} → P_{sh(X⊗Y)}`, which by
   adjunction is again "extend `η_{X⊗Y}` along `η_X⊗η_Y`" = `η_X⊗η_Y ∈ W`.

**Every reformulation collapses to `η_P ⊗ η_Q ∈ W` ⟺ `IsIso(sh.map(η_P ▷ Q))` ⟺
`W.IsMonoidal` ⟺ strong monoidality of module sheafification.** The crux is mathematically
IRREDUCIBLE for any associative ring on the CORRECT sheaf sections. (Same shape as the
iter-043 FBC "illusory pivot" lesson: the pivot reduces to the same keystone.)

## Analogues found (routes to the crux, ranked by NEW infra needed, lowest first)

### Analogue 1: abelian-`J.W`-monoidality transfer via the relative-tensor coequalizer  [NEW]
- **Domain**: category theory / homological algebra (exactness + colimit-preservation of
  a left adjoint).
- **Same problem there**: the ABELIAN crux is already SOLVED in Mathlib. For sheaves of
  abelian groups on the site, `J.W` (local isos) is monoidal: `GrothendieckTopology.W.monoidal`
  (`Mathlib/CategoryTheory/Sites/Monoidal.lean`), discharged via "internal hom into a sheaf
  is a sheaf", `CategoryTheory.Presheaf.isSheaf_functorEnrichedHom` (same file) — CONFIRMED
  present. So `η_P^{ab} ⊗_ℤ 1 ∈ J.W` for the ℤ-tensor.
- **Technique**: bridge ℤ-tensor monoidality of `J.W` to the relative `⊗_{R₀}` of module
  presheaves by exactness. The underlying abelian presheaf of `P ⊗_{R₀} Q` is the
  objectwise relative tensor `U ↦ P(U) ⊗_{R₀(U)} Q(U)` = the coequalizer
  `coeq(P⊗_ℤ R₀⊗_ℤ Q ⇉ P⊗_ℤ Q)` in `Cᵒᵖ ⥤ AddCommGrp` (colimits objectwise). The module
  whiskering `η_P ▷_{R₀} Q`, forgotten to abelian, is the induced map on coequalizers from
  the two rows connected by `η_P ⊗_ℤ (–)`. Now:
  * `W (η_P ▷ Q)` in `X.Modules` ⟺ (by `GrothendieckTopology.W_iff` /
    `W_iff_isIso_map_of_adjunction`, and `W = J.W.inverseImage toPresheaf`)
    `J.W (underlying-abelian (η_P ▷ Q))`, i.e. `a(–)` iso where `a = presheafToSheaf J AddCommGrp`.
  * `a` is a LEFT ADJOINT ⇒ preserves coequalizers (no exactness needed!). So
    `a(coeq) = coeq(a(–))`.
  * `a(η_P ⊗_ℤ 1)` and `a(η_P ⊗_ℤ 1 ⊗_ℤ 1)` are ISOS (abelian `J.W.monoidal`: `η_P ∈ J.W`,
    `J.W` closed under `⊗_ℤ`-whiskering). An iso of parallel-pair diagrams induces an iso of
    coequalizers ⇒ `a(η_P ▷ Q)` iso ⇒ `η_P ▷ Q ∈ W` ⇒ `IsIso(sh.map(η_P ▷ Q))`. CRUX DONE.
- **Mapping to project**: prove a single helper `isIso_sheafification_whiskerRight`
  `: IsIso ((Scheme.Modules.sheafification).map (η_P ▷ Q))` in `SectionGradedRing.lean`,
  by the chain above. Inputs all present: `GrothendieckTopology.W.monoidal`,
  `W_iff_isIso_map_of_adjunction`, `Localization.lean:48` (module sheafification IS the
  localization at `J.W.inverseImage toPresheaf`), and `Adjunction.preserves coequalizers`.
- **Porting cost**: medium-high. The genuinely new plumbing = exhibit `P ⊗_{R₀} Q` underlying
  abelian as the categorical coequalizer in `Cᵒᵖ ⥤ AddCommGrp` and identify `η_P ▷ Q` with the
  induced map (relate Mathlib `PresheafOfModules.monoidalCategory` tensor to the `ModuleCat`
  relative-tensor coequalizer presentation). Risk: this presentation may not be cleanly
  exposed; if it requires re-deriving `TensorProduct`-as-coequalizer in the presheaf category,
  cost rises. But it adds the LEAST genuinely-absent infra (reuses the present abelian W
  machinery), unlike Analogues 2–3 which need a wholly absent brick.
- **Verdict**: ANALOGUE_FOUND (top principled, present-bricks route).

### Analogue 2: stalkwise-iso criterion (the standard Stacks proof)
- **Domain**: sheaf theory on spaces. Mathlib `TopCat.Presheaf` has stalks +
  `TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso` (iso ⟺ stalkwise iso).
- **Same problem there**: `(F⊗G)_x = F_x ⊗_{O_x} G_x`; the crux `(η_P ▷ Q)_x = (η_P)_x ⊗ 1`
  is iso because `(η_P)_x` is iso (sheafification iso on stalks) and ANY functor preserves
  isos — right-exactness never enters AT THE STALK. This is the textbook proof.
- **Technique**: reduce `IsIso` to stalks; stalk-of-tensor = tensor-of-stalks; functor
  preserves the stalk iso.
- **Mapping to project**: would need a stalk theory for `X.Modules` (`F_x` as `O_{X,x}`-module
  via `colim_{x∈U}`), `isIso ⟺ stalkwise iso` for module-sheaf morphisms, and
  `(F⊗G)_x ≅ F_x ⊗ G_x`. All ABSENT in pinned Mathlib for sheaves of modules.
- **Porting cost**: high (a whole stalk package for module sheaves). Mathematically the
  cleanest, infra-wise the heaviest.
- **Verdict**: PARTIAL_ANALOGUE (cleanest math, absent prerequisites).

### Analogue 3: Day's reflection theorem (snap-assoc Analogue 2, reconfirmed)
- **Domain**: category theory, reflective subcategories. `Monoidal/Braided/Reflection.lean`
  `isIso_tfae`: condition (1) "internal hom into a local object is local" ⟹ (3)
  `IsIso(L.map(η ▷ d'))` = the crux, AND yields `MonoidalClosed` of the reflection.
- **Technique**: condition (1) via `adjRetraction`; abstract form of `isSheaf_functorEnrichedHom`.
- **Mapping to project**: needs `MonoidalClosed (PresheafOfModules R)` — CONFIRMED ABSENT
  (local search: only `Rep`, distributive, and the bare class exist). Building it is the
  `NEEDS_MATHLIB_GAP_FILL` core; module presheaves are NOT a plain functor category
  (restriction-of-scalars in transitions), so `Rep`/functor-category closed instances do
  not transfer.
- **Porting cost**: high (build module-presheaf internal hom + sheaf-preservation).
- **Verdict**: PARTIAL_ANALOGUE (robust, site-general, but most absent infra).

### Analogue 4: scope sidestep — concrete very-ample presentation / defer the ring
- **Domain**: algebraic geometry idiom.
- **Observation**: Mathlib has NO "section ring / Proj of an abstract invertible sheaf"
  idiom that sidesteps tensor-power coherence — `Proj` (`Mathlib.AlgebraicGeometry.Proj`,
  `ProjectiveSpectrum`) takes a CONCRETE graded ring, where associativity is the ambient
  ring's. The only escape from the crux that avoids new infra is mathematical: present `L`
  concretely (very ample ⇒ closed immersion into ℙⁿ, so `R(L)` is a quotient of the
  homogeneous coordinate ring = a concrete graded algebra with ambient associativity), OR
  build only the graded MODULE / Hilbert-function data the Quot/Hilbert-poly route consumes
  and defer the abstract ring.
- **Porting cost**: variable; changes the math scope (a planner/strategy decision, not a
  Lean lemma). Cheapest *if* downstream tolerates it.
- **Verdict**: ANALOGUE_FOUND (pragmatic; needs a scope decision).

## Top suggestion
Two-track, given the irreducibility finding.
**(Principled, present bricks) Analogue 1 — the abelian-`J.W` coequalizer transfer.** Add one
helper to `AlgebraicJacobian/Picard/SectionGradedRing.lean`:
`IsIso ((sheafification).map (η_P ▷ Q))`, proved by reducing through
`GrothendieckTopology.W_iff_isIso_map_of_adjunction` to `J.W` of the underlying abelian
morphism, then using that abelian sheafification preserves coequalizers (left adjoint) and
that `GrothendieckTopology.W.monoidal` (`Mathlib/CategoryTheory/Sites/Monoidal.lean`) makes
`η_P^{ab}` survive ℤ-tensor whiskering, so the induced map on the relative-tensor coequalizer
is inverted. Read `Sites/Monoidal.lean` (`W.monoidal`, `isSheaf_functorEnrichedHom`),
`Sites/Localization.lean` (`W_iff_isIso_map_of_adjunction`, `W_adj_unit_app`), and
`ModuleCat/Sheaf/Localization.lean:48` (module sheafification = localization at
`J.W.inverseImage toPresheaf`). The lone risk is exposing the coequalizer presentation of the
relative module-presheaf tensor; scout that first.
**(Strategy) Surface the irreducibility to the planner** so route (b) is not attempted: the
crux cannot be dodged by working at presheaf level + Γ-at-end. If the abelian-transfer
plumbing balloons, fall back to Analogue 4 (concrete very-ample presentation / defer ring),
which is the only genuinely crux-free path but costs a math-scope change.

## Discarded
- Presheaf section ring `⊕ P_L^{⊗m}(⊤)` then Γ: wrong object (tensor algebra on `Γ(L)`), and
  η@⊤ doesn't transport associativity. (= route (b), killed above.)
- `Rep.MonoidalClosed` / functor-category closed → `MonoidalClosed(PresheafOfModules)`:
  PresheafOfModules is not a plain functor category (restriction-of-scalars transitions), so
  these closed instances don't transfer.
- snap-assoc Analogue-4 local-freeness alone: per directive, insufficient — still needs the
  associator MAP (then the local-iso criterion needs an absent invertibility predicate +
  absent "module-sheaf morphism iso ⟺ locally iso").
- Generic monoidal-functor inverse-image `W.IsMonoidal` (`Localization/Monoidal/Basic.lean`):
  inapplicable — `toPresheaf` is not strong monoidal (`⊗_{R₀} ≠ ⊗_ℤ`). (Analogue 1 routes
  around this precisely by going through the ℤ-tensor coequalizer, not `toPresheaf`.)
