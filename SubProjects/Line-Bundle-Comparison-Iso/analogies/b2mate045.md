# Analogy: B2 mate-calculus coherence (`restrictFunctorIsoPullback_comp_compat`)

## Mode
api-alignment

## Slug
b2mate045

## Iteration
045

## Question
Does Mathlib's adjunction/mate API already provide the composition/coherence lemmas
B2's residual is about to hand-roll (mate vertical-composition, `leftAdjointUniq_trans`),
and should B2 be phrased as a single mate/conjugate equality rather than an 80–120 LOC
sectionwise unit chase?

## Project artifact(s)
- `AlgebraicJacobian/Picard/TensorObjInverse.lean:196` — `restrictFunctorIsoPullback_comp_compat` (B2), residual `sorry` at L243.
- `AlgebraicJacobian/Picard/TensorObjInverse.lean:180` — `restrictCompReindex` (the `ρ` reindex, = `restrictFunctorCongr` ∘ `restrictFunctorComp`).

## Mathlib facts established (all real, cited)

- `CategoryTheory.Adjunction.leftAdjointUniq` — `Mathlib/CategoryTheory/Adjunction/Unique.lean:36`.
  `= ((conjugateIsoEquiv adj1 adj2).symm (Iso.refl G)).symm`. Requires **same right adjoint `G`**.
- `Adjunction.leftAdjointUniq_trans` — `…/Unique.lean:79` `@[reassoc (attr := simp)]`:
  `(leftAdjointUniq adj1 adj2).hom ≫ (leftAdjointUniq adj2 adj3).hom = (leftAdjointUniq adj1 adj3).hom`.
  Plus `_trans_app` (L86), `_refl` (L94), `unit_leftAdjointUniq_hom_app` (L51),
  `homEquiv_leftAdjointUniq_hom_app` (L39). **All three adjunctions must share `G`.**
- Mate composition API, `Mathlib/CategoryTheory/Adjunction/Mates.lean`:
  - `conjugateEquiv` (L272): `(L₂ ⟶ L₁) ≃ (R₁ ⟶ R₂)`, same `(C,D)`.
  - `conjugateEquiv_comp` (L338): `conjugateEquiv adj₁ adj₂ α ≫ conjugateEquiv adj₂ adj₃ β = conjugateEquiv adj₁ adj₃ (β ≫ α)` — vertical chain, **same `(C,D)`**.
  - `conjugateEquiv_id` (L312).
  - `mateEquiv_vcomp`, `mateEquiv_hcomp` — `mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄) (α.vComp β) = (mateEquiv adj₃ adj₄ β).hComp (mateEquiv adj₁ adj₂ α)` — **THIS is the "compose mates across composite adjunctions `L₁∘L₂ ⊣ R₂∘R₁`" lemma** the directive asked for (uses `Adjunction.comp`).
  - `iterated_mateEquiv_conjugateEquiv` — converts a doubly-iterated mate into `conjugateEquiv (adj₁.comp adj₄) (adj₃.comp adj₂)`; the bridge between cross-category mates and single-category conjugates.
  - `mateEquiv_conjugateEquiv_vcomp`, `conjugateEquiv_mateEquiv_vcomp`, `mateEquiv_square`.
- `restrictFunctorIsoPullback f := (restrictAdjunction f).leftAdjointUniq (pullbackPushforwardAdjunction f)` — `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean:371`. **`restrictAdjunction f` and `pullbackPushforwardAdjunction f` share the same right adjoint `pushforward f`.**
- `conjugateEquiv_pullbackComp_inv` (`…/Sheaf.lean:238`): `conjugateEquiv ((pPA g).comp (pPA f)) (pPA (f≫g)) (pullbackComp f g).inv = (pushforwardComp f g).hom`. **The load-bearing pseudofunctor↔conjugate bridge.**
- `pushforwardComp_hom_app_app = 𝟙` (`…/Sheaf.lean:214`); `pushforwardCongr_hom_app_app = presheaf.map (eqToHom …)` (L228); `restrictFunctorComp_hom_app_app = presheaf.map (eqToHom …)` (L401, `rfl`); `pullbackCongr = eqToIso` (L235).
- **Absent in Mathlib**: any `restrictFunctorIsoPullback_comp` compatibility lemma (grep: only the def + a docstring mention); any restrict-side analogue of `conjugateEquiv_pullbackComp_inv`.

## Decisions identified

### Decision: are mate vertical-composition lemmas available?
- **Mathlib idiom**: yes — `mateEquiv_vcomp`/`mateEquiv_hcomp`/`conjugateEquiv_comp`/`iterated_mateEquiv_conjugateEquiv` in `Adjunction/Mates.lean`. `mateEquiv_hcomp` is exactly the `(L₁∘L₂ ⊣ R₂∘R₁)` composite case.
- **Project's path**: directive proposed a hand-rolled "mate-vcomp coherence" unit chase.
- **Gap**: divergent-with-cost — Mathlib already provides the vcomp algebra; hand-rolling it re-derives library lemmas.
- **Verdict**: PROCEED on the API (use Mathlib's lemmas); do NOT hand-roll vcomp.

### Decision: is `leftAdjointUniq_trans` available?
- **Mathlib idiom**: yes (`Unique.lean:79`), `@[simp]`. **Caveat: same `G`.**
- **Project's path**: directive assumed it must be derived ("a `leftAdjointUniq_trans` … or must it be derived").
- **Gap**: identical — it exists. The only work is making B2's three legs share `G = pushforward V.ι` (via `pushforwardComp` + `pushforwardCongr hjι`), after which `leftAdjointUniq_trans`/`_refl` collapse the chain.
- **Verdict**: PROCEED — cite `leftAdjointUniq_trans`; build the right-adjoint identification, not the trans lemma.

### Decision: is the project re-deriving Mathlib's mate/conjugate calculus, and what is B2's idiomatic shape?
- **Mathlib idiom**: B2 = "the `leftAdjointUniq` family `restrictFunctorIsoPullback` is compatible with composition of adjunctions". Since `restrict_•` and `pullback_•` are left adjoints of the **same** `pushforward_•`, the whole RHS is a `leftAdjointUniq`/conjugate chain over a fixed `(X.Mod, V.Mod, pushforward V.ι)`, once the composite right adjoint `pushforward j ⋙ pushforward U.ι` is identified with `pushforward V.ι`.
- **Project's path**: NOT re-deriving — it correctly *uses* Mathlib `leftAdjointUniq`, `conjugateEquiv`, `conjugateEquiv_pullbackComp_inv`, `pullbackComp`, `pushforwardComp` (all live in Mathlib, not project copies). But the planned residual is a **sectionwise unit/tmul chase** (wrong shape).
- **Gap**: divergent-with-cost — right *components*, wrong *proof shape*.
- **Cost of the sectionwise path**: the project's own K1/cocycle history (memory: `lhs-tmul-*`, `mu-appiso-collapse-abstract-helper`, `cocycle-a-collapse-mechanism`) shows sectionwise `tmul`/unit chases run 40–120 LOC each and repeatedly dead-end on carrier diamonds, dependent motives, and `erw`-only defeq seams; the directive's own 80–120 LOC estimate is in that danger zone. The abstract conjugate route avoids sectionwise reasoning entirely and rides `@[simp]`-tagged library lemmas.
- **Verdict**: PROCEED on components; re-shape the proof (see Recommendation). The one genuine gap is `NEEDS_MATHLIB_GAP_FILL` for the restrict-side bridge below.

## Recommendation (idiomatic B2 shape — replaces the sectionwise chase)

Prove B2 by reducing the iso equality to a **right-adjoint natural-transformation equality**, then
collapse it with library conjugate/leftAdjointUniq algebra:

1. Both sides are isos `restrictFunctor V.ι ≅ pullback V.ι`, both left adjoint to `pushforward V.ι`.
   Apply `conjugateIsoEquiv (restrictAdjunction V.ι) (pullbackPushforwardAdjunction V.ι)` (equiv ⇒ injective),
   or equivalently compare images under `(restrictAdjunction V.ι).homEquiv` as the LHS handling already does
   (`homEquiv_leftAdjointUniq_hom_app`). The LHS image is the identity-ish unit (already discharged, L221–224).

2. On the RHS, push the conjugate through the 5-term composite using `conjugateEquiv_comp` (same-cat legs c₁,c₂,c₆)
   and `mateEquiv_hcomp`/`iterated_mateEquiv_conjugateEquiv` (cross-category composite-adjunction legs c₃,c₄,c₅).
   This converts the composite into a product of *known* right-adjoint maps.

3. Discharge each factor with library identities:
   - c₅ (`pullbackComp`): `conjugateEquiv_pullbackComp_inv` ⇒ `(pushforwardComp …).hom`.
   - c₃,c₄ (`restrictFunctorIsoPullback` at `U.ι`/`j`): `unit_leftAdjointUniq_hom_app` ⇒ pushforward-side identities.
   - c₆,c₁ (`pullbackCongr`/`restrictFunctorCongr` from `hjι`): `pushforwardCongr` eqToHom on `presheaf.map`.
   - the trivial `pushforwardComp_hom_app_app = 𝟙`.

4. Collapse the resulting same-`G` (`= pushforward V.ι`) chain with `leftAdjointUniq_trans` + `leftAdjointUniq_refl`.

**Gap to fill first (cheap, ~10–20 LOC):** derive the restrict-side mirror of `conjugateEquiv_pullbackComp_inv`,
i.e. `conjugateEquiv ((restrictAdjunction U.ι).comp (restrictAdjunction j)) (restrictAdjunction V.ι)
(restrictFunctorComp …).inv = (pushforwardComp …).hom` (same RHS `pushforwardComp.hom`). `restrictFunctorComp`
is eqToHom-valued (`restrictFunctorComp_hom_app_app`, `rfl`) and `pushforwardComp_app_app = 𝟙`, so this should
close by `conjugateEquiv` app-computation + `simp`/`ext` — mirroring how Mathlib proves the pullback version.
This is the genuine Mathlib-gap; everything else is library citation.

The `hjι : j ≫ U.ι = V.ι` shim genuinely cannot be `subst`-eliminated (directive's DEAD probe, confirmed:
`V.ι` is compound, `j` a parameter) — thread it via `pushforwardCongr`/`pullbackCongr`/`restrictFunctorCongr`
eqToHom as the project already does. That part of the scaffold is correct and stays.
