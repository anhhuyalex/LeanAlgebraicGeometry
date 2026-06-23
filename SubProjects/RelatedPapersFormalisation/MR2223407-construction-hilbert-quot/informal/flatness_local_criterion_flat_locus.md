# Missing ingredient: openness of the flat locus (EGA IV 11.1.1 / 11.3.1)

## Where it is needed

`MR2223407ConstructionHilbertQuot/Variants.lean`, `flatness_local_criterion`, part **(2)**:

```lean
(∀ {X Y : Scheme.{u}} (f : Y ⟶ X) [IsLocallyNoetherian X] [LocallyOfFiniteType f],
    IsOpen {y : Y | RingHom.Flat (f.stalkMap y).hom})
```

i.e. for a morphism `f : Y ⟶ X` locally of finite type over a locally noetherian
target, the **flat locus** `{y ∈ Y | O_{Y,y} is flat over O_{X,f(y)}}` is open in `Y`.

(Part (1) of the same lemma — flat + locally of finite type over a noetherian base
is an open map — is **proved** via `UniversallyOpen.of_flat` after upgrading
`LocallyOfFiniteType` to `LocallyOfFinitePresentation` over the noetherian base.
Part (3), the fibre local criterion, is omitted at the statement level as a citation.)

## Why it is a gap

This is the classical **openness of flatness** (EGA IV, 11.1.1 and 11.3.1; Stacks
project tag 0399 / 01V9). Mathlib currently has:

* `Algebra.isOpen_smoothLocus` — the *smooth* locus of a finitely-presented algebra is open;
* `Module.freeLocus` + its openness — the locus where a finitely-presented module is
  locally free is open (a subset of `PrimeSpectrum` of the *base* ring).

Neither gives openness of the *flat* locus of the **stalk maps** of a morphism: the
stalk `O_{Y,y}` is not a finite module over `O_{X,f(y)}`, so the free-locus result does
not apply directly, and flatness is strictly weaker than smoothness.

## Precise ring-theoretic statement to add (the real obligation)

Openness of the flat locus for a finitely-presented algebra over a noetherian ring:

> Let `A` be a noetherian ring and `B` a finitely-presented `A`-algebra (equivalently,
> finite type, since `A` is noetherian). Then
> `{q ∈ Spec B | B_q is flat over A_{(A→B)⁻¹ q}}` is open in `Spec B`.

From this, the scheme statement follows by working on affine charts `Spec B → Spec A`
of `f` (using `LocallyOfFiniteType`/`IsLocallyNoetherian` locality) and translating the
stalk-flatness condition `RingHom.Flat (f.stalkMap y).hom` to local-ring flatness on the
chart.

## Standard proof outline (for a future `mathlib-build` lane)

1. Reduce to the affine case `Spec B → Spec A`, `A` noetherian, `B` finite type over `A`.
2. Use the **local criterion of flatness** (`Module.flat_iff_of_isNoetherian`-style /
   `Tor₁` vanishing) to express flatness of `B_q` at a prime.
3. Generic flatness (`Algebra.exists_flat_of_finiteType` / `genericFlatness`) provides a
   dense open of flatness over each irreducible component of `Spec A`.
4. Noetherian induction on `Spec A` together with constructibility of the flat locus and
   stability of flatness under generization upgrades "constructible + stable under
   generization" to "open".

Steps 2–4 require `Tor`-based local criteria and constructibility infrastructure that is
not yet assembled in Mathlib for this purpose.

## Status of the surrounding lemma

`flatness_local_criterion` is therefore left with a single `sorry` (part (2)), inside a
structured `by`-block with the context introduced and the gap documented inline. Parts (1)
is fully proved and axiom-clean. The sibling lemma `descent_of_subschemes` (both parts) is
fully proved and axiom-clean in the same iteration.
