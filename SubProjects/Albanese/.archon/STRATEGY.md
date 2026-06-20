# Strategy

## Goal

Discharge every inline `sorry` in the dependency cone of the **Albanese universal
property** `thm:albanese_universal_property` (Milne, *Abelian Varieties*, III §6
Prop. 6.1): the identity component `J := Pic⁰_{C/k}` together with the Abel–Jacobi
morphism `fᴾ : C → J` is the Albanese object of the pointed curve `(C, P)`. End
state: zero project axioms, kernel-only axioms.

This is the Albanese slice of the parent Algebraic-Jacobian-Challenge arc. The
parent's other routes — the cohomology `Rⁱf_*` Čech engine, FGA Picard
representability (A.2.c), Riemann–Roch (frozen under the parent's USER Route-C
pause), and the differential / Serre-duality rigidity route — are **out of scope**
here and were dropped at extract time. The construction of `Pic⁰_{C/k}` itself is
assumed (referenced as context); this subproject proves the universal property on
top of it plus the geometric input it needs.

## The proof arc (Milne III §6, as carved)

1. **Symmetrise + descend.** `C^g → A` is symmetric, factors through the symmetric
   power `C^{(g)}`, and composes with the (birational) Abel–Jacobi map to give a
   *rational* map `ψ : J ⇢ A`. (`AlbaneseUP.lean`: `symmetric_product_*`,
   `descent_through_birational_sigma`, `albanese_eq_iff_symmetricPower_eq`.)

2. **Extend the rational map (the rate-limiter).** Milne I §3 Thm 3.2: a rational
   map from a nonsingular variety into an abelian variety is everywhere defined.
   This is the composite of Thm 3.1 (everywhere-extension outside codimension ≥ 2,
   via the valuative criterion) with Lemma 3.3 (the indeterminacy locus into a
   group variety is pure codimension one). The codim-1 half is the riskiest piece
   and the one with the least Mathlib support — `CodimOneExtension.lean` +
   `Thm32RationalMapExtension.lean` (`thm:codim_one_extension`,
   `lem:milne_codim1_indeterminacy`, `lem:av_codimOneFree_of_indeterminacy`).
   Its commutative-algebra backbone is **Auslander–Buchsbaum** + the
   **coheight ↔ Krull-dimension** bridge (`AuslanderBuchsbaum.lean`,
   `CoheightBridge.lean`).

3. **Pointed ⇒ homomorphism.** The extended regular map sending `0 ↦ 0` is a
   homomorphism by the rigidity corollaries (`RigidityLemma.lean`: rigidity lemma,
   additivity Cor. 1.5, Cor. 1.2).

4. **Uniqueness.** Two such homomorphisms agree on `fᴾ(C)` and hence on the sumset
   filling `J` (dimension count `dim C^{(g)} = g = dim J` + properness).

## Phase / risk notes

| Piece | Status | Risk |
|---|---|---|
| Albanese UP assembly (`AlbaneseUP.lean`) | sorries in the symmetric-power / descent lemmas | depends on the symmetric-power-of-schemes Mathlib gap, shared with the parent's historical Route B |
| Thm 3.2 codim-1 extension | open (`thm:codim_one_extension`) | **highest** — no Mathlib Weil-divisor API for Lemma 3.3; the pointwise-valuative detour (run the valuative criterion at each codim-1 DVR separately) is the candidate that side-steps building Weil-divisor theory |
| Auslander–Buchsbaum / depth | mostly proved; substrate | Ext-vanishing / depth bookkeeping |
| Rigidity corollaries | proved in parent | none expected |

## Notes for the prover

- The kept `Picard/FGAPicRepresentability.lean` and `RiemannRoch/WeilDivisor.lean`
  are **thin slices** — only the declarations the cone consumes remain; the rest
  of those developments was carved.
- Do not attempt to re-derive `Pic⁰_{C/k}` or the cohomology engine; they are not
  in this subproject.
- The symmetric-power / Abel–Jacobi `sorry`s and the Thm 3.2 codim-1 `sorry` are
  the two genuine poles; everything else is bookkeeping around them.
