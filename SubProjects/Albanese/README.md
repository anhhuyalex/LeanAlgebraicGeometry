# AlgebraicJacobian — Albanese subproject

<!-- archon:readme -->

## Project

A standalone subproject, extracted from the **Algebraic-Jacobian-Challenge**, focused on the
**Albanese universal property** of the Jacobian of a smooth proper geometrically irreducible
curve `C/k`: that the identity component `J := Pic⁰_{C/k}` of the Picard scheme, together with
the Abel–Jacobi morphism `fᴾ : C → J` at a fixed `k`-rational point `P`, exhibits `J` as the
**Albanese object** of the pointed curve `(C, P)` — every pointed morphism `C → A` into an
abelian variety factors uniquely through a homomorphism `J → A` (Milne, *Abelian Varieties*,
III §6, Prop. 6.1).

The cone kept here is the Albanese universal property together with the geometric and
commutative-algebra substrate its proof rests on:

- the **rational-map-extension theorem** (Milne I §3, Thm 3.2: a rational map from a
  nonsingular variety to an abelian variety is everywhere defined);
- the **codimension-one indeterminacy** machinery feeding Thm 3.2;
- the **Auslander–Buchsbaum** formula and its `depth` / projective-dimension substrate;
- the **coheight ↔ Krull-dimension** bridge for scheme stalks;
- the **rigidity lemma** (Milne/Mumford) and its additivity corollaries;
- a thin slice of the **Weil-divisor** and **FGA Picard** developments that the above consume.

The full Pic⁰ construction (cohomology `Rⁱf_*` engine, FGA representability, Riemann–Roch,
differentials) lives in the parent project and is **not** part of this subproject; it is
referenced in the blueprint only as context. The headline target
`AlgebraicGeometry.Scheme.Pic.albaneseUP` (the Albanese universal property statement) is the
unproven seed of this subproject.

This is an AI challenge inspired by Kevin Buzzard's analogous formalization for Riemann
surfaces.

## References

See [`references/summary.md`](references/summary.md) for a description of each source.

## Structure

- `AlgebraicJacobian/Albanese/AlbaneseUP.lean` — the Albanese universal property
- `AlgebraicJacobian/Albanese/Thm32RationalMapExtension.lean` — Milne I §3 Thm 3.2
- `AlgebraicJacobian/Albanese/CodimOneExtension.lean` — codimension-one indeterminacy extension
- `AlgebraicJacobian/Albanese/AuslanderBuchsbaum.lean` — Auslander–Buchsbaum / `depth`
- `AlgebraicJacobian/Albanese/CoheightBridge.lean` — coheight ↔ Krull-dimension bridge
- `AlgebraicJacobian/RigidityLemma.lean` — the rigidity lemma and its corollaries
- `AlgebraicJacobian/Picard/FGAPicRepresentability.lean`,
  `AlgebraicJacobian/RiemannRoch/WeilDivisor.lean` — kept slices feeding the above
- `AlgebraicJacobian/Genus0BaseObjects/`, `AlgebraicJacobian/Cohomology/StructureSheafModuleK/`
  — compile-time substrate imported by the kept files
- `blueprint/` — leanblueprint source (build with `leanblueprint pdf` and `leanblueprint web`)
- `references/` — informal sources backing the formalization
- `.archon/` — agent state (not committed)

## How to build

```bash
lake exe cache get   # download Mathlib olean cache
lake build           # compile the project
```

## How to run the formalization loop

```bash
archon loop .
```

This launches the plan → prove → review loop and opens a dashboard.
