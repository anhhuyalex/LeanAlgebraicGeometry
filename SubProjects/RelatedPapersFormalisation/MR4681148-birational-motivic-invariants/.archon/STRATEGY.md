# Strategy

## Goal

Formalize Section 2 of Lin–Shinder "Motivic invariants of birational maps"
(MR4681148, arXiv:2207.07389): construct the truncated Grothendieck group
`K₀(Var^{≤n}/k)`, the invariant `c̃: Bir(X,Y) → K₀(Var^{≤n-1}/k)` (Theorem 2.3), and
prove `Ker(ι_{n-1}) = Σ_X c̃(Bir(X))` (Proposition 2.9) — all sorry-free.

## Phases & estimations

| Phase | Status | Iters left | LOC | Key Mathlib needs | Risks |
|-------|--------|-----------|-----|-------------------|-------|
| 1 — Blueprint | ACTIVE | 1 | ~0 | — | done this iter |
| 2a — BirationalMap | NEXT | 2–3 | ~100–180 | `AlgebraicGeometry.Scheme.PartialMap`; `AlgebraicGeometry.OpenImmersion` | `RationalMap ∘ RationalMap` not in Mathlib; build composition via `PartialMap` pairs |
| 2b — TruncGrothendieck + FreeBiratClasses | NEXT | 2–3 | ~120–200 | `GroupTheory.FreeAbelianGroup`; `AlgebraicGeometry.Noetherian`; `irreducibleComponents` | generators = finite-type k-schemes (not varieties); need `FreeIsoClasses` for `lem_kernelXU` |
| 3a — c̃ (no codimension) | NEXT | 2–3 | ~100–160 | `AlgebraicGeometry.OpenImmersion` | well-definedness of c̃ = independence of U; pure cut-and-paste argument |
| 3b — c and codimension | NEXT | 3–5 | ~150–280 | `AlgebraicGeometry.Scheme.residueField`; `Ideal.height`; codim gap | codim-1 iteration over Ex(φ); residue-field → birational-class bridge; Noetherian finiteness |
| 4 — Main theorem | NEXT | 3–5 | ~200–400 | — | cut-and-paste bookkeeping in K₀(Var^{≤n-1}/k) |
| 5 — Kernel theorem | NEXT | 2–3 | ~100–200 | `AddSubgroup.closure` | permutation-orbit argument; quotient manipulation |

## Completed

| Phase | Iters (done@ · used) | LOC | Files | Key results | Reusable techniques | Pitfalls |
|-------|----------------------|-----|-------|-------------|---------------------|----------|
| — | — | — | — | — | — | — |

## Routes

Single route: formalize Section 2 of Lin–Shinder directly.
Phase 2a: `BirationalMap` built atop Mathlib's `Scheme.PartialMap` pairs; exceptional
set = complement of open-immersion locus (not just morphism domain).
Phase 2b (parallel): `TruncatedGrothendieckGroup` as quotient of `FreeAbelianGroup`
on finite-type k-schemes (not just varieties) of dim ≤ n, modulo cut-and-paste;
`FreeBiratClasses n k` (birational equiv `Setoid`) and `FreeIsoClasses n k`
(isomorphism `Setoid` — needed for `lem_kernelXU` whose K₀ presentation uses
isomorphism classes, not birational classes).
Phase 3 split: 3a proves c̃ and its homomorphism property first (no codimension
needed — pure cut-and-paste, unlocks Phase 4); 3b then proves c via codimension-1
iteration and residue-field bridge (needed only for final relation c = π_{n-1} ∘ c̃).

## Open strategic questions

- Codimension API: `Ideal.height` vs `LocalRing.krullDim` for a scheme-point codimension
  wrapper. Phase 3b will determine which path is cheaper.
- Universe level for birational `Setoid`: the equivalence relation "∃ birational map"
  on dim-n varieties needs universe-safe Lean treatment.
- `FreeIsoClasses n k` (free abelian group on isomorphism classes): distinct from
  `FreeBiratClasses n k`; needed only for the statement/proof of `lem_kernelXU` and
  `lem_kernelXY` — may reuse the same `Quotient` infrastructure.

## Mathlib gaps & new material

Gaps to fill:
- `BirationalMap X Y`: `PartialMap` pairs + open-immersion locus exceptional set.
- `FreeBiratClasses n k`: birational equivalence quotient; `FreeAbelianGroup` thereof.
- `FreeIsoClasses n k`: isomorphism quotient of dim-n varieties; needed for `lem_kernelXU`.
- `TruncatedGrothendieckGroup n k`: `FreeAbelianGroup` on finite-type k-schemes mod cut-and-paste.
- Codimension-1 point iteration + `AlgebraicGeometry.Scheme.residueField`-to-birational-class
  bridge (Phase 3b gap); `AlgebraicGeometry.Noetherian` for finiteness.

New project material:
- `cInvariant`, `cTildeInvariant`, `iotaMap`, `piMap` — all new; no Mathlib analogues.
