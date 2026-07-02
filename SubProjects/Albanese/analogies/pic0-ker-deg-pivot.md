# Analogy: Pic⁰_{C/k} via ker(deg) instead of identity-component

## Mode
api-alignment

## Slug
pic0-ker-deg-pivot

## Iteration
197

## Question

Should the project pivot from defining `Pic⁰_{C/k}` as `IdentityComponent
(PicScheme C)` (Stacks 04KU/04KV, parked ~4 iters at 0/it) to defining
it as `ker(deg : Pic_{C/k} → ℤ_{C/k})` (A.3.vii, gated)?

## Project artifact(s)
- `AlgebraicJacobian/Picard/IdentityComponent.lean:236-258` —
  `IdentityComponent` def (general substrate).
- `AlgebraicJacobian/Picard/IdentityComponent.lean:737-743` —
  `Scheme.Pic0Scheme C` def (currently `sorry`; specialises substrate
  to `G = PicScheme C`).
- `AlgebraicJacobian/Picard/IdentityComponent.lean:412-479` —
  `geometricallyConnected_of_connected_of_section`
  (Stacks 04KU helper; `sorry`-bodied, pending Stacks 037Q / 04KV
  substrate in Mathlib).
- `AlgebraicJacobian/Picard/IdentityComponent.lean:779-784` —
  `PicScheme.degree` def (degree map on `k`-points, currently `sorry`).
- `AlgebraicJacobian/Picard/Pic0AbelianVariety.lean` — downstream
  consumer; uses `Pic0Scheme C : Over (Spec k)` opaquely.
- `AlgebraicJacobian/Albanese/AlbaneseUP.lean:41-76` — further
  downstream consumer; uses `Pic0.jacobianScheme = (bundle C).scheme`
  with `Pic0Scheme` underlying.

## Decisions identified

The directive bundles two distinct decisions:

1. **What is `Pic⁰_{C/k}` definitionally?** Identity-component (Stacks
   04KU/04KV) vs degree-zero open-and-closed subscheme (Kleiman
   `thm:Pphifin` + `ex:curves`)?
2. **Is there a Mathlib idiom for "kernel of a group-scheme
   morphism"** that the project should use directly?

### Decision 1: Underlying scheme of `Pic⁰_{C/k}`

- **Mathlib idiom**: NEITHER `IdentityComponent` of a group scheme NOR
  `ker(deg)` of a morphism of group schemes exists in Mathlib b80f227.
  Mathlib has `MonoidHom.ker` (sets / `Subgroup G`) but no
  scheme-level `GrpObj.ker`. Mathlib's `CategoryTheory.Limits.kernel`
  requires `HasZeroMorphisms`, which `Scheme` does not satisfy
  (`Scheme` is cartesian-monoidal, not abelian). The **literature**
  has two equivalent definitions for smooth-proper-curve targets:
  Kleiman `prp:pic0` (identity component) and Kleiman
  `ex:curves` + Milne III.1 p.~87 (kernel of degree = `Pic⁰=Pic^0`).
- **Project's current path**: Identity-component via Stacks 04KU/04KV
  (parked, ~350 LOC pending Mathlib upstream `Stacks 037Q` /
  `04KV`).
- **Gap**: divergent-with-cost. The identity-component definition
  requires building project-side or upstream Mathlib infrastructure
  (`LocallyConnectedSpace` for locally-Noetherian schemes;
  `geometricallyConnected_of_connected_of_section`; descent of clopen
  partitions along fpqc base change). The degree-stratification
  definition only requires Kleiman §6 `thm:Pphifin` (the Hilbert-
  polynomial open-and-closed decomposition) and the curve-specific
  identification "leading coefficient of Hilbert polynomial = degree"
  (Riemann–Roch, RR.1).
- **Cost of divergence (current shipped path)**:
  - 2 typed sorries in `IdentityComponent.lean` (`geometricallyConnected_of_connected_of_section`,
    `IdentityComponent.baseChangeIso` iso slot) waiting on Stacks
    037Q / 04KV substrate not in Mathlib b80f227.
  - 1 typed sorry in `IdentityComponent.isSubgroupHomomorphism`
    needing EGA IV₂ 4.5.8 (smooth × geom-conn → conn) + Stacks 04KU.
  - 1 typed sorry in `IdentityComponent.isFiniteTypeGeometricallyIrreducible`
    needing the group-translation argument (EGA IV₂ 4.5.8/4.6.1).
  - Phase A.3.i parked at ~0/iter for 4 iters; ~350 LOC of
    Mathlib-upstream-grade work remaining.
- **Verdict**: **STRUCTURAL_OK** (pivot recommended).

### Decision 2: Mathlib kernel idiom for `f : G → H` of group schemes

- **Mathlib idiom**: No direct idiom. The category-theoretic shape
  ("kernel of a group-object morphism in a finite-limit category") is
  the pullback `pullback f (e_H ∘ !) : ker f ⟶ G`, where
  `e_H : 𝟙_C ⟶ H` is the identity of the target group object and
  `!` is the unique map to the terminal. Mathlib supports this
  IMPLICITLY via `CategoryTheory.Limits.HasPullbacks` on schemes, but
  does not package `GrpObj.ker` as a named construction.
  Closest precedents:
  - `MonoidHom.ker` (`Mathlib.Algebra.Group.Subgroup.Ker`): plain
    group homomorphism in Type, returns `Subgroup G`. Not applicable
    at scheme level.
  - `AlgebraicGeometry.Scheme.Hom.ker`
    (`Mathlib.AlgebraicGeometry.IdealSheaf.Basic`): kernel ideal
    sheaf of a scheme morphism, i.e. `Y.IdealSheafData` not a
    `Scheme`. A different concept (set-theoretic preimage of zero
    section, not the categorical fiber over the identity element).
  - `CategoryTheory.Limits.kernel`: requires `HasZeroMorphisms`, not
    applicable to `Scheme` or `Over (Spec k)`.
  - `MonoidHom.fiberEquivKer`: the categorical insight (kernel =
    fiber over identity), but in Type only.
- **Project's natural reframing**: The directive's "Pic⁰ := ker(deg)"
  framing is conceptual. The PRACTICAL construction is the
  degree-stratification:
  `PicScheme C = ∐_{d∈ℤ} Pic^d C` (Kleiman `ex:curves`), with
  `Pic⁰ := Pic^0` the degree-0 open-and-closed subscheme. This sidesteps
  the categorical-pullback definition entirely.
- **Gap**: NEEDS_MATHLIB_GAP_FILL (categorical `GrpObj.ker`) but with
  workaround: the degree-stratification gives the kernel directly,
  without invoking pullback-of-identity. The kernel is the union of
  connected components mapping to `0 ∈ ℤ`, and in the discrete
  codomain case this is just the preimage of an open-and-closed
  point.
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** for the abstract idiom, but
  not on the critical path: the project does not need to invoke a
  generic kernel construction, only the curve-specific
  decomposition. The "ker(deg)" framing in the directive should be
  read as a NAMING / MATHEMATICAL JUSTIFICATION for the degree-0
  component, not as a literal `kernel.lift` / `pullback.lift`
  invocation.

## Confirmation of the equivalence "ker(deg) = identity component"

### Kleiman §6, `ex:curves` (lines 4665–4681 of `references/kleiman-picard-src/kleiman-picard.tex`)

> *Assume $X/S$ is locally projective over $S$ and flat, and its
> geometric fibers are integral curves. Given an integer $m$, let
> $\Pic^m_{X/S} \subset \Pic_{X/S}$ be the set of points representing
> invertible sheaves $\mathcal L$ of degree $m$. Show the $\Pic^m_{X/S}$
> are open and closed subschemes of finite type; show they are
> disjoint and cover; and show that forming them commutes with
> changing $S$.*
>
> *Show there is no abuse of notation: the fiber of $\Pic^0_{X/S}$
> over $s\in S$ is the connected component of $0\in\Pic_{X_s/k_s}$.
> Show there is no torsion: $\Pic^0_{X/S}=\Pic^\tau_{X/S}$. Show each
> $\Pic^m_{X/S}$ is an fppf-torsor under $\Pic^0_{X/S}$.*

This is the **direct citation** for `ker(deg) = identity component` on
smooth proper geometrically integral curves: the degree-0 component IS
the connected component of the identity. The project's curve hypotheses
(`SmoothOfRelativeDimension 1 C.hom + IsProper C.hom + GeometricallyIntegral C.hom`)
satisfy Kleiman's setup.

### Milne III.1 (PDF p.~93 / book p.~87)

> *Let $\Pic^r(C)$ be the set of divisor classes of degree $r$. For
> a fixed point $P_0$ on $C$, the map $[D]\mapsto[D+rP_0]:
> \Pic^0(C)\to\Pic^r(C)$ is a bijection **(both $\Pic^0(C)$ and
> $\Pic^r(C)$ are fibres of the map $\deg : \Pic(C)\to\Z$)**.*

And p.~88:
> *We write $\Pic^0(C)$ for the group of isomorphism classes of
> invertible sheaves of degree zero on $C$.*

This is the **textbook definition of `Pic⁰` for a curve**: kernel of
the degree map. Milne's Theorem 1.6 then says this functor `P_C^0` is
represented by an abelian variety (the Jacobian), with no detour
through identity-component theory at all.

### Kleiman §6 `rmk:curves` (line 4682)

> *There is another important case where $\Pic^0_{X/S}=\Pic^\tau_{X/S}$,
> namely, when $X$ is an Abelian $S$-scheme. [...]*

Confirms the identification also holds in the abelian-scheme case
(used downstream when iterating to `Pic⁰` of `Pic⁰`).

**Conclusion**: The equivalence `ker(deg) = identity component` is
mathematically standard, explicitly cited in both primary sources
(Kleiman) and the project's secondary reference (Milne). For the
project's curve hypothesis it is provable from Kleiman §6 alone,
WITHOUT invoking 04KU / 04KV.

## Recommendation

**Pivot to ker(deg)-style Pic⁰ via the degree-stratification**, with
concrete plan:

1. **Repurpose `IdentityComponent.lean`** (or split into two files).
   The abstract `GroupScheme.IdentityComponent` substrate can stay
   for future use (no urgency to close its sorries — those are
   pure-Mathlib upstream-grade lemmas).

2. **Add Kleiman `ex:curves` decomposition** as the substrate.
   Sketch (using Mathlib b80f227 instances `inferInstance` shape):
   ```lean
   /-- Kleiman ex:curves: the degree-`d` component of the Picard scheme
   of a smooth proper geom integral curve, as an open-and-closed
   subscheme of `PicScheme C`. -/
   noncomputable def PicScheme.degComp {k : Type u} [Field k]
       (C : Over (Spec (.of k)))
       [SmoothOfRelativeDimension 1 C.hom] [IsProper C.hom]
       [GeometricallyIntegral C.hom]
       (d : ℤ) : Over (Spec (.of k)) := ...

   /-- The open-and-closed inclusion `Pic^d_{C/k} ↪ Pic_{C/k}`. -/
   noncomputable def PicScheme.degComp.ι {k : Type u} [Field k]
       (C : Over (Spec (.of k))) [...] (d : ℤ) :
       PicScheme.degComp C d ⟶ PicScheme C := ...
   ```

3. **Redefine `Pic0Scheme C := PicScheme.degComp C 0`** in
   `IdentityComponent.lean` (or new file `Picard/Pic0ByDegree.lean`).
   The TYPE remains `Over (Spec k)`, so downstream consumers in
   `Pic0AbelianVariety.lean` and `Albanese/AlbaneseUP.lean` are
   ABI-unchanged.

4. **Inherit `GrpObj (Pic0Scheme C)`** from the multiplication on
   `PicScheme C`: `deg(L ⊗ M) = deg L + deg M`, so `Pic^0 × Pic^0 →
   Pic^0` via restricted multiplication. Closure under inverses:
   `deg(L⁻¹) = -deg L`, zero at degree 0. Identity: `O_C` has
   degree 0. Total LOC for the `GrpObj` instance: ~30–50.

5. **The geometric-irreducibility statement** (currently
   `Pic0.geometricallyIrreducible` in `Pic0AbelianVariety.lean`)
   STILL depends on identity-component theory in the long run
   (Kleiman `prp:pic0`), but with the pivot:
   - The statement no longer blocks the **definition** of `Pic⁰` or
     its downstream `Pic^0`-torsor structure.
   - The substrate "`Pic^0` connected over `k̄`" can be deferred or
     attacked via the same Stacks 04KU machinery in isolation.
   - Or, in characteristic zero, derived from `Pic^τ` finiteness +
     `Pic^0 = Pic^τ` (Kleiman `ex:curves`), bypassing 04KU entirely.

6. **The "Pic⁰ = IdentityComponent" equivalence** becomes a separate
   theorem (currently captured loosely in
   `Pic0Scheme.kPoints_iff_kerDegree`), provable when 04KU/04KV land
   upstream. It is NOT on the critical path for
   `nonempty_jacobianWitness`.

### Mathlib alignment summary

| Item | Mathlib idiom | Project path | Verdict |
|---|---|---|---|
| `Pic⁰` underlying scheme | (none — both routes are project-side) | currently identity-component (parked); should pivot to degree-stratification | STRUCTURAL_OK |
| `GrpObj.ker` for group schemes | NEEDS_MATHLIB_GAP_FILL (no idiom); workaround via curve-specific degree decomposition | not needed under the workaround | NEEDS_MATHLIB_GAP_FILL (sidestepped) |
| Hilbert-polynomial open-and-closed decomposition (Kleiman `thm:Pphifin`) | (none — Mathlib has no scheme-level Hilbert polynomial yet) | A.3.vii substrate (gated, ~80–200 LOC) | NEEDS_MATHLIB_GAP_FILL — but cheaper than 04KU/04KV |
| Pic⁰ = ker(deg) equivalence | (none — too specialised) | post-hoc theorem | NEEDS_MATHLIB_GAP_FILL (deferrable) |

### Estimated cost of pivot

| Component | LOC | Status |
|---|---|---|
| Kleiman `thm:Pphifin` / `ex:curves` decomposition of `PicScheme` | ~80–150 | A.3.vii substrate (gated) |
| `Pic0Scheme C := PicScheme.degComp C 0` | ~10 | trivial |
| Open-and-closed inclusion `Pic^0 ↪ PicScheme` | ~10 | trivial |
| `GrpObj (Pic0Scheme C)` via restricted multiplication | ~30–50 | needs `deg(L ⊗ M) = deg L + deg M` + restriction |
| Downstream consumer updates (none required for type) | ~0–25 | ABI-preserving for `Pic0Scheme` type |
| **TOTAL (pivot path)** | **~130–245** | replaces ~350 LOC parked identity-component path |

### Net effect on Route A iter budget

- Identity-component path (parked): 4 iters elapsed at 0/it, ~350 LOC
  outstanding with substrate-unowned Mathlib gaps (Stacks 037Q,
  04KU/04KV). Best-case ~20+ iters; risk of unbounded park.
- Pivot path: ~6–10 iters (under Cartier route assumption for A.3.vii
  substrate ~3–5 iters + Pic⁰ assembly ~3–5 iters). Critical
  Mathlib gap is Hilbert-polynomial open-and-closed decomposition
  (Kleiman `thm:Pphifin`), which the project ALREADY plans to build
  for A.3.vii regardless.

The pivot saves an estimated **10–18 iters** and removes the
unbounded-park risk on Stacks 04KU/04KV.

### Caveat — the geometric-irreducibility theorem still needs care

`Pic0.geometricallyIrreducible` in `Pic0AbelianVariety.lean` is the
ONE downstream statement where the identity-component substrate
matters intrinsically: Kleiman `prp:pic0` proves
`Pic⁰ geometrically irreducible` precisely because it is the
connected component of the identity (in a smooth group scheme,
connected components are irreducible). Under the degree-stratification
definition, the geom-irreducibility of `Pic^0` is NOT immediate — it
still needs to be shown that `Pic^0` (= degree-0 component) is
connected, which IS the content of Stacks 04KU once you have a
section.

However, with the pivot:
- Geometric irreducibility no longer BLOCKS the definition of
  `Pic⁰` or the bulk of downstream construction.
- It is needed only at the assembly stage (`Pic0.isAbelianVariety`),
  and can be attacked in isolation with the same Stacks 04KU
  substrate (or finessed via `Pic^τ` finiteness in characteristic 0).
- The other three conjuncts of "abelian variety" (smooth, proper,
  `GrpObj`) are independent and proceed via the pivot definition.

This is a partial decoupling, not a full elimination. But it converts
the Stacks 04KU dependency from "blocks the whole positive-genus
arm" to "blocks one of four conjuncts of the assembly statement",
which is a strict improvement.

### When the pivot might be wrong

The pivot would be REJECTED if:
- Downstream consumers depend on `Pic0Scheme` being defined as
  `IdentityComponent (PicScheme C)` ABI (none do — confirmed by
  reading `Pic0AbelianVariety.lean` and `Albanese/AlbaneseUP.lean`).
- The curve hypothesis `GeometricallyIntegral C.hom` were dropped
  (then `Pic^0 ≠ Pic⁰` is possible; cf. Kleiman `eg:Pphifin` for
  disjoint-lines). Project hypothesis is fixed.
- Mathlib were to ship 04KU/04KV imminently (low probability —
  no PR visible at b80f227).
