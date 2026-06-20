# Analogy: Rigidity-refactor scoping — drop unused hypotheses on the source

## Slug
rigidity-refactor-scoping-iter124

## Iteration
124

## Question

The closed declaration `AlgebraicGeometry.GrpObj.eq_of_eqOnOpen`
(`AlgebraicJacobian/Rigidity.lean:79–114`) carries source-side
hypotheses (`[GrpObj X]`, `[SmoothOfRelativeDimension n X.hom]`,
`[IsProper X.hom]`, `[GeometricallyIrreducible X.hom]`) that the
proof body does not use, and that block the M2.a application site
(`X = ℙ¹_{k̄}`, which is not a group object). What hypotheses are
truly used, what is the Mathlib-aligned shape of the refactored
declaration, and what does this cost?

## Project artifact(s)
- `AlgebraicJacobian/Rigidity.lean:79–114` — `GrpObj.eq_of_eqOnOpen`,
  the closed Mumford-rigidity wrapper.
- `AlgebraicJacobian/Rigidity.lean:62–67` — the file's own comment
  block acknowledging the unused hypotheses, kept "for
  forward-compatibility with the informal Mumford statement".
- `blueprint/src/chapters/Rigidity.tex:10–19` — blueprint statement
  with the same forward-compatible hypotheses.
- `blueprint/src/chapters/Jacobian.tex:319–352` — C.2.a/b sub-step
  that needs the refactored declaration: explicitly notes "$\mathbb
  P^1_{\bar k}$ is not a group scheme; however, the group-object
  structure on $X$ is used in the proof of
  Theorem~\ref{thm:GrpObj_eq_of_eqOnOpen} only to form a difference
  morphism … and the underlying equaliser-closed argument goes
  through verbatim".

## Hypothesis-use audit (project file)

Lines 90–114 of `Rigidity.lean` are the entire proof body. The
typeclass uses are:

| Line | Tactic / term | Hypothesis it consumes |
|---|---|---|
| 96–97 | `haveI : IsSeparated (Y.left ↘ Spec (CommRingCat.of k)) := IsProper.toIsSeparated` | `[IsProper Y.hom]` (USED — but only as a source of separatedness) |
| 101–102 | `GeometricallyIrreducible.irreducibleSpace_of_subsingleton X.hom` | `[GeometricallyIrreducible X.hom]` (USED — gives `IrreducibleSpace X.left` from the `Subsingleton (Spec k)` + `Nonempty (Spec k)` instances) |
| 105–106 | `Scheme.PartialMap.Opens.isDominant_ι (IsOpen.dense U.isOpen hU)` | `hU` plus the just-derived `IrreducibleSpace X.left` |
| 112 | `Over.OverMorphism.ext` | structural (no typeclass) |
| 113–114 | `ext_of_isDominant_of_isSeparated' (S := Spec (.of k))` | `[IsReduced X.left]` (USED, explicit instance); the `[g.IsOver S]`, `[g.left.IsOver S]` instances are auto-derived from the `Over (Spec (.of k))` ambient via `OverClass.fromOver` |

UNUSED hypotheses (verified by line-by-line audit):

- `{n : ℕ}`
- `[SmoothOfRelativeDimension n X.hom]`
- `[IsProper X.hom]`
- `[GrpObj X]`
- `{m : ℕ}`
- `[SmoothOfRelativeDimension m Y.hom]`
- `[GeometricallyIrreducible Y.hom]`
- `[GrpObj Y]`

The file's own comment (L62–68) already enumerates these as
unused. This audit confirms it.

## Decisions identified

### Decision 1: Which (potentially unused) hypotheses should the refactored declaration keep?

- **Mathlib idiom**: minimally state the typeclass hypotheses
  actually used by the proof. The Mathlib analogue
  `ext_of_isDominant_of_isSeparated'` carries exactly the three
  hypotheses its body needs: `[IsReduced X]`, `[IsSeparated (Y ↘
  S)]`, `[IsDominant ι]`. No "forward-compatible" decorations.
  Cite: `Mathlib.AlgebraicGeometry.Morphisms.Separated:319–322`.
  Why Mathlib chose it: the `ext_of_isDominant_of_isSeparated'`
  lemma is a low-level glue corollary applied in several different
  callers (one-liner specializations exist for `IsProper Y` callers,
  for `Y.IsSeparated` callers via `ext_of_isDominant`, etc.). Each
  caller derives its needed instance from its own context; the core
  lemma stays minimal.
- **Project's current path**: ten hypotheses, of which eight are
  decorative and only three are load-bearing. The decorative ones
  block the M2.a application site (`X = ℙ¹_{k̄}` is not a
  `GrpObj`).
- **Gap**: divergent-with-cost. The cost is concrete: the M2.a
  blueprint sub-step C.2.b (`Jacobian.tex:328`) explicitly calls
  out that the existing signature blocks the M2.a application, and
  the only paths forward are (i) "a thin variant of the lemma"
  (i.e. this refactor) or (ii) "inlining its proof template" (a
  full duplicate of the proof). The refactor cost is ~10 LOC; the
  inline-duplicate cost is ~25 LOC plus carrying a parallel copy
  of `Rigidity.lean`'s proof at the M2.a site.
- **Verdict**: ALIGN_WITH_MATHLIB. The proof body is already
  Mathlib-shaped (a one-liner over `ext_of_isDominant_of_isSeparated'`);
  the signature should mirror the body. The decoration was always
  cosmetic and is now an active blocker.

### Decision 2: Should the `[IsProper Y.hom]` hypothesis be weakened to `[IsSeparated Y.hom]`?

- **Mathlib idiom**: state the hypothesis the proof actually uses.
  The proof needs only separatedness of `Y → Spec k`; properness
  is overkill. `Mathlib.AlgebraicGeometry.Morphisms.Proper:42`
  defines `IsProper f extends IsSeparated f, …`, so the
  `IsProper.toIsSeparated` projection is automatic, making the
  `[IsSeparated Y.hom]` form strictly more general at zero caller
  cost.
- **Project's current path**: `[IsProper Y.hom]` is kept, which
  works at the M2.a call site (where `A` is proper by assumption)
  but rules out other potential callers (e.g. rigidity on
  separated-but-non-proper targets like `𝔸¹_k`).
- **Gap**: divergent-with-cost (small). The cost is one future
  generalisation hop; this is well within "PROCEED with the
  generalisation now since it's free".
- **Verdict**: ALIGN_WITH_MATHLIB. Weaken `[IsProper Y.hom]` to
  `[IsSeparated Y.hom]`; M2.a's `A_{k̄}` satisfies the weaker
  hypothesis trivially.

### Decision 3: Should `[GeometricallyIrreducible X.hom]` be weakened to `[IrreducibleSpace X.left]`?

- **Mathlib idiom**: the strict-minimum-hypothesis idiom would
  prefer `[IrreducibleSpace X.left]` (what the proof actually
  uses). However, this is a borderline case — for source schemes
  over a field, `[GeometricallyIrreducible X.hom]` is the
  geometrically-natural hypothesis and is often what callers
  have. Mathlib's `ext_of_isDominant_of_isSeparated'` carries
  `[IsDominant ι]` (the strict use) rather than the
  geometrically-natural "non-empty open of an irreducible
  source", but that is a different decision shape (the lemma
  speaks about morphisms, not opens).
- **Project's current path**: `[GeometricallyIrreducible X.hom]`,
  with `Spec (.of k)` baked-in (uses `Subsingleton + Nonempty
  (Spec k)` via the `Spec` of a field).
- **Gap**: divergent-equivalent (M2.a's `ℙ¹_{k̄}` satisfies both
  forms cleanly). Keeping `[GeometricallyIrreducible X.hom]` is
  ergonomic; weakening to `[IrreducibleSpace X.left]` is more
  general but the M2.a caller already has the stronger form. The
  proof body's `Subsingleton (Spec k)` reliance also keeps the
  field-specific shape natural.
- **Verdict**: PROCEED (project's path is fine, keep
  `[GeometricallyIrreducible X.hom]`). If a future caller needs
  the `IrreducibleSpace`-only form, it can be added as a sibling
  `eq_of_eqOnOpen_of_irreducibleSpace`.

### Decision 4: Namespace shape (`GrpObj.eq_of_eqOnOpen` → ?)

- **Mathlib idiom**: name the declaration after its mathematical
  content. `Mathlib.AlgebraicGeometry.Morphisms.Separated:285,319`
  uses `ext_of_isDominant_of_isSeparated` (no `Scheme.` prefix; at
  the root `AlgebraicGeometry` namespace) for analogous "scheme
  morphism equality from agreement-on-a-dense-locus" lemmas. The
  project's `GrpObj.eq_of_eqOnOpen` is fundamentally misnamed:
  there is no `GrpObj` in the type, and the body does not use any
  `GrpObj` operation.
- **Project's current path**: `AlgebraicGeometry.GrpObj.eq_of_eqOnOpen`
  with the `GrpObj.` prefix kept "for forward-compatibility with
  the informal Mumford statement" (`Rigidity.lean:64–66`).
- **Gap**: divergent-and-misleading. The namespace is a beacon
  of intent that the type signature contradicts. After the
  hypothesis drop, the namespace becomes actively wrong.
- **Verdict**: ALIGN_WITH_MATHLIB. Rename to drop the `GrpObj.`
  prefix. Recommended targets:
  - `AlgebraicGeometry.Scheme.Over.ext_of_eqOnOpen` — mirrors
    Mathlib's `ext_of_*` family.
  - `AlgebraicGeometry.eq_of_eqOnOpen` — keep the project's
    `eq_of_*` name style but at the root `AlgebraicGeometry`
    namespace.
  - The first is preferable for Mathlib alignment; the second is
    a smaller diff.
  The blueprint `\lean{AlgebraicGeometry.GrpObj.eq_of_eqOnOpen}`
  reference in `Rigidity.tex:13` and the `\uses{thm:GrpObj_eq_of_eqOnOpen}`
  in `Jacobian.tex:248` must be updated.

## Recommendation

Execute the refactor as a single small iter-125 task. The new
declaration:

```lean
/-- Rigidity for morphisms of schemes (scheme-level form): two morphisms
`g₁, g₂ : X ⟶ Y` between schemes over `Spec k` whose restrictions to a
non-empty open `U ⊆ X` agree as scheme morphisms — for `X` reduced and
geometrically irreducible over `Spec k` and `Y` separated over `Spec k`
— agree everywhere. -/
theorem AlgebraicGeometry.Scheme.Over.ext_of_eqOnOpen
    {X Y : Over (Spec (.of k))}
    [IsSeparated Y.hom]
    [GeometricallyIrreducible X.hom]
    [IsReduced X.left]
    (g₁ g₂ : X ⟶ Y) (U : X.left.Opens) (hU : (U : Set X.left).Nonempty)
    (h : (U.ι : (U : X.left.Opens).toScheme ⟶ X.left) ≫ g₁.left =
      (U.ι : (U : X.left.Opens).toScheme ⟶ X.left) ≫ g₂.left) :
    g₁ = g₂ := by
  haveI : IsSeparated (Y.left ↘ Spec (CommRingCat.of k)) := ‹IsSeparated Y.hom›
  haveI : IrreducibleSpace X.left :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton X.hom
  haveI : IsDominant (U.ι : (U : X.left.Opens).toScheme ⟶ X.left) :=
    Scheme.PartialMap.Opens.isDominant_ι (IsOpen.dense U.isOpen hU)
  refine Over.OverMorphism.ext ?_
  exact ext_of_isDominant_of_isSeparated' (S := Spec (.of k))
    (X := X.left) (Y := Y.left) (f := g₁.left) (g := g₂.left) U.ι h
```

Blueprint update in `Rigidity.tex`: drop the smoothness/properness/group-object
hypotheses from the informal statement (or restate as "Let $X, Y$ be
schemes over $k$ with $X$ reduced and geometrically irreducible and $Y$
separated over $\Spec k$ …"); update the `\lean{...}` reference.

Blueprint update in `Jacobian.tex:328` (sub-step C.2.b): the "however,
the group-object structure on $X$ is used in the proof of
Theorem~\ref{thm:GrpObj_eq_of_eqOnOpen} only to form a difference
morphism …" note becomes obsolete and should be replaced with a
direct citation of the refactored declaration.

The `[IsProper Y.hom]` weakening to `[IsSeparated Y.hom]` is free
(via `IsProper.toIsSeparated` at any caller with a proper target).
M2.a's `A_{k̄}` is proper, so the weakening costs the caller
nothing.

Project-internal consumers: ZERO Lean consumers (only `Rigidity.lean`
itself references the symbol); blueprint references are TWO
mechanical updates (`Rigidity.tex:10–19`, `Jacobian.tex:248,328`).

**Mathlib contribution candidate**: the refactored declaration in
the `Over (Spec S)`-bundled form is a thin specialization of
`ext_of_isDominant_of_isSeparated'`. Not a strong contribution
candidate on its own — Mathlib's `ext_of_isDominant_of_isSeparated'`
is already the strict generalization. The `(non-empty open) ⇒ (dense
inclusion is dominant)` packaging could be lifted as a Mathlib
corollary `AlgebraicGeometry.Scheme.Over.ext_of_eqOnNonemptyOpen`
in `Mathlib.AlgebraicGeometry.Morphisms.Separated`, but the
incremental value (over composing the two existing lemmas) is small.

If the project ever wants a Mathlib upstream from this work, the
candidate is the corollary form

```
theorem AlgebraicGeometry.ext_of_eqOnNonemptyOpen
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsReduced X] [IsSeparated (Y ↘ S)] [IrreducibleSpace X]
    {f g : X ⟶ Y} [f.IsOver S] [g.IsOver S]
    (U : X.Opens) (hU : (U : Set X).Nonempty)
    (h : U.ι ≫ f = U.ι ≫ g) : f = g
```

placed in `Mathlib.AlgebraicGeometry.Morphisms.Separated` next to
`ext_of_isDominant_of_isSeparated'`. This is a ~5-line lemma whose
value is the API convenience of "non-empty open of an irreducible
space" over "dominant morphism".
