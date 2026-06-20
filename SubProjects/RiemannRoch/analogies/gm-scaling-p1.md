# Analogy: shape of `ProjectiveLineBar`, `Gm`, `Ga`, `gmScalingP1` for the 𝔾ₘ-scaling shortcut

## Mode
api-alignment

## Slug
gm-scaling-p1

## Iteration
165

## Question
What is the Mathlib-aligned shape for the three new infrastructure declarations
`ProjectiveLineBar`, `Gm` (with `Ga` as the demoted-route companion), and
`gmScalingP1 : ℙ¹ × 𝔾_m ⟶ ℙ¹`, in particular: which Mathlib API does each
extend (Proj? AffineSpace? a from-scratch Spec? a typeclass? a bare morphism?),
and where should the declarations live?

## Project artifact(s)
- `AlgebraicJacobian/AbelianVarietyRigidity.lean:909-989` — three scaffolds (`morphism_P1_to_grpScheme_const`, `genusZero_curve_iso_P1`, `rigidity_genus0_curve_to_grpScheme`) consume the to-be-built objects via an *abstract* `P1 : Over (Spec kbar)` proxy.
- `blueprint/src/chapters/AbelianVarietyRigidity.tex:908-989` (def:genus0_base_objects, def:gaTranslationP1) — informal description of the three new objects + chartwise σ_× / σ.

## Mathlib state (verified by LSP + on-disk grep)
- **ℙ¹ as a scheme**: NO `ProjectiveSpace` constructor exists. The canonical idiom is `AlgebraicGeometry.Proj 𝒜` for graded rings (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`).
  - `IsProper (Proj.toSpecZero 𝒜)` is shipped (`Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper:366`) when `Algebra.FiniteType (𝒜 0) A`. ⇒ `IsProper ProjectiveLineBar.hom` is FREE on this realization.
  - `Proj.affineOpenCover` (`ProjectiveSpectrum.Basic`) ships the standard `D₊(xᵢ)` chart cover.
  - `Proj.awayι : Spec (HomogeneousLocalization.Away 𝒜 f) ⟶ Proj 𝒜` and `Proj.instIsOpenImmersionAwayι` give the two charts `𝔸¹ = D₊(X)` and `D₊(Y) = ℙ¹ \ {0}` directly.
  - `Smooth`, `SmoothOfRelativeDimension 1`, `GeometricallyIrreducible` are NOT shipped on `Proj 𝒜.toSpecZero`. These are project-side proofs.
- **`AffineSpace n S`** (`Mathlib.AlgebraicGeometry.AffineSpace:46`) ships:
  - `IsAffine` (when `S` is affine), `IsAffineHom`, `Surjective`, `LocallyOfFinitePresentation` (when `n` finite), `SpecIso n R : 𝔸(n; Spec R) ≅ Spec (CommRingCat.of (MvPolynomial n R))`, `homOverEquiv : { f : X ⟶ 𝔸(n; S) // f.IsOver S } ≃ (n → Γ(X, ⊤))`, `homOfVector` (build a morphism from a tuple of global sections).
  - NO `Smooth`/`GeometricallyIrreducible` instances. (Project-side.)
- **Group schemes 𝔾_m / 𝔾_a**: NOT in Mathlib. No `AlgebraicGeometry.Gm`/`Ga` declaration, no `GroupScheme` namespace.
- **`GrpObj` Yoneda installer**: `CategoryTheory.GrpObj.ofRepresentableBy (F : Cᵒᵖ ⥤ GrpCat) (α : (F ⋙ forget).RepresentableBy X) : GrpObj X` at `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_:35` — the canonical way to install a group-object instance on a Yoneda-representable presheaf of groups. (Project's `Cotangent/GrpObj.lean` already uses `GrpObj` from this namespace.)
- **Smoothness of GrpObj over k̄**: `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed` (`Mathlib.AlgebraicGeometry.Group.Smooth:38`) — `[GrpObj (Over.mk f)] + [LocallyOfFinitePresentation f] + [IsReduced G] + [IsAlgClosed K] ⇒ Smooth f`. ⇒ For `Gm`/`Ga` as `GrpObj`, `Smooth` is FREE.
- **GrpObj base change**: `AlgebraicGeometry.Scheme.GrpObjAsOverPullback` (`Mathlib.AlgebraicGeometry.Pullbacks:808`) — `GrpObj (asOver M S) ⇒ GrpObj (asOver (pullback (M ↘ S) f) T)`. ⇒ If we ever build `Gm` integrally (over `Spec ℤ`), the `GrpObj` over `Spec k̄` is FREE by pullback. (Out of scope for this iter — just keep the option open.)
- **Glue chartwise morphisms**: `AlgebraicGeometry.Scheme.Cover.glueMorphisms` (`Mathlib.AlgebraicGeometry.Gluing:?`) — given a cover `𝒰` of `X` and `f i : 𝒰.X i ⟶ Y` matching on pairwise pullbacks, get `X ⟶ Y`. This is the canonical "define a morphism on each chart" tool.
- **Rigidity glue**: `ext_of_isDominant_of_isSeparated'` (`Mathlib.AlgebraicGeometry.Morphisms.Separated:319`) — already used by the project (`AlgebraicJacobian/Rigidity.lean:91`, `AbelianVarietyRigidity.lean:709`). 𝔾ₘ-density in ℙ¹ via `IsOpen.dense U.isOpen hU` + this lemma is the consumer pattern.

## Decisions identified

### Decision D1: realization of `ProjectiveLineBar`

- **Mathlib idiom**: `AlgebraicGeometry.Proj 𝒜` of a graded ring, specialised to `𝒜 = ℕ → Submodule k̄ (MvPolynomial (Fin 2) k̄)` (the standard ℕ-grading by total degree). The two charts `𝔸¹ = D₊(X₀)` and `ℙ¹ \ {0} = D₊(X₁)` are then `Proj.awayι` images. Cite: `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme:?` (Proj), `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic:?` (Proj.awayι, Proj.affineOpenCover), `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper:366` (IsProper).
- **Project's current path**: abstract proxy `P1 : Over (Spec kbar)` with the curve-typeclass bundle `[SmoothOfRelativeDimension 1, IsProper, GeometricallyIrreducible, genus = 0]`. The proxy is genuinely abstract — there is no concrete underlying scheme.
- **Gap**: divergent-with-cost. The abstract proxy *cannot* define a chartwise morphism (`σ_×`) — it has no charts. It also cannot provide an `𝔸¹` chart on which 𝔾ₘ is the dense open subset. So the proxy must be replaced by a concrete construction once we want `gmScalingP1` to exist as a Lean term.
- **Cost of divergence**: the proxy approach forces `gmScalingP1` to remain a `sorry`-stubbed black box; no chartwise definition, no `σ_×(0, λ) = 0` proof. The whole 𝔾ₘ-scaling shortcut becomes unprovable. The Proj realization, by contrast, gives `IsProper` free and gives the two affine charts as actual `Spec` schemes the prover can compute on.
- **Verdict**: **ALIGN_WITH_MATHLIB** — define `ProjectiveLineBar : Over (Spec (.of kbar))` as the base change to `Spec k̄` of `Proj 𝒜` for `𝒜` the standard ℕ-grading on `MvPolynomial (Fin 2) k̄` (or pulled back from `Spec ℤ` if upstreaming is in scope). The two charts are then `Proj.awayι 𝒜 X₀ …` and `Proj.awayι 𝒜 X₁ …`, both of which are `Spec` of an explicit `HomogeneousLocalization.Away` — exactly what the chartwise σ_× definition needs.
  - `[IsProper ProjectiveLineBar.hom]` — FREE (`IsProper (Proj.toSpecZero 𝒜)` for `Algebra.FiniteType k̄ k̄[X₀,X₁]`).
  - `[GeometricallyIrreducible ProjectiveLineBar.hom]`, `[SmoothOfRelativeDimension 1 _]`: project-side sub-proofs. Both are sub-builds (no Mathlib instance for `Proj`). Marked `NEEDS_MATHLIB_GAP_FILL` *inside* this `ALIGN` verdict.
  - `genus ProjectiveLineBar = 0` — still blocked on Riemann–Roch (same as the proxy path), but at least the statement is concrete.

### Decision D2: realization of `Gm` and `Ga` as group objects

- **Mathlib idiom**: install `GrpObj` via `GrpObj.ofRepresentableBy` from `Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_:35`, presenting the Yoneda-functor of groups (units / additive group of global sections). Use Mathlib's `AffineSpace (Fin 1) (Spec k̄)` for the underlying scheme of `Ga`, and `Spec (.of (Localization.Away (X : MvPolynomial Unit k̄)))` (= `Spec k̄[t, t⁻¹]`) for `Gm`. Use `smooth_of_grpObj_of_isAlgClosed` (`Mathlib.AlgebraicGeometry.Group.Smooth:38`) to derive `Smooth` for free.
- **Project's current path**: not yet built — the blueprint says `AffineSpace 𝔸(1; Spec k̄)` for `Ga` and "𝔾_m = 𝔸¹ \ {0}" for `Gm`, both with a `GrpObj` instance. No body yet.
- **Gap**: in-proposal — there is no shipped code to compare against. The blueprint's *idea* (use `AffineSpace` for `Ga`, the basic-open of `𝔸¹` for `Gm`) is the right *direction* but has two sub-decisions where Mathlib has a clear preferred shape:
  1. **Direct vs. Yoneda installation of `GrpObj`.** Mathlib's idiom (used internally for the projection of representability) is `GrpObj.ofRepresentableBy`. The blueprint isn't explicit about which approach. ⇒ pick `ofRepresentableBy`.
  2. **`Gm` as `(AffineSpace _).basicOpen (coord _ 0)` vs. `Spec k̄[t, t⁻¹]`.** Both are isomorphic schemes; only the second is *directly affine*. The second is far cleaner for installing `GrpObj` (it has `IsAffine` for free; basic-opens carry over the structure-sheaf API via `IsLocalization.Away` but are not affine by definition in Mathlib's API).
- **Verdict**: **NEEDS_MATHLIB_GAP_FILL** (Mathlib doesn't ship these), with two **ALIGN_WITH_MATHLIB** sub-rules:
  - **D2.a — `Ga`**: define `Ga : Over (Spec (.of kbar)) := (AffineSpace (Fin 1) (Spec (.of kbar))).asOver (Spec (.of kbar))` (or the canonical Over via `AffineSpace.over`). Install `GrpObj Ga` via `GrpObj.ofRepresentableBy` with the additive-group functor `(T ↦ AddGrpCat.of Γ(T.left, ⊤))`, using `AffineSpace.homOverEquiv` (`Mathlib.AlgebraicGeometry.AffineSpace:155`) as the representable-by witness (S-morphisms `T ⟶ 𝔸(1; S)` ≃ `Γ(T, ⊤)`). DO NOT define the multiplication by `Pi.lift` of an ad-hoc `homOfVector` — that builds a parallel API. The Yoneda installer is cheaper and composes with the rest of Mathlib's `Hom.group` API.
  - **D2.b — `Gm`**: define `Gm : Over (Spec (.of kbar))` as the canonical Over of `Spec (CommRingCat.of (Localization.Away (X : MvPolynomial Unit kbar)))` — i.e. `Spec k̄[t, t⁻¹]`. Install `GrpObj Gm` via `GrpObj.ofRepresentableBy` with the multiplicative-group functor `(T ↦ GrpCat.of Γ(T.left, ⊤)ˣ)`, the representable-by witness being the standard "morphism into Spec of away-localization ↔ unit in global sections" bijection. (Mathlib has `IsLocalization.Away f Γ(X, X.basicOpen f)` at `AffineScheme:632/651/666` and `Spec_basicOpen` at `AffineScheme:596` — these supply the bijection.) DO NOT define `Gm` as `(AffineSpace _).basicOpen _` — the basic-open path has weaker `IsAffine`/structure-sheaf instances and forces bridge lemmas at every consumer site.
  - **D2.c — `Smooth`**: both `Gm.hom` and `Ga.hom` should derive `Smooth` from `smooth_of_grpObj_of_isAlgClosed`. Project responsibility is to provide `[LocallyOfFinitePresentation _.hom]` (free for `Ga` from `AffineSpace.instLocallyOfFinitePresentation…OfFinite`; for `Gm` from `IsAffineHom` + `Algebra.FinitePresentation k̄ k̄[t,t⁻¹]`) and `[IsReduced _.left]` (free — both `MvPolynomial Unit k̄` and `Localization.Away t` are domains over a field).
  - **D2.d — `GeometricallyIrreducible`**: again project-side. Both are `Spec` of an integral domain over `k̄` and base-change to `Spec k̄` is itself (`k̄ = k̄`), so `GeometricallyIntegral` reduces to `IsIntegral` on global sections; conclude via `GeometricallyIntegral → GeometricallyIrreducible` (`Mathlib.AlgebraicGeometry.Geometrically.Integral:58`).

### Decision D3: shape of `gmScalingP1`

- **Mathlib idiom**: bare morphism `gmScalingP1 : ProjectiveLineBar ⊗ Gm ⟶ ProjectiveLineBar` in `Over (Spec (.of kbar))`, defined chartwise by `AlgebraicGeometry.Scheme.Cover.glueMorphisms` (`Mathlib.AlgebraicGeometry.Gluing:?`). No `IsAction` / `MulAction` typeclass exists at scheme level in Mathlib — every scheme-level "action" the library knows is a bare morphism plus named property lemmas. Cite as precedent: `GrpObj.mulRight` (`Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_:?`) — a one-sided multiplication packaged as a morphism, no typeclass wrapper.
- **Project's current path**: not yet built — the blueprint description is chartwise (`(x, λ) ↦ λx` on `𝔸¹ × 𝔾_m`; `1/(λx) = u/λ` near `∞`), with `σ_×(0, λ) = 0` highlighted as the load-bearing property.
- **Gap**: in-proposal. The risk is over-engineering — wrapping σ_× in a typeclass / `MulAction`-style structure that doesn't exist anywhere else in Mathlib.
- **Verdict**: **ALIGN_WITH_MATHLIB** — define `gmScalingP1` as a *bare* `Over (Spec (.of kbar))`-morphism. Expose the load-bearing property as a separate lemma (named e.g. `gmScalingP1_zero_fixed` or `gmScalingP1_collapse_at_zero`):
  ```lean
  -- The fixed-point lemma that the rigidity consumer needs:
  -- σ_×(0, ·) = const 0, packaged as the W-axis collapse hypothesis
  -- of `hom_additive_decomp_of_rigidity`:
  lemma gmScalingP1_collapse_at_zero :
      lift (𝟙 ProjectiveLineBar)
        (toUnit ProjectiveLineBar ≫ (zeroPoint : 𝟙_ ⟶ Gm)) ≫
        ... = ... := by ...
  ```
  Use `Scheme.Cover.glueMorphisms` over the two `Proj.awayι`-charts × `Gm` (which together cover `ℙ¹ × 𝔾_m` because `Proj.affineOpenCover` does). Each chart-restriction is then a `Spec.map` of an explicit ring map between `k̄[t, λ, λ⁻¹]`-algebras (on `𝔸¹ × 𝔾_m`: `t ↦ λ·t`; near `∞`: `u ↦ u/λ`). DO NOT introduce a custom typeclass `class IsSchemeMulAction (G H : ...) ...` — there is no Mathlib precedent and the only consumer needs only the bare morphism + the one fixed-point property.
  - The `Gluing.glueMorphisms` precondition (agreement on pairwise pullbacks) reduces to an equality of `Spec.map`s on the localization `k̄[t, t⁻¹, λ, λ⁻¹]` — a direct ring-level computation.
  - The "𝔾_m as both source and target factor" — only on the source. On the target (ℙ¹) we just hit the chart we like.

### Decision D4: file location

- **Mathlib idiom**: a small, focused scheme construction with one main downstream consumer gets a short file directly under that consumer. Closest precedent: `Mathlib.AlgebraicGeometry.Group.Smooth` (62 lines), `Mathlib.AlgebraicGeometry.Group.Abelian` (147 lines) — each defines a new instance/lemma in a focused file imported by exactly one or two downstream proofs.
- **Project's current path**: AVR.lean is already 992 lines and the new infrastructure (definitions, 4–5 instances, glue lemmas, the chartwise σ_× construction) is ~150–400 LOC.
- **Gap**: would not break correctness either way, but inlining 250+ LOC of new scheme infrastructure into the rigidity-proof file makes both the proofs and the infrastructure harder to read and harder to upstream later.
- **Verdict**: **ALIGN_WITH_MATHLIB** — split into a new file `AlgebraicJacobian/Genus0BaseObjects.lean`, imported by AVR.lean. Keep `morphism_P1_to_grpScheme_const` / `genusZero_curve_iso_P1` / `rigidity_genus0_curve_to_grpScheme` in AVR.lean; move `ProjectiveLineBar`, `Ga`, `Gm`, `gmScalingP1`, and their typeclass instances + chart-level helper lemmas to the new file. Rationale: matches Mathlib's "one focused file per scheme construction with ~one downstream consumer" pattern, keeps AVR.lean's rigidity-proof content centred, and leaves a clean unit for upstream PR'ing later (e.g. as `Mathlib.AlgebraicGeometry.ProjectiveSpace.One` / `Mathlib.AlgebraicGeometry.Group.Gm` / `…Group.Ga`).

## Recommendation

Land the scaffold this iter as:

```text
AlgebraicJacobian/Genus0BaseObjects.lean       -- NEW FILE
  - import AlgebraicJacobian.AbelianVarietyRigidity-prerequisites
    (Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper,
     Mathlib.AlgebraicGeometry.AffineSpace,
     Mathlib.AlgebraicGeometry.Group.Smooth,
     Mathlib.CategoryTheory.Monoidal.Cartesian.Grp_)
  - namespace AlgebraicGeometry
  - def standardGrading : ℕ → Submodule k̄ (MvPolynomial (Fin 2) k̄)
    + GradedRing instance (project-side, but a routine MvPolynomial homogeneous-decomposition)
  - def ProjectiveLineBar : Over (Spec (.of kbar)) := … (Proj-based)
    instance [IsAlgClosed kbar] : IsProper ProjectiveLineBar.hom := … -- FREE from ProjectiveSpectrum.Proper
    instance : GeometricallyIrreducible ProjectiveLineBar.hom := sorry
    instance : SmoothOfRelativeDimension 1 ProjectiveLineBar.hom := sorry
    def zeroPt, onePt, inftyPt : 𝟙_ ⟶ ProjectiveLineBar := … (Proj.awayι-image of the standard k̄-points)
  - def Ga : Over (Spec (.of kbar)) := AffineSpace (Fin 1) (Spec (.of kbar)) |>.asOver _
    instance : GrpObj Ga := GrpObj.ofRepresentableBy Ga (… additive functor …) (… via AffineSpace.homOverEquiv …)
    instance : Smooth Ga.hom := smooth_of_grpObj_of_isAlgClosed _ (instances inferred)
  - def Gm : Over (Spec (.of kbar)) := (Spec (CommRingCat.of (Localization.Away (X : MvPolynomial Unit kbar)))).asOver _
    instance : GrpObj Gm := GrpObj.ofRepresentableBy Gm (… units functor …) (… via Spec.map-of-away ↔ unit …)
    instance : Smooth Gm.hom := smooth_of_grpObj_of_isAlgClosed _ (instances inferred)
  - def gmScalingP1 : ProjectiveLineBar ⊗ Gm ⟶ ProjectiveLineBar := … (Scheme.Cover.glueMorphisms over the two Proj.awayι charts × Gm)
  - lemma gmScalingP1_collapse_at_zero : lift (toUnit (… ≫ zeroPt)) (𝟙 Gm) ≫ gmScalingP1 = toUnit Gm ≫ zeroPt := …
  - (optional, if/when needed) gmScalingP1_action_id : lift (𝟙 ProjectiveLineBar) (toUnit _ ≫ onePt_of_Gm) ≫ gmScalingP1 = 𝟙 ProjectiveLineBar
end AlgebraicGeometry

AlgebraicJacobian/AbelianVarietyRigidity.lean
  import AlgebraicJacobian.Genus0BaseObjects   -- NEW
  -- morphism_P1_to_grpScheme_const, genusZero_curve_iso_P1, rigidity_genus0_curve_to_grpScheme
  -- are refactored to take the concrete `ProjectiveLineBar` (no more abstract `(P1 : Over …)` proxy)
```

The four big shape rules — **(1)** Proj-based ℙ¹ (not abstract proxy, not glued-from-charts directly), **(2)** Yoneda-installed GrpObj via `ofRepresentableBy` (not direct `μ`-by-hand), **(3)** Spec(`k̄[t,t⁻¹]`) for Gm (not basic-open of `𝔸¹`), **(4)** bare morphism for σ_× (not typeclass) — together remove every parallel-API risk the iter-164 progress critic flagged. The infrastructure built this way also stays directly upstream-able to Mathlib later (no `archon-`-specific wrappers to peel off).

The work the project still owes regardless of this choice — and which `NEEDS_MATHLIB_GAP_FILL` for `Proj 𝒜`-side: `GeometricallyIrreducible` and `SmoothOfRelativeDimension 1` of `Proj.toSpecZero 𝒜.hom` for `𝒜` = standard ℕ-grading on `k̄[X₀, X₁]`, and `genus ProjectiveLineBar = 0` (Riemann–Roch debt; same on every realization).
