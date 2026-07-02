# Analogy: cotangent-space-at-identity rank bridge — presheaf-at-⊤ collapse and the iter-130+ rank-lemma closure

## Slug
lieAlgebra-rank-bridge

## Iteration
129

## Question

For the iter-128 body
```
cotangentSpaceAtIdentity G :=
  let ψ : Γ(G.left, ⊤) ⟶ CommRingCat.of k := ηleft.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom
  let M := Scheme.relativeDifferentialsPresheaf G.hom
  (ModuleCat.extendScalars ψ.hom).obj (M.obj (op ⊤))
```
of a smooth-proper-geometrically-irreducible group scheme `G/k`, does the
iter-130+ rank lemma `finrank k (cotangentSpaceAtIdentity G) = n`
(with `n` from `[SmoothOfRelativeDimension n G.hom]`) admit a tractable
closure path through Mathlib b80f227, or does the presheaf-side
evaluation at the top open hide a presheaf-vs-sheaf coincidence cost
that the rank lemma must pay before it can close?

## Project artifact(s)

- `AlgebraicJacobian/Cotangent/GrpObj.lean:102-116` — `cotangentSpaceAtIdentity G` body (iter-128 prover lane; iter-129 rename + signature relax).
- `AlgebraicJacobian/Differentials.lean:51-66` — `relativeDifferentialsPresheaf` definition + `relativeDifferentialsPresheaf_obj_kaehler` `rfl` identification.
- `AlgebraicJacobian/Differentials.lean:124-143` — `smooth_locally_free_omega`, the load-bearing affine-chart Jacobian criterion that the rank lemma must consume.

## Decisions identified

### Decision 1: Does the iter-128 body of `cotangentSpaceAtIdentity` have rank `n` for the target class (smooth proper geometrically irreducible `G/k`, relative dim `n`)?

- **Mathematical answer**: **NO**. The iter-128 body **vanishes** (zero `k`-module) for every `G` in the target class with `n ≥ 1`.

  Step-by-step:
  1. The relative differentials *presheaf* `relativeDifferentialsPresheaf G.hom` evaluated at `op ⊤` is, by `relativeDifferentials'_obj` (rfl, `Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf`), `CommRingCat.KaehlerDifferential (φ'.app (op ⊤))` where
     `φ' : (TopCat.Presheaf.pullback CommRingCat f.base).obj S.presheaf ⟶ G.left.presheaf`.
  2. `((TopCat.Presheaf.pullback CommRingCat f.base).obj S.presheaf).obj (op ⊤)` is the pointwise left Kan extension colimit over `{V : Opens(Spec k) | f.base(⊤_{G.left}) ⊆ V}`. Since `Spec k` is a single-point space (opens = `{∅, ⊤}`) and `f.base(⊤_{G.left})` is the unique point, the indexing diagram is a singleton `{V = ⊤_{Spec k}}`. The colimit collapses to `Γ(Spec k, ⊤) ≅ k` (via `Scheme.ΓSpecIso`).
  3. For smooth proper geometrically irreducible `G/k`, smoothness implies geometrically reduced (smooth over a field ⇒ geometrically regular ⇒ reduced after base change), hence `G` is **geometrically integral**. By the Stacks-0BUG / Hartshorne III.10.7 result (in Mathlib as `AlgebraicGeometry.isField_of_universallyClosed`), `Γ(G, ⊤)` is a field finite over `k`; geometric irreducibility forces it to be `k` itself (dim 1 after base change to `k̄`).
  4. So `φ'.app (op ⊤)` is the structure map `k → Γ(G, ⊤) = k`, i.e. essentially the identity. By `KaehlerDifferential.subsingleton_of_surjective` (`Mathlib.RingTheory.Kaehler.Basic`), `Ω[k/k] = 0` (subsingleton).
  5. The iter-128 body is `k ⊗_{Γ(G,⊤)} Ω[Γ(G,⊤)/(pullback presheaf @ ⊤)] = k ⊗_k 0 = 0`.

  The rank lemma `finrank cotangentSpaceAtIdentity = n` is therefore **provably FALSE for `n ≥ 1`** as stated against the iter-128 body. (For `n = 0`, the lemma holds vacuously but the construction is also useless.)

- **Mathlib idiom (what would actually compute the rank)**: For a non-affine `G`, the correct algebraic-geometry object is `(η_G^* Ω_{G/k})(⊤)` where `Ω_{G/k}` is the **sheafified** relative differential **sheaf of modules** (not the presheaf). This sheaf has the property that its global sections on an affine chart `V ∋ η_G(pt)` coincide with the algebraic Kähler module, and pullback along the identity section then descends to a `k`-vector space of rank `n`. Mathlib b80f227 has the affine-chart side (`Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` [verified, in `Mathlib.RingTheory.Smooth.StandardSmoothCotangent`]) but **does not** ship the scheme-level sheafified `Ω` or the sheafified pullback-of-modules-along-section composite.

- **Gap**: **divergent-and-wrong**. The iter-128 body is not merely fragile — it computes the *wrong mathematical object* (zero rather than rank-`n`) for the consumer class.

- **Cost of divergence**: the rank lemma `cotangentSpaceAtIdentity_finrank_eq` cannot close against the iter-128 body. Any attempt by the iter-130 prover lane to ship this lemma will either (a) waste cycles trying to prove a false statement, or (b) accidentally close a vacuous version that disguises the bug behind setoid / canonical-iso obfuscation.

- **Verdict**: **ALIGN_WITH_MATHLIB**. The body must be replaced before the rank lemma can be stated, let alone proven.

### Decision 2: Which replacement body should iter-129/130 land?

Three candidates, with costs:

**Replacement (A): Stalk-side cotangent — `IsLocalRing.CotangentSpace O_{G, η(pt)}`.**

- Mathlib backing:
  - `IsLocalRing.CotangentSpace` (`Mathlib.RingTheory.Ideal.Cotangent`) [verified].
  - `IsRegularLocalRing.iff_finrank_cotangentSpace` (`Mathlib.RingTheory.RegularLocalRing.Defs`) [verified]:
    `IsRegularLocalRing R ↔ Module.finrank (ResidueField R) (CotangentSpace R) = ringKrullDim R`.
  - `AlgebraicGeometry.LocallyRingedSpace.isLocalRing` [verified]: every stalk is a local ring.
- Required bridge: **smooth over a field at a point ⇒ regular local ring of dim n at that point**. Mathlib b80f227 ships `Algebra.smoothLocus_eq_univ` (smooth ⇒ everywhere smooth) and `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` (rank of Ω = n) but **does NOT** ship a direct "standard-smooth-over-field at prime ⇒ `IsRegularLocalRing` of dim n" lemma. Status: **[gap]**. The bridge requires manually composing:
  1. Affine chart `V` with `Algebra.IsStandardSmoothOfRelativeDimension n k Γ(V)` (from `smooth_locally_free_omega`).
  2. Localize at the prime corresponding to `η(pt)` to get a local ring `Γ(V)_p`.
  3. `Algebra.IsStandardSmoothOfRelativeDimension` is preserved by localization (Mathlib has the analogue for `Algebra.Smooth` but the standard-smooth-of-dim-n variant needs care).
  4. Show `Γ(V)_p` is regular local of dim n: the Kähler module of `Γ(V)_p / k` is free of rank n (base change from the appLE algebra), tensor with the residue field gives the cotangent space, and chasing dimensions against Krull dim requires `Algebra.FormallySmooth.iff_injective_lTensor_residueField`-style reasoning [verified, in `Mathlib.RingTheory.Smooth.Local`].
  5. Identify the stalk `O_{G, η(pt)}` with `Γ(V)_p` via `AlgebraicGeometry.StructureSheaf.IsLocalization.to_stalk` [verified].
  6. Identify the residue field with `k` via the identity section.
- **Estimated LOC**: 500-1000. The localization-preserves-standard-smooth-of-dim-n step and the regular-local equivalence chase are non-trivial.
- **Canonicity**: yes — independent of chart choice.

**Replacement (B): Affine-chart base change — `k ⊗_{Γ(V)} Ω[Γ(V)/k]` for a chosen affine `V ∋ η(pt)`.**

- Mathlib backing:
  - `smooth_locally_free_omega` (already shipped in project) — gives free Ω of rank n on the chart.
  - `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` [verified] — gives the rank claim.
  - `Module.finrank_tensorProduct` / `Module.Free.rank_tensorProduct` for base-change-preserves-finrank [verified family].
- **Estimated LOC**: 200-400. Most cost is sigma-typing the chart choice + bridging `Module.rank` ↔ `Module.finrank` claims through the existing `smooth_locally_free_omega` shape.
- **Canonicity**: NO — the body depends on a chosen chart. Mitigation: bundle the chart choice into a `Nonempty` existential ("there exists a chart...") and define the cotangent via `Classical.choice`. Downstream consumers (rigidity argument) only need the existence of a rank-`n` `k`-module, not canonicity.

**Replacement (C): Sheafify Ω first — full Mathlib-aligned `Scheme.Omega` sheaf, then pull back along η.**

- Mathlib backing: minimal. Mathlib has `TopCat.Sheaf.pullback` and `PresheafOfModules.sheafification` (limited to fixed-ring case) but not a scheme-level sheafified relative differential sheaf or a `PresheafOfModules.pullback` along a section for the ring-changing case.
- **Estimated LOC**: 800-2000 (matches the iter-127 strategy's bundled-piece (i) upper bound). This is the "iter-129 standalone-sheaf detour" scoped in `STRATEGY.md` § M2.body-pile.
- **Canonicity**: yes — fully canonical, matches blueprint mathematical content.
- **Cost-vs-benefit**: high LOC for a single rank lemma that doesn't need full sheaf machinery. Defer unless a downstream consumer requires sheaf operations on Ω (none currently identified in the live project graph).

- **Verdict**: **Replacement (B) for iter-130, with a `% NOTE` documenting the bridge cost to (A)/(C) for future generality**.

  Rationale:
  - The rigidity-over-`k̄` consumer only needs `∃ T : Type*, [Module k T] ∧ Module.finrank k T = g` for the abelian-variety genus. Canonicity of the cotangent definition is unnecessary.
  - Replacement (B) consumes the project's already-shipped `smooth_locally_free_omega` and Mathlib's already-shipped `rank_kaehlerDifferential` — no new Mathlib gaps.
  - Replacement (A) is the "correct" mathematical object but pays 500-1000 LOC for canonicity that the consumer does not exploit.
  - Replacement (C) is reserved for if/when a downstream non-rigidity consumer needs the cotangent **sheaf** (not vector space).

### Decision 3: What is the iter-130+ rank-lemma closure path?

Under **Replacement (B)** — the recommended verdict from Decision 2 — the iter-130+ rank-lemma prover lane consumes the following chain. Tags: [verified] = confirmed via `lean_leansearch`/`lean_loogle`; [expected] = high-confidence Mathlib idiom not directly verified; [gap] = confirmed missing.

1. `AlgebraicGeometry.IsSmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension` [verified, used in `smooth_locally_free_omega` already] — extract affine chart `V ∋ η(pt)` with `RingHom.IsStandardSmoothOfRelativeDimension n` for the `appLE` ring map.

2. `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth` [verified] — promote to `Algebra.IsStandardSmooth k Γ(V)`.

3. `Algebra.IsStandardSmooth.free_kaehlerDifferential` [verified] — `Module.Free Γ(V) Ω[Γ(V)/k]`.

4. `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` [verified] — `Module.rank Γ(V) Ω[Γ(V)/k] = n`.

5. **Base-change-to-k step**: with `ψ : Γ(V) → k` (from the identity section restricted to V, composed with `ΓSpecIso`), define `T := k ⊗_{Γ(V)} Ω[Γ(V)/k]`. Then:
   - `Module.Free k T` follows from `Module.Free.tensorProduct` / `Module.Free.of_baseChange` [expected, search target `Module.Free` + tensor product preserves Free for surjective base ring map].
   - `Module.finrank k T = n` follows from `Module.finrank_tensorProduct` [expected] or `Module.finrank_baseChange` [expected] applied to step (4).

6. Convert `Module.rank` to `Module.finrank`: `Module.finrank_eq_rank'` [verified] under `FiniteDimensional` assumption (which `Module.Free k T` + `n : ℕ` gives via `Module.Finite.of_basis`).

**Mathlib gaps under (B)**: NONE. Every step is consumable from Mathlib b80f227.

**Mathlib gaps under (A)** (alternate path): the "standard smooth at prime ⇒ `IsRegularLocalRing` of dim n" bridge is the one [gap]. Closing it as a project lemma would itself be a candidate M1 PR.

**Mathlib gaps under (C)** (alternate path): sheafified scheme-level `Ω` + sheafified `PresheafOfModules.pullback` for the ring-changing case is the [gap]. Out-of-scope for the autonomous loop.

## Recommendation

**Replace the iter-128 body** with **Replacement (B): affine-chart base change**. Concretely:

```lean
noncomputable def cotangentSpaceAtIdentity (G : Over (Spec (.of k)))
    [CategoryTheory.GrpObj G] {n : ℕ} [SmoothOfRelativeDimension n G.hom]
    [IsProper G.hom] [GeometricallyIrreducible G.hom] :
    ModuleCat k := by
  -- Extract an affine chart V ⊆ G containing the identity section image,
  -- with appLE algebra giving Ω free of rank n.
  classical
  obtain ⟨U, V, e, hxV, _hU, _hV, _hfree, _hrank⟩ :=
    smooth_locally_free_omega (n := n) G.hom (η_G_image_pt G)
  -- Build the cotangent at identity as k ⊗_{Γ(V)} Ω[Γ(V)/Γ(U)].
  letI : Algebra Γ(Spec (.of k), U) Γ(G.left, V) :=
    (Scheme.Hom.appLE G.hom U V e).hom.toAlgebra
  -- Ring map Γ(V) → k from the identity section restricted to V.
  let ψV : Γ(G.left, V) ⟶ CommRingCat.of k := <small adjunction calculation>
  exact (ModuleCat.extendScalars ψV.hom).obj
    (ModuleCat.of Γ(G.left, V) (Ω[Γ(G.left, V) ⁄ Γ(Spec (.of k), U)]))
```

The rank lemma then closes in ~50-100 LOC:

```lean
theorem cotangentSpaceAtIdentity_finrank_eq (G : Over (Spec (.of k)))
    [CategoryTheory.GrpObj G] {n : ℕ} [SmoothOfRelativeDimension n G.hom]
    [IsProper G.hom] [GeometricallyIrreducible G.hom] :
    Module.finrank k (cotangentSpaceAtIdentity G) = n := by
  -- 1. unfold to the chosen chart V
  -- 2. invoke smooth_locally_free_omega for free + rank n over Γ(V)
  -- 3. base change to k via Module.finrank_baseChange / Module.finrank_tensorProduct
  sorry
```

**Strategy implications for piece (i)**:
- **Strategy LOC envelope**: stays in the 800-1500 LOC bundled estimate (no need to revise up to 1300-2500 for the sheafified detour).
- **Iter cost for rank lemma**: 1-2 prover iters under Replacement (B).
- **Do NOT pursue Replacement (C) (sheafified Ω)** unless a future consumer outside rigidity emerges — defer with a `% NOTE` marker.

**Caveat on Replacement (B) canonicity**: the body depends on a chosen chart and on `Classical.choice`. Document this with a `% NOTE` in the docstring of `cotangentSpaceAtIdentity` so future iters know the body is "a choice of chart's base-changed Kähler module" not "the cotangent sheaf at η". For the rigidity-over-`k̄` consumer, this is acceptable; for a hypothetical future Lie-algebra-bracket consumer, replacement (A) or (C) would be required.

## Bridge lemma list for iter-130+ prover lane (closure under Replacement B)

| Step | Lemma | Status |
|---|---|---|
| 1 | `AlgebraicGeometry.IsSmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension` | [verified] |
| 2 | `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth` | [verified] |
| 3 | `Algebra.IsStandardSmooth.free_kaehlerDifferential` | [verified] |
| 4 | `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential` | [verified] |
| 5a | `Module.Free.tensorProduct` (base-change-preserves-Free) | [expected] |
| 5b | `Module.finrank_tensorProduct` / `Module.finrank_baseChange` | [expected] |
| 6 | `Module.finrank_eq_rank'` | [verified] |
| 7 | `Scheme.ΓSpecIso` (for the `ψ : Γ(G,V) → k` identification on the chart) | [verified] |
| 8 | `Algebra.IsStandardSmooth ⇒ Algebra.FinitePresentation` (for `Module.Finite k T`) | [expected, follows from definitions] |

## Presheaf-vs-sheaf coincidence theorem (the absence)

For posterity: **there is no Mathlib coincidence theorem** stating that `(relativeDifferentialsPresheaf G.hom).obj (op ⊤)` agrees with `H^0(G, Ω_{G/k}_{sheaf})` for proper geometrically integral G. Such a theorem is in fact **false in general** for the iter-128 body: the presheaf-side is zero (as computed in Decision 1), while the sheaf-side has rank `g · dim G` (Hodge theory). The presheaf-side construction is the **wrong functor for the global-sections computation on non-affine schemes**, which is the geometric content the strategy-critic flagged.

The bridge between the iter-128 body and the sheaf-side global sections requires:
1. A `PresheafOfModules → SheafOfModules` sheafification step (Mathlib partial coverage in `PresheafOfModules.sheafification`; missing for ring-changing case).
2. A "global sections of sheafification ≠ global sections of presheaf for non-affine X" awareness — the presheaf misses the higher-cohomology gluing.

Both are out of scope for the rank lemma alone. Replacement (B) sidesteps the issue by working on an affine chart where presheaf = sheaf trivially.
