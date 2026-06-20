# Analogy: morphism-level proof of `gammaPushforwardIso_comp` (kill the element/junction route)

## Mode
api-alignment

## Slug
fbc-morphism-comp

## Iteration
015

## Question
`gammaPushforwardIso_comp` is proved element-level (`ModuleCat.hom_ext; LinearMap.ext fun x`), which
whnf's the value-`ModuleCat`/`X.Modules` junction once per wrapper; the composite reduction compounds
past the deterministic-timeout limit (VERIFIED cold-build kernel bomb, iter-014). Find + validate a
MORPHISM-LEVEL proof using `restrictScalars` functoriality + `restrictScalarsComp` coherence (no
`LinearMap.ext`, no per-element junction whnf); OR name the junction-free reconstruction of
`gammaPushforwardIso`.

## Project artifact(s)
- `AlgebraicJacobian/Cohomology/FlatBaseChange.lean`
  - `gammaPushforwardIso` def @L308 — `(restrictScalarsComp'App _ _ _ rfl SecN).symm ≪≫
    (restrictScalarsCongr hcomp).app SecN ≪≫ (restrictScalarsComp'App _ _ _ rfl SecN)` over
    `SecN := Γ(N,⊤)`. Every constituent is identity-on-carrier.
  - `gammaPushforwardIso_comp` theorem @L743 — per-component composition coherence; body `sorry` @L776.
  - `gammaPushforwardNatIso_comp` @L808 — nat-iso version; its body (L820–832) reduces to
    `exact gammaPushforwardIso_comp φ ρ N`. **Fix the per-component lemma and this one is already wired.**
  - PROVED ring content: `globalSectionsIso_hom_comp3_specMap_appTop` @L290 (3-fold ring coherence).

## The exact morphism-level goal (from `lean_goal` @L753, BEFORE the `hom_ext`/`LinearMap.ext` descent)
```
(gammaPushforwardIso (φ ≫ ρ) N).hom =
  moduleSpecΓFunctor.map ((eqToIso _).hom.app N ≫ (pushforwardComp (Spec.map ρ) (Spec.map φ)).inv.app N)
    ≫ (gammaPushforwardIso φ ((pushforward (Spec.map ρ)).obj N)).hom
    ≫ (ModuleCat.restrictScalars φ.hom).map (gammaPushforwardIso ρ N).hom
    ≫ (ModuleCat.restrictScalarsComp φ.hom ρ.hom).inv.app (moduleSpecΓFunctor.obj N)
```
This is an equation of morphisms in `ModuleCat R`. **Only ONE factor crosses the value/X.Modules
junction**: `moduleSpecΓFunctor.map (cast)`. Every other factor is pure `restrictScalars` coherence
over the single section module `Γ(N,⊤)`.

## Decisions identified

### Decision 1: Does Mathlib carry morphism-level coherence for a triple `restrictScalars` composite?
- **Mathlib idiom — YES, fully present** (`Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`). The
  coherence is available as explicit MORPHISM-LEVEL rewrite lemmas (NOT only as element lemmas):
  - `ModuleCat.restrictScalarsComp'App f g gf hgf M : (restrictScalars gf).obj M ≅
    (restrictScalars f).obj ((restrictScalars g).obj M)` (object iso; `hgf : gf = g.comp f`).
  - `ModuleCat.restrictScalarsComp'App_hom_naturality (f g gf hgf) (φ : M ⟶ N) :
    (restrictScalars gf).map φ ≫ (…App f g gf hgf N).hom
      = (…App f g gf hgf M).hom ≫ (restrictScalars f).map ((restrictScalars g).map φ)` — **slides the
    coherence iso past a `restrictScalars`-image map at the morphism level.** ← workhorse.
  - `…restrictScalarsComp'App_hom_naturality_assoc` — same with a trailing `≫ h` (the form that fits
    the goal's right-nested composite). Also `…_inv_naturality` for the `.inv` direction.
  - `ModuleCat.restrictScalarsComp'_hom_app` / `…_inv_app` : `(restrictScalarsComp' f g gf hgf).hom.app X
    = (…App f g gf hgf X).hom` (convert functor-iso ↔ object-iso).
  - `ModuleCat.restrictScalarsComp f g : restrictScalars (g.comp f) ≅ (restrictScalars g).comp
    (restrictScalars f)` is **definitionally** `restrictScalarsComp' f g (g.comp f) rfl`; so
    `(restrictScalarsComp φ.hom ρ.hom).inv.app M = (restrictScalarsComp'App φ.hom ρ.hom _ rfl M).inv`
    (reduce via `restrictScalarsComp'_inv_app` after rewriting `restrictScalarsComp` to
    `restrictScalarsComp' _ _ _ rfl`).
  - `ModuleCat.restrictScalarsCongr (e : f = g) : restrictScalars f ≅ restrictScalars g` — depends only
    on the endpoints; `e` is a `Prop`, so two `restrictScalarsCongr` with the same endpoints are EQUAL
    as morphisms by proof-irrelevance (this is how the ring content enters element-free).
  - `ModuleCat.restrictScalarsId R`, `restrictScalarsCongr_symm` — identity/symm coherence.
  - Bicategorical packaging (heavier, usually unnecessary): `RingCat.moduleCatRestrictScalarsPseudofunctor`
    / `CommRingCat.moduleCatRestrictScalarsPseudofunctor` with `…_mapComp = Cat.Hom.isoMk
    (restrictScalarsComp …)`, `…_mapId = Cat.Hom.isoMk (restrictScalarsId …)`. The `Pseudofunctor`
    associator/triangle laws are THE associativity coherence but are awkward to apply pointwise; prefer
    the explicit `…App_hom_naturality` lemmas.
- **Verdict: PROCEED** — the morphism-level associativity/triangle coherence is in Mathlib; no gap-fill
  needed for the ModuleCat side.

### Decision 2: Is a morphism-level proof of `gammaPushforwardIso_comp` achievable on the CURRENT shape?
- **Yes in principle, with ONE irreducible junction crossing isolated as a morphism-level bridge lemma.**
  The element route's fatal property is that it crosses the junction once *per wrapper, per element*, and
  `simp only [comp_apply, …_concreteApply …]` DISTRIBUTES that crossing across the whole composite →
  compounding whnf → bomb. The morphism route crosses it **exactly once** (iter-014 established: a single
  junction `rfl` is cold-build GREEN; only the compounded distribution bombs).
- **Project's current path**: `apply ModuleCat.hom_ext; refine LinearMap.ext fun x` then
  `gammaPushforwardIso_hom_apply` + `simp only [… _concreteApply …]`. **Gap: divergent-and-wrong** — this
  is the verified bomb.
- **Cost of the morphism route**: needs 1 new project-local morphism-level `rfl` lemma (the cast bridge,
  below) + a coherence-rewrite chain. Intricate but element-free.
- **Verdict: ALIGN_WITH_MATHLIB** (drop `LinearMap.ext`; use the `…App_hom_naturality` coherence chain).

### Decision 3: Is `gammaPushforwardIso` mis-shaped (junction-free reconstruction)?
- **DECISIVE FACT**: the goal's RHS is *verbatim* the RHS of Mathlib's `PresheafOfModules.map_comp`:
  `self.map (f ≫ g) = self.map f ≫ (restrictScalars (R.map f)).map (self.map g) ≫
   (restrictScalarsComp' (R.map f) (R.map g) (R.map (f≫g)) _).inv.app (self.obj Z)`
  (`Mathlib.Algebra.Category.ModuleCat.Presheaf`). The `gammaPushforwardIso_comp` statement is THIS law
  with `self.map ↦ gammaPushforwardIso`, modulo (a) the `moduleSpecΓFunctor.map (pushforward cast)`
  prefactor correcting `pushforward (Spec (φ≫ρ))` vs `pushforward(Specφ)∘pushforward(Specρ)`, and (b)
  `restrictScalarsComp` vs `restrictScalarsComp'` (defeq). **So this coherence is the `map_comp` of a
  presheaf-of-modules-shaped structure** — i.e. a `cat_disch`/`aesop_cat`-discharged structure field,
  proven ONCE at construction, not re-derived per use.
- **Project's current path**: `gammaPushforwardIso` is built pointwise via `restrictScalarsComp'App` over
  a `set SecN := Γ(N,⊤)`, with the iso's DOMAIN typed as the junction side `moduleSpecΓFunctor.obj
  (pushforward.obj N)` and made only DEFEQ (not syntactically equal) to the `restrictScalars` tower. Every
  downstream coherence proof must therefore re-cross the junction. This is a **parallel hand-rolled API**
  for what Mathlib packages as `PresheafOfModules.map_comp` / the restrictScalars pseudofunctor.
- **Gap: divergent-with-cost.** Cost = the `_comp` coherence (and any future coherence: pentagon, unit,
  naturality squares) is element-bombing instead of `cat_disch`-cheap; and the iter-009 analogy
  `fbc-pst-pseudofunctor.md` mis-recorded the cost as "pointwise `rfl` (`ext x; rfl`)" — which is the
  bomb — so the whole `pst` mate-glue stack downstream inherits a false "cheap rfl" assumption.
- **Verdict: ALIGN_WITH_MATHLIB** (strategic) — reconstruct so the junction is crossed once and coherence
  is `restrictScalars` pseudofunctor algebra.

## Recommendation

**Fast unblock for THIS iter (morphism-level proof on the current shape).** Replace the body of
`gammaPushforwardIso_comp` (delete `apply ModuleCat.hom_ext; refine LinearMap.ext fun x => ?_` —
that descent is the bomb's entry point). Work on the morphism goal above. Recipe:

1. **(rw, term-mode)** Normalise the codomain glue: rewrite `ModuleCat.restrictScalarsComp φ.hom ρ.hom`
   to `ModuleCat.restrictScalarsComp' φ.hom ρ.hom (ρ.hom.comp φ.hom) rfl` (defeq; `show`/`change` or a
   one-line `have … := rfl`), then `rw [ModuleCat.restrictScalarsComp'_inv_app]` to expose
   `(restrictScalarsComp'App φ.hom ρ.hom _ rfl _).inv`.
2. **(rw, morphism-level `rfl` lemma — ADD)** Unfold each `(gammaPushforwardIso ψ N).hom` to its defining
   composite `(…App _ _ _ rfl SecN).inv ≫ (restrictScalarsCongr hcomp).hom.app SecN ≫ (…App _ _ _ rfl
   SecN).hom` via a new `gammaPushforwardIso_hom_def` proved by `rfl` (single-layer; GREEN in isolation).
   Do this for `φ≫ρ`, `φ`, and `ρ`. Pure morphism rewrites — no elements.
3. **(rw)** Slide the middle factor `(restrictScalars φ.hom).map (gammaPushforwardIso ρ N).hom` leftward
   using `ModuleCat.restrictScalarsComp'App_hom_naturality_assoc` / `…_inv_naturality` (the goal's
   right-nested `≫` shape matches the `_assoc` form). This is the workhorse step that re-aligns the two
   sides without touching carriers.
4. **(rw — the ONE junction crossing; ADD a morphism-level bridge lemma)** Prove
   `moduleSpecΓFunctor.map ((eqToIso (Spec.map_comp φ ρ)).hom.app N ≫ (pushforwardComp (Spec.map ρ)
   (Spec.map φ)).inv.app N) = <explicit restrictScalars coherence morphism over SecN>` as a SEPARATE
   lemma (its proof is the single junction `rfl`/short reduction — cold-build GREEN per iter-014; the
   cast is identity-on-carrier). Substitute it. After this, the goal contains NO `moduleSpecΓFunctor.map`
   and no `pushforward` — it is a pure `restrictScalars`-coherence identity over `Γ(N,⊤)`.
5. **(term-mode, proof-irrelevance)** Close the residual `restrictScalarsCongr` endpoint mismatch: the two
   sides differ only by `restrictScalarsCongr e₁` vs `restrictScalarsCongr e₂` with provably-equal
   endpoints (the equality is exactly `globalSectionsIso_hom_comp3_specMap_appTop`). Since the congr iso
   depends only on the (now-equal) endpoints and `eᵢ : Prop`, they are equal by proof-irrelevance /
   `Subsingleton` — NO `ext`, NO elements. Finish with `congr 1`/`Subsingleton.elim` on the proofs, or
   rewrite the endpoints by the ring lemma then `rfl`.

The linchpin is step 4 (single junction crossing) + step 5 (proof-irrelevance instead of `ext x`). The
next lane MUST cold-`lake build AlgebraicJacobian.Cohomology.FlatBaseChange` to confirm — LSP hides the
bomb. If steps 3–5 prove fragile under the exact syntactic shapes, escalate to the refactor below.

**Strategic fix (refactor — the real alignment).** Reconstruct `gammaPushforwardIso` so the junction is
crossed ONCE, centrally. Introduce a single morphism-level iso (proven once, `rfl`/short)
`moduleSpecΓObjIso N : moduleSpecΓFunctor.obj N ≅ (restrictScalars gs•hom).obj (Γ(N,⊤))` presenting the
junction explicitly, and route `gammaPushforwardIso` + ALL its coherence through it; OR package the
family as the structure map of a `PresheafOfModules` (or a pseudo-natural transformation between the
`pushforward` pseudofunctor and `CommRingCat.moduleCatRestrictScalarsPseudofunctor`), so
`gammaPushforwardIso_comp` becomes the `map_comp` field discharged by `cat_disch` at construction. After
this, `_comp`, naturality, and any future pentagon/unit coherence are pure `restrictScalars` pseudofunctor
algebra — junction never re-crossed. This also corrects the false "pointwise `rfl`" cost recorded in
`fbc-pst-pseudofunctor.md` (Decision 2), which the entire `pst` mate-glue stack currently assumes.

## Correction to prior analogy
`analogies/fbc-pst-pseudofunctor.md` (iter-009), Decision 2 / Recommendation step 3, states the
`gammaPushforwardNatIso`/`gammaPushforwardIso` composition coherence is "pointwise `rfl`
(`ext x; rfl` / `ext; rfl`)". **This is FALSE at the kernel level** — `ext x; rfl` on this goal is the
iter-014-VERIFIED cold-build kernel bomb. Treat that lemma as morphism-level (recipe above), not
`ext x; rfl`.
