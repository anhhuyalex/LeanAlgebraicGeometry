# Analogy: rewriting one factor inside a long functor-image composite past an obj-nested ↔ ⋙-composed instance diamond

## Mode
cross-domain-inspiration

## Slug
fbc-diamond

## Iteration
029

## Structural problem (abstracted)
We have a long composite of `Functor.map` images in a category with a transparent `CategoryStruct.comp`
instance, `F.map u₁ ≫ F.map u₂ ≫ … ≫ F.map uₙ`. One factor `F.map uₖ` is provably equal to `𝟙`
(or to another morphism) by a lemma `h`. We must splice `h` in WITHOUT a head-symbol `rw`/`simp`/`erw`,
because the implicit (co)domain object carried by `uₖ` is in a DIFFERENT-but-DEFEQ syntactic form from
the one the lemma fixes: the goal's factor presents the shared object as the **nested-`obj`** form
`G.obj (H.obj M)` (produced by `rw [Functor.map_comp]`), while the collapse lemma's term presents it as
the **composed-`⋙`** form `(H ⋙ G).obj M` (the `.hom.app` domain of a `pushforwardComp` coherence iso).
These two are definitionally but not syntactically equal, so keyed `rw`/`simp` cannot abstract the motive
("did not find pattern" / "no progress") and a defeq-tolerant `erw` blows the `whnf` heartbeat budget on
the multi-thousand-node concrete leg term.

## Failed approaches (from directive)
- `rw`/`simp only [gammaMap_pushforwardComp_hom_eq_id]` (or via a pre-elaborated `hpfc`): obj-nested vs
  ⋙-composed mismatch ⇒ keyed match fails ("no occurrence").
- `rw`/`simp only [Functor.map_comp]` on the assembled goal: no progress (same diamond on `CategoryStruct.comp`).
- `erw [gammaMap_pushforwardComp_hom_eq_id]`: `whnf` heartbeat timeout (1.6M then 4M) on the huge leg term.

## Analogues found

### Analogue 0 (DECISIVE, in-project): this file already ports the GR recipe over `X.Modules`

The GR recipe (`GrassmannianCells.lean:884` `chartTransition'_fac`) is: (a) build the cancellation on a
FRESH clean term via `have`; (b) lift it into the composite context with `congrArg (_ ≫ ·)`; (c) close
with `exact …`, whose defeq check absorbs the instance diamond + associativity — the move `rw`/`simp`/`erw`
cannot make at acceptable cost. GR's diamond is a `HasPullback`/Scheme one; FBC's is an `X.Modules` /
composed-functor-`obj` one. **The recipe ports because the file already contains three working instances of
it over the exact `X.Modules` / `Functor.map` setting FBC lives in:**

1. `FlatBaseChange.lean:1144` `pullbackPushforward_unit_comp` — `X.Modules` unit/pushforward composite.
   `have h := unit_conjugateEquiv …; rw […] at h; rw [← Category.assoc]; exact h`. The closing `exact h`
   bridges the `X.Modules` `CategoryStruct.comp` diamond by defeq — identical role to GR's `exact congrArg`.
2. `FlatBaseChange.lean:1304` `base_change_mate_fstar_reindex_legs_gammaDistribute` — distributes
   `F.map ((a≫b≫c)≫d) = F.map a ≫ F.map b ≫ F.map c ≫ F.map d` for arbitrary `F`, in pure term mode:
   `exact (F.map_comp _ _).trans (congrArg (· ≫ F.map _) ((F.map_comp _ _).trans (congrArg (F.map _ ≫ ·) (F.map_comp _ _))))`.
   This is the canonical term-mode `Functor.map_comp` distributor AND the template for one-sided
   `congrArg (· ≫ _)` / `congrArg (_ ≫ ·)` single-factor surgery with `_`-inferred neighbours.
3. `FlatBaseChange.lean:1534` `base_change_mate_inner_eCancel_pushforwardComp` — lifts
   `(Spec φ)_*.map_id` through `Γ` with `Functor.congr_map`:
   `(Γ.congr_map ((Spec φ)_*.map_id _)).trans (Γ.map_id _)`. This is the factor-3 collapse already packaged
   in the SHIPPED Γ∘(Spec φ)_* form the goal needs (NOT the bare `gammaMap_pushforwardComp_hom_eq_id` form).

- **Domain**: same (algebraic geometry / `X.Modules`), but a different lane (GR) and different sub-lemmas.
- **Technique**: `congrArg (· ≫ _)` / `congrArg (_ ≫ ·)` / `Functor.congr_map F h`, chained with `.trans`,
  closed with `exact`; `eqToHom`/`eqToHom_map` for genuine object-equality repackaging; the `exact`/`.trans`
  seam carries the defeq (obj-nested ↔ ⋙-composed) bridge. NEVER a head `rw`/`simp`/`erw` on the locked composite.
- **Mapping to project**: see "Top suggestion" — it is a direct splice using lemmas already in the file.
- **Porting cost**: low — no new infrastructure; the three template proofs already compile.
- **Verdict**: ANALOGUE_FOUND.

### Analogue 1: adjunction mate / conjugate calculus — `Mathlib/CategoryTheory/Adjunction/Mates.lean`

- **Domain**: pure category theory (adjunction 2-categorical calculus).
- **Same structural problem there**: prove an equality between two long composites of unit/counit and
  `Functor.map` images differing by coherence isos. Mathlib NEVER `rw`s a factor inside the locked
  composite; it states `unit_conjugateEquiv` / `unit_mateEquiv` / `conjugateEquiv` naturality as clean
  equations and composes them with `congrArg`/whiskering + `Category.assoc` in term/`rw`-on-hypothesis mode.
- **Technique**: build the mate identity on the abstract adjunction (`conjugateEquiv`), normalise it on a
  separate hypothesis (`rw [...] at h`), then `exact h` — the goal's concrete diamond is bridged by `exact`.
  `FlatBaseChange.lean:1154` already calls `CategoryTheory.unit_conjugateEquiv` this way.
- **Mapping to project**: FBC's inner composite IS a mate computation; the surviving telescoping is the
  same `unit ≫ functor-image-of-unit ≫ coherence` shape that `Mates.lean` resolves abstractly.
- **Porting cost**: low–medium — `unit_conjugateEquiv` is already imported and used; the residual is
  bookkeeping, not new theory.
- **Verdict**: ANALOGUE_FOUND.

### Analogue 2: simplicial identities — `Mathlib/CategoryTheory/SimplicialObject/Basic.lean`

- **Domain**: algebraic topology (cosimplicial/simplicial objects) — genuinely distant.
- **Same structural problem there**: `δ_comp_δ`, `δ_comp_δ'`, `δ_comp_δ_self'` rewrite ONE face-map factor
  `X.δ k` inside a composite `X.δ j ≫ X.δ i`, where an index-arithmetic coherence (`j = i.castSucc`,
  `i.castSucc < j`) creates a defeq-but-not-syntactic gap on the `Fin`-indexed (co)domain — the same shape
  as FBC's obj-form gap, with `Fin` arithmetic playing the role of the ⋙/obj coherence.
- **Technique**: the primed `'` variants take the index equality/inequality as an explicit hypothesis (so
  the gap is named, not matched), discharge it through `SimplexCategory` arrow identities, and repackage the
  residual with `eqToHom` + `congrArg`/`Functor.congr_map` — never a keyed `rw` across the coherence.
- **Mapping to project**: mirror the primed-variant discipline — carry the object/leg equality as an
  explicit hypothesis (FBC already does this with the `_legs` parametrisation + `hfst`/`hsnd`) and repackage
  the obj-form residual with `eqToHom` (cf. `gammaMap_pushforwardCongr_hom`'s `= eqToHom (by rw [hfg])`).
- **Porting cost**: medium — conceptual transfer, not a copy; confirms the "name the diamond, don't match it" tactic.
- **Verdict**: ANALOGUE_FOUND.

### Analogue 3: monoidal coherence — `Mathlib/CategoryTheory/Monoidal/Category.lean` & friends

- **Domain**: monoidal category theory.
- **Same structural problem there**: rewrite one factor past associator/unitor diamonds in a long tensor
  composite. Solved with `whiskerLeft f` / `whiskerRight f` (= `congrArg`-for-tensor with the neighbour
  fixed), `reassoc` lemmas (pre-baked `_ ≫ X` forms), and the `coherence`/`monoidal` tactic for the diamond.
- **Technique**: the portable kernel is `whiskerLeft`/`whiskerRight` = one-sided congruence, exactly the
  `congrArg (· ≫ _)` / `(_ ≫ ·)` idiom; `reassoc` shows the value of pre-associating a lemma to the form the
  goal needs rather than rewriting in place.
- **Mapping to project**: low direct transfer — FBC's diamond is on `Functor.map` domains, not associators,
  so the `coherence` tactic does not apply; but it independently confirms the one-sided-congruence kernel.
- **Porting cost**: framing only.
- **Verdict**: PARTIAL_ANALOGUE.

## Top suggestion
Do NOT search further — the answer is already in this file. Port the three local templates above. Concretely
at the `sorry` (FlatBaseChange.lean:1445):

1. **Distribute** `(Spec φ)_*` then `Γ` over the `unitExpand` four-factor with the term-mode lemma
   `base_change_mate_fstar_reindex_legs_gammaDistribute` (apply it for `F := moduleSpecΓFunctor` after first
   distributing `(Spec φ)_*` via `Functor.map_comp` applied in term mode — exactly the `gammaDistribute`
   body), NOT `rw`/`simp [Functor.map_comp]`. This is the diamond-safe distributor.
2. **Collapse the surviving `pushforwardComp(g',Spec φ).hom` Γ-factor** with the SHIPPED lemma
   `base_change_mate_inner_eCancel_pushforwardComp e.hom (Spec.map inclA) φ (tilde M)` (already in the goal's
   `Γ ∘ (Spec φ)_*` form — do NOT use the bare `gammaMap_pushforwardComp_hom_eq_id` / `hpfc`), spliced with
   `congrArg (· ≫ _)` / `congrArg (_ ≫ ·)` (underscore neighbours, inferred), chained by `.trans`, then drop
   the `𝟙` with `Category.id_comp` / `Category.comp_id`.
3. **Splice the three eCancel atoms** (`_eUnit` via its `IsIso` + `asIso`/`IsIso.hom_inv_id`,
   `_pushforwardComp`, `_pullbackComp`) the same way against the UNFOLDED `base_change_mate_codomain_read_legs`.
4. **Close with `exact … .trans …`** landing on `base_change_mate_inner_value`; the final `exact` absorbs the
   residual obj-nested ↔ ⋙-composed / associativity defeq — precisely the GR `exact congrArg` role.

Mechanism summary (functor-image analogue of GR `exact congrArg`/`Iso.inv_comp_eq`):
`congrArg (· ≫ _)` / `congrArg (_ ≫ ·)` / `Functor.congr_map F h` (`Mathlib/CategoryTheory/Functor/Basic.lean`),
`.trans`-chained, `exact`-closed; `eqToHom` for true object-equality coherence. The diamond is bridged at the
`exact`/`.trans` seam by defeq, which `rw`/`simp`/`erw` structurally cannot do here.
