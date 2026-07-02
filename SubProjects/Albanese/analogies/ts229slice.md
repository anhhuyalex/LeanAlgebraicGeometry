# Analogy: open-immersion slice-internal-hom commutes with restriction

## Mode
cross-domain-inspiration

## Slug
ts229slice

## Iteration
229

## Structural problem (abstracted)
A (pre)sheaf whose value at an object `X` is defined via the **over-category /
slice** `Over X` (here: `ℋom(A,B)(V) = (A|_{Over V} ⟶ B|_{Over V})`, a compatible
family over all `W ≤ V`) must be shown to **commute with restriction along an open
immersion** `U ↪ X` (equivalently pullback along a morphism of sites whose inverse
image is exact). Concretely close
`(pushforward β).obj (dual A) ≅ dual ((pushforward β).obj A)`,
`dual = internalHom(−, 𝟙_)` the slice internal hom in `PresheafOfModules` over the
ringed space `(X, 𝒪_X)`.

## Failed approaches (from directive)
- Verbatim mirror of the sectionwise tensor restrict-iso (`tensorObj_restrict_iso`):
  the dual is NOT sectionwise `restrictScalars`, so the ModuleCat shadow can't lift;
  residual H2′ does not close.
- Abandoned d.2 stalk-⊗ route: ~300–500 LOC dead end; structurally a stalk, not a slice.

## Analogues found

### Analogue: `TopologicalSpace.Opens.overEquivalence` (`Mathlib.Topology.Sheaves.Over`)
- **Domain**: point-set topology / sheaves on spaces (one shelf over schemes).
- **Same structural problem there**: for `U : Opens X`, the slice category `Over U`
  (objects `V : Opens X` with `V ⟶ U`, i.e. `V ≤ U`) is **equivalent to `Opens ↥U`**,
  the opens of the open subspace. `def overEquivalence : Over U ≌ Opens ↥U` — this IS
  the "open-immersion slice-site reindexing equivalence" the prover estimated at
  150–300 LOC, already built in ~25 LOC (functor = `Subtype.val ⁻¹' ·`, inverse =
  `Subtype.val '' ·`, unit/counit by `eqToIso`/`aesop`).
- **Technique**: works entirely in the **poset** `Opens X`; the equivalence's coherence
  (`unitIso`, `counitIso`) is discharged by `eqToIso (by ext; aesop)` because hom-sets
  are subsingletons. The file's own `## TODO` states verbatim the project's missing
  piece: "show that both functors of `overEquivalence U` are continuous and induce an
  equivalence between `Sheaf ((Opens.grothendieckTopology X).over U) A` and
  `Sheaf (Opens.grothendieckTopology U) A` for any `A`."
- **Mapping to project**: the project's "restrict `dual A` along open immersion `U ↪ X`"
  is `Sheaf.over (−) U` transported across `overEquivalence U`. The residual
  `(pushforward β)(dual A) ≅ dual(pushforward β A)` becomes: re-evaluating `dual` at
  `V ⊆ U` ranges over `Over V` computed in `Opens U`, and `overEquivalence`/
  `iteratedSliceEquiv` identifies that with `Over V` computed in `Opens X`. Because
  `V ≤ U`, the down-set `↓V` is identical in both posets, so the comparison is an iso
  of thin categories and naturality is automatic.
- **Porting cost**: low–medium. `overEquivalence` is free; the continuity ⇒ sheaf-
  equivalence TODO is the remaining work, but much of it is already discharged by the
  general `Sites/Over.lean` instances below + `IsDenseSubsite.sheafEquiv`.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `CategoryTheory.Sites.Over` (`Mathlib.CategoryTheory.Sites.Over`)
- **Domain**: category theory / sheaves on a general site.
- **Same structural problem there**: builds the slice topology `J.over X`, the
  over-pullback `Sheaf.over F X = (J.overPullback A X).obj F`, proves `Over.forget X`
  is **cover-preserving + cover-lifting** (continuous + cocontinuous), and crucially
  proves `iteratedSliceEquiv f` is a **dense subsite** relating `J.over f.left` with
  `(J.over X).over f` — i.e. *slice-of-slice ≃ slice*, the general form of the
  open-immersion reindexing — with continuity/cocontinuity in **both** directions.
  Also `overMapPullback{Id,Comp}`, `overMapPullback_assoc`: the full `Over.map`
  pseudofunctor coherence the prover anticipated needing.
- **Technique**: `Sieve.overEquiv Y : Sieve Y ≃ Sieve Y.left` lifts to the topology;
  the equivalence of sheaf categories then comes for free from
  `Functor.IsDenseSubsite.sheafEquiv` (`Sites/DenseSubsite/Basic.lean`).
- **Mapping to project**: this is the GENERAL engine; specialise `C := Opens X`,
  `J := Opens.grothendieckTopology X`. `over_toGrothendieck_eq_toGrothendieck_comap_forget`
  ties `J.over U` to the comap of the forgetful functor — the bridge to make the
  open-immersion restriction literally an over-pullback.
- **Porting cost**: medium — most of it is reused, not rebuilt; the `Over.map`
  coherences the project keeps re-deriving by hand (`hom_app_heq`+`subst`) already
  exist here.
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `CategoryTheory.Sites.SheafHom` (`Mathlib.CategoryTheory.Sites.SheafHom`)
- **Domain**: category theory / internal hom of sheaves.
- **Same structural problem there**: defines `presheafHom F G` with
  `obj X := (Over.forget X.unop).op ⋙ F ⟶ (Over.forget X.unop).op ⋙ G` — literally the
  project's "morphisms between restrictions of `A` and `B` to `Over X`" — and proves it
  is a sheaf (`presheafHom_isSheafFor`, `Presheaf.IsSheaf.hom`), giving `sheafHom F G`.
- **Technique**: the presheaf structure map is `whiskerLeft (Over.map f.unop).op`, and
  `map_id`/`map_comp` are proven via `Over.mapId`/`Over.mapComp` — the exact coherence
  the project fights. **The file is Type-valued** (hom-SET), and its `## TODO` lists
  "turn `presheafHom`/`sheafHom` into bifunctors" — so Mathlib has NOT yet proven
  internal-hom-commutes-with-restriction; the project's residual is genuinely new.
- **Mapping to project**: confirms the project's `dual` construction is the right shape
  and is the Mathlib idiom; the value-category gap (Type vs ModuleCat) is why the
  project must keep its own `homModule`/`internalHom`. The decisive lesson is the
  **poset trivialisation** of the `Over.map{Id,Comp}` coherence (see Top suggestion).
- **Porting cost**: low–medium (mostly already mirrored by the project).
- **Verdict**: ANALOGUE_FOUND.

### Analogue: `CategoryTheory.LocallyCartesianClosed.ExponentiableMorphism`
- **Domain**: category theory / locally cartesian closed categories (dependent product).
- **Same structural problem there**: for `f : I ⟶ J`, the pullback functor
  `pullback f : Over J ⥤ Over I` has a right adjoint `pushforward f` (the dependent
  product / internal hom along `f`), with the Beck–Chevalley iso
  `toOverIteratedSliceForwardIsoPullback` (`pullback f ≅ toOver(Over.mk f) ⋙
  iteratedSliceForward`) and full `pushforwardComp`/`pushforwardId` coherence.
- **Technique**: mate calculus / adjunction transposition; the comparison
  `internal-hom ∘ inverse-image ≅ inverse-image ∘ internal-hom` is a base-change
  (Beck–Chevalley) iso, an iso for the exact inverse image of an open immersion.
- **Mapping to project**: the abstract REASON the residual is an iso, but the internal
  hom here is the **cartesian** one (over the terminal object of the slice), not the
  ModuleCat internal hom; porting would require re-deriving in the module-valued
  setting. Suggestive framing, not directly liftable.
- **Porting cost**: high (value-category mismatch + heavy mate-calculus dependency).
- **Verdict**: PARTIAL_ANALOGUE.

## Top suggestion
The decisive observation is structural, not a lemma: **the project's base `Opens X` is
a poset, i.e. a thin category — every hom-set is a subsingleton.** Every place the
project has fought `Over.map` pseudofunctor coherence (`map_id`/`map_comp` not `rfl`,
the `hom_app_heq`+`subst` gymnastics recorded in iters 218–220) is pain inherited from
mirroring Mathlib's GENERAL-site `Sites/SheafHom.lean` + `Sites/Over.lean`, where
hom-sets are arbitrary. On `Opens X` those coherence squares commute automatically by
`Subsingleton.elim` / `Subsingleton.helim` (and `Over.OverMorphism.ext` reduces an
`Over` hom-equality to its underlying poset-hom, itself a subsingleton). So:

1. Port `TopologicalSpace.Opens.overEquivalence U : Over U ≌ Opens ↥U` (Mathlib already
   has it — `Mathlib/Topology/Sheaves/Over.lean`).
2. Read the **explicit `## TODO`** in that file — it is the project's blocker stated
   verbatim — and fill "the two functors are continuous ⇒ they induce a sheaf-category
   equivalence", leaning on `Sites/Over.lean`'s ready-made continuity/cocontinuity +
   dense-subsite instances and `Functor.IsDenseSubsite.sheafEquiv`
   (`Sites/DenseSubsite/Basic.lean`).
3. Reduce `(pushforward β)(dual A) ≅ dual(pushforward β A)` to the poset slice identity
   "`Over V` in `Opens U` = `Over V` in `Opens X` for `V ≤ U`": the comparison functor
   is `overEquivalence`/`iteratedSliceEquiv`, and naturality/compatibility is
   `Subsingleton.elim`, NOT a bespoke coherence engine.

First Mathlib file to read: `Mathlib/Topology/Sheaves/Over.lean` (25 LOC, the TODO).
First project file to touch: the file holding `dual`/`internalHom`
(`Scheme.Modules.dual`) — add the open-immersion `overEquivalence` transport there.
This is expected to come in WELL UNDER the 150–300 LOC general-`Over.map` estimate
precisely because thinness kills the coherence obligations; the honest residual cost is
the continuity-of-`overEquivalence` TODO, not a from-scratch slice-site build.
