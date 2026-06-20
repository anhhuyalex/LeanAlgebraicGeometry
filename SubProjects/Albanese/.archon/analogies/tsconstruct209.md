# Analogy: is `sheafification ∘ PresheafTensor` the Mathlib-aligned shape for the line-bundle group law, or is `tensorObj_restrict_iso`'s difficulty an artifact?

## Mode
api-alignment

## Slug
tsconstruct209

## Iteration
209

## Question
Is the `sheafification ∘ PresheafOfModules.tensorObj` construction the Mathlib-aligned
shape for obtaining the line-bundle (invertible-sheaf) group law, or is
`tensorObj_restrict_iso`'s difficulty an ARTIFACT of this construction? Evaluate
whether a cheaper construction makes restriction-compatibility definitional/trivial:
(a) transition 1-cocycles in `𝒪_X^×`; (b) `Pic X = H¹(X, 𝒪_X^×)`;
(c) lift `Module.Invertible` / `CommRing.Pic` via affine-local gluing. For the
cheapest, say whether `tensorObj_restrict_iso` is even needed and what must be built.

## Project artifact(s)
- `Picard/TensorObjSubstrate.lean:199-202` — `tensorObj := sheafification ∘ PresheafOfModules.Monoidal.tensorObj`.
- `Picard/TensorObjSubstrate.lean:330-399` — `tensorObj_restrict_iso` (blocked 4 iters; 3 reductions + residual `sorry`).
- `Picard/TensorObjSubstrate.lean:401-425` — `tensorObj_isLocallyTrivial` (the SOLE consumer of `restrict_iso`).
- `Picard/TensorObjSubstrate.lean:438-453` — `exists_tensorObj_inverse` (the dual; `sorry`), `tensorObjOnProduct`.
- `Picard/RelPicFunctor.lean:235-269` — `addCommGroup` (final consumer; intended `QuotientAddGroup` build).
- `Picard/LineBundlePullback.lean` — `LineBundle.IsLocallyTrivial` (geometric predicate), `OnProduct = { M // IsLocallyTrivial M }`.

## Diagnosis (the single load-bearing observation)

`tensorObj_restrict_iso` is **needed at exactly one place**: inside
`tensorObj_isLocallyTrivial` (line 423), to run
`(M⊗N)|_W ≅ M|_W ⊗ N|_W ≅ 𝒪_W⊗𝒪_W ≅ 𝒪_W`. Local-triviality of the tensor is in
turn needed because the carrier `OnProduct` is the **subtype cut out by the
GEOMETRIC predicate** `IsLocallyTrivial M` (≡ "∀ x, ∃ affine `U ∋ x`, `M.restrict U.ι ≅ 𝒪_U`").

So the chain that produces the blocker is:
**geometric `IsLocallyTrivial` carrier  ⇒  must prove `tensorObj_isLocallyTrivial`
⇒  must compare a GLOBALLY-sheafified `⊗` against a LOCAL restriction  ⇒
`tensorObj_restrict_iso`  ⇒  opaque `PresheafOfModules.pullback` left adjoint (~200–300 LOC).**

The same geometric predicate independently forces the OTHER open sorry,
`exists_tensorObj_inverse` (construct the dual `L⁻¹ = Hom(L,𝒪)` and the contraction
`L ⊗ L⁻¹ ≅ 𝒪`) — which is what made iter-206 reach for the verified-absent
`MonoidalClosed (PresheafOfModules R₀)`.

**Conclusion: the difficulty is an ARTIFACT — not of "tensor on sheaves of modules"
(that definition is fine), but of proving a GEOMETRIC local-triviality statement
about a GLOBALLY-defined `⊗`. Mathlib's `Pic` idiom never proves such a statement.**

## Decisions identified

### Decision 1: the "line bundle" predicate — geometric local-triviality vs. monoidal ⊗-invertibility

- **Mathlib idiom**: an invertible module / line object is defined by **⊗-invertibility**:
  `Module.Invertible M` ⟺ `∃ N, M ⊗ N ≅ R` (the categorical `IsInvertible` / `Pic`-units
  notion). Cite: `Mathlib.RingTheory.PicardGroup` (`CommRing.Pic`, `Module.Invertible`)
  **[LSP-verified this session]**. Why Mathlib chose it: ⊗-invertibility
  is **manifestly closed under `⊗`** by pure monoidal algebra
  (`L⊗L'≅𝒪 ∧ M⊗M'≅𝒪 ⇒ (L⊗M)⊗(L'⊗M')≅𝒪` via associator/braiding/unitor isos), and the
  inverse is **carried by the predicate**. No restriction, no locality, no internal-hom.
- **Project's current path**: geometric `IsLocallyTrivial` (locally `≅ 𝒪`), a subtype `OnProduct`.
- **Gap**: divergent-with-cost. The geometric predicate is the *root cause* of BOTH open
  sorries. With ⊗-invertibility: `tensorObj_isLocallyTrivial` → free (monoidal algebra),
  `exists_tensorObj_inverse` → definitional (predicate carries the witness),
  `tensorObj_restrict_iso` → **not needed**.
- **Cost of divergence**: `tensorObj_restrict_iso` (~200–300 LOC / 4 absent Mathlib
  ingredients, per `informal/tensorObj_restrict_iso.md`) **plus** `exists_tensorObj_inverse`
  (the dual / internal-hom, the iter-206 `MonoidalClosed` wall). Both are charged to the
  geometric predicate and both vanish under the Mathlib predicate.
- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision 2: group-law construction — per-axiom existence-isos on a subtype vs. `Units` of the iso-class monoid

- **Mathlib idiom**: `CommRing.Pic R = Units (Skeleton (ModuleCat R))` — the abelian group
  is the **units of the commutative monoid of ⊗-iso-classes**; every group axiom is
  *inherited* from the monoid (which is inherited from the coherence ISOS of `⊗`), and the
  inverse is the `Units` structure on invertible elements. Cite **[LSP-verified,
  `Mathlib.RingTheory.PicardGroup`]**: `CommRing.Pic`, `instCommGroupPic`,
  `instSmallUnitsSkeletonModuleCat : Small (Skeleton (ModuleCat R))ˣ`.
- **Project's current path** (iter-206 PIVOT, `TensorObjSubstrate.lean:221-233`): abandon the
  monoidal instance, "build the group law directly on the line-bundle subcategory from four
  existence-of-iso lemmas." One of those four IS `tensorObj_restrict_iso`.
- **Gap**: divergent-with-cost. The per-axiom route re-introduced, in a different guise, the
  exact geometric obligations (`restrict_iso`, dual) that the `Units (Skeleton)` route never
  incurs. The iter-206 pivot correctly rejected the *full `MonoidalCategory`+`MonoidalClosed`*
  instance, but the corrective swapped one hard obligation set for an equally hard one rather
  than removing it.
- **Cost of divergence**: see Decision 1 — the per-axiom route keeps `restrict_iso` on the
  critical path.
- **Verdict**: ALIGN_WITH_MATHLIB.

### Decision 3: the `tensorObj := sheafification ∘ PresheafTensor` definition itself

- **Mathlib idiom**: to get `⊗` on `SheafOfModules`/`Scheme.Modules`, sheafify the
  `PresheafOfModules.Monoidal` tensor — exactly what the project does.
- **Project's current path**: `TensorObjSubstrate.lean:199-202`.
- **Gap**: identical. The `⊗` *object* definition is the right shape; so are the already-built
  `tensorObjIsoOfIso` (252) and `tensorObj_unit_iso` (266) — both are `sheafification.mapIso
  (presheaf-level iso)`, the cheap pattern with no pullback.
- **Verdict**: PROCEED.

### Decision 4 (route comparison): (a) cocycles, (b) H¹(X,𝒪_X^×), (c) Module.Invertible/Pic gluing

- **(a) transition 1-cocycles in `𝒪_X^×`**: restriction-compat IS free (Čech cocycles restrict),
  but this is a **large parallel build** — cocycle-data structure, choice of trivializing covers,
  the equivalence "line bundle ≅ cocycle mod coboundary", and a bridge to the existing iso-class
  carrier. Mathlib has **no `𝒪_X^×` cocycle infra**; the project's Čech machinery is `ModuleCat k`
  -valued (additive), not for the multiplicative `𝒪_X^×`. NEEDS_MATHLIB_GAP_FILL, not cheaper.
- **(b) `Pic X = H¹(X, 𝒪_X^×)`**: group structure automatic, BUT needs the **multiplicative sheaf
  of units `𝒪_X^×`** as a sheaf of abelian groups (fresh infra; the project's `Cohomology/*`
  `HModule` is `ModuleCat k`-valued — **near-zero reuse**, honest assessment), no Mathlib
  `Scheme.Pic` as H¹, AND to connect to the `OnProduct` carrier you must re-prove
  `H¹(X,𝒪_X^×) ≅ {iso classes of invertible sheaves}` — itself a tensor-of-line-bundles theorem,
  i.e. circular for *this* goal. NEEDS_MATHLIB_GAP_FILL, strictly more work.
- **(c) lift `Module.Invertible`/`CommRing.Pic`**: this is the right *idiom* (Decisions 1+2).
  Naive "glue affine Picard groups by descent" is itself substantial, and the directive notes a
  `PicardGroup.lean` TODO "connect to invertible sheaves" is unbuilt. But the **specialization
  that does NOT require global gluing** is: take the ⊗-invertibility predicate + a `CommMonoid`
  on iso-classes assembled *directly* from `tensorObj`'s coherence isos (no `Skeleton`/
  `Localization.Monoidal` typeclass needed). THIS is the cheapest concrete path.
- **Verdict on routes**: (c)-specialized = the cheapest; (a),(b) = NEEDS_MATHLIB_GAP_FILL and
  not cheaper.

## Recommendation

**The construction is the right *shape* (`⊗ = sheafify ∘ presheaf-tensor` is correct; keep it),
but the group law is built on the wrong *predicate*. Adopt Mathlib's `Module.Invertible` /
`CommRing.Pic = Units(Skeleton)` idiom: make ⊗-invertibility — not geometric local-triviality —
the predicate that defines the line-bundle carrier and the group.** Concretely:

1. Define `IsInvertible (M : X.Modules) : Prop := ∃ N, Nonempty (tensorObj M N ≅ 𝒪_X)`
   (the `Module.Invertible` analogue; `𝒪_X = SheafOfModules.unit X.ringCatSheaf`).
2. Build the three remaining coherence isos of `tensorObj` — **associator**, **left/right
   unitor**, **braiding** — each as `sheafification.mapIso (PresheafOfModules.Monoidal.<coherence iso>)`,
   the SAME cheap pattern as the already-landed `tensorObjIsoOfIso` / `tensorObj_unit_iso`
   (no `pullback`, no opaque adjoint, no missing Mathlib instance). ~15 LOC each.
3. Assemble a `CommMonoid` on ⊗-iso-classes from those isos (op = `tensorObj`, well-defined via
   `tensorObjIsoOfIso`), then the group on the invertible elements is `Units` of it — group
   axioms free.
4. **`tensorObj_restrict_iso`, `tensorObj_isLocallyTrivial`, and `exists_tensorObj_inverse` are
   then NOT on the critical path** to `RelPicFunctor.addCommGroup`. Closure under ⊗ and the
   inverse come from monoidal algebra + the predicate.

**This is reverting to the project's own documented intent, not a new divergence.**
`LineBundlePullback.lean:50-58` states `OnProduct` was meant to pair the carrier with an
**`IsInvertible` witness** "once that predicate is in Mathlib (or proven internally)", and
`:93-98,106` calls `IsLocallyTrivial` "the project-side stand-in for the missing Mathlib
`IsInvertible` predicate" (citing `Module.Invertible R M` in `Mathlib.RingTheory.PicardGroup`).
Verified this session: `archon-protected.yaml` freezes only `Genus`/`Jacobian`/`AbelJacobi`
declarations — `IsLocallyTrivial` (`:115`) and `OnProduct` (`:130-131`) are **NOT frozen**, so a
structural/prover agent may change the predicate (plan/review then update the `OnProduct` blueprint
pin). **No user escalation required.** Moreover the `preimage_subgroup` Setoid already presupposes
the relation `L ~ L' ↔ L ⊗ (L')⁻¹ ∈ π_T^* Pic(T)` (`:42-43,349-351`), so it too needs `⊗`+inverse
on the carrier — which ⊗-invertibility supplies for free. The equivalence
`IsInvertible ⟺ IsLocallyTrivial` (`invertible ⟺ locally free rank 1 ⟺ locally trivial`) can be
proved later, **off** the group-law critical path.

If, after all of the above, a geometric `IsLocallyTrivial` statement is still genuinely required
downstream, note that EVERY route (including the full `Localization.Monoidal` + `W.IsMonoidal`
monoidal-instance route the iter-206 §2 comment describes) bottoms out in the SAME fact
"sheafification/⊗ commutes with localization-to-an-open" — so no route makes restriction-compat
literally free; the value of the recommendation is moving it **off the group-law critical path**,
not eliminating it from mathematics.
