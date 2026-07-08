## Emitted Thinking

Let me analyze the Lean goal state and the blueprint plan to understand what's being asked. I need to:

1. Understand the mathematical goal
2. Search for relevant definitions and theorems
3. Create a ranked list of relevant results
4. Write a mathematical proof plan

Let me start by reading the current file and searching for relevant definitions.

Now I have a comprehensive picture of the goal. Let me analyze:

## The Mathematical Goal

**Goal**: `instance pullback_preservesFiniteLimits (g : S' ⟶ S) [Flat g] : Limits.PreservesFiniteLimits (Scheme.Modules.pullback g)`

This states: if `g : S' → S` is a flat morphism of schemes, then the pullback functor `g* : QCoh(S) → QCoh(S')` (on sheaves of modules / quasi-coherent sheaves) preserves finite limits.

In plain mathematics: **flat pullback is left-exact**.
The strategy is to decompose the pullback functor into three parts: sheafification, the presheaf pullback, and the forgetful functor. The outer two factors already preserve finite limits in Mathlib, so I just need to show the middle presheaf pullback preserves them when `g` is flat. Looking at the instances available in Mathlib, I see that `forget` preserves finite limits and `sheafification` preserves them too, but the real question is whether `PresheafOfModules.pullback` preserves finite limits when the ring map is flat — this is the missing piece that would complete the chain of reasoning. The stalkwise perspective shows that the pullback of presheaves of modules is exact when the base map is flat, since extension of scalars along a flat ring map preserves exactness. However, Mathlib doesn't currently have this packaged as a `PreservesFiniteLimits` instance for `PresheafOfModules.pullback`. Let me trace through the actual composition order in the `pullbackIso` definition to see how the pieces fit together. The `⋙` operator chains these functors left-to-right: we forget the sheaf structure to get a presheaf, apply the presheaf-level pullback along the ring homomorphism, then sheafify the result to recover the sheaf structure on the target.

To prove the composite preserves finite limits, I need each component to preserve them—the forget and sheafification functors are handled by Mathlib, but the presheaf pullback is the missing piece that requires the flatness assumption on `g`.

Looking at the actual Lean code, there's a sorry at line 164-165 declaring that `Scheme.Modules.pullback g` preserves finite limits when `g` is flat, and the comment flags this as the genuine gap in the homology argument—apparently a multi-hundred line proof.

The mathematics is straightforward: for a flat morphism between schemes, the pullback functor on sheaves of modules is left-exact. This follows from the classical fact that extension of scalars along a flat ring homomorphism is exact, and the general case reduces to checking this stalkwise.

What's blocking the Lean formalization is the need for a pointwise description of the pullback functor (currently just defined as a left adjoint), identifying stalks with extension of scalars, and establishing that extension of scalars preserves finite limits when the base map is flat. image is exact as a left adjoint in the presheaf topos, extension of scalars is left-exact for flat ring maps, and composing exact functors preserves exactness—this all amounts to several hundred lines of Lean code. Let me now write out a comprehensive mathematical analysis covering the natural language explanation, the key equations, the proof strategy, relevant Lean results ranked by importance, and what's currently missing from the library. `O_{S'}`-modules) preserves finite limits.

In other words: flat pullback is left-exact.

Now I'm writing out the formal statement in KaTeX notation, expressing that if $g : S' \to S$ is flat, then the pullback functor $g^*$ from quasi-coherent sheaves on $S$ to quasi-coherent sheaves on $S'$ is left-exact and preserves finite limits.

For the proof strategy, I'm using the factorization through `SheafOfModules.pullbackIso` to establish this result.

The key insight is that the pullback functor decomposes into three steps: forgetting the sheaf condition, applying the presheaf-level pullback via the ring homomorphism, and then re-sheafifying the result. Since each of these component functors preserves finite limits, their composition does as well.

The first two factors are straightforward—forgetting is a right adjoint so it preserves all limits, and sheafification is left-exact as a left adjoint with a conservative right adjoint. The real work lies in showing that the presheaf-level pullback preserves finite limits precisely when the morphism $g$ is flat. This is where the flatness condition becomes essential to the argument. The extension of scalars $\mathcal{O}_{S'} \otimes_{g^{-1}\mathcal{O}_S} -$ is left-exact precisely when $g$ is flat, since flatness ensures the tensor product preserves exactness. At the level of stalks, this becomes $(\mathcal{O}_{S', s'}) \otimes_{\mathcal{O}_{S,s}} \mathcal{F}_s$, which is exact because $\mathcal{O}_{S',s'}$ is flat over $\mathcal{O}_{S,s}$, and finite limits commute with stalks on a locally ringed site.

The Lean proof faces a concrete gap: `PresheafOfModules.pullback` is defined abstractly as an adjoint without a pointwise description, so identifying its stalks with extension of scalars requires additional work that isn't yet in Mathlib. While the library has `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` for flat extension of scalars, this hasn't been lifted to the presheaf or sheaf level. Looking at the goal state, there are no goals remaining at the declaration point, but the `sorry` on line 165 is still there as a placeholder for the proof body. Let me now compile the full ranked list of relevant Lean results to address the original question.

## Assistant Text

I'll read the current file and search for relevant definitions simultaneously.

Now I have everything I need. Let me compile the full analysis.

---

## Natural Language Explanation

The goal is to prove that **flat pullback of sheaves of modules is left-exact**: given a flat morphism of schemes `g : S' → S`, the functor `g* : Mod(S) → Mod(S')` (pulling back quasi-coherent `O_S`-modules to `O_{S'}`-modules) preserves finite limits.

Preserving finite limits is the categorical formulation of left-exactness: the functor commutes with kernels, equalizers, and all finite limits, equivalently it sends exact sequences `0 → A → B → C` to exact sequences `0 → g*A → g*B → g*C`.

---

## The Goal in KaTeX

Let $g : S' \to S$ be a flat morphism of schemes. The claim is:

$$g^* : \mathcal{O}_S\text{-Mod} \longrightarrow \mathcal{O}_{S'}\text{-Mod} \quad \text{preserves finite limits.}$$

Equivalently, for every finite diagram $D : \mathcal{J} \to \mathcal{O}_S\text{-Mod}$ with $\mathcal{J}$ finite, the canonical comparison morphism
$$g^*\!\left(\varprojlim_{j \in \mathcal{J}} D(j)\right) \xrightarrow{\;\sim\;} \varprojlim_{j \in \mathcal{J}} g^*(D(j))$$
is an isomorphism.

---

## Mathematical Proof (Putnam Style)

**Theorem.** *If $g : S' \to S$ is a flat morphism of schemes, then $g^* : \mathcal{O}_S\text{-Mod} \to \mathcal{O}_{S'}\text{-Mod}$ preserves finite limits.*

### Step 1: Factor $g^*$ via `SheafOfModules.pullbackIso`

By the Mathlib lemma `SheafOfModules.pullbackIso` (file `PullbackContinuous.lean`, line 106), the sheaf-level pullback factors as:
$$g^* \;\cong\; \underbrace{\operatorname{forget}_S}_{(i)} \;\circ\; \underbrace{\operatorname{PresheafMod.pullback}(\varphi_{\mathrm{hom}})}_{(ii)} \;\circ\; \underbrace{\operatorname{sheafification}}_{(iii)}$$
where:
- $(i)$: $\operatorname{ShvMod}(S) \to \operatorname{PreshMod}(\mathcal{O}_S)$ forgets the sheaf condition
- $(ii)$: $\operatorname{PreshMod}(\mathcal{O}_S) \to \operatorname{PreshMod}(\mathcal{O}_{S'})$ is the presheaf-level pullback along $\varphi_{\mathrm{hom}}$
- $(iii)$: $\operatorname{PreshMod}(\mathcal{O}_{S'}) \to \operatorname{ShvMod}(S')$ re-sheafifies

Since a composite of left-exact functors is left-exact, it suffices to show each factor preserves finite limits.

### Step 2: Factors $(i)$ and $(iii)$ preserve finite limits unconditionally

**Factor $(i)$ — forget:** `SheafOfModules.forget` is right adjoint to sheafification, hence it preserves all limits. Mathlib provides `SheafOfModules.forgetPreservesFiniteLimits` (`Sheaf/Limits.lean`, lines 100–101). ✓

**Factor $(iii)$ — sheafification:** Sheafification $\operatorname{PreshMod} \to \operatorname{ShvMod}$ is a left-exact reflector (localization at the class of local isomorphisms). Mathlib provides `PreservesFiniteLimits (sheafification α)` (`Presheaf/Sheafification.lean`, lines 183–185), derived from the fact that the composite with the forgetful functor to presheaves of abelian groups is left-exact (since `presheafToSheaf J AddCommGrpCat` is left-exact), together with the conservativity of `SheafOfModules.toSheaf`. ✓

### Step 3: Factor $(ii)$ preserves finite limits when $g$ is flat

This is the only content requiring flatness.

**Claim.** If $g$ is flat, then $F := \operatorname{PresheafMod.pullback}(\varphi_{\mathrm{hom}}) : \operatorname{PreshMod}(\mathcal{O}_S) \to \operatorname{PreshMod}(\mathcal{O}_{S'})$ preserves finite limits.

**Proof.** We argue stalkwise. For a point $s' \in S'$ with image $s = g(s') \in S$, the stalk of $F(\mathcal{F})$ at $s'$ is:
$$\bigl(F(\mathcal{F})\bigr)_{s'} \;=\; \mathcal{O}_{S',s'} \otimes_{\mathcal{O}_{S,s}} \mathcal{F}_s.$$
This is the extension of scalars functor $\mathcal{O}_{S',s'} \otimes_{\mathcal{O}_{S,s}} -$ applied to the stalk $\mathcal{F}_s$.

Since $g$ is flat, by definition $\mathcal{O}_{S',s'}$ is a flat $\mathcal{O}_{S,s}$-module for every $s'$. Flatness of a module $M$ over a ring $R$ is equivalent to $M \otimes_R -$ being an exact functor, i.e., preserving finite limits in $R\text{-Mod}$. This is `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` in Mathlib.

Since the stalk functors at every point are jointly conservative on sheaves (a morphism of sheaves is an isomorphism iff it is an isomorphism on all stalks), and finite limits in sheaf categories are computed stalkwise, we conclude $F$ preserves finite limits.

### Step 4: Assemble

Since all three factors in the factorization
$$g^* \;\cong\; \operatorname{forget} \;\circ\; \operatorname{PresheafMod.pullback}(\varphi_{\mathrm{hom}}) \;\circ\; \operatorname{sheafification}$$
preserve finite limits, their composite $g^*$ preserves finite limits. $\blacksquare$

---

## Provability Check

**The statement is true** with the given hypothesis `[Flat g]`. The `sorry` in the Lean file reflects a **formalization gap**, not a mathematical deficiency.

The gap lives entirely in factor $(ii)$: Mathlib defines `PresheafOfModules.pullback φ` as `(pushforward φ).leftAdjoint` (an abstract left adjoint, `Presheaf/Pullback.lean`, line 44), with **no pointwise/stalkwise description**. The proof above requires:

1. Identifying the stalks of `PresheafOfModules.pullback φ.hom` with extension of scalars — **not packaged in Mathlib**.
2. Lifting `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` through this stalkwise identification — **not packaged**.
3. Transferring finite-limit preservation through `pullbackIso` — requires resolving `HasSheafify` and related typeclass instances for the concrete scheme site.

The file's own docstring (lines 136–153) confirms this analysis precisely.

---

## Ranked List of Relevant Lean Results

### Tier 1 — Directly load-bearing for the strategy

| Rank | Name | File | Lines | Role |
|------|------|------|-------|------|
| 1 | `SheafOfModules.pullbackIso` | `Mathlib/.../Sheaf/PullbackContinuous.lean` | 106–111 | The factorization `g* ≅ forget ∘ pullback(φ.hom) ∘ sheafification`; the entire strategy rests on this |
| 2 | `SheafOfModules.forgetPreservesFiniteLimits` | `Mathlib/.../Sheaf/Limits.lean` | 100–101 | Factor (i) left-exactness; unconditional Mathlib instance |
| 3 | `PreservesFiniteLimits (sheafification α)` | `Mathlib/.../Presheaf/Sheafification.lean` | 183–185 | Factor (iii) left-exactness; unconditional Mathlib instance |
| 4 | `ModuleCat.preservesFiniteLimits_extendScalars_of_flat` | Mathlib (ModuleCat) | — | The affine-local flat-exactness engine; the only flatness-dependent input |
| 5 | `pullback_preservesFiniteLimits` (with `sorry`) | `CechHigherDirectImageUnconditional.lean` | 164–165 | The target itself; currently `sorry` |

### Tier 2 — Supporting structure needed to close the gap

| Rank | Name | File | Lines | Role |
|------|------|------|-------|------|
| 6 | `PresheafOfModules.pullback` | `Mathlib/.../Presheaf/Pullback.lean` | 44–45 | Defined as left adjoint to pushforward; needs a pointwise description to enable the stalkwise argument |
| 7 | `PresheafOfModules.pullbackPushforwardAdjunction` | `Mathlib/.../Presheaf/Pullback.lean` | 50–51 | Adjunction `pullback ⊣ pushforward`; needed to identify factor (ii) |
| 8 | `PresheafOfModules.sheafification` | `Mathlib/.../Presheaf/Sheafification.lean` | 54–68 | Factor (iii); definition of the sheafification functor |
| 9 | `PresheafOfModules.sheafificationAdjunction` | `Mathlib/.../Presheaf/Sheafification.lean` | 125–126 | Right adjoint to sheafification is `forget ∘ restrictScalars`; needed to confirm `forget` is a right adjoint |
| 10 | `SheafOfModules.sheafificationCompPullback` | `Mathlib/.../Sheaf/PullbackContinuous.lean` | 118–126 | Coherence iso `sheafification ∘ pullback ≅ pullback(φ.hom) ∘ sheafification`; supports transport arguments |

### Tier 3 — Project-local context

| Rank | Name | File | Lines | Role |
|------|------|------|-------|------|
| 11 | `pullback_preservesFiniteColimits` | `CechHigherDirectImageUnconditional.lean` | 129–130 | Left-adjoint instance (free, no flatness needed); shows colimit side is already closed |
| 12 | `pullback_preservesHomology` | `CechHigherDirectImageUnconditional.lean` | 169–170 | Derived from `pullback_preservesFiniteLimits`; shows the homology-side gap propagation |
| 13 | `cech_flatBaseChange` | `CechHigherDirectImageUnconditional.lean` | 912–933 | Ultimate consumer of this instance; the entire flat base change proof depends on closing this sorry |

---

## Summary of What Is Missing

The statement is **mathematically provable** from `[Flat g]`. No hypotheses are missing. The Lean proof requires three ingredients not yet in Mathlib:

1. **A stalkwise/pointwise description** of `PresheafOfModules.pullback φ.hom` — that its sections (or stalks) are computed by extension of scalars along the corresponding ring maps.
2. **Lifting** `preservesFiniteLimits_extendScalars_of_flat` from the affine/module-category level through that stalkwise description to the presheaf-of-modules level.
3. **Transporting** across `SheafOfModules.pullbackIso` and resolving the concrete `HasSheafify` instances for the scheme site.

This is a genuine multi-hundred-line Mathlib development, correctly described as the "irreducible core" in the file's docstring.