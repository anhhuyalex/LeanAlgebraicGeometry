All work is landed, verified, and committed. Here is my report.

## Summary

Landed the complete **group-theoretic/algebraic content of Milne Lemma 3.3 sub-step 2** (the hard direction of the difference-map converse), the last remaining sorry gating the Albanese rational-map-extension chain. Milne's reconstruction `f(x) = Φ(x,u)·f(u)` is now a formal, axiom-clean domain bound `Dom(Φ) ⊓ pr₂⁻¹(Dom f) ≤ Dom(f∘pr₁)`, plus two reusable Mathlib-gap bricks for the `RationalMap` API. All kernel-verified, root build green (8660 jobs), and adversarially verified sound+faithful (3-lens workflow, no blockers/majors).

## Progress
- AlgebraicJacobian/Albanese/DifferenceMap.lean: +6 axiom-clean decls (`GrpObj.lift_diff_lift_mul`, `grpObjMulLeft`, `pullback_lift_diff_lift_mul`, `reconstruct_precomp_fst`, `le_domain_precomp_fst_of_difference`); still sorry-free.
- AlgebraicJacobian/Albanese/RationalMapPrecomp.lean: +`RationalMap.le_domain_precomp` (general: `p⁻¹ᵁ f.domain ≤ (f.precomp p).domain`), axiom-clean.
- AlgebraicJacobian/Albanese/RationalMapProd.lean: +`pairPartialMap`, `pairPartialMap_toRationalMap`, `le_domain_prod` (general `prod` domain lower bound), axiom-clean.
- AlgebraicJacobian/Albanese/CodimOneExtension.lean: unchanged — the one intended sorry `indeterminacy_pure_codim_one_into_grpScheme` (:1692) still open (out of one-session reach).
- blueprint/src/chapters/Albanese_CodimOneExtension.tex: +6 `\leanok` nodes wired into `lem:milne_codim1_indeterminacy`; substep-2 prose updated; hypothesis + purity fixes from the audit.
- informal/milne-lemma-3.3.md: substep-2 status rewritten (algebraic content done; topology remainder scoped).

## Issues
- The headline `indeterminacy_pure_codim_one_into_grpScheme` sorry is unchanged (expected): it needs substep-2 *topology* + substeps 3/4b, all genuinely multi-session.
- Minor cosmetic (not a bug): `le_domain_prod` carries a redundant `[IsReduced X]` binder (derivable from `[IsIntegral X]`); left as-is to avoid touching kernel-verified Lean. Flagged by the audit as "nothing dead."
- Adversarial verify: 0 blockers/majors; 1 minor (blueprint hypotheses under-specified) — **fixed** this session.

## Why I stopped
Task not complete: T9's Albanese universal property is still gated on the Milne 3.3 sorry (and the UP leg on the missing `Sym^g` scheme substrate). But I carried one well-scoped piece — sub-step 2's entire algebraic content — as far as it goes in one session, kernel-verified and adversarially checked. The two remaining sub-step-2 pieces are purely topological (fiber irreducibility for existence of `u`; and the fppf smooth-descent reflection `Dom(f∘pr₁) ⊆ pr₁⁻¹(Dom f)`, a from-scratch general theorem), plus substeps 3 (germ definedness at `e`) and 4b (diagonal Krull) — none one-session.

## Next
- Sub-step 2 topology: (a) prove existence of `u` with `(x,u)∈Dom(Φ)`, `u∈Dom(f)` via irreducibility of `X_{κ(x)}` (this is *why* `GeometricallyIrreducible` is a hypothesis); (b) the smooth-descent reflection `Dom(f∘pr₁) ⊆ pr₁⁻¹(Dom f)` — likely a multi-session fppf-descent-of-definedness build.
- Sub-step 3: germ-pullback definedness criterion at the anchor `e` (probably via `PartialMap.ofFromSpecStalk` + spreading-out).
- Sub-step 4b: diagonal codim-1 Krull bound (4a `PolePurity.lean` already done).
- `reconstruct_precomp_fst` / `le_domain_precomp_fst_of_difference` are ready to be consumed by the eventual `indeterminacy_pure_codim_one_into_grpScheme` proof in `CodimOneExtension.lean`.
