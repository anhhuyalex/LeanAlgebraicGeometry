# `sectionsMul_mul_comm` is false for general `L` — needs invertibility

## Statement (current, unsound)

```lean
theorem sectionsMul_mul_comm (L : X.Modules) {na nb : ℕ}
    (a : sectionDeg L na) (b : sectionDeg L nb) :
    sectionsCast L (add_comm na nb) (GradedMonoid.GMul.mul a b) =
    GradedMonoid.GMul.mul b a
```

No hypothesis on `L`. This is **false**.

## Why it is false

The degreewise product is `a · b = Γ(μ_{i,j})(η(a ⊗ₜ b))`, the multiplication of the
**free tensor algebra** `T(Γ(L)) = ⊕ₘ Γ(L^{⊗m})`. Take `L = 𝒪_X²` (rank 2, non-invertible) and
evaluate at a point, so `R = Γ(𝒪)`, `Γ(L) = R²`, `Γ(L^{⊗2}) = R² ⊗_R R²`, and the sheafification unit
`η` is an isomorphism. For `a, b ∈ Γ(L) = R²`:

```
a · b = μ_{1,1}(a ⊗ₜ b),   b · a = μ_{1,1}(b ⊗ₜ a).
```

`μ_{1,1}` is a bijection and `a ⊗ₜ b ≠ b ⊗ₜ a` in `R² ⊗ R²`, so `a · b ≠ b · a`. The tensor algebra
on a rank-≥2 module is non-commutative.

## Where the blueprint sketch goes wrong

`lem:tensorPowAdd_comm` claims `μ_{m,n} = μ_{n,m} ∘ β_{L^m,L^n}` "by Mac Lane coherence for the
symmetric structure". But symmetric-monoidal coherence equates two canonical morphisms only when they
induce the **same permutation** of the (identical) tensor factors:

- `μ_{m,n}` : identity permutation of the `m+n` copies of `L`;
- `μ_{n,m} ∘ β` : the block transposition.

These differ (e.g. `β_{L,L} ≠ 𝟙` in `Vect` for `L = k²`), so the identity is **not** a coherence
consequence. It holds **iff `β_{L,L} = 𝟙`**, i.e. iff `L` is invertible (rank ≤ 1).

## Fix

Add an invertibility / line-bundle hypothesis to `sectionsMul_mul_comm`, to `lem:tensorPowAdd_comm`,
and to the `GCommSemiring` assembly (`lem:sectionGradedRing_gcommSemiring`). The natural Mathlib
hook is whatever expresses "`L` invertible in the symmetric monoidal `X.Modules`" — e.g. an instance
giving `β_{L,L} = 𝟙` (the braiding on an invertible object is trivial), or carrying `L` as a
`Picard`/invertible-sheaf datum. Under that hypothesis the leg closes from the **already-proven**
`tensorBraiding_hom_sectionsMul` plus the reduction now in the proof body:

```
simp only [gMul_mul_apply]
rw [← tensorBraiding_hom_sectionsMul (tensorPow L na) (tensorPow L nb) a b]
-- residue: sectionsCast (add_comm na nb) (Γ(μ_{na,nb}) x) = Γ(μ_{nb,na}) (Γ(β) x)
-- = `tensorPowAdd_comm` on x, which needs β_{L,L} = 𝟙 (invertibility).
```

## Status of the assoc partner

`sectionsMul_mul_assoc` / `tensorObjAssoc_hom_sectionsMul` / `tensorPowAdd_assoc` are **TRUE** for
arbitrary `L` (associativity holds in the free tensor algebra) — those remain genuine,
in-progress targets, NOT impossibilities.
