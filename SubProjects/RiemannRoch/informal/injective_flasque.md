# `Scheme.IsFlasque.injective_flasque` — missing Mathlib ingredient

**File:** `AlgebraicJacobian/RiemannRoch/H1Vanishing.lean`
**Declaration:** `AlgebraicGeometry.Scheme.IsFlasque.injective_flasque`
**Blueprint:** `lem:isFlasque_injective` (Hartshorne III, Lemma 2.4)
**Status (iter-198):** typed `sorry`, reduced to the per-`(V ≤ U)` surjectivity
goal (`intro U V h` done); the surjectivity step is the genuine gap.

## Statement

For an injective object `I` of `Sheaf (Opens.grothendieckTopology X) (ModuleCat kbar)`,
`I` is flasque: for every `V ≤ U`, the restriction `I(U) → I(V)` is surjective
on underlying `kbar`-modules.

## Intended proof (Hartshorne III.2.4)

For an open `U` let `j_{U!} 𝒪_U` denote the **extension by zero** of the
constant `kbar`-module sheaf on `U` — concretely the sheafification of the
free `ModuleCat kbar`-presheaf on the representable `よU`, i.e. the presheaf
`e_U : W ↦ (kbar if W ≤ U else 0)` with identity/zero restriction maps.

1. There is a natural isomorphism `Hom_{Sheaf}(j_{U!} 𝒪_U, I) ≅ I(U)`,
   natural in `U` (Yoneda for the free-module-on-representable presheaf,
   composed with the sheafification adjunction). Under it the restriction
   `I(U) → I(V)` corresponds to precomposition with the inclusion
   `j_{V!} 𝒪_V ↪ j_{U!} 𝒪_U`.
2. The presheaf map `e_V → e_U` (identity on `kbar` where both are `kbar`,
   zero elsewhere) is a sectionwise monomorphism; sheafification preserves
   monos, so `j_{V!} 𝒪_V ↪ j_{U!} 𝒪_U` is a monomorphism of sheaves.
3. `I` injective ⟹ `Hom(-, I)` sends this mono to an epimorphism of
   `kbar`-modules, i.e. `Hom(j_{U!} 𝒪_U, I) → Hom(j_{V!} 𝒪_V, I)` is
   surjective. Transporting along the iso of (1) gives `I(U) → I(V)` surjective.

## Precise missing ingredient

Mathlib (snapshot `b80f227`) ships **no** extension-by-zero functor `j_!`
(the left adjoint to the open-immersion restriction functor) for
`Sheaf (Opens X) (ModuleCat kbar)`. Confirmed by search:

- `AlgebraicGeometry.Scheme.Modules.restrictAdjunction` is
  `restrictFunctor ⊣ pushforward` — the *restriction has a right adjoint*
  (pushforward), which is the wrong direction.
- No `Sheaf`-level `j_! ⊣ (restriction along an open immersion)` adjunction
  exists, nor a free-module-sheaf-on-a-representable construction with the
  Hom-iso of step (1).

The smallest self-contained substrate to add (project-local, est. ~100–150 LOC):

```
-- the extension-by-zero presheaf
def extByZeroPresheaf (U : Opens X) : (Opens X)ᵒᵖ ⥤ ModuleCat kbar :=
  { obj := fun W => if W.unop ≤ U then ModuleCat.of kbar kbar else 0
    map := ... }              -- identity where both ≤ U, zero otherwise
-- its sheafification `j_{U!} 𝒪_U := (presheafToSheaf _ _).obj (extByZeroPresheaf U)`
-- the Hom-iso, natural in U:
def homIso (U : Opens X) (I : Sheaf _ _) :
    (j_{U!} 𝒪_U ⟶ I) ≃ (I.val.obj (op U))           -- Yoneda + free⊣forget + sheafify adj
-- monotonicity: `V ≤ U → (j_{V!} 𝒪_V ⟶ j_{U!} 𝒪_U)` mono
```

Then `injective_flasque` follows from `Injective.factors`/`Injective.comp_factorThru`
applied to the mono, transported along `homIso`.

## Notes for the planner

- This lemma is **out of the headline cone**: the degree-1 vanishing
  `H1_skyscraperSheaf_finrank_eq_zero` uses only the `n = 0` base case of
  `HModule_flasque_subsingleton_aux`, which does not touch
  `injective_flasque`. The lemma is needed only to make the general-`i`
  statement `HModule_flasque_eq_zero` (and the `n ≥ 1` inductive step)
  sorry-free.
- Recommend assigning the `extByZeroPresheaf` + `homIso` substrate in
  `mathlib-build` mode (or upstreaming `j_!` to Mathlib).
- No informal-agent API key was configured this run, so the external-LLM
  route from the prover protocol could not be exercised.
