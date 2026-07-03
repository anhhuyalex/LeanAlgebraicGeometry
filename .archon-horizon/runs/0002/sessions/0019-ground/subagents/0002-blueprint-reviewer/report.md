I have all the evidence needed. Let me compile the findings.

## Review summary: Albanese T3 blueprint changes vs Lean

**Verdict: clean.** All six new `\leanok` nodes point at Lean declarations that exist under the fully-qualified names given, statements match, proofs are complete, the `\uses` DAG is correct and acyclic, and no node is marked green over a `sorry`.

### 1. Declaration existence + name/namespace + statement match

| Blueprint node | `\lean{...}` | Lean location | Match |
|---|---|---|---|
| `lem:mvPolynomial_height_eq_natCard_of_isMaximal` | `MvPolynomial.height_eq_natCard_of_isMaximal` | StandardSmoothDimension.lean:72 | ✓ `M.height = Nat.card ι` = "height exactly #I" |
| `lem:standard_smooth_le_height_of_isMaximal` | `Algebra.IsStandardSmoothOfRelativeDimension.natCast_le_height_of_isMaximal` | :126 (inside `namespace Algebra.IsStandardSmoothOfRelativeDimension`) | ✓ `(n:ℕ∞) ≤ m.height` |
| `lem:standard_smooth_le_ringKrullDim_localization` | `...le_ringKrullDim_of_isLocalization_atPrime` | :186 | ✓ `(n:WithBot ℕ∞) ≤ ringKrullDim Sₘ` with `[IsLocalization.AtPrime Sₘ m]` |
| `lem:regular_of_finrank_cotangent_le_dim` | `IsRegularLocalRing.of_finrank_cotangentSpace_le_ringKrullDim` | :208 | ✓ Noetherian local, `finrank κ (m/m²) ≤ ringKrullDim A ⟹ regular` |
| `lem:standard_smooth_regular_at_rational_point` | `AlgebraicGeometry.Scheme.isRegularLocalRing_localization_of_isStandardSmooth_of_bijective_residue` | CodimOneExtension.lean:1015 (inside `AlgebraicGeometry`→`Scheme`) | ✓ bijectivity is on `algebraMap k (ResidueField Sₘ)` = composite k→Sₘ→κ(m) |
| `lem:standard_smooth_regular_at_closed_point_algclosed` | `AlgebraicGeometry.Scheme.isRegularLocalRing_localizationAtPrime_of_isStandardSmooth_of_isAlgClosed` | :1063 | ✓ `[IsAlgClosed k]`, every maximal `m`, `IsRegularLocalRing (Localization.AtPrime m)` |

Namespace context verified: lines 1015/1063 sit inside `namespace AlgebraicGeometry` (123) → `namespace Scheme` (125), so the `AlgebraicGeometry.Scheme.` prefix in the blueprint is correct. Both are public `theorem`s (not `private`).

### 2. Proof completeness (house style)
All six blueprint proofs are complete rigorous arguments (induction over `#I`; submersive presentation + Krull height theorem; Nakayama + Krull; Zariski's lemma). No "clearly/omitted/TODO/sketch", no Lean tactics leaking into prose.

### 3. `\uses` edges — dependency-correct
- Every cited label resolves to a real node in the blueprint (all 7 sibling labels + `lem:smooth_to_regular_local_ring` confirmed present, exactly one `\label` each).
- Node 5's 7 `\uses` each correspond to a real call in the Lean proof (lines 1031, 1034, 1035, 1037, 1043, 1046, 1048). Node 6 → node 5 matches the Lean call at line 1070. Node 3 → node 2 + `ringKrullDim_localization_eq_height_atPrime` matches lines 193–194. Node 2 → node 1 matches line 136.
- The extended `\uses` on `lem:smooth_to_regular_local_ring` (line 1604) adds `lem:standard_smooth_regular_at_closed_point_algclosed`, a real sibling label (node 6). DAG is acyclic: `smooth_to_regular → node6 → node5 → {node3,node4,…} → node2 → node1`, all edges pointing to earlier lemmas.

### 4. No false green flags
- StandardSmoothDimension.lean: 0 `sorry`. CodimOneExtension.lean lines 1015–1089 (both new theorems): 0 `sorry`.
- `lem:smooth_to_regular_local_ring`: its Lean `isRegularLocalRing_stalk_of_smooth` (CodimOneExtension.lean:1452, `private`) does still contain a `sorry` (line 1563), but the node's `\leanok` (line 1595) is **statement-level only** — it sits in the `lemma` environment; the `proof` environment (lines 1677–1712) carries **no** `\leanok`. That is honest per the convention (signature formalized, proof not). No violation.

### Minor observations (not defects)
- The six new proof environments carry no proof-level `\leanok`, even though their Lean proofs are complete and `sorry`-free. This under-claims (the DAG won't show them as fully proved) but is conservative/honest, not a false positive — worth adding proof `\leanok` in a later pass.
- Node 6's blueprint phrasing "the local ring S_m" is stated generically, while the Lean fixes the concrete model `Localization.AtPrime m`. Mathematically equivalent (transport via `IsRegularLocalRing.of_ringEquiv`, as the Lean docstring notes); a mild generality gap, not drift.

Relevant files:
- `/AI4M/users/Axel/LeanAlgebraicGeometry-Horizon/SubProjects/Albanese/blueprint/src/chapters/Albanese_CodimOneExtension.tex`
- `/AI4M/users/Axel/LeanAlgebraicGeometry-Horizon/SubProjects/Albanese/AlgebraicJacobian/Albanese/StandardSmoothDimension.lean`
- `/AI4M/users/Axel/LeanAlgebraicGeometry-Horizon/SubProjects/Albanese/AlgebraicJacobian/Albanese/CodimOneExtension.lean`

No inbox items filed — no actionable defects.
