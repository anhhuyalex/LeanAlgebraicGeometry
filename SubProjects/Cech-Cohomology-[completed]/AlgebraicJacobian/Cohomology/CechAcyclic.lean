/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import AlgebraicJacobian.Cohomology.CechHigherDirectImage
import AlgebraicJacobian.Cohomology.PresheafCech

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme.Modules

/-! ## Project-local Mathlib supplement — `CombinatorialCech`

The constant-coefficient combinatorial core of standard-cover Čech acyclicity
(planner step **L3**, `analogies/p3-localisation.md`).  After localising the
extended Čech complex at a spanning element `s_r` (planner step L2, via
`exact_of_isLocalized_span`), the fixed index `r` becomes globally available, and
the alternating Čech coboundary admits the explicit contracting homotopy
`h(t)_{i₀…i_p} = t_{r i₀…i_p}` of Stacks
`lemma-cech-cohomology-quasi-coherent-trivial`.

This section formalises that homotopy and its consequences for the **constant
coefficient** complex `Cᵖ = (Fin (p+1) → ι) → M` with alternating coface
differential — abstracted away from the localisation/geometry so the purely
combinatorial cancellation (`combHomotopy`) and the simplicial identity
(`combDifferential_comp`, `d² = 0`) are isolated and reusable.  The remaining
work to close `CechAcyclic.affine` is the **L1** categorical bridge identifying
the abstract `CechComplex` terms with the away-localisation modules `M_{s_σ}` and
its differential with this `combDifferential` (after localising at `s_r`); these
lemmas are then fed to `exact_of_isLocalized_span` node by node.

These declarations are `private`: they exist only to close `CechAcyclic.affine`
in this file.  The intended blueprint home is the `\lean{...}` bundle of
`lem:cech_acyclic_affine`. -/

namespace CombinatorialCech

variable {ι : Type*} {M : Type*} [AddCommGroup M] {n : ℕ}

/-- Alternating coface (Čech) differential with constant coefficients in `M`:
`Cⁿ = (Fin n → ι) → M ⟶ Cⁿ⁺¹`, `(d t)(σ) = ∑ⱼ (-1)ʲ • t (σ ∘ j.succAbove)`.
The argument `σ ∘ j.succAbove` is the `(n)`-tuple obtained from the `(n+1)`-tuple
`σ` by deleting the `j`-th index. -/
private def combDifferential (t : (Fin n → ι) → M) : (Fin (n + 1) → ι) → M :=
  fun σ => ∑ j : Fin (n + 1), (-1 : ℤ) ^ (j : ℕ) • t (σ ∘ j.succAbove)

/-- The contracting homotopy of the localised complex: prepend the fixed
(globally invertible after localising at `s_r`) index `r`.
`(h u)(τ) = u (Fin.cons r τ)`. -/
private def combHomotopy (r : ι) (u : (Fin (n + 1) → ι) → M) : (Fin n → ι) → M :=
  fun τ => u (Fin.cons r τ)

@[simp] private lemma combHomotopy_zero (r : ι) :
    combHomotopy (M := M) (n := n) r 0 = 0 := by
  funext τ; simp [combHomotopy]

/-- Composing `Fin.cons r` with the `(j+1)`-th coface map is `Fin.cons r` of the
`j`-th coface map: the bookkeeping identity behind the homotopy computation. -/
lemma cons_comp_succAbove_succ (r : ι) (σ : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons r σ : Fin (n + 2) → ι) ∘ (k.succ).succAbove
      = Fin.cons r (σ ∘ k.succAbove) := by
  funext l
  refine Fin.cases ?_ ?_ l
  · simp
  · intro i; simp [Fin.succ_succAbove_succ]

/-- **Contracting-homotopy identity** (planner L3; Stacks
`lemma-cech-cohomology-quasi-coherent-trivial`):
`d ∘ h + h ∘ d = id` on `Cⁿ⁺¹`.  This is the alternating-sum cancellation: the
`j = 0` term of `h (d t)` is `t`, and the remaining terms cancel against `d (h t)`
in pairs of opposite sign. -/
private lemma combHomotopy_spec (r : ι) (t : (Fin (n + 1) → ι) → M) :
    combDifferential (combHomotopy r t) + combHomotopy r (combDifferential t) = t := by
  funext σ
  simp only [combDifferential, combHomotopy, Pi.add_apply]
  rw [Fin.sum_univ_succ (f := fun j : Fin (n + 2) =>
    (-1 : ℤ) ^ (j : ℕ) • t ((Fin.cons r σ : Fin (n + 2) → ι) ∘ j.succAbove))]
  have h0 : (Fin.cons r σ : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = σ := by
    funext i; simp
  rw [h0]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  rw [add_left_comm, ← Finset.sum_add_distrib]
  rw [Finset.sum_eq_zero (fun x _ => by
    rw [cons_comp_succAbove_succ, pow_succ, mul_comm, neg_one_mul, neg_smul]; abel), add_zero]

/-- Every cocycle is a coboundary in positive degree: if `d t = 0` then
`t = d (h t)`.  This is the homological content of `combHomotopy_spec` and is the
half (`ker d ⊆ im d`) carrying the geometric input. -/
private lemma combDifferential_eq_of_cocycle (r : ι) (t : (Fin (n + 1) → ι) → M)
    (ht : combDifferential t = 0) : combDifferential (combHomotopy r t) = t := by
  have h := combHomotopy_spec r t
  rw [ht, combHomotopy_zero, add_zero] at h
  exact h

/-- Sign-cancellation behind `d² = 0`: under the index swap
`(j, i) ↦ (j.succAbove i, i.predAbove j)` the alternating sign flips. -/
private lemma combSign_flip (j : Fin (n + 2)) (i : Fin (n + 1)) :
    ((-1 : ℤ) ^ (j : ℕ)) * ((-1) ^ (i : ℕ))
      = - (((-1 : ℤ) ^ ((j.succAbove i : Fin (n + 2)) : ℕ))
            * ((-1) ^ ((i.predAbove j : Fin (n + 1)) : ℕ))) := by
  rcases lt_or_ge (i.castSucc) j with h | h
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.predAbove_of_castSucc_lt _ _ h,
        Fin.val_castSucc, Fin.val_pred]
    have hpos : 0 < (j : ℕ) := lt_of_le_of_lt (Nat.zero_le _) (by exact_mod_cast h)
    obtain ⟨m, hm⟩ : ∃ m, (j : ℕ) = m + 1 := ⟨(j : ℕ) - 1, by omega⟩
    rw [hm]; simp only [Nat.add_sub_cancel, pow_succ]; ring
  · rw [Fin.succAbove_of_le_castSucc _ _ h, Fin.predAbove_of_le_castSucc _ _ h,
        Fin.val_succ, Fin.coe_castPred]
    rw [pow_succ]; ring

/-- **`d² = 0`** for the constant-coefficient alternating Čech complex.  Proved by
the standard sign-reversing involution `(j, i) ↦ (j.succAbove i, i.predAbove j)` on
the double sum: the swap fixes the underlying composite coface
(`Fin.succAbove_succAbove_succAbove_predAbove`), is an involution
(`Fin.succAbove_succAbove_predAbove`, `Fin.predAbove_predAbove_succAbove`), has no
fixed point (`Fin.succAbove_ne`), and flips the sign (`combSign_flip`). -/
private lemma combDifferential_comp (t : (Fin n → ι) → M) :
    combDifferential (combDifferential t) = 0 := by
  funext σ
  simp only [combDifferential, Pi.zero_apply, Finset.smul_sum, smul_smul]
  rw [← Fintype.sum_prod_type (f := fun p : Fin (n + 2) × Fin (n + 1) =>
    ((-1 : ℤ) ^ (p.1 : ℕ) * (-1) ^ (p.2 : ℕ)) • t ((σ ∘ p.1.succAbove) ∘ p.2.succAbove))]
  apply Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1))
  · rintro ⟨j, i⟩ _
    have harg : (σ ∘ (j.succAbove i).succAbove) ∘ (i.predAbove j).succAbove
        = (σ ∘ j.succAbove) ∘ i.succAbove := by
      funext k
      simp only [Function.comp_apply]
      rw [Fin.succAbove_succAbove_succAbove_predAbove]
    simp only [harg]
    rw [← add_smul, combSign_flip j i]
    simp
  · rintro ⟨j, i⟩ _ _
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro hj
    exact absurd hj (Fin.succAbove_ne j i)
  · rintro ⟨j, i⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨Fin.succAbove_succAbove_predAbove j i, Fin.predAbove_predAbove_succAbove j i⟩
  · intro a _; exact Finset.mem_univ _

/-- **Positive-degree exactness** of the constant-coefficient Čech complex in the
`Function.Exact` form that `exact_of_isLocalized_span` (planner L2) consumes node
by node.  Combines `combDifferential_comp` (`im ⊆ ker`) with
`combDifferential_eq_of_cocycle` (`ker ⊆ im`, the homotopy half).  Requires a
distinguished index `r : ι` — supplied, after localising at `s_r`, by the
spanning element itself. -/
private lemma combDifferential_exact (r : ι) (n : ℕ) :
    Function.Exact (combDifferential : ((Fin (n + 1) → ι) → M) → ((Fin (n + 2) → ι) → M))
      (combDifferential : ((Fin (n + 2) → ι) → M) → ((Fin (n + 3) → ι) → M)) := by
  intro x
  constructor
  · intro hx
    exact ⟨combHomotopy r x, combDifferential_eq_of_cocycle r x hx⟩
  · rintro ⟨y, rfl⟩
    exact combDifferential_comp y

/-! ### Dependent-coefficient port (planner **L3 port**)

The localised complex that `exact_of_isLocalized_span` (planner **L2**) consumes
node-by-node has *varying* coefficients `M_{s_σ}` — the away localisation of `M`
at the product `s_σ = ∏ₖ s_{σ k}` — not a single constant module `M`.  After
localising the whole extended complex at a spanning element `s_r`, the index `r`
is globally available and `s_r` becomes a unit, so the prepend
`σ ↦ Fin.cons r σ` is an *isomorphism* on the coefficients:
`M_{s_{cons r σ}} = M_{s_r · s_σ} ≅ M_{s_σ}` because `s_r` is already invertible.

This section ports the constant-coefficient cancellation
(`combHomotopy_spec`, `combDifferential_eq_of_cocycle`) to that dependent
setting.  The away-localisation restriction maps are abstracted as additive
coface maps `δ` (`M_{s_{σ∘dⱼ}} → M_{s_σ}`, well defined because `s_σ` carries the
extra factor `s_{σ j}`) and the prepend isomorphisms as additive maps `c`
(`M_{s_{cons r σ}} → M_{s_σ}`).  The two compatibility identities below are
exactly the ones the away-localisation maps satisfy:

* the **unit** identity `c ∘ δ₀ = id` (deleting the prepended `r` from `cons r σ`
  recovers `σ`; on localisations the composite restriction is the identity since
  `s_r` is a unit), and
* the **shift** identity `c ∘ δ_{k+1} = δ_k ∘ c` (prepend commutes with the later
  cofaces), which is `cons_comp_succAbove_succ` lifted to the localisation maps.

Threading the dependent family through the same alternating-sum cancellation as
the constant case then yields the dependent homotopy identity and the
cocycle⟹coboundary corollary that L2 consumes.  Constructing the actual `δ`/`c`
from `IsLocalizedModule.Away` (Mathlib `tilde` API:
`AlgebraicGeometry.Modules.Tilde`, `IsLocalizedModule (.powers f)`) and the L1
identification of the abstract `CechComplex` terms with `∏_σ M_{s_σ}` remain the
outstanding bridge (see `CechAcyclic.affine`). -/

section Dependent

variable {A : (m : ℕ) → (Fin m → ι) → Type*} [∀ m σ, AddCommGroup (A m σ)]
variable (r : ι)
variable (δ : (m : ℕ) → (σ : Fin (m + 1) → ι) → (j : Fin (m + 1)) →
    A m (σ ∘ j.succAbove) →+ A (m + 1) σ)
variable (c : (m : ℕ) → (σ : Fin m → ι) → A (m + 1) (Fin.cons r σ) →+ A m σ)

omit [∀ m σ, AddCommGroup (A m σ)] in
/-- Transport of a dependent cochain value along an equality of index tuples.
The transport friction that the constant-coefficient proof avoided (there every
coefficient is the same `M`) is isolated here. -/
lemma depTransport {m : ℕ} {x y : Fin m → ι} (h : x = y)
    (t : ∀ σ : Fin m → ι, A m σ) : h ▸ t x = t y := by
  subst h; rfl

/-- Deleting the prepended index `r` (the `0`-th coface of `Fin.cons r σ`)
recovers `σ`. -/
lemma cons_comp_zero_succAbove {m : ℕ} (σ : Fin m → ι) :
    (Fin.cons r σ : Fin (m + 1) → ι) ∘ (0 : Fin (m + 1)).succAbove = σ := by
  funext i; simp

/-- Dependent (varying-coefficient) alternating Čech differential built from the
coface (localisation restriction) maps `δ`. -/
def depDiff {m : ℕ} (t : ∀ σ : Fin m → ι, A m σ) :
    ∀ σ : Fin (m + 1) → ι, A (m + 1) σ :=
  fun σ => ∑ j : Fin (m + 1), (-1 : ℤ) ^ (j : ℕ) • δ m σ j (t (σ ∘ j.succAbove))

/-- Dependent contracting homotopy: prepend the distinguished index `r`, then
apply the prepend map `c`. -/
def depHomotopy {m : ℕ} (u : ∀ σ : Fin (m + 1) → ι, A (m + 1) σ) :
    ∀ σ : Fin m → ι, A m σ :=
  fun σ => c m σ (u (Fin.cons r σ))

/-- **Dependent contracting-homotopy identity** (planner L3 port): `d ∘ h + h ∘ d
= id`, evaluated at a tuple `σ`.  Same alternating-sum cancellation as
`combHomotopy_spec`, threaded through the varying coefficients via the unit
identity `hu` (`c ∘ δ₀ = id`) and the shift identity `hsh`
(`c ∘ δ_{k+1} = δ_k ∘ c`). -/
lemma depHomotopy_spec
    (hu : ∀ {m : ℕ} (σ : Fin (m + 1) → ι)
        (y : A (m + 1)
          ((Fin.cons r σ : Fin (m + 2) → ι) ∘ (0 : Fin (m + 2)).succAbove)),
        c (m + 1) σ (δ (m + 1) (Fin.cons r σ) 0 y)
          = (cons_comp_zero_succAbove r σ) ▸ y)
    (hsh : ∀ {m : ℕ} (σ : Fin (m + 1) → ι) (k : Fin (m + 1))
        (y : A (m + 1)
          ((Fin.cons r σ : Fin (m + 2) → ι) ∘ (k.succ).succAbove)),
        c (m + 1) σ (δ (m + 1) (Fin.cons r σ) (k.succ) y)
          = δ m σ k (c m (σ ∘ k.succAbove) ((cons_comp_succAbove_succ r σ k) ▸ y)))
    {m : ℕ} (t : ∀ σ : Fin (m + 1) → ι, A (m + 1) σ) (σ : Fin (m + 1) → ι) :
    depDiff δ (depHomotopy r c t) σ + depHomotopy r c (depDiff δ t) σ = t σ := by
  simp only [depDiff, depHomotopy]
  rw [map_sum]
  simp only [map_zsmul]
  rw [Fin.sum_univ_succ (f := fun k : Fin (m + 2) =>
    (-1 : ℤ) ^ (k : ℕ) • c (m + 1) σ
      (δ (m + 1) (Fin.cons r σ) k (t ((Fin.cons r σ : Fin (m + 2) → ι) ∘ k.succAbove))))]
  -- the `k = 0` term collapses to `t σ` via the unit identity
  rw [hu σ (t _)]
  rw [depTransport (cons_comp_zero_succAbove r σ) t]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_succ]
  -- the `k = j.succ` terms cancel against the `d ∘ h` sum in pairs of opposite sign
  rw [add_left_comm, ← Finset.sum_add_distrib]
  rw [Finset.sum_eq_zero (fun x _ => by
    rw [hsh σ x (t _), depTransport (cons_comp_succAbove_succ r σ x) t,
      pow_succ, mul_comm, neg_one_mul, neg_smul]
    abel), add_zero]

/-- Dependent cocycle⟹coboundary (the geometric half consumed by L2): if
`depDiff t = 0` then `t = depDiff (depHomotopy t)`. -/
lemma depDiff_eq_of_cocycle
    (hu : ∀ {m : ℕ} (σ : Fin (m + 1) → ι)
        (y : A (m + 1)
          ((Fin.cons r σ : Fin (m + 2) → ι) ∘ (0 : Fin (m + 2)).succAbove)),
        c (m + 1) σ (δ (m + 1) (Fin.cons r σ) 0 y)
          = (cons_comp_zero_succAbove r σ) ▸ y)
    (hsh : ∀ {m : ℕ} (σ : Fin (m + 1) → ι) (k : Fin (m + 1))
        (y : A (m + 1)
          ((Fin.cons r σ : Fin (m + 2) → ι) ∘ (k.succ).succAbove)),
        c (m + 1) σ (δ (m + 1) (Fin.cons r σ) (k.succ) y)
          = δ m σ k (c m (σ ∘ k.succAbove) ((cons_comp_succAbove_succ r σ k) ▸ y)))
    {m : ℕ} (t : ∀ σ : Fin (m + 1) → ι, A (m + 1) σ)
    (ht : depDiff δ t = 0) (σ : Fin (m + 1) → ι) :
    depDiff δ (depHomotopy r c t) σ = t σ := by
  have h := depHomotopy_spec r δ c hu hsh t σ
  rw [show depHomotopy r c (depDiff δ t) σ = 0 by rw [ht]; simp [depHomotopy], add_zero] at h
  exact h

omit [∀ m σ, AddCommGroup (A m σ)] in
/-- The composite coface tuple is symmetric under the `d²=0` index swap
`(j, i) ↦ (j.succAbove i, i.predAbove j)` (dependent analogue of the `harg` step
inside `combDifferential_comp`). -/
lemma comp_succAbove_swap {m : ℕ} (σ : Fin (m + 2) → ι)
    (j : Fin (m + 2)) (i : Fin (m + 1)) :
    (σ ∘ (j.succAbove i).succAbove) ∘ (i.predAbove j).succAbove
      = (σ ∘ j.succAbove) ∘ i.succAbove := by
  funext k
  simp only [Function.comp_apply]
  rw [Fin.succAbove_succAbove_succAbove_predAbove]

/-- **Dependent `d² = 0`** for the varying-coefficient alternating Čech complex.
Same sign-reversing involution `(j, i) ↦ (j.succAbove i, i.predAbove j)` as
`combDifferential_comp`, with the coefficient transport handled by
`comp_succAbove_swap` and the coface-commutation hypothesis `hcomm` (the two
restriction maps into `M_{s_σ}` agree — a formal property of localisation maps,
independent of the choice of `r`). -/
lemma depDiff_comp
    (hcomm : ∀ {m : ℕ} (σ : Fin (m + 2) → ι) (j : Fin (m + 2)) (i : Fin (m + 1))
        (z : A m ((σ ∘ j.succAbove) ∘ i.succAbove)),
        δ (m + 1) σ j (δ m (σ ∘ j.succAbove) i z)
          = δ (m + 1) σ (j.succAbove i)
              (δ m (σ ∘ (j.succAbove i).succAbove) (i.predAbove j)
                ((comp_succAbove_swap σ j i).symm ▸ z)))
    {m : ℕ} (t : ∀ σ : Fin m → ι, A m σ) :
    depDiff δ (depDiff δ t) = 0 := by
  funext σ
  simp only [depDiff, Pi.zero_apply, map_sum, map_zsmul, Finset.smul_sum, smul_smul]
  rw [← Fintype.sum_prod_type (f := fun p : Fin (m + 2) × Fin (m + 1) =>
    ((-1 : ℤ) ^ (p.1 : ℕ) * (-1) ^ (p.2 : ℕ)) •
      δ (m + 1) σ p.1 (δ m (σ ∘ p.1.succAbove) p.2 (t ((σ ∘ p.1.succAbove) ∘ p.2.succAbove))))]
  apply Finset.sum_involution (fun p _ => (p.1.succAbove p.2, p.2.predAbove p.1))
  · rintro ⟨j, i⟩ _
    simp only []
    rw [hcomm σ j i (t _), depTransport (comp_succAbove_swap σ j i).symm t,
      ← add_smul, combSign_flip j i]
    simp
  · rintro ⟨j, i⟩ _ _
    simp only [ne_eq, Prod.mk.injEq, not_and]
    intro hj
    exact absurd hj (Fin.succAbove_ne j i)
  · rintro ⟨j, i⟩ _
    simp only [Prod.mk.injEq]
    exact ⟨Fin.succAbove_succAbove_predAbove j i, Fin.predAbove_predAbove_succAbove j i⟩
  · intro a _; exact Finset.mem_univ _

/-- **Dependent positive-degree exactness** in the `Function.Exact` form that
`exact_of_isLocalized_span` (planner **L2**) consumes after localising at a
spanning element `s_r`.  Combines `depDiff_comp` (`im ⊆ ker`) with
`depDiff_eq_of_cocycle` (`ker ⊆ im`, the homotopy half carrying the
`s_r`-invertibility input).  This is the dependent-coefficient analogue of
`combDifferential_exact`. -/
lemma depDiff_exact
    (hu : ∀ {m : ℕ} (σ : Fin (m + 1) → ι)
        (y : A (m + 1)
          ((Fin.cons r σ : Fin (m + 2) → ι) ∘ (0 : Fin (m + 2)).succAbove)),
        c (m + 1) σ (δ (m + 1) (Fin.cons r σ) 0 y)
          = (cons_comp_zero_succAbove r σ) ▸ y)
    (hsh : ∀ {m : ℕ} (σ : Fin (m + 1) → ι) (k : Fin (m + 1))
        (y : A (m + 1)
          ((Fin.cons r σ : Fin (m + 2) → ι) ∘ (k.succ).succAbove)),
        c (m + 1) σ (δ (m + 1) (Fin.cons r σ) (k.succ) y)
          = δ m σ k (c m (σ ∘ k.succAbove) ((cons_comp_succAbove_succ r σ k) ▸ y)))
    (hcomm : ∀ {m : ℕ} (σ : Fin (m + 2) → ι) (j : Fin (m + 2)) (i : Fin (m + 1))
        (z : A m ((σ ∘ j.succAbove) ∘ i.succAbove)),
        δ (m + 1) σ j (δ m (σ ∘ j.succAbove) i z)
          = δ (m + 1) σ (j.succAbove i)
              (δ m (σ ∘ (j.succAbove i).succAbove) (i.predAbove j)
                ((comp_succAbove_swap σ j i).symm ▸ z)))
    (m : ℕ) :
    Function.Exact (depDiff δ (m := m + 1)) (depDiff δ (m := m + 2)) := by
  intro x
  constructor
  · intro hx
    exact ⟨depHomotopy r c x,
      funext fun σ => depDiff_eq_of_cocycle r δ c hu hsh x hx σ⟩
  · rintro ⟨y, rfl⟩
    exact depDiff_comp δ hcomm y

end Dependent

end CombinatorialCech

/-! ## Project-local Mathlib supplement — away-localisation comparison maps

The concrete `δ` (coface) and `c` (prepend) maps that the dependent combinatorial
core `CombinatorialCech.Dependent.depDiff_exact` consumes are, for the standard
affine cover, the canonical comparison maps between away-localisations
`M_a → M_b` available whenever `a ∣ b` — so that `a`, a divisor of the invertible
`b`, is itself invertible in `M_b`.  This section builds that comparison map and
its functoriality from `IsLocalizedModule` abstractly, independent of the sheaf
identification (L1), so it can be assembled into the localised {\v C}ech complex.

Everything here is `R`-module algebra; no sheaf theory enters. The maps are
characterised by uniqueness of localisation lifts (`IsLocalizedModule.lift_unique`),
which is what makes the composition/identity laws — the algebraic heart of the
`hu`/`hsh`/`hcomm` compatibilities — provable. -/

namespace AwayComparison

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- The clean hypothesis under which a canonical comparison `M_a → Mb` exists: the
element `a` acts invertibly on the target localisation `Mb`. Because the scalar
action is `algebraMap` into the (central) endomorphism ring, this is closed under
multiplication and holds for any divisor of an already-invertible element — exactly
the two ways `δ` (divisibility) and `c` (a product of invertible factors) arise. -/
def Inverts (a : R) (Mb : Type u) [AddCommGroup Mb] [Module R Mb] : Prop :=
  IsUnit (algebraMap R (Module.End R Mb) a)

/-- A divisor `a` of `b` acts invertibly on any localisation `M_b` of `M` away
from `b`: since `b` is a unit there and `b = a · c` with the scalar actions
commuting (both lie in the image of the central `algebraMap`), `a` is a unit too. -/
lemma Inverts.of_dvd {a b : R} (hab : a ∣ b)
    {Mb : Type u} [AddCommGroup Mb] [Module R Mb] (fb : M →ₗ[R] Mb)
    [IsLocalizedModule (Submonoid.powers b) fb] :
    Inverts a Mb := by
  obtain ⟨c, rfl⟩ := hab
  have hb : IsUnit (algebraMap R (Module.End R Mb) (a * c)) :=
    IsLocalizedModule.map_units fb ⟨a * c, Submonoid.mem_powers _⟩
  rw [map_mul] at hb
  have hcomm : Commute (algebraMap R (Module.End R Mb) a) (algebraMap R (Module.End R Mb) c) :=
    (Commute.all a c).map _
  exact (hcomm.isUnit_mul_iff.mp hb).1

/-- `Inverts` is closed under multiplication: a product of invertibly-acting
elements acts invertibly. This supplies the `c` (prepend) comparison, whose source
localising element `s_r · s_{cons r σ}` factors into divisors of the target. -/
lemma Inverts.mul {a a' : R} {Mb : Type u} [AddCommGroup Mb] [Module R Mb]
    (ha : Inverts a Mb) (ha' : Inverts a' Mb) : Inverts (a * a') Mb := by
  rw [Inverts, map_mul]
  exact IsUnit.mul ha ha'

/-- The power version of the `Inverts` hypothesis, as the `IsLocalizedModule.lift`
universal property consumes it (`∀ x ∈ powers a`). -/
lemma Inverts.isUnit_powers {a : R} {Mb : Type u} [AddCommGroup Mb] [Module R Mb]
    (ha : Inverts a Mb) (x : Submonoid.powers a) :
    IsUnit (algebraMap R (Module.End R Mb) (x : R)) := by
  obtain ⟨n, hn⟩ := x.2
  rw [← hn, map_pow]
  exact ha.pow n

/-- The canonical comparison map `M_a → Mb` between localisations of `M`, defined
whenever `a` acts invertibly on `Mb` (`Inverts a Mb`). It is the unique `R`-linear
map `M_a → Mb` commuting with the localisation structure maps (`comparison_unique`);
this universal characterisation is what makes the functoriality laws below provable. -/
noncomputable def comparison {a : R}
    {Ma Mb : Type u} [AddCommGroup Ma] [Module R Ma] [AddCommGroup Mb] [Module R Mb]
    (fa : M →ₗ[R] Ma) [IsLocalizedModule (Submonoid.powers a) fa]
    (fb : M →ₗ[R] Mb) (hb : Inverts a Mb) :
    Ma →ₗ[R] Mb :=
  IsLocalizedModule.lift (Submonoid.powers a) fa fb hb.isUnit_powers

@[simp] lemma comparison_apply {a : R}
    {Ma Mb : Type u} [AddCommGroup Ma] [Module R Ma] [AddCommGroup Mb] [Module R Mb]
    (fa : M →ₗ[R] Ma) [IsLocalizedModule (Submonoid.powers a) fa]
    (fb : M →ₗ[R] Mb) (hb : Inverts a Mb) (x : M) :
    comparison fa fb hb (fa x) = fb x :=
  IsLocalizedModule.lift_apply _ _ _ _ x

lemma comparison_comp_structure {a : R}
    {Ma Mb : Type u} [AddCommGroup Ma] [Module R Ma] [AddCommGroup Mb] [Module R Mb]
    (fa : M →ₗ[R] Ma) [IsLocalizedModule (Submonoid.powers a) fa]
    (fb : M →ₗ[R] Mb) (hb : Inverts a Mb) :
    comparison fa fb hb ∘ₗ fa = fb :=
  IsLocalizedModule.lift_comp _ _ _ _

/-- Uniqueness: any `R`-linear `l : M_a → Mb` commuting with the structure maps
equals the comparison map. -/
lemma comparison_unique {a : R}
    {Ma Mb : Type u} [AddCommGroup Ma] [Module R Ma] [AddCommGroup Mb] [Module R Mb]
    (fa : M →ₗ[R] Ma) [IsLocalizedModule (Submonoid.powers a) fa]
    (fb : M →ₗ[R] Mb) (hb : Inverts a Mb)
    (l : Ma →ₗ[R] Mb) (hl : l ∘ₗ fa = fb) :
    comparison fa fb hb = l :=
  IsLocalizedModule.lift_unique _ _ _ _ l hl

/-- **Identity law.** The comparison of a localisation with itself is the identity. -/
@[simp] lemma comparison_self {a : R}
    {Ma : Type u} [AddCommGroup Ma] [Module R Ma]
    (fa : M →ₗ[R] Ma) [IsLocalizedModule (Submonoid.powers a) fa] (ha : Inverts a Ma) :
    comparison fa fa ha = LinearMap.id :=
  comparison_unique _ _ _ _ (by ext x; simp)

/-- **Composition law** (functoriality): comparison maps compose.  Proved by
uniqueness — both sides become `fc` after precomposing with the structure map `fa`.
This is the reusable algebraic core underlying the `hsh`/`hcomm` compatibilities of
the dependent {\v C}ech port. -/
lemma comparison_comp {a b : R}
    {Ma Mb Mc : Type u} [AddCommGroup Ma] [Module R Ma] [AddCommGroup Mb] [Module R Mb]
    [AddCommGroup Mc] [Module R Mc]
    (fa : M →ₗ[R] Ma) [IsLocalizedModule (Submonoid.powers a) fa]
    (fb : M →ₗ[R] Mb) [IsLocalizedModule (Submonoid.powers b) fb]
    (fc : M →ₗ[R] Mc)
    (hb : Inverts a Mb) (hc : Inverts b Mc) (hac : Inverts a Mc) :
    (comparison fb fc hc) ∘ₗ (comparison fa fb hb) = comparison fa fc hac :=
  (comparison_unique fa fc hac _ (by
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, comparison_apply])).symm

/-- Pointwise form of the composition law. -/
lemma comparison_comp_apply {a b : R}
    {Ma Mb Mc : Type u} [AddCommGroup Ma] [Module R Ma] [AddCommGroup Mb] [Module R Mb]
    [AddCommGroup Mc] [Module R Mc]
    (fa : M →ₗ[R] Ma) [IsLocalizedModule (Submonoid.powers a) fa]
    (fb : M →ₗ[R] Mb) [IsLocalizedModule (Submonoid.powers b) fb]
    (fc : M →ₗ[R] Mc)
    (hb : Inverts a Mb) (hc : Inverts b Mc) (hac : Inverts a Mc) (x : Ma) :
    comparison fb fc hc (comparison fa fb hb x) = comparison fa fc hac x :=
  LinearMap.congr_fun (comparison_comp fa fb fc hb hc hac) x

/-- A power of an invertibly-acting element acts injectively on a localisation:
the scalar-cancellation device behind localisation transitivity. -/
lemma Inverts.smul_pow_cancel {a : R} {N : Type u} [AddCommGroup N] [Module R N]
    (ha : Inverts a N) (n : ℕ) {p q : N} (h : a ^ n • p = a ^ n • q) : p = q := by
  have hu : IsUnit (algebraMap R (Module.End R N) (a ^ n)) := by
    rw [map_pow]; exact ha.pow n
  apply ((Module.End.isUnit_iff _).mp hu).injective
  simpa only [Module.algebraMap_end_eq_smul_id, LinearMap.smul_apply, LinearMap.id_coe,
    id_eq] using h

/-- **Localisation transitivity for the away comparison.** If `Ma` localises `M`
away from `a` and `Mb` away from `a * b`, the comparison map `Ma → Mb` exhibits
`Mb` as the localisation of `Ma` away from `b` — the "localisation of a
localisation" identity `M_a[1/b] = M_{ab}`.  This is the keystone that feeds the
per-spanning-element reduction `exact_of_isLocalized_span` of the section Čech
complex: localising the un-localised coefficient `M_{s_σ}` at a spanning element
`s_r` yields the doubly-localised coefficient `M_{s_r · s_σ}` of `cechCoeff`. -/
lemma comparison_isLocalizedModule {a b : R}
    {Ma Mb : Type u} [AddCommGroup Ma] [Module R Ma] [AddCommGroup Mb] [Module R Mb]
    (fa : M →ₗ[R] Ma) [IsLocalizedModule (Submonoid.powers a) fa]
    (fb : M →ₗ[R] Mb) [IsLocalizedModule (Submonoid.powers (a * b)) fb]
    (hb : Inverts a Mb) :
    IsLocalizedModule (Submonoid.powers b) (comparison fa fb hb) := by
  have hbB : Inverts b Mb := Inverts.of_dvd ⟨a, by rw [mul_comm]⟩ fb
  have haA : Inverts a Ma := Inverts.of_dvd dvd_rfl fa
  refine ⟨fun x => hbB.isUnit_powers x, ?_, ?_⟩
  · -- surjectivity
    intro y
    obtain ⟨⟨m, u⟩, hu⟩ := IsLocalizedModule.surj (Submonoid.powers (a * b)) fb y
    obtain ⟨n, hn⟩ := u.2
    have hnR : (a * b) ^ n = (u : R) := hn
    refine ⟨⟨IsLocalizedModule.mk' fa m (⟨a ^ n, n, rfl⟩ : Submonoid.powers a),
      (⟨b ^ n, n, rfl⟩ : Submonoid.powers b)⟩, ?_⟩
    apply hb.smul_pow_cancel n
    -- RHS: a^n • comparison (mk' fa m ⟨a^n⟩) = fb m
    have hz : (a ^ n : R) • IsLocalizedModule.mk' fa m (⟨a ^ n, n, rfl⟩ : Submonoid.powers a)
        = fa m := by
      have h := IsLocalizedModule.mk'_cancel' fa m (⟨a ^ n, n, rfl⟩ : Submonoid.powers a)
      rwa [Submonoid.smul_def] at h
    rw [Submonoid.smul_def, ← _root_.map_smul, hz, comparison_apply]
    -- LHS: a^n • (b^n • y) = fb m
    rw [smul_smul, ← mul_pow, hnR, ← Submonoid.smul_def]
    exact hu
  · -- exists_of_eq
    intro x₁ x₂ e
    set w := x₁ - x₂ with hw
    have hcw : comparison fa fb hb w = 0 := by rw [hw, map_sub, e, sub_self]
    obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers a) fa w
    obtain ⟨k, hk⟩ := s.2
    have hsw : a ^ k • w = fa m := by
      rw [Submonoid.smul_def] at hs
      rwa [show (s : R) = a ^ k from hk.symm] at hs
    have hfbm : fb m = 0 := by
      have h1 : comparison fa fb hb (fa m) = 0 := by
        rw [← hsw, _root_.map_smul, hcw, smul_zero]
      rwa [comparison_apply] at h1
    have hmz : fb m = fb 0 := by rw [hfbm, map_zero]
    obtain ⟨d, hd⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (a * b)) fb).mp hmz
    obtain ⟨j, hj⟩ := d.2
    have hdm : (a * b) ^ j • m = 0 := by
      rw [smul_zero] at hd
      rw [Submonoid.smul_def] at hd
      rwa [show (d : R) = (a * b) ^ j from hj.symm] at hd
    -- a^{j+k} • (b^j • w) = 0
    have key : (a * b) ^ j • (a ^ k • w) = (0 : Ma) := by
      rw [hsw, ← _root_.map_smul, hdm, map_zero]
    have hzero : a ^ (j + k) • (b ^ j • w) = (0 : Ma) := by
      rw [smul_smul] at key
      rw [smul_smul, show a ^ (j + k) * b ^ j = (a * b) ^ j * a ^ k by
        rw [mul_pow, pow_add]; ring]
      exact key
    have hbw : b ^ j • w = 0 :=
      haA.smul_pow_cancel (j + k) (hzero.trans (smul_zero _).symm)
    refine ⟨(⟨b ^ j, j, rfl⟩ : Submonoid.powers b), ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def]
    rw [hw, smul_sub, sub_eq_zero] at hbw
    exact hbw

end AwayComparison

/-! ## Project-local Mathlib supplement — multi-index localising elements

The localising element attached to a {\v C}ech multi-index `σ : Fin m → ι` is the
product `s_σ = ∏ₖ s (σ k)`.  The two divisibility facts below are exactly the
hypotheses the away-comparison maps of `AwayComparison` need to become the
coface `δ` and prepend `c` maps of the dependent combinatorial core: a coface
deletes an index (so `s_{σ∘dⱼ} ∣ s_σ`), and the prepend multiplies by `s r`. -/

namespace CechLocalized

variable {R : Type u} [CommRing R] {ι : Type*} (s : ι → R)

/-- `s_σ = ∏ₖ s (σ k)`, the localising element for the multi-index `σ`. -/
def sprod {m : ℕ} (σ : Fin m → ι) : R := ∏ k, s (σ k)

@[simp] lemma sprod_cons {m : ℕ} (i : ι) (σ : Fin m → ι) :
    sprod s (Fin.cons i σ) = s i * sprod s σ := by
  simp [sprod, Fin.prod_univ_succ]

/-- A coface (index deletion) only drops the factor `s (σ j)`, so the smaller
product divides the larger: `s_{σ∘dⱼ} ∣ s_σ`.  This supplies the `Inverts`
hypothesis for the coface comparison `δ`. -/
lemma sprod_succAbove_dvd {m : ℕ} (σ : Fin (m + 1) → ι) (j : Fin (m + 1)) :
    sprod s (σ ∘ j.succAbove) ∣ sprod s σ := by
  have h : sprod s σ = s (σ j) * sprod s (σ ∘ j.succAbove) := by
    rw [sprod, sprod, Fin.prod_univ_succAbove _ j]; rfl
  exact ⟨s (σ j), by rw [h]; ring⟩

/-! ### The localised coefficient family and the concrete `δ`/`c` maps

After localising the whole section {\v C}ech complex at a spanning element `s r`,
its degree-`p` coefficient at the multi-index `σ` is `M` localised at the product
`s r · s_σ` (the away localisation at `s_σ`, further localised at `s r`).  We model
that double localisation by the single away localisation at `s r · s_σ`.  The coface
`δ` and prepend `c` maps are the away-comparison maps of `AwayComparison`; the
`Inverts` hypotheses come from `sprod_succAbove_dvd` (for `δ`) and from
`Inverts.mul` together with `sprod_cons` (for `c`). -/

variable (M : Type u) [AddCommGroup M] [Module R M] (r : ι)

/-- The localised {\v C}ech coefficient `A_σ = M_{s r · s_σ}` (after localising at the
fixed index `r`). -/
abbrev cechCoeff {m : ℕ} (σ : Fin m → ι) : Type u :=
  LocalizedModule (Submonoid.powers (s r * sprod s σ)) M

/-- The coface comparison `δ : A_{σ∘dⱼ} → A_σ`, the canonical localisation map for the
divisibility `s r · s_{σ∘dⱼ} ∣ s r · s_σ`. -/
noncomputable def cechCoface (m : ℕ) (σ : Fin (m + 1) → ι) (j : Fin (m + 1)) :
    cechCoeff s M r (σ ∘ j.succAbove) →+ cechCoeff s M r σ :=
  (AwayComparison.comparison (M := M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s (σ ∘ j.succAbove))) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M)
    (AwayComparison.Inverts.of_dvd (mul_dvd_mul_left (s r) (sprod_succAbove_dvd s σ j))
      (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M))).toAddMonoidHom

/-- The prepend comparison `c : A_{cons r σ} → A_σ`, the canonical localisation map.
Its source localises at `s r · s_{cons r σ} = s r · (s r · s_σ)`, a product whose
factors are all invertible in `A_σ`, supplied by `Inverts.mul`. -/
noncomputable def cechPrepend (m : ℕ) (σ : Fin m → ι) :
    cechCoeff s M r (Fin.cons r σ) →+ cechCoeff s M r σ :=
  (AwayComparison.comparison (M := M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s (Fin.cons r σ))) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M)
    (by
      change AwayComparison.Inverts (s r * sprod s (Fin.cons r σ))
        (LocalizedModule (Submonoid.powers (s r * sprod s σ)) M)
      have h : s r * sprod s (Fin.cons r σ) = s r * (s r * sprod s σ) := by
        rw [sprod_cons]
      rw [h]
      exact AwayComparison.Inverts.mul
        (AwayComparison.Inverts.of_dvd ⟨sprod s σ, rfl⟩
          (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M))
        (AwayComparison.Inverts.of_dvd dvd_rfl
          (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M)))).toAddMonoidHom

/-- A transport of a {\v C}ech coefficient along an equality of multi-index tuples
`τ₁ = τ₂` is the canonical comparison map (both localise `M` at the *same* element
`s r · s_τ`, since `s_τ` depends only on the function `τ`). This is the bridge
between the dependent-type transports `▸` of the combinatorial core and the
away-comparison maps. -/
lemma cechCoeff_transport_eq_comparison {m : ℕ} {τ₁ τ₂ : Fin m → ι} (hτ : τ₁ = τ₂)
    (hinv : AwayComparison.Inverts (s r * sprod s τ₁) (cechCoeff s M r τ₂))
    (y : cechCoeff s M r τ₁) :
    hτ ▸ y = AwayComparison.comparison
      (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s τ₁)) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s τ₂)) M) hinv y := by
  subst hτ
  rw [AwayComparison.comparison_self]
  rfl

/-- **Unit compatibility** `hu` for the concrete localised {\v C}ech maps:
`c ∘ δ₀ = transport`.  Deleting the prepended `r` (the `0`-th coface) and then
applying the prepend `c` is, on the away localisations, the identity transport,
because all three maps are away-comparison maps and compose by `comparison_comp`. -/
lemma cech_hu {m : ℕ} (σ : Fin (m + 1) → ι)
    (y : cechCoeff s M r ((Fin.cons r σ : Fin (m + 2) → ι) ∘ (0 : Fin (m + 2)).succAbove)) :
    cechPrepend s M r (m + 1) σ (cechCoface s M r (m + 1) (Fin.cons r σ) 0 y)
      = (CombinatorialCech.cons_comp_zero_succAbove r σ) ▸ y := by
  have heq : (Fin.cons r σ : Fin (m + 2) → ι) ∘ (0 : Fin (m + 2)).succAbove = σ :=
    CombinatorialCech.cons_comp_zero_succAbove r σ
  have hinv : AwayComparison.Inverts
      (s r * sprod s ((Fin.cons r σ : Fin (m + 2) → ι) ∘ (0 : Fin (m + 2)).succAbove))
      (cechCoeff s M r σ) :=
    AwayComparison.Inverts.of_dvd (dvd_of_eq (by rw [heq])) (LocalizedModule.mkLinearMap _ M)
  simp only [cechPrepend, cechCoface, LinearMap.toAddMonoidHom_coe]
  change _ = heq ▸ y
  rw [cechCoeff_transport_eq_comparison s M r heq hinv,
    AwayComparison.comparison_comp_apply]

/-- **Shift compatibility** `hsh` for the concrete localised {\v C}ech maps:
`c ∘ δ_{k+1} = δ_k ∘ c` (modulo the index transport).  Both composites are
away-comparison maps from the same source localisation to the same target, hence
equal — assembled from `comparison_comp` and the transport bridge. -/
lemma cech_hsh {m : ℕ} (σ : Fin (m + 1) → ι) (k : Fin (m + 1))
    (y : cechCoeff s M r ((Fin.cons r σ : Fin (m + 2) → ι) ∘ (k.succ).succAbove)) :
    cechPrepend s M r (m + 1) σ (cechCoface s M r (m + 1) (Fin.cons r σ) k.succ y)
      = cechCoface s M r m σ k
          (cechPrepend s M r m (σ ∘ k.succAbove)
            ((CombinatorialCech.cons_comp_succAbove_succ r σ k) ▸ y)) := by
  have heq' : (Fin.cons r σ : Fin (m + 2) → ι) ∘ (k.succ).succAbove
      = Fin.cons r (σ ∘ k.succAbove) := CombinatorialCech.cons_comp_succAbove_succ r σ k
  have hinv' : AwayComparison.Inverts
      (s r * sprod s ((Fin.cons r σ : Fin (m + 2) → ι) ∘ (k.succ).succAbove))
      (cechCoeff s M r (Fin.cons r (σ ∘ k.succAbove))) :=
    AwayComparison.Inverts.of_dvd (dvd_of_eq (by rw [heq'])) (LocalizedModule.mkLinearMap _ M)
  have key : AwayComparison.Inverts (s r * sprod s (Fin.cons r (σ ∘ k.succAbove)))
      (cechCoeff s M r σ) := by
    rw [show s r * sprod s (Fin.cons r (σ ∘ k.succAbove))
          = s r * (s r * sprod s (σ ∘ k.succAbove)) from by rw [sprod_cons]]
    exact AwayComparison.Inverts.mul
      (AwayComparison.Inverts.of_dvd (dvd_mul_right (s r) (sprod s σ))
        (LocalizedModule.mkLinearMap _ M))
      (AwayComparison.Inverts.of_dvd (mul_dvd_mul_left (s r) (sprod_succAbove_dvd s σ k))
        (LocalizedModule.mkLinearMap _ M))
  simp only [cechPrepend, cechCoface, LinearMap.toAddMonoidHom_coe]
  rw [cechCoeff_transport_eq_comparison s M r heq' hinv',
    AwayComparison.comparison_comp_apply, AwayComparison.comparison_comp_apply,
    AwayComparison.comparison_comp_apply]
  · rw [heq']; exact key
  · exact key

/-- **Coface commutation** `hcomm` (the `d² = 0` swap identity) for the concrete
localised {\v C}ech maps.  Both bracketings of the double coface are away-comparison
maps from the (swap-invariant) double-deletion localisation to `A_σ`, hence equal. -/
lemma cech_hcomm {m : ℕ} (σ : Fin (m + 2) → ι) (j : Fin (m + 2)) (i : Fin (m + 1))
    (z : cechCoeff s M r ((σ ∘ j.succAbove) ∘ i.succAbove)) :
    cechCoface s M r (m + 1) σ j (cechCoface s M r m (σ ∘ j.succAbove) i z)
      = cechCoface s M r (m + 1) σ (j.succAbove i)
          (cechCoface s M r m (σ ∘ (j.succAbove i).succAbove) (i.predAbove j)
            ((CombinatorialCech.comp_succAbove_swap σ j i).symm ▸ z)) := by
  have heqc : (σ ∘ j.succAbove) ∘ i.succAbove
      = (σ ∘ (j.succAbove i).succAbove) ∘ (i.predAbove j).succAbove :=
    (CombinatorialCech.comp_succAbove_swap σ j i).symm
  have hinvc : AwayComparison.Inverts (s r * sprod s ((σ ∘ j.succAbove) ∘ i.succAbove))
      (cechCoeff s M r ((σ ∘ (j.succAbove i).succAbove) ∘ (i.predAbove j).succAbove)) :=
    AwayComparison.Inverts.of_dvd (dvd_of_eq (by rw [heqc])) (LocalizedModule.mkLinearMap _ M)
  have key : AwayComparison.Inverts (s r * sprod s ((σ ∘ j.succAbove) ∘ i.succAbove))
      (cechCoeff s M r σ) :=
    AwayComparison.Inverts.of_dvd
      (mul_dvd_mul_left (s r)
        (dvd_trans (sprod_succAbove_dvd s (σ ∘ j.succAbove) i) (sprod_succAbove_dvd s σ j)))
      (LocalizedModule.mkLinearMap _ M)
  simp only [cechCoface, LinearMap.toAddMonoidHom_coe]
  rw [cechCoeff_transport_eq_comparison s M r heqc hinvc,
    AwayComparison.comparison_comp_apply, AwayComparison.comparison_comp_apply,
    AwayComparison.comparison_comp_apply]
  · exact key
  · rw [CombinatorialCech.comp_succAbove_swap]; exact key

/-- **Positive-degree exactness of the localised section {\v C}ech complex.**
After localising the standard-cover section {\v C}ech complex at a spanning element
`s r`, the resulting complex of away-localisations `A_σ = M_{s r · s_σ}` is exact in
positive degrees.  This is the dependent combinatorial core
`CombinatorialCech.depDiff_exact` fed the concrete coface `cechCoface`, prepend
`cechPrepend`, and the compatibilities `cech_hu`/`cech_hsh`/`cech_hcomm`.  It is the
`Function.Exact` input that `exact_of_isLocalized_span` consumes node by node in the
L1 categorical→module bridge (the remaining gaps: the finite-product localisation
`∏_σ M_{s_σ}` and the sheaf-section identification `F(D(s_σ)) = M_{s_σ}`). -/
lemma cechLocalized_exact (m : ℕ) :
    Function.Exact
      (CombinatorialCech.depDiff (A := fun _ σ => cechCoeff s M r σ) (cechCoface s M r)
        (m := m + 1))
      (CombinatorialCech.depDiff (A := fun _ σ => cechCoeff s M r σ) (cechCoface s M r)
        (m := m + 2)) :=
  CombinatorialCech.depDiff_exact (A := fun _ σ => cechCoeff s M r σ) r
    (cechCoface s M r) (cechPrepend s M r)
    (cech_hu s M r) (cech_hsh s M r) (cech_hcomm s M r) m

end CechLocalized

/-! ## Project-local Mathlib supplement — composite away-localisation (route B, change-of-ring)

The route-B change-of-ring transfer (`lem:away_comparison_isLocalizedModule`, used by
`dDiff_exact_of_localizationAway`) needs the elementary fact that *localising twice*
— first `M ⇝ M_f` at `powers f`, then `M_f ⇝ N` at `powers (algebraMap R R_f a)` over the
localisation ring `R_f` — presents `N` as the single away localisation `M_a`, provided `f` is
already inverted once `a` is (`a^j = f·h`, i.e. `f ∈ √(a)`).  This is the module analogue of
`Localization.Away f` then `Localization.Away a = Localization.Away a` when `f ∣ aⁿ`. -/

namespace AwayComparison

/-- **Composite of two away localisations is an away localisation.**  See the section
docstring.  The `R`-linear composite `gN ∘ mkf : M → N` exhibits `N` as `M` localised at
`Submonoid.powers a`, given `a^j = f * h` (so `f` divides a power of `a`). -/
lemma isLocalizedModule_comp_away
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {Rf : Type u} [CommRing Rf] [Algebra R Rf]
    {Mf : Type u} [AddCommGroup Mf] [Module R Mf] [Module Rf Mf] [IsScalarTower R Rf Mf]
    {N : Type u} [AddCommGroup N] [Module R N] [Module Rf N] [IsScalarTower R Rf N]
    (f a h : R) {j : ℕ} (hfa : a ^ j = f * h)
    (mkf : M →ₗ[R] Mf) [IsLocalizedModule (Submonoid.powers f) mkf]
    (gN : Mf →ₗ[Rf] N) [IsLocalizedModule (Submonoid.powers (algebraMap R Rf a)) gN] :
    IsLocalizedModule (Submonoid.powers a) ((gN.restrictScalars R) ∘ₗ mkf) := by
  have smulN : ∀ (r : R) (y : N), r • y = (algebraMap R Rf r) • y :=
    fun r y => (IsScalarTower.algebraMap_smul Rf r y).symm
  have smulMf : ∀ (r : R) (y : Mf), r • y = (algebraMap R Rf r) • y :=
    fun r y => (IsScalarTower.algebraMap_smul Rf r y).symm
  -- `a^j = f h` lifts to `a^{j n} = f^n h^n`
  have hfa' : ∀ n : ℕ, a ^ (j * n) = f ^ n * h ^ n := fun n => by
    rw [pow_mul, hfa, mul_pow]
  refine ⟨?_, ?_, ?_⟩
  · -- map_units: `a` acts invertibly on `N` (as `algebraMap R Rf a` does)
    rintro ⟨x, n, rfl⟩
    rw [Module.End.isUnit_iff]
    have hb : Function.Bijective
        (⇑(algebraMap Rf (Module.End Rf N) ((algebraMap R Rf a) ^ n))) :=
      (Module.End.isUnit_iff _).1 (by
        rw [map_pow]
        exact (IsLocalizedModule.map_units gN
          ⟨algebraMap R Rf a, Submonoid.mem_powers _⟩).pow n)
    have hfun : ⇑(algebraMap R (Module.End R N) (a ^ n))
        = ⇑(algebraMap Rf (Module.End Rf N) ((algebraMap R Rf a) ^ n)) := by
      funext y
      simp only [Module.algebraMap_end_eq_smul_id, LinearMap.smul_apply, LinearMap.id_apply]
      rw [smulN, map_pow]
    rw [hfun]; exact hb
  · -- surjectivity
    intro y
    obtain ⟨⟨mf, u⟩, hu⟩ := IsLocalizedModule.surj (Submonoid.powers (algebraMap R Rf a)) gN y
    obtain ⟨k, hk⟩ := u.2
    obtain ⟨⟨m0, v⟩, hv⟩ := IsLocalizedModule.surj (Submonoid.powers f) mkf mf
    obtain ⟨l, hl⟩ := v.2
    simp only [] at hk hl
    rw [Submonoid.smul_def] at hu hv
    dsimp only at hu hv
    have hay : (a ^ k : R) • y = gN mf := by
      rw [smulN, map_pow, hk]; exact hu
    have hfm : (f ^ l : R) • mf = mkf m0 := by rw [hl]; exact hv
    refine ⟨⟨h ^ l • m0, ⟨a ^ (j * l + k), j * l + k, rfl⟩⟩, ?_⟩
    rw [Submonoid.smul_def]
    change (a ^ (j * l + k) : R) • y = gN (mkf (h ^ l • m0))
    have lhs : (a ^ (j * l + k) : R) • y = (f ^ l * h ^ l) • gN mf := by
      rw [pow_add, hfa' l, mul_smul, hay]
    have rhs : gN (mkf (h ^ l • m0)) = (h ^ l * f ^ l) • gN mf := by
      rw [_root_.map_smul, ← hfm, LinearMap.map_smul_of_tower,
        LinearMap.map_smul_of_tower, ← mul_smul]
    rw [lhs, rhs, mul_comm (f ^ l) (h ^ l)]
  · -- exists_of_eq
    intro x1 x2 hx
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply] at hx
    obtain ⟨u, hu⟩ := IsLocalizedModule.exists_of_eq
      (S := Submonoid.powers (algebraMap R Rf a)) (f := gN) hx
    obtain ⟨k, hk⟩ := u.2
    simp only [] at hk
    rw [Submonoid.smul_def] at hu
    have h1 : mkf ((a ^ k : R) • x1) = mkf ((a ^ k : R) • x2) := by
      rw [_root_.map_smul, _root_.map_smul]
      simp only [smulMf, map_pow, hk]
      exact hu
    obtain ⟨w, hw⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f) (f := mkf) h1
    obtain ⟨l, hl⟩ := w.2
    simp only [] at hl
    rw [Submonoid.smul_def] at hw
    have h2 : (f ^ l : R) • (a ^ k : R) • x1 = (f ^ l : R) • (a ^ k : R) • x2 := by
      rw [hl]; exact hw
    refine ⟨⟨a ^ (j * l + k), j * l + k, rfl⟩, ?_⟩
    rw [Submonoid.smul_def]
    change (a ^ (j * l + k) : R) • x1 = (a ^ (j * l + k) : R) • x2
    have hexp : a ^ (j * l + k) = h ^ l * (f ^ l * a ^ k) := by
      rw [pow_add, hfa' l]; ring
    simp only [hexp, mul_smul]
    rw [h2]

end AwayComparison

/-! ## Project-local Mathlib supplement — base-change composite localisation (route B1, change-of-ring)

The general-affine-open seed (Stacks 02KG over an arbitrary affine `V = ⨆ᵢ D(gᵢ)`, NOT a single
`D(f)`) is proved by change of base to `S = Γ(V)`, where the cover family `ḡᵢ = algebraMap R S gᵢ`
DOES span the unit ideal.  The transport back to `R` needs, per Čech multi-index `σ`, the fact that
the composite `M → M ⊗_R S → (M ⊗_R S)_{ḡσ}` (base change to `S`, then localise at `ḡσ`) presents the
localised tensor as the localisation `M_{gσ}` of `M` at `powers gσ` over `R`.  This is the algebraic
analogue of `AwayComparison.isLocalizedModule_comp_away`, but with the FIRST leg a base change
(`IsBaseChange S`) rather than a localisation: `M → M_S` is not a localisation of `M` (S is not a
localisation of `R`).  The single geometric input — that the localised ring is simultaneously an
`R`-localisation at `powers gσ` — is supplied as the instance `[IsLocalization (powers a) Aloc]`. -/

/-- **Base-change composite is a localisation.**  Let `bc : M →ₗ[R] MS` exhibit `MS` as the base
change of `M` to an `R`-algebra `S` (`IsBaseChange S bc`), and let `gN : MS →ₗ[S] N` localise `MS`
at `powers (algebraMap R S a)` over `S`, with localised ring `Aloc`.  If `Aloc` is moreover an
`R`-localisation at `powers a` (the geometric input, encoding `D(a) ⊆ Spec S` when `S = Γ(V)`), then
the `R`-linear composite `gN ∘ bc : M →ₗ[R] N` exhibits `N` as the localisation of `M` at `powers a`.

Pure base-change algebra: `IsBaseChange` is transitive (`IsBaseChange.comp`), and
`isLocalizedModule_iff_isBaseChange` converts both directions.  This is the route-B1 replacement for
`AwayComparison.isLocalizedModule_comp_away` in the general-affine `dDiff_exact_of_affineCover`. -/
theorem isLocalizedModule_baseChange_away
    {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
    {S : Type u} [CommRing S] [Algebra R S]
    {MS : Type u} [AddCommGroup MS] [Module R MS] [Module S MS] [IsScalarTower R S MS]
    (bc : M →ₗ[R] MS) (hbc : IsBaseChange S bc)
    {a : R}
    {N : Type u} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (gN : MS →ₗ[S] N)
    (Aloc : Type u) [CommRing Aloc] [Algebra S Aloc]
    [IsLocalization (Submonoid.powers (algebraMap R S a)) Aloc]
    [Module Aloc N] [IsScalarTower S Aloc N]
    [IsLocalizedModule (Submonoid.powers (algebraMap R S a)) gN]
    [Algebra R Aloc] [IsScalarTower R S Aloc] [IsScalarTower R Aloc N]
    [IsLocalization (Submonoid.powers a) Aloc] :
    IsLocalizedModule (Submonoid.powers a) ((gN.restrictScalars R) ∘ₗ bc) := by
  have hg : IsBaseChange Aloc gN :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers (algebraMap R S a)) Aloc gN).mp
      inferInstance
  exact (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) Aloc _).mpr (hbc.comp hg)

/-! ## Project-local Mathlib supplement — the un-localised section Čech module complex `D•`

`D^m` is the product `∏_{σ : Fin m → ι} M_{s_σ}` of away-localisations of
`M = Γ(Spec R, F)` at the multi-index products `s_σ = ∏ₖ s_{σ k}`; its differential
is the alternating sum of the canonical localisation comparison maps (index deletion
drops a factor, so `s_{σ∘dⱼ} ∣ s_σ`).  This is the concrete `R`-module complex `D•`
of `lem:section_cech_homology_exact` that the section Čech complex is identified
with.  Positive-degree exactness is reduced — via `exact_of_isLocalized_span` — to
the localised complexes already shown exact in `CechLocalized.cechLocalized_exact`;
the bridge is the localisation-transitivity lemma
`AwayComparison.comparison_isLocalizedModule` (applied here as
`dToCech_isLocalizedModule`). -/

namespace SectionCechModule

open CechLocalized AwayComparison

variable {R : Type u} [CommRing R] {ι : Type*} (s : ι → R)
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The un-localised section Čech coefficient `D_σ = M_{s_σ}`. -/
abbrev dCoeff {m : ℕ} (σ : Fin m → ι) : Type u :=
  LocalizedModule (Submonoid.powers (sprod s σ)) M

/-- The un-localised coface comparison `δ : M_{s_{σ∘dⱼ}} → M_{s_σ}` (R-linear), the
canonical localisation map for the divisibility `s_{σ∘dⱼ} ∣ s_σ`. -/
noncomputable def dCoface (m : ℕ) (σ : Fin (m + 1) → ι) (j : Fin (m + 1)) :
    dCoeff s M (σ ∘ j.succAbove) →ₗ[R] dCoeff s M σ :=
  comparison
    (LocalizedModule.mkLinearMap (Submonoid.powers (sprod s (σ ∘ j.succAbove))) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (sprod s σ)) M)
    (Inverts.of_dvd (sprod_succAbove_dvd s σ j)
      (LocalizedModule.mkLinearMap (Submonoid.powers (sprod s σ)) M))

/-- The un-localised differential `d : D^m → D^{m+1}` as an `R`-linear map: the
alternating sum of cofaces, assembled with `LinearMap.pi` over the output tuple. -/
noncomputable def dDiff (m : ℕ) :
    (∀ σ : Fin m → ι, dCoeff s M σ) →ₗ[R] (∀ σ : Fin (m + 1) → ι, dCoeff s M σ) :=
  LinearMap.pi fun σ => ∑ j : Fin (m + 1),
    (-1 : ℤ) ^ (j : ℕ) • (dCoface s M m σ j ∘ₗ LinearMap.proj (σ ∘ j.succAbove))

/-- Apply form of `dDiff`: the alternating sum of cofaces of the deleted faces. -/
lemma dDiff_apply (m : ℕ) (t : ∀ σ : Fin m → ι, dCoeff s M σ) (σ : Fin (m + 1) → ι) :
    dDiff s M m t σ
      = ∑ j : Fin (m + 1), (-1 : ℤ) ^ (j : ℕ) • dCoface s M m σ j (t (σ ∘ j.succAbove)) := by
  rw [dDiff, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun d _ => rfl

variable (r : ι)

/-- The per-index localisation comparison `M_{s_σ} → M_{s_r · s_σ}` carrying the
un-localised coefficient to the `cechCoeff` coefficient localised at `s_r`. -/
noncomputable def dToCech {m : ℕ} (σ : Fin m → ι) :
    dCoeff s M σ →ₗ[R] cechCoeff s M r σ :=
  comparison
    (LocalizedModule.mkLinearMap (Submonoid.powers (sprod s σ)) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M)
    (Inverts.of_dvd (dvd_mul_left (sprod s σ) (s r))
      (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M))

/-- **Transitivity payoff**: `dToCech` exhibits the localised coefficient
`cechCoeff = M_{s_r · s_σ}` as the localisation of the un-localised coefficient
`M_{s_σ}` away from the spanning element `s_r`.  Direct from
`AwayComparison.comparison_isLocalizedModule`; this is the per-coefficient input the
`exact_of_isLocalized_span` reduction of the section Čech complex consumes. -/
lemma dToCech_isLocalizedModule {m : ℕ} (σ : Fin m → ι) :
    IsLocalizedModule.Away (s r) (dToCech s M r σ) := by
  haveI inst : IsLocalizedModule (Submonoid.powers (sprod s σ * s r))
      (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M) := by
    rw [mul_comm]; infer_instance
  unfold dToCech
  exact comparison_isLocalizedModule (a := sprod s σ) (b := s r) _ _ _

/-- **Per-coface localisation naturality**: the localised coface `cechCoface`
intertwines the per-index comparison `dToCech` with the un-localised coface
`dCoface`.  Both composites are away-comparison maps from `M_{s_{σ∘dⱼ}}` to
`M_{s_r · s_σ}`, hence equal by `comparison_comp`.  This is the square that, summed
over the alternating signs, identifies the localised differential
`IsLocalizedModule.map (dDiff)` with `CombinatorialCech.depDiff (cechCoface)` —
the final brick of the `exact_of_isLocalized_span` reduction. -/
lemma cechCoface_dToCech {m : ℕ} (σ : Fin (m + 1) → ι) (j : Fin (m + 1))
    (x : dCoeff s M (σ ∘ j.succAbove)) :
    cechCoface s M r m σ j (dToCech s M r (σ ∘ j.succAbove) x)
      = dToCech s M r σ (dCoface s M m σ j x) := by
  simp only [cechCoface, dToCech, dCoface, LinearMap.toAddMonoidHom_coe]
  rw [comparison_comp_apply, comparison_comp_apply]
  exact Inverts.of_dvd (dvd_trans (sprod_succAbove_dvd s σ j) (dvd_mul_left (sprod s σ) (s r)))
    (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M)

/-- **Differential-naturality square** (the heart of the `exact_of_isLocalized_span`
reduction): localising the un-localised differential `dDiff` at a spanning element
`s_r` — via the per-index comparisons `dToCech` — yields the localised differential
`CombinatorialCech.depDiff (cechCoface)`.  Summing the per-coface squares
`cechCoface_dToCech` over the alternating signs.  Combined with
`dToCech_isLocalizedModule`, `IsLocalizedModule.pi`, and the uniqueness of
`IsLocalizedModule.map`, this identifies the localised `dDiff` with the
exact complex `CechLocalized.cechLocalized_exact`. -/
lemma dToCech_comm (m : ℕ) (t : ∀ σ : Fin m → ι, dCoeff s M σ) :
    CombinatorialCech.depDiff (A := fun _ σ => cechCoeff s M r σ) (cechCoface s M r) (m := m)
        (fun σ => dToCech s M r σ (t σ))
      = fun σ => dToCech s M r σ (dDiff s M m t σ) := by
  funext σ
  simp only [CombinatorialCech.depDiff, dDiff_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, cechCoface_dToCech]

/-! ### Assembly of step (a): positive-degree exactness of `D•`

The localised differential at a fixed index `r`, bundled as an `R`-linear map
(`locDiff`), so that `IsLocalizedModule.map` uniqueness identifies it with the
localisation of `dDiff`.  Everything here is at a *fixed* index `r : ι` (no
`Classical.choose`), hence friction-free; the spanning-element bookkeeping is
confined to the final `dDiff_exact`. -/

/-- R-linear underlying map of the localised coface `cechCoface` (the `comparison`
before `.toAddMonoidHom`). -/
noncomputable def cechCofaceLin (r : ι) (m : ℕ) (σ : Fin (m + 1) → ι) (j : Fin (m + 1)) :
    cechCoeff s M r (σ ∘ j.succAbove) →ₗ[R] cechCoeff s M r σ :=
  comparison
    (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s (σ ∘ j.succAbove))) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M)
    (Inverts.of_dvd (mul_dvd_mul_left (s r) (sprod_succAbove_dvd s σ j))
      (LocalizedModule.mkLinearMap (Submonoid.powers (s r * sprod s σ)) M))

lemma cechCoface_apply (r : ι) (m : ℕ) (σ : Fin (m + 1) → ι) (j : Fin (m + 1))
    (x : cechCoeff s M r (σ ∘ j.succAbove)) :
    cechCoface s M r m σ j x = cechCofaceLin s M r m σ j x := rfl

/-- The localised section Čech differential at index `r`, as a bundled `R`-linear
map (mirrors `dDiff` with the localised cofaces). -/
noncomputable def locDiff (r : ι) (m : ℕ) :
    (∀ σ : Fin m → ι, cechCoeff s M r σ) →ₗ[R] (∀ σ : Fin (m + 1) → ι, cechCoeff s M r σ) :=
  LinearMap.pi fun σ => ∑ j : Fin (m + 1),
    (-1 : ℤ) ^ (j : ℕ) • (cechCofaceLin s M r m σ j ∘ₗ LinearMap.proj (σ ∘ j.succAbove))

lemma locDiff_apply (r : ι) (m : ℕ) (t : ∀ σ : Fin m → ι, cechCoeff s M r σ)
    (σ : Fin (m + 1) → ι) :
    locDiff s M r m t σ
      = ∑ j : Fin (m + 1),
          (-1 : ℤ) ^ (j : ℕ) • cechCofaceLin s M r m σ j (t (σ ∘ j.succAbove)) := by
  rw [locDiff, LinearMap.pi_apply, LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun d _ => rfl

/-- `locDiff` agrees, as a raw function, with the localised combinatorial
differential `CombinatorialCech.depDiff (cechCoface)` already shown exact. -/
lemma locDiff_eq_depDiff (r : ι) (m : ℕ) :
    ⇑(locDiff s M r m)
      = CombinatorialCech.depDiff (A := fun _ σ => cechCoeff s M r σ)
          (cechCoface s M r) (m := m) := by
  funext t σ
  rw [locDiff_apply]
  simp only [CombinatorialCech.depDiff]
  exact Finset.sum_congr rfl fun j _ => by rw [cechCoface_apply]

/-- Positive-degree exactness of the bundled localised differential, transported
from `CechLocalized.cechLocalized_exact`. -/
lemma locDiff_exact (r : ι) (m : ℕ) :
    Function.Exact (locDiff s M r (m + 1)) (locDiff s M r (m + 2)) := by
  rw [locDiff_eq_depDiff, locDiff_eq_depDiff]
  exact CechLocalized.cechLocalized_exact s M r m

/-- The product localisation map `D^m → ∏_σ M_{s_r·s_σ}` at index `r`. -/
noncomputable def fLoc (r : ι) (m : ℕ) :
    (∀ σ : Fin m → ι, dCoeff s M σ) →ₗ[R] (∀ σ : Fin m → ι, cechCoeff s M r σ) :=
  LinearMap.pi fun σ => dToCech s M r σ ∘ₗ LinearMap.proj σ

lemma fLoc_apply (r : ι) (m : ℕ) (t : ∀ σ : Fin m → ι, dCoeff s M σ) (σ : Fin m → ι) :
    fLoc s M r m t σ = dToCech s M r σ (t σ) := by
  simp only [fLoc, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- `fLoc` exhibits the product localised coefficient as the localisation of `D^m`
away from `s_r` (from `IsLocalizedModule.pi` + `dToCech_isLocalizedModule`). -/
instance fLoc_isLocalizedModule [Finite ι] (r : ι) (m : ℕ) :
    IsLocalizedModule.Away (s r) (fLoc s M r m) := by
  haveI : ∀ σ : Fin m → ι, IsLocalizedModule (Submonoid.powers (s r)) (dToCech s M r σ) :=
    fun σ => dToCech_isLocalizedModule s M r σ
  exact IsLocalizedModule.pi (Submonoid.powers (s r)) fun σ => dToCech s M r σ

/-- The localised differential intertwines `fLoc` with `dDiff` (the `dToCech_comm`
square, packaged through the bundled maps). -/
lemma locDiff_fLoc (r : ι) (m : ℕ) (t : ∀ σ : Fin m → ι, dCoeff s M σ) :
    locDiff s M r m (fLoc s M r m t) = fLoc s M r (m + 1) (dDiff s M m t) := by
  have h1 : ⇑(locDiff s M r m) (fLoc s M r m t)
      = CombinatorialCech.depDiff (A := fun _ σ => cechCoeff s M r σ) (cechCoface s M r) (m := m)
          (fun σ => dToCech s M r σ (t σ)) := by
    rw [locDiff_eq_depDiff]
    exact congrArg _ (funext fun σ => fLoc_apply s M r m t σ)
  rw [h1, dToCech_comm]
  funext σ
  exact (fLoc_apply s M r (m + 1) (dDiff s M m t) σ).symm

/-- `IsLocalizedModule.map` of `dDiff` is the bundled localised differential
`locDiff` — by `IsLocalizedModule.ext`, the comparison reducing to `locDiff_fLoc`.
Stated for an arbitrary away element `a` (with `s r = a`) so the spanning-element
bookkeeping in `dDiff_exact` needs no `↑ρ`-rewrite inside the localised map. -/
lemma map_dDiff_eq_locDiff (r : ι) (m : ℕ) {a : R}
    [IsLocalizedModule (Submonoid.powers a) (fLoc s M r m)]
    [IsLocalizedModule (Submonoid.powers a) (fLoc s M r (m + 1))] :
    IsLocalizedModule.map (Submonoid.powers a) (fLoc s M r m) (fLoc s M r (m + 1))
        (dDiff s M m) = locDiff s M r m := by
  apply IsLocalizedModule.ext (Submonoid.powers a) (fLoc s M r m)
    (fun x => IsLocalizedModule.map_units (fLoc s M r (m + 1)) x)
  apply LinearMap.ext; intro t
  rw [LinearMap.comp_apply, LinearMap.comp_apply, IsLocalizedModule.map_apply, locDiff_fLoc]

/-- A chosen `ι`-index realising a spanning-set element as `s i`, kept opaque so
the spanning-element rewrite in `dDiff_exact` has a type-correct motive (the index
must not syntactically contain `↑ρ`). -/
private noncomputable def spanIdx (ρ : ↑(Set.range s)) : ι := ρ.2.choose

omit [CommRing R] in
private lemma spanIdx_spec (ρ : ↑(Set.range s)) : s (spanIdx s ρ) = ↑ρ := ρ.2.choose_spec

/-- **Step (a): positive-degree exactness of the un-localised section Čech module
complex `D•`** (`lem:cech_acyclic_affine`, the `R`-module core).  For a spanning
family `s : ι → R` (`Ideal.span (Set.range s) = ⊤`), the complex
`∏_σ M_{s_σ}` is exact in positive degrees.  Reduced — via
`exact_of_isLocalized_span` localising at each spanning element `s_r` — to the
exactness `locDiff_exact` of the localised complexes (which is the dependent
combinatorial core `CechLocalized.cechLocalized_exact`), through the localised-
differential identification `map_dDiff_eq_locDiff`. -/
lemma dDiff_exact [Finite ι] (hs : Ideal.span (Set.range s) = ⊤) (m : ℕ) :
    Function.Exact (dDiff s M (m + 1)) (dDiff s M (m + 2)) := by
  classical
  haveI inst1 : ∀ ρ : ↑(Set.range s),
      IsLocalizedModule.Away (↑ρ) (fLoc s M (spanIdx s ρ) (m + 1)) := fun ρ => by
    rw [← spanIdx_spec s ρ]; infer_instance
  haveI inst2 : ∀ ρ : ↑(Set.range s),
      IsLocalizedModule.Away (↑ρ) (fLoc s M (spanIdx s ρ) (m + 2)) := fun ρ => by
    rw [← spanIdx_spec s ρ]; infer_instance
  haveI inst3 : ∀ ρ : ↑(Set.range s),
      IsLocalizedModule.Away (↑ρ) (fLoc s M (spanIdx s ρ) (m + 3)) := fun ρ => by
    rw [← spanIdx_spec s ρ]; infer_instance
  refine exact_of_isLocalized_span (Set.range s) hs
    (fun ρ => ∀ σ : Fin (m + 1) → ι, cechCoeff s M (spanIdx s ρ) σ)
    (fun ρ => fLoc s M (spanIdx s ρ) (m + 1))
    (fun ρ => ∀ σ : Fin (m + 2) → ι, cechCoeff s M (spanIdx s ρ) σ)
    (fun ρ => fLoc s M (spanIdx s ρ) (m + 2))
    (fun ρ => ∀ σ : Fin (m + 3) → ι, cechCoeff s M (spanIdx s ρ) σ)
    (fun ρ => fLoc s M (spanIdx s ρ) (m + 3))
    (dDiff s M (m + 1)) (dDiff s M (m + 2)) fun ρ => ?_
  rw [map_dDiff_eq_locDiff s M (spanIdx s ρ) (m + 1),
    map_dDiff_eq_locDiff s M (spanIdx s ρ) (m + 2)]
  exact locDiff_exact s M (spanIdx s ρ) m

set_option maxHeartbeats 1600000 in
-- raised: the change-of-ring ladder repeatedly synthesises `AddMonoidHomClass` over the
-- `dCoeff`-abbreviated `LocalizedModule` carriers, which is instance-search heavy.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Route-B positive-degree exactness of the un-localised section Čech module complex
`D•` over a standard *sub*cover of `D(f)`** (`lem:affine_cech_vanishing_tilde_subcover`,
module core).  Here `s = g` need NOT span the unit ideal of `R`; only its image `s/1`
spans the unit ideal of the away ring `R_f` (`hspan`), and each `s i` lies in `√(f)`
(`hmem`).  The complex `∏_σ M_{s_σ}` is then exact in positive degrees.

Route B (change-of-ring): instantiate `dDiff_exact` over `R_f = Localization.Away f` with
the module `M_f = LocalizedModule (powers f) M` and the spanning family `s/1`, then transport
the resulting positive-degree exactness back to the `R`-side along the degreewise additive
isomorphisms `M_{s_σ} ≅ (M_f)_{s_σ}` (`AwayComparison.isLocalizedModule_comp_away` + the
universal `IsLocalizedModule.iso`), which intertwine the alternating-sum localisation
differentials. -/
lemma dDiff_exact_of_localizationAway [Finite ι] (f : R)
    (hmem : ∀ i, ∃ k, f ∣ s i ^ k)
    (hspan : Ideal.span (Set.range (fun i => algebraMap R (Localization.Away f) (s i))) = ⊤)
    (m : ℕ) :
    Function.Exact (dDiff s M (m + 1)) (dDiff s M (m + 2)) := by
  classical
  set Rf := Localization.Away f with hRf
  set Mf := LocalizedModule (Submonoid.powers f) M with hMf
  set g' : ι → Rf := fun i => algebraMap R Rf (s i) with hg'
  -- `R_f`-side positive-degree exactness (the black-box reuse of `dDiff_exact`).
  have Hf : Function.Exact (dDiff g' Mf (m + 1)) (dDiff g' Mf (m + 2)) :=
    dDiff_exact g' Mf hspan m
  -- `sprod g' σ` is the image of `sprod s σ`.
  have hsprod : ∀ {n : ℕ} (σ : Fin n → ι), sprod g' σ = algebraMap R Rf (sprod s σ) := by
    intro n σ; simp only [g', sprod, map_prod]
  -- per (nonempty) `σ`: `f` divides a power of `sprod s σ`.
  have hdvd : ∀ {n : ℕ} (σ : Fin (n + 1) → ι), ∃ k, f ∣ sprod s σ ^ k := by
    intro n σ
    obtain ⟨k, hk⟩ := hmem (σ 0)
    refine ⟨k, ?_⟩
    have he : sprod s σ ^ k = s (σ 0) ^ k * (∏ x : Fin n, s (σ x.succ)) ^ k := by
      rw [sprod, Fin.prod_univ_succ, mul_pow]
    rw [he]; exact hk.mul_right _
  -- the composite localisation structure map `M → M_f → (M_f)_{s_σ}` localises `M` at `s_σ`.
  have inst_comp : ∀ {n : ℕ} (σ : Fin (n + 1) → ι),
      IsLocalizedModule (Submonoid.powers (sprod s σ))
        ((LocalizedModule.mkLinearMap (Submonoid.powers (sprod g' σ)) Mf).restrictScalars R ∘ₗ
          LocalizedModule.mkLinearMap (Submonoid.powers f) M) := by
    intro n σ
    obtain ⟨k, h, hh⟩ := hdvd σ
    haveI : IsLocalizedModule (Submonoid.powers (algebraMap R Rf (sprod s σ)))
        (LocalizedModule.mkLinearMap (Submonoid.powers (sprod g' σ)) Mf) := by
      rw [← hsprod σ]; infer_instance
    exact AwayComparison.isLocalizedModule_comp_away f (sprod s σ) h hh
      (LocalizedModule.mkLinearMap (Submonoid.powers f) M)
      (LocalizedModule.mkLinearMap (Submonoid.powers (sprod g' σ)) Mf)
  -- the per-σ `R`-linear comparison `(M_f)_{s_σ} ≅ M_{s_σ}` (Rf-side → R-side).
  let eσL : ∀ {n : ℕ} (σ : Fin (n + 1) → ι), dCoeff g' Mf σ ≃ₗ[R] dCoeff s M σ :=
    fun {n} σ =>
      haveI := inst_comp σ
      (IsLocalizedModule.iso (Submonoid.powers (sprod s σ))
        ((LocalizedModule.mkLinearMap (Submonoid.powers (sprod g' σ)) Mf).restrictScalars R ∘ₗ
          LocalizedModule.mkLinearMap (Submonoid.powers f) M)).symm
  -- `eσL τ` undoes the composite structure map: it sends `compMap τ mval ↦ mk_{s_τ} mval`.
  have heσL : ∀ {n : ℕ} (τ : Fin (n + 1) → ι) (mval : M),
      eσL τ ((LocalizedModule.mkLinearMap (Submonoid.powers (sprod g' τ)) Mf)
          (LocalizedModule.mkLinearMap (Submonoid.powers f) M mval))
        = LocalizedModule.mkLinearMap (Submonoid.powers (sprod s τ)) M mval := by
    intro n τ mval
    haveI := inst_comp τ
    exact DFunLike.congr_fun (IsLocalizedModule.iso_symm_comp (Submonoid.powers (sprod s τ))
      ((LocalizedModule.mkLinearMap (Submonoid.powers (sprod g' τ)) Mf).restrictScalars R ∘ₗ
        LocalizedModule.mkLinearMap (Submonoid.powers f) M)) mval
  -- per-coface naturality: `eσ` intertwines the two cofaces.
  have nat : ∀ {n : ℕ} (σ : Fin (n + 2) → ι) (j : Fin (n + 2))
      (z : dCoeff g' Mf (σ ∘ j.succAbove)),
      eσL σ (dCoface g' Mf (n + 1) σ j z)
        = dCoface s M (n + 1) σ j (eσL (σ ∘ j.succAbove) z) := by
    intro n σ j z
    haveI := inst_comp (σ ∘ j.succAbove)
    -- reduce to elements `compMap (σ∘d) mval` by localisation extensionality
    have key : (eσL σ).toLinearMap ∘ₗ (dCoface g' Mf (n + 1) σ j).restrictScalars R
        = (dCoface s M (n + 1) σ j) ∘ₗ (eσL (σ ∘ j.succAbove)).toLinearMap := by
      apply IsLocalizedModule.ext (Submonoid.powers (sprod s (σ ∘ j.succAbove)))
        (LinearMap.restrictScalars R
            (LocalizedModule.mkLinearMap (Submonoid.powers (sprod g' (σ ∘ j.succAbove))) Mf)
          ∘ₗ LocalizedModule.mkLinearMap (Submonoid.powers f) M)
        (fun x => (AwayComparison.Inverts.of_dvd (sprod_succAbove_dvd s σ j)
          (LocalizedModule.mkLinearMap (Submonoid.powers (sprod s σ)) M)).isUnit_powers x)
      apply LinearMap.ext; intro mval
      simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
        LinearEquiv.coe_coe]
      -- LHS
      have hL : dCoface g' Mf (n + 1) σ j
            ((LocalizedModule.mkLinearMap (Submonoid.powers (sprod g' (σ ∘ j.succAbove))) Mf)
              (LocalizedModule.mkLinearMap (Submonoid.powers f) M mval))
          = (LocalizedModule.mkLinearMap (Submonoid.powers (sprod g' σ)) Mf)
              (LocalizedModule.mkLinearMap (Submonoid.powers f) M mval) := by
        simp only [dCoface]
        exact AwayComparison.comparison_apply _ _ _ _
      rw [hL, heσL σ mval, heσL (σ ∘ j.succAbove) mval]
      -- RHS
      simp only [dCoface]
      exact (AwayComparison.comparison_apply _ _ _ mval).symm
    exact DFunLike.congr_fun key z
  -- bundle the per-σ comparisons into product `AddEquiv`s.
  let E : (n : ℕ) → ((σ : Fin (n + 1) → ι) → dCoeff g' Mf σ) ≃+
      ((σ : Fin (n + 1) → ι) → dCoeff s M σ) :=
    fun n => AddEquiv.piCongrRight (fun σ => (eσL σ).toAddEquiv)
  -- the ladder squares.
  have sq : ∀ r : ℕ,
      (dDiff s M (r + 1)).toAddMonoidHom.comp (E r).toAddMonoidHom
        = (E (r + 1)).toAddMonoidHom.comp (dDiff g' Mf (r + 1)).toAddMonoidHom := by
    intro r
    apply AddMonoidHom.ext; intro x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    funext σ
    change dDiff s M (r + 1) (fun τ => eσL τ (x τ)) σ
      = eσL σ (dDiff g' Mf (r + 1) x σ)
    rw [dDiff_apply, dDiff_apply, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_zsmul, nat]
  exact Function.Exact.of_ladder_addEquiv_of_exact (E m) (E (m + 1)) (E (m + 2))
    (sq m) (sq (m + 1)) Hf

set_option maxHeartbeats 1600000 in
-- raised: like `dDiff_exact_of_localizationAway`, the change-of-ring ladder repeatedly synthesises
-- `AddMonoidHomClass`/base-change instances over the `dCoeff`-abbreviated `LocalizedModule` carriers.
set_option synthInstance.maxHeartbeats 800000 in
/-- **Route-B1 positive-degree exactness of the un-localised section Čech module complex `D•` over a
cover of a *general affine open* `V = ⨆ᵢ D(sᵢ)`** (`lem:affine_cech_vanishing_general_seed`, module
core).  The cover family `s = g` need NOT span the unit ideal of `R`, and `V` need NOT be a single
distinguished `D(f)`; only the images `sᵢ ↦ S = Γ(V)` span the unit ideal of `S` (`hspan`).  Then the
complex `∏_σ M_{s_σ}` is exact in positive degrees.

Route B1 (change of ring to `S = Γ(V)` via algebraic base change `M ⊗_R S`): instantiate `dDiff_exact`
over `S` with the module `M_S = M ⊗_R S` and the spanning family `s̄ = algebraMap R S ∘ s`, then transport
the resulting positive-degree exactness back to the `R`-side along the degreewise additive isomorphisms
`M_{s_σ} ≅ (M_S)_{s̄_σ}` (`isLocalizedModule_baseChange_away` + the universal `IsLocalizedModule.iso`),
which intertwine the alternating-sum localisation differentials.  The geometric input — that the
localisation `(M_S)_{s̄_σ}`'s ring is simultaneously an `R`-localisation at `powers (s_σ)`, encoding
`D(s_σ) ⊆ V` — is supplied per Čech multi-index `σ` by the `hloc` family (discharged at the wrapper
from `IsAffineOpen V` via `IsAffineOpen.isLocalization_of_eq_basicOpen`). -/
lemma dDiff_exact_of_affineCover [Finite ι]
    (S : Type u) [CommRing S] [Algebra R S]
    (hspan : Ideal.span (Set.range (fun i => algebraMap R S (s i))) = ⊤)
    (hloc : ∀ {n : ℕ} (σ : Fin (n + 1) → ι),
      IsLocalization (Submonoid.powers (sprod s σ))
        (Localization (Submonoid.powers (algebraMap R S (sprod s σ)))))
    (m : ℕ) :
    Function.Exact (dDiff s M (m + 1)) (dDiff s M (m + 2)) := by
  classical
  set MS := TensorProduct R S M with hMS
  set bc : M →ₗ[R] MS := TensorProduct.mk R S M 1 with hbc
  set gS : ι → S := fun i => algebraMap R S (s i) with hgS
  -- `S`-side positive-degree exactness (the black-box reuse of `dDiff_exact`).
  have Hf : Function.Exact (dDiff gS MS (m + 1)) (dDiff gS MS (m + 2)) :=
    dDiff_exact gS MS hspan m
  -- `sprod gS σ` is the image of `sprod s σ`.
  have hsprod : ∀ {n : ℕ} (σ : Fin n → ι), sprod gS σ = algebraMap R S (sprod s σ) := by
    intro n σ; simp only [hgS, sprod, map_prod]
  -- the composite localisation structure map `M → M_S → (M_S)_{s_σ}` localises `M` at `s_σ`.
  have inst_comp : ∀ {n : ℕ} (σ : Fin (n + 1) → ι),
      IsLocalizedModule (Submonoid.powers (sprod s σ))
        ((LocalizedModule.mkLinearMap (Submonoid.powers (sprod gS σ)) MS).restrictScalars R ∘ₗ bc) := by
    intro n σ
    haveI hL : IsLocalization (Submonoid.powers (algebraMap R S (sprod s σ)))
        (Localization (Submonoid.powers (sprod gS σ))) := by
      rw [← hsprod σ]; infer_instance
    haveI hLM : IsLocalizedModule (Submonoid.powers (algebraMap R S (sprod s σ)))
        (LocalizedModule.mkLinearMap (Submonoid.powers (sprod gS σ)) MS) := by
      rw [← hsprod σ]; infer_instance
    haveI hR : IsLocalization (Submonoid.powers (sprod s σ))
        (Localization (Submonoid.powers (sprod gS σ))) := by
      rw [hsprod σ]; exact hloc σ
    exact isLocalizedModule_baseChange_away bc (TensorProduct.isBaseChange R M S)
      (LocalizedModule.mkLinearMap (Submonoid.powers (sprod gS σ)) MS)
      (Localization (Submonoid.powers (sprod gS σ))) (a := sprod s σ)
  -- the per-σ `R`-linear comparison `(M_S)_{s_σ} ≅ M_{s_σ}` (S-side → R-side).
  let eσL : ∀ {n : ℕ} (σ : Fin (n + 1) → ι), dCoeff gS MS σ ≃ₗ[R] dCoeff s M σ :=
    fun {n} σ =>
      haveI := inst_comp σ
      (IsLocalizedModule.iso (Submonoid.powers (sprod s σ))
        ((LocalizedModule.mkLinearMap (Submonoid.powers (sprod gS σ)) MS).restrictScalars R ∘ₗ
          bc)).symm
  -- `eσL τ` undoes the composite structure map: it sends `compMap τ mval ↦ mk_{s_τ} mval`.
  have heσL : ∀ {n : ℕ} (τ : Fin (n + 1) → ι) (mval : M),
      eσL τ ((LocalizedModule.mkLinearMap (Submonoid.powers (sprod gS τ)) MS) (bc mval))
        = LocalizedModule.mkLinearMap (Submonoid.powers (sprod s τ)) M mval := by
    intro n τ mval
    haveI := inst_comp τ
    exact DFunLike.congr_fun (IsLocalizedModule.iso_symm_comp (Submonoid.powers (sprod s τ))
      ((LocalizedModule.mkLinearMap (Submonoid.powers (sprod gS τ)) MS).restrictScalars R ∘ₗ
        bc)) mval
  -- per-coface naturality: `eσ` intertwines the two cofaces.
  have nat : ∀ {n : ℕ} (σ : Fin (n + 2) → ι) (j : Fin (n + 2))
      (z : dCoeff gS MS (σ ∘ j.succAbove)),
      eσL σ (dCoface gS MS (n + 1) σ j z)
        = dCoface s M (n + 1) σ j (eσL (σ ∘ j.succAbove) z) := by
    intro n σ j z
    haveI := inst_comp (σ ∘ j.succAbove)
    have key : (eσL σ).toLinearMap ∘ₗ (dCoface gS MS (n + 1) σ j).restrictScalars R
        = (dCoface s M (n + 1) σ j) ∘ₗ (eσL (σ ∘ j.succAbove)).toLinearMap := by
      apply IsLocalizedModule.ext (Submonoid.powers (sprod s (σ ∘ j.succAbove)))
        (LinearMap.restrictScalars R
            (LocalizedModule.mkLinearMap (Submonoid.powers (sprod gS (σ ∘ j.succAbove))) MS)
          ∘ₗ bc)
        (fun x => (AwayComparison.Inverts.of_dvd (sprod_succAbove_dvd s σ j)
          (LocalizedModule.mkLinearMap (Submonoid.powers (sprod s σ)) M)).isUnit_powers x)
      apply LinearMap.ext; intro mval
      simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
        LinearEquiv.coe_coe]
      have hL : dCoface gS MS (n + 1) σ j
            ((LocalizedModule.mkLinearMap (Submonoid.powers (sprod gS (σ ∘ j.succAbove))) MS)
              (bc mval))
          = (LocalizedModule.mkLinearMap (Submonoid.powers (sprod gS σ)) MS) (bc mval) := by
        simp only [dCoface]
        exact AwayComparison.comparison_apply _ _ _ _
      rw [hL, heσL σ mval, heσL (σ ∘ j.succAbove) mval]
      simp only [dCoface]
      exact (AwayComparison.comparison_apply _ _ _ mval).symm
    exact DFunLike.congr_fun key z
  -- bundle the per-σ comparisons into product `AddEquiv`s.
  let E : (n : ℕ) → ((σ : Fin (n + 1) → ι) → dCoeff gS MS σ) ≃+
      ((σ : Fin (n + 1) → ι) → dCoeff s M σ) :=
    fun n => AddEquiv.piCongrRight (fun σ => (eσL σ).toAddEquiv)
  -- the ladder squares.
  have sq : ∀ r : ℕ,
      (dDiff s M (r + 1)).toAddMonoidHom.comp (E r).toAddMonoidHom
        = (E (r + 1)).toAddMonoidHom.comp (dDiff gS MS (r + 1)).toAddMonoidHom := by
    intro r
    apply AddMonoidHom.ext; intro x
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    funext σ
    change dDiff s M (r + 1) (fun τ => eσL τ (x τ)) σ
      = eσL σ (dDiff gS MS (r + 1) x σ)
    rw [dDiff_apply, dDiff_apply, map_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [map_zsmul, nat]
  exact Function.Exact.of_ladder_addEquiv_of_exact (E m) (E (m + 1)) (E (m + 2))
    (sq m) (sq (m + 1)) Hf

end SectionCechModule

/-! ## Project-local Mathlib supplement — quasi-coherent sections as away localisations (L1, step (b))

The categorical→module bridge needs the section-identification of
`def:qcoh_sections_localized`: over a basic open `D(g)` the sections of a
quasi-coherent sheaf are the away localisation `M_g`, and the restriction maps
between basic opens are the canonical localisation comparison maps.  For the
standard sheaf `tilde M` this is *verbatim* from Mathlib's `Tilde` development
(`AlgebraicGeometry.tilde.toOpen` carries `IsLocalizedModule (.powers g)` and the
restriction compatibility is `tilde.toOpen_res`); the only project-local content is
(i) the multi-index intersection `⨅ₖ D(s_{σ k}) = D(s_σ)` identification, which lets
the degree-`p` section group over the `(p+1)`-fold intersection be read as the
localisation `M_{s_σ}` (this is what `lem:section_cech_homology_exact` consumes
degreewise), and (ii) the identification of the abstract presheaf restriction with
`AwayComparison.comparison`, the differential brick.

For an *arbitrary* quasi-coherent `F` the remaining input is the affine equivalence
`F ≅ tilde(ΓF)` (Stacks 01I8); see `def:qcoh_sections_localized`.  The tilde case
below is the gap-free part that lands the named target. -/

/-- Splitting an indexed infimum over `Fin (n+1)` into the `0`-th term and the
infimum over the tail.  Lattice-combinatorial helper behind `basicOpen_sprod`. -/
private lemma iInf_fin_succ {α : Type*} [CompleteLattice α] (n : ℕ) (f : Fin (n + 1) → α) :
    (⨅ i, f i) = f 0 ⊓ ⨅ i : Fin n, f i.succ := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (le_iInf fun i => iInf_le _ i.succ)
  · refine le_iInf fun i => ?_
    refine Fin.cases inf_le_left (fun j => le_trans inf_le_right (iInf_le _ j)) i

/-- **Multi-index basic-open intersection** (geometric input to step (c)): the
`(p+1)`-fold intersection of the basic opens `D(s_{σ k})` of a {\v C}ech multi-index
`σ : Fin n → ι` is the basic open `D(s_σ)` of the product `s_σ = ∏ₖ s_{σ k}`.  This
identifies the section group `F(⨅ₖ D(s_{σ k}))` of `sectionCechCosimplicial` with the
away localisation `M_{s_σ}` of `SectionCechModule.dCoeff`. -/
lemma basicOpen_sprod {R : CommRingCat.{u}} {ι : Type u} (n : ℕ) (s : ι → R) (σ : Fin n → ι) :
    (⨅ k, PrimeSpectrum.basicOpen (s (σ k)) : (Spec R).Opens)
      = PrimeSpectrum.basicOpen (∏ k, s (σ k)) := by
  induction n with
  | zero =>
      rw [show (∏ k, s (σ k)) = 1 from Finset.prod_of_isEmpty _]
      simp only [PrimeSpectrum.basicOpen_one]
      exact iInf_of_empty _
  | succ m ih =>
      rw [Fin.prod_univ_succ, PrimeSpectrum.basicOpen_mul, ← ih (fun i => σ i.succ),
        iInf_fin_succ]
      rfl

/-- **Quasi-coherent sections over a {\v C}ech intersection are an away localisation**
(`def:qcoh_sections_localized`, tilde case — step (b) of the L1 bridge).  For the
standard sheaf `tilde M` of an `R`-module `M`, the section-restriction map from `M`
to the sections over the `(p+1)`-fold basic-open intersection
`⨅ₖ D(s_{σ k}) = D(s_σ)` exhibits that section group as the away localisation
`M_{s_σ}` (`IsLocalizedModule` for `Submonoid.powers (∏ₖ s_{σ k})`).  Combines the
Mathlib instance `IsLocalizedModule (.powers g) (tilde.toOpen M (D g)).hom` with the
intersection identification `basicOpen_sprod`.  This is the degreewise section
identification that `lem:section_cech_homology_exact` consumes; the restriction
compatibility (item (5) of the blueprint definition) is `tilde.toOpen_res` together
with `qcohRestriction_eq_comparison` below. -/
lemma qcohSectionsAwayLocalized {R : CommRingCat.{u}} {ι : Type u}
    (M : ModuleCat.{u} R) {n : ℕ} (s : ι → R) (σ : Fin n → ι) :
    IsLocalizedModule (Submonoid.powers (∏ k, s (σ k)))
      (AlgebraicGeometry.tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))).hom := by
  rw [basicOpen_sprod]
  infer_instance

/-- **Restriction = localisation comparison** (`def:qcoh_sections_localized`, item (5);
the differential brick of step (c)).  For the standard sheaf `tilde M`, the presheaf
restriction map between basic-open section groups `M_a → M_b` (along an inclusion
`D(b) ⊆ D(a)`) is, as an `R`-linear map, the canonical away-localisation comparison
`AwayComparison.comparison` — provided `a` acts invertibly on `M_b` (`Inverts a M_b`,
which holds whenever `a ∣ b`, the {\v C}ech-face case).  Proved by the universal
property `AwayComparison.comparison_unique`: both the restriction and the comparison
are `R`-linear maps that recover `tilde.toOpen M (D b)` after precomposition with
`tilde.toOpen M (D a)` (the restriction does so by `tilde.toOpen_res`).  Summed over
the alternating signs, this identifies the section {\v C}ech differential with the
module differential `SectionCechModule.dDiff`. -/
lemma qcohRestriction_eq_comparison {R : CommRingCat.{u}} (M : ModuleCat.{u} R) {a b : R}
    (i : (PrimeSpectrum.basicOpen b : (Spec R).Opens) ⟶ PrimeSpectrum.basicOpen a)
    (hb : AwayComparison.Inverts a
      ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj
        (Opposite.op (PrimeSpectrum.basicOpen b)))) :
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.map i.op).hom
      = AwayComparison.comparison (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen a)).hom
          (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen b)).hom hb := by
  haveI : IsLocalizedModule (Submonoid.powers a)
      (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen a)).hom := inferInstance
  refine (AwayComparison.comparison_unique
    (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen a)).hom
    (AlgebraicGeometry.tilde.toOpen M (PrimeSpectrum.basicOpen b)).hom hb _ ?_).symm
  have h := AlgebraicGeometry.tilde.toOpen_res M (PrimeSpectrum.basicOpen a)
    (PrimeSpectrum.basicOpen b) i
  exact congrArg ModuleCat.Hom.hom h

/-! ## Project-local Mathlib supplement — section {\v C}ech homology bridge (L1 steps c, d)

The categorical→module bridge of `lem:section_cech_homology_exact`: the
`Ab`-valued section {\v C}ech complex `sectionCechComplex` (of `PresheafCech.lean`)
has its degree-`p` object a *categorical product* `∏ᶜ_σ F(⨅ₖ U (σ k))` in `Ab`, and
its differential the alternating sum of the {\v C}ech coface restrictions.  These
lemmas (c1)–(c3) move that abstract complex to the concrete localised-module complex
`SectionCechModule.dDiff` (whose positive-degree exactness `dDiff_exact` is step (a)),
and read off homology vanishing. -/

section SectionCechBridge

open CategoryTheory.Limits AlgebraicTopology

variable {X : Scheme.{u}}

/-- **(c1) Element-level product equivalence** (`lem:section_cech_product_equiv`):
the underlying type of the degree-`p` object `∏ᶜ_σ F(⨅ₖ U (σ k))` of the section
{\v C}ech cosimplicial object is the dependent product `∏_σ ToType (F(⨅ₖ U (σ k)))`.
Supplied by `CategoryTheory.Limits.Concrete.productEquiv` (the forgetful functor of
`Ab` preserves discrete products). -/
noncomputable def sectionCechProductEquiv {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (F : X.PresheafOfModules) (p : ℕ) :
    ToType ((sectionCechCosimplicial U F).obj (SimplexCategory.mk p)) ≃
      (∀ σ : Fin (p + 1) → ι, ToType (F.presheaf.obj (Opposite.op (⨅ k, U (σ k))))) :=
  Concrete.productEquiv
    (fun σ : Fin (p + 1) → ι => F.presheaf.obj (Opposite.op (⨅ k, U (σ k))))

/-- Coordinate projection of `sectionCechProductEquiv`: the `σ`-component is the
underlying group map of the categorical projection `Pi.π … σ`.  A definitional
restatement of `Concrete.productEquiv_apply_apply`, named so that downstream proofs can
`rw` it without fighting the `Concrete.productEquiv` coercion. -/
lemma sectionCechProductEquiv_apply {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (F : X.PresheafOfModules) (p : ℕ)
    (y : ToType ((sectionCechCosimplicial U F).obj (SimplexCategory.mk p)))
    (σ : Fin (p + 1) → ι) :
    sectionCechProductEquiv U F p y σ
      = ConcreteCategory.hom
          (Pi.π (fun σ : Fin (p + 1) → ι => F.presheaf.obj (Opposite.op (⨅ k, U (σ k)))) σ) y :=
  Concrete.productEquiv_apply_apply _ y σ

/-- **Homology-to-exactness reduction** (the `Ab`-side of `lem:section_cech_ab_exact`):
the degree-`(q+1)` homology of the section {\v C}ech complex vanishes once the
underlying group homomorphisms of the two consecutive coface differentials
`objD q`, `objD (q+1)` form an exact sequence.  Pure homological algebra: combines
`exactAt_iff_isZero_homology`, `exactAt_iff'`, and the abelian-group exactness
criterion `ShortComplex.ab_exact_iff_function_exact`. -/
lemma sectionCech_isZero_homology_of_objD_exact {ι : Type u}
    (U : ι → TopologicalSpace.Opens X) (F : X.PresheafOfModules) (q : ℕ)
    (h : Function.Exact
      (ConcreteCategory.hom (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial U F) q))
      (ConcreteCategory.hom
        (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial U F) (q + 1)))) :
    IsZero ((sectionCechComplex U F).homology (q + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      (sectionCechComplex U F).exactAt_iff' q (q + 1) (q + 2) (by simp) (by simp),
      ShortComplex.ab_exact_iff_function_exact]
  have hf : (sectionCechComplex U F).d q (q + 1)
      = AlternatingCofaceMapComplex.objD (sectionCechCosimplicial U F) q :=
    CochainComplex.of_d _ _ (AlternatingCofaceMapComplex.d_squared _) q
  have hg : (sectionCechComplex U F).d (q + 1) (q + 2)
      = AlternatingCofaceMapComplex.objD (sectionCechCosimplicial U F) (q + 1) :=
    CochainComplex.of_d _ _ (AlternatingCofaceMapComplex.d_squared _) (q + 1)
  change Function.Exact
      (ConcreteCategory.hom ((sectionCechComplex U F).d q (q + 1)))
      (ConcreteCategory.hom ((sectionCechComplex U F).d (q + 1) (q + 2)))
  rw [hf, hg]
  exact h

/-- Application of a finite sum of `Ab`-morphisms distributes over the sum. -/
private lemma ab_hom_finsetSum_apply {A B : Ab.{u}} {κ : Type*}
    (s : Finset κ) (f : κ → (A ⟶ B)) (t : ToType A) :
    ConcreteCategory.hom (∑ i ∈ s, f i) t = ∑ i ∈ s, ConcreteCategory.hom (f i) t := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, AddCommGrpCat.hom_add_apply, ih]

/-- The `i`-th section {\v C}ech face restriction at a multi-index `σ` of the
cosimplicial section object: the presheaf restriction of `F` from the deleted-face
intersection `⨅ₗ U (σ (δ i l))` to the full intersection `⨅ₖ U (σ k)`.  Factored as a
named `def` so the cosimplicial differential (`sectionCech_objD_apply`) refers to it
by name rather than re-elaborating the `homOfLE (le_iInf …)` term. -/
noncomputable def sectionCechFaceRestr {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (F : X.PresheafOfModules) {q : ℕ} (σ : Fin (q + 2) → ι) (i : Fin (q + 2)) :
    F.presheaf.obj (Opposite.op (⨅ l, U ((σ ∘ (SimplexCategory.δ i).toOrderHom) l)))
      ⟶ F.presheaf.obj (Opposite.op (⨅ k, U (σ k))) :=
  F.presheaf.map (homOfLE (le_iInf
    (fun l => iInf_le _ ((SimplexCategory.δ i).toOrderHom l)))).op

/-- **(c2, abstract) Coface match**: the underlying group action of the section
{\v C}ech coface differential `objD q`, read through the product equivalence, is the
alternating sum of the presheaf restriction maps applied to the deleted-face
coordinates — exactly the shape of `SectionCechModule.dDiff`.  This is purely about
the cosimplicial structure of `sectionCechCosimplicial`; no sheaf identification yet. -/
lemma sectionCech_objD_apply {ι : Type u} (U : ι → TopologicalSpace.Opens X)
    (F : X.PresheafOfModules) (q : ℕ)
    (t : ToType ((sectionCechCosimplicial U F).obj (SimplexCategory.mk q)))
    (σ : Fin (q + 2) → ι) :
    sectionCechProductEquiv U F (q + 1)
        (ConcreteCategory.hom
          (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial U F) q) t) σ
      = ∑ i : Fin (q + 2), (-1 : ℤ) ^ (i : ℕ) •
          ConcreteCategory.hom (sectionCechFaceRestr U F σ i)
            (sectionCechProductEquiv U F q t (σ ∘ (SimplexCategory.δ i).toOrderHom)) := by
  classical
  rw [sectionCechProductEquiv_apply,
      show ConcreteCategory.hom
            (Pi.π (fun σ : Fin (q + 2) → ι => F.presheaf.obj (Opposite.op (⨅ k, U (σ k)))) σ)
            (ConcreteCategory.hom
              (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial U F) q) t)
          = ConcreteCategory.hom
              (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial U F) q
                ≫ Pi.π (fun σ : Fin (q + 2) → ι => F.presheaf.obj (Opposite.op (⨅ k, U (σ k)))) σ) t
          from rfl,
      AlternatingCofaceMapComplex.objD, Preadditive.sum_comp, ab_hom_finsetSum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Preadditive.zsmul_comp]
  simp only [AddCommGrpCat.hom_zsmul, AddMonoidHom.smul_apply]
  rw [sectionCechProductEquiv_apply]
  congr 1
  have hmap : (sectionCechCosimplicial U F).map (SimplexCategory.δ i) ≫ Pi.π _ σ
      = Pi.π _ (σ ∘ (SimplexCategory.δ i).toOrderHom) ≫ sectionCechFaceRestr U F σ i :=
    Pi.lift_π _ σ
  rw [CosimplicialObject.δ, hmap]
  rfl

end SectionCechBridge

/-! ## Project-local Mathlib supplement — tilde-bridge and affine vanishing (L1 steps A, B, d)

The final stretch of the L1 categorical→module bridge for the **tilde sheaf**
`F = ~M`.  The previous section moved the abstract `Ab`-valued section {\v C}ech complex
to the shape of an alternating sum of presheaf restrictions
(`sectionCech_objD_apply`); here we identify, degreewise, those section groups with the
away-localisation coefficients `dCoeff` and the restrictions with the localisation
cofaces `dCoface`, via the per-σ comparison `φ_σ` (`IsLocalizedModule.iso`).  Transporting
the already-proven module exactness `SectionCechModule.dDiff_exact` across the resulting
degreewise additive isomorphism (`Function.Exact.of_ladder_addEquiv_of_exact`) discharges
the underlying-group exactness, which `sectionCech_isZero_homology_of_objD_exact` turns
into positive-degree homology vanishing of the section {\v C}ech complex
(`sectionCech_affine_vanishing`). -/

section SectionCechTilde

open AlgebraicTopology Scheme.Modules SectionCechModule CechLocalized AwayComparison

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) {ι : Type u} (s : ι → R)

set_option maxHeartbeats 800000 in
-- raised: the `IsLocalizedModule.ext` reduction over the heavy `modulesSpecToSheaf` section
-- types is defeq-intensive (the accessor-2 `~M` sections do not reduce cheaply).
/-- **Linear-level per-coface naturality** (`R`-linear).  The comparison `φ_σ`
(written here as the raw `IsLocalizedModule.iso ▸ symm`, definitionally `phiL` below)
intertwines the (accessor-2) {\v C}ech face restriction with the away-localisation coface
`dCoface`.  Proved by `IsLocalizedModule.ext`: both composites send the localisation unit
`toOpen M (D s_{σ∘dᵢ})` of `M` to the localisation unit `mkLinearMap (powers s_σ)`, by
`tilde.toOpen_res` (restriction commutes with `toOpen`), `iso_symm_comp`, and
`comparison_apply` (the defining property of `dCoface`).  Stated and proved *before* the
`phiL` abbreviation so its `IsLocalizedModule.ext` elaboration is not slowed by
fold/unfold attempts against `phiL` — keeping it within the heartbeat budget. -/
private lemma phiL_naturality {q : ℕ} (σ : Fin (q + 2) → ι) (i : Fin (q + 2)) :
    haveI := qcohSectionsAwayLocalized M s σ
    (IsLocalizedModule.iso (Submonoid.powers (∏ k, s (σ k)))
        (tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))).hom).symm.toLinearMap ∘ₗ
        ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
          (homOfLE (le_iInf (fun l => iInf_le _
            ((SimplexCategory.δ i).toOrderHom l)))).op).hom
      = (dCoface s M (q + 1) σ i) ∘ₗ
        (haveI := qcohSectionsAwayLocalized M s (σ ∘ i.succAbove)
         (IsLocalizedModule.iso (Submonoid.powers (∏ k, s ((σ ∘ i.succAbove) k)))
          (tilde.toOpen M (⨅ k,
            PrimeSpectrum.basicOpen (s ((σ ∘ i.succAbove) k)))).hom).symm.toLinearMap) := by
  haveI i1 := qcohSectionsAwayLocalized M s σ
  haveI i2 := qcohSectionsAwayLocalized M s (σ ∘ i.succAbove)
  -- Abstract the concrete face-restriction map as an opaque `g` BEFORE `IsLocalizedModule.ext`,
  -- so `ext` never whnf's the (heartbeat-heavy) `modulesSpecToSheaf` restriction.  `hg` records
  -- its `toOpen` compatibility (`tilde.toOpen_res`).
  set g := ((modulesSpecToSheaf.obj (tilde M)).presheaf.map
      (homOfLE (le_iInf (fun l => iInf_le _
        ((SimplexCategory.δ i).toOrderHom l)))).op).hom with hg_def
  have hg : ∀ m : M,
      g ((tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s ((σ ∘ i.succAbove) k)))).hom m)
        = (tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))).hom m := by
    intro m
    rw [hg_def]
    exact congrFun (congrArg (fun l => (l.hom : _ → _))
      (tilde.toOpen_res M (⨅ l, PrimeSpectrum.basicOpen
          (s ((σ ∘ (SimplexCategory.δ i).toOrderHom) l)))
        (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))
        (homOfLE (le_iInf (fun l => iInf_le _ ((SimplexCategory.δ i).toOrderHom l)))))) m
  clear_value g
  refine IsLocalizedModule.ext (Submonoid.powers (∏ k, s ((σ ∘ i.succAbove) k)))
    (tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s ((σ ∘ i.succAbove) k)))).hom
    (fun x => (Inverts.of_dvd (sprod_succAbove_dvd s σ i)
      (LocalizedModule.mkLinearMap (Submonoid.powers (sprod s σ)) M)).isUnit_powers x) ?_
  apply LinearMap.ext
  intro m
  -- unfold the `LinearEquiv`-coercion compositions to plain applications (defeq), avoiding
  -- the semilinear-instance mismatch that blocks `rw`/`simp` on `↑(iso).symm ∘ₗ g`
  change (IsLocalizedModule.iso (Submonoid.powers (∏ k, s (σ k)))
      (tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))).hom).symm
        (g ((tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s ((σ ∘ i.succAbove) k)))).hom m))
      = dCoface s M (q + 1) σ i
        ((IsLocalizedModule.iso (Submonoid.powers (∏ k, s ((σ ∘ i.succAbove) k)))
          (tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s ((σ ∘ i.succAbove) k)))).hom).symm
          ((tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s ((σ ∘ i.succAbove) k)))).hom m))
  -- the two `iso_symm_comp` facts in applied (defeq) form, so `rw` matches the goal
  have e1 : (IsLocalizedModule.iso (Submonoid.powers (∏ k, s (σ k)))
        (tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))).hom).symm
          ((tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))).hom m)
        = LocalizedModule.mkLinearMap (Submonoid.powers (∏ k, s (σ k))) M m :=
    DFunLike.congr_fun (IsLocalizedModule.iso_symm_comp (Submonoid.powers (∏ k, s (σ k)))
      (tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))).hom) m
  have e2 : (IsLocalizedModule.iso (Submonoid.powers (∏ k, s ((σ ∘ i.succAbove) k)))
        (tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s ((σ ∘ i.succAbove) k)))).hom).symm
          ((tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s ((σ ∘ i.succAbove) k)))).hom m)
        = LocalizedModule.mkLinearMap (Submonoid.powers (∏ k, s ((σ ∘ i.succAbove) k))) M m :=
    DFunLike.congr_fun (IsLocalizedModule.iso_symm_comp
      (Submonoid.powers (∏ k, s ((σ ∘ i.succAbove) k)))
      (tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s ((σ ∘ i.succAbove) k)))).hom) m
  rw [hg m, e1, e2]
  exact (comparison_apply
    (LocalizedModule.mkLinearMap (Submonoid.powers (sprod s (σ ∘ i.succAbove))) M)
    (LocalizedModule.mkLinearMap (Submonoid.powers (sprod s σ)) M) _ m).symm

/-- The presheaf of `O_{Spec R}`-modules underlying the tilde sheaf `~M`; the section
{\v C}ech complex of the affine vanishing is taken on this presheaf. -/
private noncomputable abbrev tP : (Spec R).PresheafOfModules :=
  (Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M)

/-- The standard basic-open cover family `i ↦ D(s i)`. -/
private abbrev tU : ι → TopologicalSpace.Opens (Spec R) :=
  fun i => PrimeSpectrum.basicOpen (s i)

/-- The per-σ comparison `R`-linear isomorphism between the (accessor-2 `ModuleCat`)
sections of `~M` over the {\v C}ech intersection `⨅ₖ D(s_{σ k})` and the away
localisation `M_{s_σ} = dCoeff`.  Both localise `M` at `Submonoid.powers (∏ₖ s_{σ k})`
(`qcohSectionsAwayLocalized`), so they are canonically isomorphic via
`IsLocalizedModule.iso`. -/
private noncomputable def phiL {n : ℕ} (σ : Fin n → ι) :
    ((modulesSpecToSheaf.obj (tilde M)).presheaf.obj
        (Opposite.op (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))))
      ≃ₗ[R] dCoeff s M σ :=
  haveI := qcohSectionsAwayLocalized M s σ
  (IsLocalizedModule.iso (Submonoid.powers (∏ k, s (σ k)))
    (tilde.toOpen M (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))).hom).symm

/-- The additive per-σ comparison `φ_σ`, the underlying `AddEquiv` of `phiL`, stated on
the accessor-1 (`Ab`-valued) section group so it composes with `sectionCechProductEquiv`. -/
private noncomputable def phi {n : ℕ} (σ : Fin n → ι) :
    ToType ((tP M).presheaf.obj (Opposite.op (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))))
      ≃+ dCoeff s M σ :=
  (phiL M s σ).toAddEquiv

/-- The raw `IsLocalizedModule.iso ▸ symm` underlying `phi` agrees with `phiL` applied —
the definitional bridge used to feed `phiL_naturality` into `phi_naturality`. -/
private lemma phi_eq_phiL {n : ℕ} (σ : Fin n → ι)
    (y : ToType ((tP M).presheaf.obj (Opposite.op (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))))) :
    phi M s σ y = phiL M s σ y := rfl

/-- **Abstract restriction bridge.** For any inclusion of opens, the accessor-1
(`Ab`-valued) presheaf restriction of `tP = ~M` and the accessor-2 (`ModuleCat`-valued)
restriction of `modulesSpecToSheaf (~M)` agree on underlying functions.  Stated for an
abstract morphism `g` so that the (otherwise heartbeat-exploding) defeq is checked once,
abstractly, rather than on the concrete {\v C}ech inclusion. -/
private lemma restr_bridge (V W : (Spec R).Opens) (g : V ⟶ W)
    (x : ToType ((tP M).presheaf.obj (Opposite.op W))) :
    ConcreteCategory.hom ((tP M).presheaf.map g.op) x
      = (((modulesSpecToSheaf.obj (tilde M)).presheaf.map g.op).hom) x := rfl

set_option maxHeartbeats 1000000 in
-- raised: feeds `phiL_naturality` through the same defeq-heavy section types via `restr_bridge`.
/-- **Additive per-coface naturality** (accessor-1, the form the coface match consumes).
The additive comparison `φ_σ` intertwines the accessor-1 {\v C}ech face restriction
`sectionCechFaceRestr` with the away-localisation coface `dCoface`.  Obtained from the
linear naturality `phiL_naturality` via the accessor bridge `restr_bridge`. -/
private lemma phi_naturality {q : ℕ} (σ : Fin (q + 2) → ι) (i : Fin (q + 2))
    (x : ToType ((tP M).presheaf.obj (Opposite.op
        (⨅ l, PrimeSpectrum.basicOpen (s ((σ ∘ (SimplexCategory.δ i).toOrderHom) l)))))) :
    phi M s σ (ConcreteCategory.hom (sectionCechFaceRestr (tU s) (tP M) σ i) x)
      = dCoface s M (q + 1) σ i (phi M s (σ ∘ i.succAbove) x) := by
  have hb := restr_bridge M
    (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))
    (⨅ l, PrimeSpectrum.basicOpen (s ((σ ∘ (SimplexCategory.δ i).toOrderHom) l)))
    (homOfLE (le_iInf (fun l => iInf_le _ ((SimplexCategory.δ i).toOrderHom l)))) x
  simp only [sectionCechFaceRestr, tU]
  refine Eq.trans (congrArg (phi M s σ) hb) ?_
  exact DFunLike.congr_fun (phiL_naturality M s σ i) x

/-- **Additive product equivalence** for the degree-`p` section {\v C}ech term: the
underlying `AddEquiv` upgrade of `sectionCechProductEquiv` (additive because each
coordinate is the underlying group map of a categorical projection `Pi.π`). -/
private noncomputable def sectionProdAddEquiv (p : ℕ) :
    ToType ((sectionCechCosimplicial (tU s) (tP M)).obj (SimplexCategory.mk p))
      ≃+ (∀ σ : Fin (p + 1) → ι,
            ToType ((tP M).presheaf.obj
              (Opposite.op (⨅ k, PrimeSpectrum.basicOpen (s (σ k)))))) where
  toFun := sectionCechProductEquiv (tU s) (tP M) p
  invFun := (sectionCechProductEquiv (tU s) (tP M) p).symm
  left_inv := (sectionCechProductEquiv (tU s) (tP M) p).left_inv
  right_inv := (sectionCechProductEquiv (tU s) (tP M) p).right_inv
  map_add' x y := by
    funext σ
    simp only [sectionCechProductEquiv_apply, Pi.add_apply]
    exact map_add _ x y

/-- The degree-`p` comparison `AddEquiv` `ToType(∏ᶜ_σ ~M(D s_σ)) ≃+ ∏_σ M_{s_σ}`: the
additive product equivalence followed by the coordinatewise comparison `φ_σ`.  These are
the vertical maps of the ladder transporting `dDiff`-exactness to `objD`-exactness. -/
private noncomputable def sectionToModuleAddEquiv (p : ℕ) :
    ToType ((sectionCechCosimplicial (tU s) (tP M)).obj (SimplexCategory.mk p))
      ≃+ (∀ σ : Fin (p + 1) → ι, dCoeff s M σ) :=
  (sectionProdAddEquiv M s p).trans (AddEquiv.piCongrRight (fun σ => phi M s σ))

/-- Coordinate description of `sectionToModuleAddEquiv`. -/
private lemma sectionToModuleAddEquiv_apply (p : ℕ)
    (y : ToType ((sectionCechCosimplicial (tU s) (tP M)).obj (SimplexCategory.mk p)))
    (σ : Fin (p + 1) → ι) :
    sectionToModuleAddEquiv M s p y σ = phi M s σ (sectionCechProductEquiv (tU s) (tP M) p y σ) :=
  rfl

/-- Reading the inverse comparison coordinatewise: applying `sectionToModuleAddEquiv.symm`
to a module tuple `z` and projecting recovers `φ_τ⁻¹ (z τ)`. -/
private lemma sectionProdEquiv_symm_apply (q : ℕ) (z : ∀ σ : Fin (q + 1) → ι, dCoeff s M σ)
    (τ : Fin (q + 1) → ι) :
    sectionCechProductEquiv (tU s) (tP M) q ((sectionToModuleAddEquiv M s q).symm z) τ
      = (phi M s τ).symm (z τ) := by
  have h : sectionCechProductEquiv (tU s) (tP M) q ((sectionToModuleAddEquiv M s q).symm z)
      = sectionProdAddEquiv M s q ((sectionProdAddEquiv M s q).symm
          ((AddEquiv.piCongrRight (fun σ => phi M s σ)).symm z)) := rfl
  rw [h, AddEquiv.apply_symm_apply]
  rfl

/-- **(c2 + tilde-bridge) Coface match** (`lem:section_cech_coface_match`): under the
degreewise comparison `sectionToModuleAddEquiv`, the section {\v C}ech coface differential
`objD` matches the away-localisation module differential `dDiff`.  Combines the abstract
cosimplicial unfold `sectionCech_objD_apply` with the per-coface tilde-bridge
`phi_naturality`. -/
private lemma sectionCechCofaceMatch (q : ℕ) (z : ∀ σ : Fin (q + 1) → ι, dCoeff s M σ) :
    sectionToModuleAddEquiv M s (q + 1)
        (ConcreteCategory.hom
          (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial (tU s) (tP M)) q)
          ((sectionToModuleAddEquiv M s q).symm z))
      = dDiff s M (q + 1) z := by
  funext σ
  rw [sectionToModuleAddEquiv_apply, sectionCech_objD_apply, dDiff_apply, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_zsmul, sectionProdEquiv_symm_apply, phi_naturality]
  exact congrArg ((-1 : ℤ) ^ (i : ℕ) • dCoface s M (q + 1) σ i ·)
    (AddEquiv.apply_symm_apply (phi M s (σ ∘ i.succAbove)) (z (σ ∘ i.succAbove)))

/-- **(c, ladder transport) Underlying-group exactness** of two consecutive section {\v C}ech
coface differentials (`lem:section_cech_ab_exact`).  Transports the `R`-module exactness
`SectionCechModule.dDiff_exact` across the degreewise additive comparison
`sectionToModuleAddEquiv` (the squares are `sectionCechCofaceMatch`) via
`Function.Exact.of_ladder_addEquiv_of_exact`. -/
private lemma sectionCechAbExact [Finite ι] (hs : Ideal.span (Set.range s) = ⊤) (q : ℕ) :
    Function.Exact
      (ConcreteCategory.hom
        (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial (tU s) (tP M)) q))
      (ConcreteCategory.hom
        (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial (tU s) (tP M)) (q + 1))) := by
  have sq : ∀ r : ℕ,
      (ConcreteCategory.hom
            (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial (tU s) (tP M)) r)).comp
          (sectionToModuleAddEquiv M s r).symm.toAddMonoidHom
        = (sectionToModuleAddEquiv M s (r + 1)).symm.toAddMonoidHom.comp
            (dDiff s M (r + 1)).toAddMonoidHom := by
    intro r
    apply AddMonoidHom.ext
    intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [AddEquiv.eq_symm_apply]
    exact sectionCechCofaceMatch M s r z
  exact Function.Exact.of_ladder_addEquiv_of_exact
    (sectionToModuleAddEquiv M s q).symm (sectionToModuleAddEquiv M s (q + 1)).symm
    (sectionToModuleAddEquiv M s (q + 2)).symm (sq q) (sq (q + 1)) (dDiff_exact s M hs q)

/-- **(c, ladder transport) Underlying-group exactness over a standard *sub*cover of `D(f)`.**
Same ladder transport as `sectionCechAbExact`, but the `R`-module exactness input is the
route-B `SectionCechModule.dDiff_exact_of_localizationAway` (the cover spans the unit ideal only
after change of base to `R_f`), so `s` need not span the unit ideal of `R`. -/
private lemma sectionCechAbExact_loc [Finite ι] (f : R)
    (hmem : ∀ i, ∃ k, f ∣ s i ^ k)
    (hspan : Ideal.span (Set.range (fun i => algebraMap R (Localization.Away f) (s i))) = ⊤)
    (q : ℕ) :
    Function.Exact
      (ConcreteCategory.hom
        (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial (tU s) (tP M)) q))
      (ConcreteCategory.hom
        (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial (tU s) (tP M)) (q + 1))) := by
  have sq : ∀ r : ℕ,
      (ConcreteCategory.hom
            (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial (tU s) (tP M)) r)).comp
          (sectionToModuleAddEquiv M s r).symm.toAddMonoidHom
        = (sectionToModuleAddEquiv M s (r + 1)).symm.toAddMonoidHom.comp
            (dDiff s M (r + 1)).toAddMonoidHom := by
    intro r
    apply AddMonoidHom.ext
    intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [AddEquiv.eq_symm_apply]
    exact sectionCechCofaceMatch M s r z
  exact Function.Exact.of_ladder_addEquiv_of_exact
    (sectionToModuleAddEquiv M s q).symm (sectionToModuleAddEquiv M s (q + 1)).symm
    (sectionToModuleAddEquiv M s (q + 2)).symm (sq q) (sq (q + 1))
    (dDiff_exact_of_localizationAway s M f hmem hspan q)

/-- **(c, ladder transport) Underlying-group exactness over a cover of a *general affine open*.**
Same ladder transport as `sectionCechAbExact`, but the `R`-module exactness input is the route-B1
`SectionCechModule.dDiff_exact_of_affineCover` (the cover spans the unit ideal only after change of
base to `S = Γ(V)`), so `s` need not span the unit ideal of `R` and `V = ⨆ᵢ D(sᵢ)` need not be a
single `D(f)`. -/
private lemma sectionCechAbExact_affine [Finite ι]
    (S : Type u) [CommRing S] [Algebra R S]
    (hspan : Ideal.span (Set.range (fun i => algebraMap R S (s i))) = ⊤)
    (hloc : ∀ {n : ℕ} (σ : Fin (n + 1) → ι),
      IsLocalization (Submonoid.powers (sprod s σ))
        (Localization (Submonoid.powers (algebraMap R S (sprod s σ)))))
    (q : ℕ) :
    Function.Exact
      (ConcreteCategory.hom
        (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial (tU s) (tP M)) q))
      (ConcreteCategory.hom
        (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial (tU s) (tP M)) (q + 1))) := by
  have sq : ∀ r : ℕ,
      (ConcreteCategory.hom
            (AlternatingCofaceMapComplex.objD (sectionCechCosimplicial (tU s) (tP M)) r)).comp
          (sectionToModuleAddEquiv M s r).symm.toAddMonoidHom
        = (sectionToModuleAddEquiv M s (r + 1)).symm.toAddMonoidHom.comp
            (dDiff s M (r + 1)).toAddMonoidHom := by
    intro r
    apply AddMonoidHom.ext
    intro z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      LinearMap.toAddMonoidHom_coe]
    rw [AddEquiv.eq_symm_apply]
    exact sectionCechCofaceMatch M s r z
  exact Function.Exact.of_ladder_addEquiv_of_exact
    (sectionToModuleAddEquiv M s q).symm (sectionToModuleAddEquiv M s (q + 1)).symm
    (sectionToModuleAddEquiv M s (q + 2)).symm (sq q) (sq (q + 1))
    (dDiff_exact_of_affineCover s M S hspan hloc q)

end SectionCechTilde

/-- **Section {\v C}ech homology vanishes in positive degrees** (`lem:section_cech_homology_exact`),
tilde case `F = ~M`.  Reads off positive-degree homology vanishing of the section {\v C}ech
complex from the underlying-group exactness `sectionCechAbExact` via the homological precursor
`sectionCech_isZero_homology_of_objD_exact`. -/
theorem sectionCech_homology_exact {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {ι : Type u} [Finite ι] (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    (p : ℕ) (hp : 1 ≤ p) :
    IsZero ((sectionCechComplex (fun i => PrimeSpectrum.basicOpen (s i))
      ((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M))).homology p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact sectionCech_isZero_homology_of_objD_exact _ _ q (sectionCechAbExact M s hs q)

/-- **Standard-cover {\v C}ech vanishing on affines, section form** (`lem:cech_acyclic_affine`,
section form).  For a spanning family `s : ι → R` and the tilde sheaf `~M` of an `R`-module
`M`, the section {\v C}ech complex of the associated standard affine cover has vanishing
cohomology in all positive degrees.  This is the named affine-vanishing target; the general
quasi-coherent `F` is reduced to this tilde case via `F ≅ ~(ΓF)` (Stacks 01I8, deferred). -/
theorem sectionCech_affine_vanishing {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {ι : Type u} [Finite ι] (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    (p : ℕ) (hp : 1 ≤ p) :
    IsZero ((sectionCechComplex (fun i => PrimeSpectrum.basicOpen (s i))
      ((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M))).homology p) :=
  sectionCech_homology_exact M s hs p hp

/-- **Standard *sub*cover {\v C}ech vanishing for the tilde sheaf — the route-B residual**
(`lem:affine_cech_vanishing_tilde_subcover`, Stacks 02KG via
`lemma-cech-cohomology-quasi-coherent-trivial`).  Let `s : ι → R` be a finite family with
`D(f) = ⨆ᵢ D(sᵢ)` (so `{sᵢ}` covers the basic open `D(f)`, spanning only `√(f)`, NOT necessarily
the unit ideal of `R`).  Then the section {\v C}ech complex of `~M` over `{D(sᵢ)}` has vanishing
homology in all positive degrees.

This is the residual `htilde` of the 02KG cone: the cover is of a *proper* `D(f)`, so it is proved
by change of base to `R_f = Localization.Away f` (where `{sᵢ/1}` does span the unit ideal),
through `sectionCechAbExact_loc` (which feeds the change-of-ring exactness
`SectionCechModule.dDiff_exact_of_localizationAway` into the tilde-bridge ladder).  The covering
hypothesis `hcov` supplies both the `R_f`-spanning datum (mirroring
`affine_cover_span_localizationAway`) and the radical membership `sᵢ ∈ √(f)`. -/
theorem sectionCech_homology_exact_of_localizationAway {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {ι : Type u} [Finite ι] (s : ι → R) (f : R)
    (hcov : (PrimeSpectrum.basicOpen f : (Spec R).Opens)
      = ⨆ i, PrimeSpectrum.basicOpen (s i))
    (p : ℕ) (hp : 1 ≤ p) :
    IsZero ((sectionCechComplex (fun i => PrimeSpectrum.basicOpen (s i))
      ((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M))).homology p) := by
  -- each `sᵢ` lies in `√(f)` since `D(sᵢ) ⊆ D(f)`.
  have hmem : ∀ i, ∃ k, f ∣ s i ^ k := by
    intro i
    have hle : (PrimeSpectrum.basicOpen (s i) : (Spec R).Opens) ≤ PrimeSpectrum.basicOpen f := by
      rw [hcov]; exact le_iSup (fun i => PrimeSpectrum.basicOpen (s i)) i
    obtain ⟨k, hk⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff (s i) f).mp hle
    exact ⟨k, Ideal.mem_span_singleton.mp hk⟩
  -- `{sᵢ/1}` spans the unit ideal of `R_f` (mirror of `affine_cover_span_localizationAway`).
  have hspan : Ideal.span
      (Set.range (fun i => algebraMap R (Localization.Away f) (s i))) = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    simp only [← PrimeSpectrum.comap_basicOpen]
    rw [← map_iSup, ← hcov, PrimeSpectrum.comap_basicOpen, eq_top_iff]
    rintro q -
    rw [PrimeSpectrum.mem_basicOpen]
    exact fun hu => q.isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hu (IsLocalization.Away.algebraMap_isUnit f))
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact sectionCech_isZero_homology_of_objD_exact _ _ q (sectionCechAbExact_loc M s f hmem hspan q)

/-- **Cover of a general affine open: {\v C}ech vanishing for the tilde sheaf — change-of-base form**
(`lem:affine_cech_vanishing_general_seed`, Stacks 02KG over an arbitrary affine open).  For a finite
family `s : ι → R` whose distinguished opens `D(sᵢ)` cover a *general affine open* `V = ⨆ᵢ D(sᵢ)` of
`Spec R` (not necessarily a single `D(f)`), the positive-degree section {\v C}ech cohomology of the
tilde sheaf `~M` over `{D(sᵢ)}` vanishes — provided the change-of-base certificate `(S, hspan, hloc)`:
an `R`-algebra `S` (in practice `S = Γ(V, 𝒪)`) in which the images `sᵢ ↦ S` span the unit ideal
(`hspan`), together with the per-{\v C}ech-multi-index localisation datum `hloc` (encoding `D(s_σ) ⊆ V`,
so that the `S`-localisation `(M⊗_R S)_{s̄_σ}` is an `R`-localisation of `M` at `powers (s_σ)`).

This is the route-B1 analogue of `sectionCech_homology_exact_of_localizationAway`: the `D(f)` case takes
`S = Localization.Away f`, where `hspan` is `affine_cover_span_localizationAway` and `hloc` is automatic
(`Localization.Away` of an `R`-element is already an `R`-localisation); the general affine `V` needs the
genuine `S = Γ(V)` and the geometric `hloc`.  Both are discharged at the call site from `IsAffineOpen V`
via `IsAffineOpen.isLocalization_of_eq_basicOpen`. -/
theorem sectionCech_homology_exact_of_affineCover {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {ι : Type u} [Finite ι] (s : ι → R)
    (S : Type u) [CommRing S] [Algebra R S]
    (hspan : Ideal.span (Set.range (fun i => algebraMap R S (s i))) = ⊤)
    (hloc : ∀ {n : ℕ} (σ : Fin (n + 1) → ι),
      IsLocalization (Submonoid.powers (CechLocalized.sprod s σ))
        (Localization (Submonoid.powers (algebraMap R S (CechLocalized.sprod s σ)))))
    (p : ℕ) (hp : 1 ≤ p) :
    IsZero ((sectionCechComplex (fun i => PrimeSpectrum.basicOpen (s i))
      ((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M))).homology p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact sectionCech_isZero_homology_of_objD_exact _ _ q
    (sectionCechAbExact_affine M s S hspan hloc q)

end AlgebraicGeometry

/-! ## Project-local Mathlib supplement — general-affine-open seed (geometric assembly)

The final geometric wrapper `sectionCech_homology_exact_of_affineOpen` discharges the change-of-base
data `(S, hspan, hloc)` of `sectionCech_homology_exact_of_affineCover` from `IsAffineOpen V`, with
`S := Γ(V, 𝒪)`.  The section-restriction algebra `Algebra Γ(V) Γ(D a)` is NOT a synthesizable instance
(it depends on the inclusion `D a ⟶ V`); it is provided explicitly as the `.toAlgebra` of the
restriction map — the same one `IsAffineOpen.isLocalization_of_eq_basicOpen` constructs — and the
scalar tower `R → Γ(V) → Γ(D a)` is `rfl`-definitional. -/

namespace AlgebraicGeometry

open AlgebraicTopology Scheme.Modules

/-- **Basic open of a restricted global section** (geometric brick for the general-affine seed).  For
the affine scheme `Spec R`, an open `V`, and `a : R`, the basic open of the restriction
`algebraMap R Γ(V) a` of the global section `a` to `V` is `V ⊓ D(a)`.  The restriction factors through
`Γ(⊤)` *definitionally* (`algebraMap R Γ(V) a = (Spec R).presheaf.map _ (algebraMap R Γ(⊤) a)`, `rfl`),
so `Scheme.basicOpen_res` gives `V ⊓ (Spec R).basicOpen (a : Γ(⊤))` and `basicOpen_eq_of_affine`
identifies `(Spec R).basicOpen (a : Γ(⊤)) = D(a)`.  (Avoids the `Algebra Γ(⊤) Γ(V)` scoped instance,
which is shadowed in this file's open-context.)  Project-local: supplies both the spanning datum
`hspan` and the per-`σ` localisation datum `hloc` of the change-of-base seed. -/
private lemma basicOpen_algMap_section {R : CommRingCat.{u}} (V : (Spec R).Opens) (a : ↥R) :
    (Spec R).basicOpen (algebraMap ↥R ↥((Spec R).presheaf.obj (Opposite.op V)) a)
    = V ⊓ PrimeSpectrum.basicOpen a := by
  have key : (Spec R).basicOpen (algebraMap ↥R ↥((Spec R).presheaf.obj (Opposite.op ⊤)) a)
      = PrimeSpectrum.basicOpen a := basicOpen_eq_of_affine a
  rw [show algebraMap ↥R ↥((Spec R).presheaf.obj (Opposite.op V)) a
        = ConcreteCategory.hom ((Spec R).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op)
            (algebraMap ↥R ↥((Spec R).presheaf.obj (Opposite.op ⊤)) a) from rfl,
      (Spec R).basicOpen_res, key]

/-- **Cover of a general affine open: {\v C}ech vanishing for the tilde sheaf** (Stacks 02KG,
`lemma-cech-cohomology-quasi-coherent-trivial`, generalised from `D(f)` to an arbitrary affine open).
Let `s : ι → R` be a finite family whose distinguished opens `D(sᵢ)` cover an **affine** open
`V = ⨆ᵢ D(sᵢ)` of `Spec R` (`hV : IsAffineOpen V`; `V` need NOT be a single `D(f)`).  Then the section
{\v C}ech complex of the tilde sheaf `~M` over `{D(sᵢ)}` has vanishing homology in all positive degrees.

This is the residual `htilde` of the enlarged (general-affine) 02KG cone — the seed
`affine_cech_vanishing_qcoh_general_of_tildeVanishing` consumes exactly this shape.  Discharged by
`sectionCech_homology_exact_of_affineCover` with `S := Γ(V)`: the spanning datum `hspan` is
`IsAffineOpen.iSup_basicOpen_eq_self_iff` (the `D(sᵢ)` cover `V`), and the per-{\v C}ech-multi-index
localisation datum `hloc` comes from `IsAffineOpen.isLocalization_of_eq_basicOpen` (each `D(s_σ) ⊆ V`)
transported across the `R`-algebra iso `Γ(D(s_σ)) ≃ₐ[R] Localization (powers (s̄_σ))`. -/
theorem sectionCech_homology_exact_of_affineOpen {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    {ι : Type u} [Finite ι] (s : ι → R)
    (hV : IsAffineOpen (X := Spec R) (⨆ i, PrimeSpectrum.basicOpen (s i)))
    (p : ℕ) (hp : 1 ≤ p) :
    IsZero ((sectionCechComplex (fun i => PrimeSpectrum.basicOpen (s i))
      ((Scheme.Modules.toPresheafOfModules (Spec R)).obj (tilde M))).homology p) := by
  set V := (⨆ i, PrimeSpectrum.basicOpen (s i) : (Spec R).Opens) with hVdef
  -- the restricted family `s̄ᵢ = algebraMap R Γ(V) sᵢ` spans the unit ideal of `S = Γ(V)`.
  have hspan : Ideal.span (Set.range
      (fun i => algebraMap ↥R ↥((Spec R).presheaf.obj (Opposite.op V)) (s i))) = ⊤ := by
    rw [← hV.iSup_basicOpen_eq_self_iff, iSup_range']
    simp_rw [basicOpen_algMap_section V]
    rw [← inf_iSup_eq, ← hVdef, inf_idem]
  -- per Čech multi-index `σ`: the `S`-localisation at `s̄_σ` is an `R`-localisation at `powers (s_σ)`.
  have hloc : ∀ {n : ℕ} (σ : Fin (n + 1) → ι),
      IsLocalization (Submonoid.powers (CechLocalized.sprod s σ))
        (Localization (Submonoid.powers (algebraMap ↥R
          ↥((Spec R).presheaf.obj (Opposite.op V)) (CechLocalized.sprod s σ)))) := by
    intro n σ
    have hDaV : (PrimeSpectrum.basicOpen (CechLocalized.sprod s σ) : (Spec R).Opens) ≤ V := by
      have hsp : (PrimeSpectrum.basicOpen (CechLocalized.sprod s σ) : (Spec R).Opens)
          = ⨅ k, PrimeSpectrum.basicOpen (s (σ k)) := (basicOpen_sprod (n + 1) s σ).symm
      rw [hsp]
      exact le_trans (iInf_le _ 0) (le_iSup (fun i => PrimeSpectrum.basicOpen (s i)) (σ 0))
    set a := CechLocalized.sprod s σ with ha
    have e : (PrimeSpectrum.basicOpen a : (Spec R).Opens)
        = (Spec R).basicOpen (algebraMap ↥R ↥((Spec R).presheaf.obj (Opposite.op V)) a) := by
      rw [basicOpen_algMap_section V a]; exact (inf_of_le_right hDaV).symm
    -- pin the section-restriction algebra `Γ(V) → Γ(D a)` (the ad-hoc `.toAlgebra` that
    -- `isLocalization_of_eq_basicOpen` constructs from the inclusion `D a ⟶ V`) so the algEquiv
    -- and `restrictScalars` below resolve it consistently.
    letI algVDa : Algebra ↥((Spec R).presheaf.obj (Opposite.op V))
        ↥((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen a))) :=
      ((Spec R).presheaf.map (homOfLE hDaV).op).hom.toAlgebra
    haveI towerRVDa : IsScalarTower ↥R ↥((Spec R).presheaf.obj (Opposite.op V))
        ↥((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen a))) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI hS : IsLocalization.Away
        (algebraMap ↥R ↥((Spec R).presheaf.obj (Opposite.op V)) a)
        ↥((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen a))) :=
      hV.isLocalization_of_eq_basicOpen
        (algebraMap ↥R ↥((Spec R).presheaf.obj (Opposite.op V)) a) (homOfLE hDaV) e
    let eAlg : ↥((Spec R).presheaf.obj (Opposite.op (PrimeSpectrum.basicOpen a)))
        ≃ₐ[↥((Spec R).presheaf.obj (Opposite.op V))]
          Localization (Submonoid.powers
            (algebraMap ↥R ↥((Spec R).presheaf.obj (Opposite.op V)) a)) :=
      IsLocalization.algEquiv (Submonoid.powers
        (algebraMap ↥R ↥((Spec R).presheaf.obj (Opposite.op V)) a)) _ _
    exact IsLocalization.isLocalization_of_algEquiv (Submonoid.powers a) (eAlg.restrictScalars ↥R)
  exact sectionCech_homology_exact_of_affineCover M s
    ↥((Spec R).presheaf.obj (Opposite.op V)) hspan hloc p hp

end AlgebraicGeometry
