module

public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Mathlib.Data.Finset.Insert

/-!
# Finite multidimensional geometric series

For a `Finset T` and a family of complex numbers `(z_a)_{a ∈ T}` with
`‖z_a‖ < 1` for each `a ∈ T`, we have the multidimensional geometric-series
identity
$$
\prod_{a \in T} \frac{1}{1 - z_a}
  = \sum_{f : T \to \mathbb{N}} \prod_{a \in T} z_a^{f(a)}.
$$

We prove this by induction on `T`, using the binary Cauchy product
`tsum_mul_tsum_of_summable_norm` and the geometric series for a single
factor. Norm-summability of the multivariate sum is part of the
strengthened induction hypothesis.

This is the analytic core needed for the rational-prime local Euler factor
identity (REF-21c2a2A).

## Main results

* `BernoulliRegular.WeakSplitting.tsum_const_one_of_isEmpty_pi`:
  the tsum of `1` over the function type from an empty type to `ℕ` is `1`.
* `BernoulliRegular.WeakSplitting.insertFunEquiv`: the equivalence
  `(↥(insert a₀ T) → ℕ) ≃ ℕ × (↥T → ℕ)` for `a₀ ∉ T`.
* `BernoulliRegular.WeakSplitting.norm_summable_prod_pow`: norm-summability
  of `f ↦ ‖∏ a ∈ T.attach, (z a.1) ^ (f a)‖`.
* `BernoulliRegular.WeakSplitting.prod_one_sub_inv_eq_tsum_pi`: the
  multidimensional geometric-series identity.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular

namespace WeakSplitting

open Filter Topology Finset

/--
The tsum of the constant function `1 : ℂ` over the function type `β → ℕ`,
when `β` is empty, equals `1`. The function type is then a singleton.
-/
theorem tsum_const_one_of_isEmpty_pi {β : Type*} [IsEmpty β] :
    ∑' (_ : β → ℕ), (1 : ℂ) = 1 := by
  haveI : Unique (β → ℕ) := Pi.uniqueOfIsEmpty _
  exact (hasSum_unique _).tsum_eq

/--
The equivalence between functions `↥(insert a₀ T) → ℕ` and pairs
`ℕ × (↥T → ℕ)`, splitting `f` into its value at `a₀` and the restriction
to `↥T`.
-/
def insertFunEquiv {α : Type*} [DecidableEq α] {T : Finset α} {a₀ : α} (h : a₀ ∉ T) :
    (↥(insert a₀ T) → ℕ) ≃ ℕ × (↥T → ℕ) where
  toFun f := (f ⟨a₀, Finset.mem_insert_self _ _⟩,
    fun ⟨a, ha⟩ => f ⟨a, Finset.mem_insert_of_mem ha⟩)
  invFun p := fun ⟨a, ha⟩ =>
    if heq : a = a₀ then p.1
    else p.2 ⟨a, (Finset.mem_insert.mp ha).resolve_left heq⟩
  left_inv f := by
    funext ⟨a, ha⟩
    by_cases heq : a = a₀
    · subst heq; simp
    · simp [heq]
  right_inv := by
    rintro ⟨n, g⟩
    refine Prod.ext ?_ ?_
    · simp
    · funext ⟨a, ha⟩
      have hne : a ≠ a₀ := fun heq => h (heq ▸ ha)
      simp [hne]

/--
Splitting the product over `(insert a₀ T').attach` for `a₀ ∉ T'`:
the value at `⟨a₀, _⟩` separates from the product over `T'.attach`
(with appropriate subtype embedding).
-/
private lemma prod_insert_attach_split {α : Type*} [DecidableEq α] {T' : Finset α}
    {a₀ : α} (h : a₀ ∉ T') (F : ↥(insert a₀ T') → ℂ) :
    ∏ a ∈ (insert a₀ T').attach, F a =
      F ⟨a₀, Finset.mem_insert_self _ _⟩ *
        ∏ a ∈ T'.attach, F ⟨a.1, Finset.mem_insert_of_mem a.2⟩ := by
  classical
  rw [Finset.attach_insert, Finset.prod_insert]
  · congr 1
    rw [Finset.prod_image]
    intro x _ y _ hxy
    simp only [Subtype.mk.injEq] at hxy
    exact Subtype.ext hxy
  · intro hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨x, _, hxeq⟩ := hmem
    simp only [Subtype.mk.injEq] at hxeq
    exact h (hxeq ▸ x.2)

/--
**Strengthened induction (REF-21c2a2A core).** For a finset `T` and a complex
family `z` with `‖z a‖ < 1` for `a ∈ T`, the multivariate geometric sum
`f ↦ ∏ a ∈ T.attach, (z a.1) ^ (f a)` is norm-summable, and the product of
inverse local factors equals the tsum.
-/
private lemma norm_summable_and_prod_eq {α : Type*} (T : Finset α)
    (z : α → ℂ) (hz : ∀ a ∈ T, ‖z a‖ < 1) :
    Summable (fun f : ↥T → ℕ => ‖∏ a ∈ T.attach, (z a.1) ^ (f a)‖) ∧
      ∏ a ∈ T, (1 - z a)⁻¹ =
        ∑' (f : ↥T → ℕ), ∏ a ∈ T.attach, (z a.1) ^ (f a) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    haveI : IsEmpty (↥(∅ : Finset α)) :=
      ⟨fun a => absurd a.2 (Finset.notMem_empty _)⟩
    haveI : Unique (↥(∅ : Finset α) → ℕ) := Pi.uniqueOfIsEmpty _
    refine ⟨?_, ?_⟩
    · simp only [Finset.attach_empty, Finset.prod_empty, norm_one]
      exact (hasSum_unique (fun _ : ↥(∅ : Finset α) → ℕ => (1 : ℝ))).summable
    · simp only [Finset.attach_empty, Finset.prod_empty]
      exact (tsum_const_one_of_isEmpty_pi (β := ↥(∅ : Finset α))).symm
  | @insert a₀ T' h ih =>
    obtain ⟨ih_sum, ih_eq⟩ := ih (fun a ha => hz a (Finset.mem_insert_of_mem ha))
    have hz_a₀ : ‖z a₀‖ < 1 := hz a₀ (Finset.mem_insert_self _ _)
    have h_geom_sum : Summable (fun n : ℕ => ‖(z a₀) ^ n‖) :=
      summable_norm_geometric_of_norm_lt_one hz_a₀
    have h_pair_sum :
        Summable (fun p : ℕ × (↥T' → ℕ) =>
          ‖(z a₀) ^ p.1 * ∏ a ∈ T'.attach, (z a.1) ^ (p.2 a)‖) :=
      Summable.mul_norm
        (f := fun n : ℕ => (z a₀) ^ n)
        (g := fun k : ↥T' → ℕ => ∏ a ∈ T'.attach, (z a.1) ^ (k a))
        h_geom_sum ih_sum
    have prod_decomp_pair : ∀ p : ℕ × (↥T' → ℕ),
        ∏ a ∈ (insert a₀ T').attach, (z a.1) ^ ((insertFunEquiv h).symm p a) =
          (z a₀) ^ p.1 * ∏ a ∈ T'.attach, (z a.1) ^ (p.2 a) := by
      rintro ⟨n, g⟩
      rw [prod_insert_attach_split h
        (fun a => (z a.1) ^ ((insertFunEquiv h).symm (n, g) a))]
      simp only [insertFunEquiv, Equiv.coe_fn_symm_mk, dite_true]
      congr 1
      apply Finset.prod_congr rfl
      intro a _
      have hne : a.1 ≠ a₀ := fun heq => h (heq ▸ a.2)
      simp [hne]
    refine ⟨?_, ?_⟩
    · rw [← (insertFunEquiv h).symm.summable_iff]
      convert h_pair_sum using 1
      funext p
      simp only [Function.comp_apply]
      rw [prod_decomp_pair p]
    · rw [Finset.prod_insert h, ih_eq,
        show (1 - z a₀)⁻¹ = ∑' n : ℕ, (z a₀) ^ n from
          (tsum_geometric_of_norm_lt_one hz_a₀).symm,
        tsum_mul_tsum_of_summable_norm h_geom_sum ih_sum,
        show (fun p : ℕ × (↥T' → ℕ) =>
            (z a₀) ^ p.1 * ∏ a ∈ T'.attach, (z a.1) ^ (p.2 a)) =
          fun p : ℕ × (↥T' → ℕ) =>
            ∏ a ∈ (insert a₀ T').attach, (z a.1) ^ ((insertFunEquiv h).symm p a) by
          funext p; rw [prod_decomp_pair p]]
      exact (insertFunEquiv h).symm.tsum_eq
        (fun f : ↥(insert a₀ T') → ℕ =>
          ∏ a ∈ (insert a₀ T').attach, (z a.1) ^ (f a))

/--
**Norm-summability of the multivariate geometric series (REF-21c2a2A).**
For a finset `T` and a complex family `z` with `‖z a‖ < 1` on `T`, the
function `f ↦ ‖∏ a ∈ T.attach, (z a.1) ^ (f a)‖` is summable over
`↥T → ℕ`.
-/
theorem norm_summable_prod_pow {α : Type*} (T : Finset α) (z : α → ℂ)
    (hz : ∀ a ∈ T, ‖z a‖ < 1) :
    Summable (fun f : ↥T → ℕ => ‖∏ a ∈ T.attach, (z a.1) ^ (f a)‖) :=
  (norm_summable_and_prod_eq T z hz).1

/--
**Multidimensional geometric-series identity (REF-21c2a2A).** For a finset
`T` and a complex family `z` with `‖z a‖ < 1` on `T`, the product of inverse
local factors equals the tsum over `↥T → ℕ` of the multivariate monomial.
-/
theorem prod_one_sub_inv_eq_tsum_pi {α : Type*} (T : Finset α) (z : α → ℂ)
    (hz : ∀ a ∈ T, ‖z a‖ < 1) :
    ∏ a ∈ T, (1 - z a)⁻¹ =
      ∑' (f : ↥T → ℕ), ∏ a ∈ T.attach, (z a.1) ^ (f a) :=
  (norm_summable_and_prod_eq T z hz).2

end WeakSplitting

end BernoulliRegular
