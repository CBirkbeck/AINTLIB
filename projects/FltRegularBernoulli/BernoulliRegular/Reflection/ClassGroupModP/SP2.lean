import BernoulliRegular.Reflection.ClassGroupModP.AtomC
import BernoulliRegular.Reflection.ClassGroupModP.Plus
import BernoulliRegular.Reflection.ClassGroupModP.PlusMinusInstance

/-!
# SP-2: Plus-side identification (Cl(K⁺)/p nontrivial ⟹ even-eigenspace nontrivial)

Under `p ∣ h⁺(K)`, there exists an even index `i ∈ (0, p)` such that the
`ω^i`-eigenspace of `Cl(K)/p` is non-trivial.

The proof composes:

* `classGroupMap_modP_injective_unconditional` (SP-2a unconditional, in
  `Plus.lean`): `Cl(K⁺)/p ↪ Cl(K)/p`.
* `cyclotomicGalActionInstance_neg_one_classGroupMap` (in
  `PlusMinusInstance.lean`): the image is `σ_{-1}`-fixed.
* `exists_even_eigenspaceComponentNontrivial_of_sigma_fixed_nontrivial`
  (in `AtomC.lean`): a non-zero `σ_{-1}`-fixed element forces some
  even `V_k` to be non-trivial.

The `V₀ = 0` (trivial-character eigenspace) hypothesis encodes the
classical fact that `(Cl(K)/p)^Δ = 0` for cyclotomic `K`, which would
otherwise allow `i = 0` and break `IsReflectionComponentIndex p i`'s
`0 < i` constraint.

## References

* [Wash97] §10.1.
* Reviewer guidance 2026-05-22 (Q5 / SP-2 chain).
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
variable (K : Type) [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

include hp_odd in
/-- **SP-2 (Plus-side identification, conditional on V₀ trivial)**: under
`p ∣ h⁺(K)` and the trivial-character eigenspace `V₀ := (Cl(K)/p)^Δ`
being trivial, there exists an even index `i` with
`IsReflectionComponentIndex p i` (i.e. `0 < i < p`) such that the
`ω^i`-eigenspace of `Cl(K)/p` is non-trivial. -/
theorem even_eigenspace_nontrivial_of_dvd_hPlus
    (h_decomp : StandardEigenspaceDecompositionComplete
        (V := Additive (ClassGroupModP K p))
        (cyclotomicGalActionInstance (p := p) (K := K)))
    (h_V0_trivial : eigenspace (V := Additive (ClassGroupModP K p))
        (cyclotomicGalActionInstance (p := p) (K := K)) 0 = ⊥)
    (h_dvd : (p : ℕ) ∣ hPlus K) :
    ∃ i : ℕ, IsReflectionComponentIndex p i ∧ Even i ∧
      eigenspaceComponentNontrivial p K i := by
  classical
  -- Local abbreviation.
  set Kplus := NumberField.maximalRealSubfield K
  -- Step 1: Cl(K⁺)/p is non-trivial under p ∣ h⁺.
  have h_Kplus_modP_nontrivial : Nontrivial (ClassGroupModP Kplus p) := by
    rw [nontrivial_iff_exists_ne (1 : ClassGroupModP Kplus p)]
    by_contra h_triv
    push Not at h_triv
    haveI h_subsing : Subsingleton (ClassGroupModP Kplus p) :=
      ⟨fun a b => by rw [h_triv a, h_triv b]⟩
    have h_surj : Function.Surjective
        (powMonoidHom p : ClassGroup (𝓞 Kplus) →* ClassGroup (𝓞 Kplus)) := by
      rw [← MonoidHom.range_eq_top]
      rw [Subgroup.eq_top_iff']
      intro x
      have h_one : (QuotientGroup.mk x : ClassGroupModP Kplus p) = 1 :=
        Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).mp h_one
    have h_inj : Function.Injective
        (powMonoidHom p : ClassGroup (𝓞 Kplus) →* ClassGroup (𝓞 Kplus)) :=
      (Finite.injective_iff_surjective).mpr h_surj
    have h_no_p_tors : ∀ x : ClassGroup (𝓞 Kplus), x ^ p = 1 → x = 1 := by
      intro x hx
      have : (powMonoidHom p) x = (powMonoidHom p) 1 := by
        simpa [powMonoidHom] using hx
      exact h_inj this
    have h_card_eq : Fintype.card (ClassGroup (𝓞 Kplus)) = hPlus K := rfl
    obtain ⟨x, hx_ord⟩ := exists_prime_orderOf_dvd_card p (h_card_eq ▸ h_dvd)
    have hx_pow : x ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (hx_ord ▸ dvd_refl p)
    have hx_eq_one : x = 1 := h_no_p_tors x hx_pow
    rw [hx_eq_one, orderOf_one] at hx_ord
    exact (Fact.out : Nat.Prime p).one_lt.ne hx_ord
  -- Step 2: Pick a nonzero element of Cl(K⁺)/p.
  obtain ⟨cPlus, hcPlus_ne⟩ := exists_ne (1 : ClassGroupModP Kplus p)
  set v : Additive (ClassGroupModP K p) :=
    Additive.ofMul (FLT37.classGroupMap_modP p K cPlus) with hv_def
  -- Step 3: v ≠ 0 (using SP-2a unconditional).
  have hv_ne : v ≠ 0 := by
    intro heq
    apply hcPlus_ne
    have h_mul : FLT37.classGroupMap_modP p K cPlus = 1 := by
      have := congrArg Additive.toMul heq
      simpa [v] using this
    exact FLT37.classGroupMap_modP_injective_unconditional p K hp_odd
      (h_mul.trans (map_one (FLT37.classGroupMap_modP p K)).symm)
  -- Step 4: v is σ_{-1}-fixed.
  have h_fixed : cyclotomicGalActionInstance (p := p) (K := K) (-1) v = v := by
    obtain ⟨cI, rfl⟩ := QuotientGroup.mk_surjective cPlus
    simp only [v]
    change cyclotomicGalActionInstance (p := p) (K := K) (-1)
        (Additive.ofMul (FLT37.classGroupMap_modP p K (QuotientGroup.mk cI))) =
      Additive.ofMul (FLT37.classGroupMap_modP p K (QuotientGroup.mk cI))
    rw [show FLT37.classGroupMap_modP p K (QuotientGroup.mk cI) =
        QuotientGroup.mk (classGroupMap K cI) from rfl]
    exact cyclotomicGalActionInstance_neg_one_classGroupMap hp_odd cI
  -- Step 5: Apply the even-eigenspace nontriviality lemma.
  obtain ⟨i, hi_lt, hi_even, hi_nontrivial⟩ :=
    exists_even_eigenspaceComponentNontrivial_of_sigma_fixed_nontrivial
      p K hp_odd h_decomp h_fixed hv_ne
  -- Step 6: Rule out i = 0 using h_V0_trivial.
  have hi_pos : 0 < i := by
    by_contra h_not_pos
    push Not at h_not_pos
    interval_cases i
    obtain ⟨v0, hv0_mem, hv0_ne⟩ := hi_nontrivial
    apply hv0_ne
    -- hv0_mem : v0 ∈ eigenspace _ 0; h_V0_trivial : eigenspace _ 0 = ⊥ ⟹ v0 ∈ ⊥ ⟹ v0 = 0.
    rw [h_V0_trivial] at hv0_mem
    exact (Submodule.mem_bot (R := ZMod p)).mp hv0_mem
  refine ⟨i, ⟨hi_pos, ?_⟩, hi_even, hi_nontrivial⟩
  omega

end BernoulliRegular

end
