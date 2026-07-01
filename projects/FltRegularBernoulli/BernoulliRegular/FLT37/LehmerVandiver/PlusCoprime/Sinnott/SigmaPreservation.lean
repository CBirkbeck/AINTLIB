import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.CyclotomicUnitGroup
import BernoulliRegular.TotallyRealSubfield.ZetaPrime

/-!
# σ-preservation of `cyclotomicUnitsSubgroup`

The complex-conjugation automorphism `σ = unitsComplexConj K` of
`(𝓞 K)ˣ` preserves the cyclotomic-units subgroup `C`. The key
algebraic identity is

  `σ(cyclotomicUnit p K k) = ζ^{p+1-k} · cyclotomicUnit p K k` in `𝓞 K`,

which exhibits `σ(cyclotomicUnit k)` as a torsion-times-generator
element of `C`.

This uses:
* The defining identity `(ζ-1) · cyclotomicUnit k = ζ^k - 1`.
* `σ(ζ) = ζ^{p-1}` (`complexConj_apply_zeta`).
* The fact that `ζ-1` is a non-zero divisor.

This is a key building block for **Step (E)** of the Sinnott / Cor 8.19
bridge construction.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

set_option backward.isDefEq.respectTransparency false

/-- **Key identity**: `σ((ζ - 1) · cyclotomicUnit k) = (ζ^{p-1} - 1) · σ(cyclotomicUnit k)`.

Direct from σ being a ring hom and `(ζ - 1) · cyclotomicUnit k = ζ^k - 1`. -/
theorem ringOfIntegersComplexConj_zeta_sub_one_mul_cyclotomicUnit (k : ℕ) :
    ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) *
        ringOfIntegersComplexConj K (cyclotomicUnit p K k) =
      ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1) := by
  rw [← map_mul, zeta_sub_one_mul_cyclotomicUnit]

/-- **σ-conjugate of `(ζ - 1)`**: `σ(ζ - 1) = ζ^{p-1} - 1`.

Direct from `complexConj_apply_zeta`. -/
theorem ringOfIntegersComplexConj_zeta_sub_one :
    ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) - 1 := by
  rw [map_sub, map_one]
  congr 1
  exact complexConj_apply_zeta (p := p) (K := K)

/-- **σ-conjugate of `ζ^k - 1`**: `σ(ζ^k - 1) = ζ^{(p-1)·k} - 1 = (ζ^{p-1})^k - 1`. -/
theorem ringOfIntegersComplexConj_zeta_pow_sub_one (k : ℕ) :
    ringOfIntegersComplexConj K (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k - 1) =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) ^ k - 1 := by
  rw [map_sub, map_one, map_pow]
  congr 2
  exact complexConj_apply_zeta (p := p) (K := K)

omit [IsCMField K] in
/-- **Reduce `(p-1)·k` mod `p`**: `ζ^{(p-1)·k} = ζ^{p-k}` for `1 ≤ k ≤ p-1`.

Computation in `𝓞 K`: `(p-1)·k = pk - k`, and `ζ^{pk} = (ζ^p)^k = 1^k = 1`, so
`ζ^{(p-1)·k} = ζ^{pk}·ζ^{-k} = ζ^{-k} = ζ^{p-k}`. -/
theorem zeta_pow_pred_pow_eq (k : ℕ) (hk_le : k ≤ p) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) ^ k =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) := by
  have hp_pow : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
    (zeta_spec p ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
  have h1 : (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) ^ k *
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k = 1 := by
    rw [← mul_pow, ← pow_succ, Nat.sub_add_cancel hp.out.one_le, hp_pow, one_pow]
  have h2 : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) *
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k = 1 := by
    rw [← pow_add, Nat.sub_add_cancel hk_le, hp_pow]
  have hzeta_unit : IsUnit (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k) :=
    ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.out.ne_zero).pow k
  exact mul_right_cancel₀ hzeta_unit.ne_zero (h1.trans h2.symm)

/-- **σ-image of `cyclotomicUnit k`** (1 ≤ k ≤ p-1): the key identity

  `(ζ-1) · cyclotomicUnit(p-1) · σ(cyclotomicUnit k) = (ζ-1) · cyclotomicUnit(p-k)`.

Both sides equal `ζ^{p-k} - 1` after canceling `(ζ-1)`:
* LHS = `(ζ^{p-1}-1) · σ(cyclotomicUnit k)` [defining identity]
      = `σ((ζ-1) · cyclotomicUnit k)` [σ ring hom]
      = `σ(ζ^k - 1)` [defining identity]
      = `(ζ^{p-1})^k - 1 = ζ^{p-k} - 1` [reduction mod p].
* RHS = `(ζ-1) · cyclotomicUnit(p-k) = ζ^{p-k} - 1` [defining identity]. -/
theorem zeta_sub_one_mul_cyclotomicUnit_pred_mul_complexConj_cyclotomicUnit_eq
    (k : ℕ) (hk_le : k ≤ p) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K (p - 1) *
        ringOfIntegersComplexConj K (cyclotomicUnit p K k) =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K (p - k) := by
  have hLHS : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K (p - 1) *
      ringOfIntegersComplexConj K (cyclotomicUnit p K k) =
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) - 1) *
          ringOfIntegersComplexConj K (cyclotomicUnit p K k) := by
    rw [zeta_sub_one_mul_cyclotomicUnit]
  rw [hLHS]
  rw [← ringOfIntegersComplexConj_zeta_sub_one (p := p) (K := K),
      ← map_mul, zeta_sub_one_mul_cyclotomicUnit,
      ringOfIntegersComplexConj_zeta_pow_sub_one,
      zeta_pow_pred_pow_eq (p := p) (K := K) k hk_le]
  rw [zeta_sub_one_mul_cyclotomicUnit]

/-- **σ-image clean form** (1 ≤ k ≤ p-1): cancelling `(ζ-1)` from the
key identity gives

  `cyclotomicUnit(p-1) · σ(cyclotomicUnit k) = cyclotomicUnit(p-k)`

in `𝓞 K`. This expresses `σ(cyclotomicUnit k)` as a quotient of two
cyclotomic units (both in `cyclotomicUnitsSubgroup`), establishing
σ-preservation of the subgroup. -/
theorem cyclotomicUnit_pred_mul_complexConj_cyclotomicUnit_eq
    (k : ℕ) (hk_le : k ≤ p) :
    cyclotomicUnit p K (p - 1) *
        ringOfIntegersComplexConj K (cyclotomicUnit p K k) =
      cyclotomicUnit p K (p - k) := by
  have hzeta_sub_one_ne_zero : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ≠ 0 :=
    (zeta_spec p ℚ K).zeta_sub_one_prime'.ne_zero
  have h_eq' : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) *
      (cyclotomicUnit p K (p - 1) *
        ringOfIntegersComplexConj K (cyclotomicUnit p K k)) =
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) * cyclotomicUnit p K (p - k) := by
    rw [← mul_assoc]
    exact zeta_sub_one_mul_cyclotomicUnit_pred_mul_complexConj_cyclotomicUnit_eq
      (p := p) (K := K) k hk_le
  exact mul_left_cancel₀ hzeta_sub_one_ne_zero h_eq'

/-- **Unit-level σ-image identity** (1 ≤ k ≤ p-1, k coprime to p):

  `cyclotomicUnitUnit(p-1) * unitsComplexConj(cyclotomicUnitUnit k) = cyclotomicUnitUnit(p-k)`

in `(𝓞 K)ˣ`. Lift of the 𝓞 K-level identity, with `p-k` coprime to `p`
under the hypothesis. -/
theorem cyclotomicUnitUnit_pred_mul_unitsComplexConj_cyclotomicUnitUnit_eq
    {k : ℕ} (hk : k.Coprime p) (_hk_pos : 1 ≤ k) (hk_lt : k < p) (hp_two : 2 ≤ p) :
    cyclotomicUnitUnit p K (p - 1) (by
        rw [Nat.Coprime, Nat.gcd_comm]
        exact (Nat.coprime_self_sub_right hp.out.one_le).mpr (Nat.coprime_one_right p))
        hp_two *
      unitsComplexConj K (cyclotomicUnitUnit p K k hk hp_two) =
      cyclotomicUnitUnit p K (p - k) (by
        rw [Nat.Coprime, Nat.gcd_comm]
        exact (Nat.coprime_self_sub_right hk_lt.le).mpr hk.symm) hp_two := by
  apply Units.ext
  change ((cyclotomicUnitUnit p K (p - 1) _ hp_two : (𝓞 K)ˣ) : 𝓞 K) *
      ((unitsComplexConj K (cyclotomicUnitUnit p K k hk hp_two) : (𝓞 K)ˣ) : 𝓞 K) =
    ((cyclotomicUnitUnit p K (p - k) _ hp_two : (𝓞 K)ˣ) : 𝓞 K)
  rw [cyclotomicUnitUnit_val, cyclotomicUnitUnit_val]
  change cyclotomicUnit p K (p - 1) *
      ringOfIntegersComplexConj K ((cyclotomicUnitUnit p K k hk hp_two : (𝓞 K)ˣ) : 𝓞 K) =
    cyclotomicUnit p K (p - k)
  rw [cyclotomicUnitUnit_val]
  exact cyclotomicUnit_pred_mul_complexConj_cyclotomicUnit_eq (p := p) (K := K) k hk_lt.le

/-- **σ-preservation of cyclotomic-unit generators**: for each generator
`cyclotomicUnitUnit k` of `cyclotomicUnitsSubgroup`, its σ-image is also
in the subgroup.

Specifically, σ(cyclotomicUnitUnit k) = cyclotomicUnitUnit(p-1)⁻¹ ·
cyclotomicUnitUnit(p-k), and both factors are generators of the
subgroup. -/
theorem unitsComplexConj_cyclotomicUnitUnit_mem
    {k : ℕ} (hk : k.Coprime p) (hk_pos : 1 ≤ k) (hk_lt : k < p) (hp_two : 2 ≤ p) :
    unitsComplexConj K (cyclotomicUnitUnit p K k hk hp_two) ∈
      cyclotomicUnitsSubgroup p K hp_two := by
  have h_pred_coprime : (p - 1).Coprime p := by
    rw [Nat.Coprime, Nat.gcd_comm]
    exact (Nat.coprime_self_sub_right hp.out.one_le).mpr (Nat.coprime_one_right p)
  have h_sub_coprime : (p - k).Coprime p := by
    rw [Nat.Coprime, Nat.gcd_comm]
    exact (Nat.coprime_self_sub_right hk_lt.le).mpr hk.symm
  have h_solve : unitsComplexConj K (cyclotomicUnitUnit p K k hk hp_two) =
      (cyclotomicUnitUnit p K (p - 1) h_pred_coprime hp_two)⁻¹ *
        cyclotomicUnitUnit p K (p - k) h_sub_coprime hp_two := by
    rw [eq_inv_mul_iff_mul_eq]
    exact cyclotomicUnitUnit_pred_mul_unitsComplexConj_cyclotomicUnitUnit_eq
      (p := p) (K := K) hk hk_pos hk_lt hp_two
  rw [h_solve]
  apply Subgroup.mul_mem
  · apply Subgroup.inv_mem
    exact cyclotomicUnitUnit_mem_cyclotomicUnitsSubgroup p K h_pred_coprime
      (Nat.sub_pos_of_lt hp.out.one_lt) (Nat.sub_lt hp.out.pos Nat.one_pos) hp_two
  · exact cyclotomicUnitUnit_mem_cyclotomicUnitsSubgroup p K h_sub_coprime
      (Nat.sub_pos_of_lt hk_lt) (Nat.sub_lt hp.out.pos hk_pos) hp_two

/-- **σ stabilises `cyclotomicUnitsSubgroup`**: for every `u ∈ C`,
the σ-image is also in `C`.

Proof: it suffices to show generators map into `C`. Generators are:
* `cyclotomicUnitUnit k` for `1 ≤ k < p` and `k.Coprime p` — handled by
  `unitsComplexConj_cyclotomicUnitUnit_mem`.
* Torsion elements — σ takes torsion to torsion (preserves finite order),
  and torsion ⊆ C. -/
theorem unitsComplexConj_mem_cyclotomicUnitsSubgroup_of_mem (hp_two : 2 ≤ p)
    {u : (𝓞 K)ˣ} (hu : u ∈ cyclotomicUnitsSubgroup p K hp_two) :
    unitsComplexConj K u ∈ cyclotomicUnitsSubgroup p K hp_two := by
  suffices h_le : cyclotomicUnitsSubgroup p K hp_two ≤
      Subgroup.comap (unitsComplexConj K).toMonoidHom
        (cyclotomicUnitsSubgroup p K hp_two) by
    exact h_le hu
  unfold cyclotomicUnitsSubgroup
  refine sup_le ?_ ?_
  ·
    rw [Subgroup.closure_le]
    rintro v ⟨k, hk, hk_pos, hk_lt, rfl⟩
    change cyclotomicUnitUnit p K k hk hp_two ∈
      Subgroup.comap (unitsComplexConj K).toMonoidHom
        (Subgroup.closure (cyclotomicUnitsSet p K hp_two) ⊔ NumberField.Units.torsion K)
    rw [Subgroup.mem_comap]
    change unitsComplexConj K (cyclotomicUnitUnit p K k hk hp_two) ∈
      Subgroup.closure (cyclotomicUnitsSet p K hp_two) ⊔ NumberField.Units.torsion K
    simpa [cyclotomicUnitsSubgroup] using
      unitsComplexConj_cyclotomicUnitUnit_mem (p := p) (K := K) hk hk_pos hk_lt hp_two
  ·
    intro v hv
    rw [Subgroup.mem_comap]
    apply Subgroup.mem_sup_right
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    change unitsComplexConj K v ∈ NumberField.Units.torsion K
    change v ∈ NumberField.Units.torsion K at hv
    rw [NumberField.Units.torsion, CommGroup.mem_torsion] at hv ⊢
    rw [isOfFinOrder_iff_pow_eq_one] at hv ⊢
    obtain ⟨n, hn_pos, hn⟩ := hv
    exact ⟨n, hn_pos, by rw [← map_pow, hn, map_one]⟩

end Sinnott

end FLT37

end BernoulliRegular

end
