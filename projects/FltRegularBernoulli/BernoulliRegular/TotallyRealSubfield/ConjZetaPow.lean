import BernoulliRegular.TotallyRealSubfield.Conjugation

/-!
# K-level σ(ζ^m) = ζ^{-m}
-/

noncomputable section

open BernoulliRegular NumberField NumberField.IsCMField

namespace BernoulliRegular

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

/-- **`complexConj K (ζ^m) = (ζ^m)⁻¹`** at K-level. -/
theorem complexConj_zeta_pow_eq_inv (hp_odd : p ≠ 2) (m : ℕ) :
    complexConj K (IsCyclotomicExtension.zeta p ℚ K ^ m) =
      (IsCyclotomicExtension.zeta p ℚ K ^ m)⁻¹ := by
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  -- conj_zeta_pow at the 𝓞 K level via RingOfIntegers.ext: actually returns
  -- equation in K via the Units.ext + RingOfIntegers.ext chain.
  have h_unit := conj_zeta_pow (p := p) (K := K) (hζ := hζ) (m := m)
  set η : (𝓞 K)ˣ := (hζ.toInteger_isPrimitiveRoot.isUnit (NeZero.ne p)).unit with hη_def
  -- h_unit : complexConj K (↑↑(η^m)) = ↑↑((η^m)⁻¹).
  -- Goal: complexConj K (zeta^m) = (zeta^m)⁻¹.
  -- It suffices to show ↑↑(η^m) = zeta^m and ↑↑((η^m)⁻¹) = (zeta^m)⁻¹.
  -- Step 1: η^m as K element = zeta^m. By map_pow + def.
  have h_pow_eq : (((η ^ m : (𝓞 K)ˣ) : 𝓞 K) : K) =
      IsCyclotomicExtension.zeta p ℚ K ^ m := by
    rw [hη_def, Units.val_pow_eq_pow_val]
    push_cast
    rfl
  -- Step 2: (η^m)⁻¹ as K element = (zeta^m)⁻¹.
  have h_pow_inv_mul : (((η ^ m)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) *
      ((η ^ m : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    have : ((η ^ m)⁻¹ * η ^ m : (𝓞 K)ˣ) = 1 := inv_mul_cancel _
    rw [← Units.val_mul, this, Units.val_one]
  have h_inv_eq : ((((η ^ m)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) =
      (IsCyclotomicExtension.zeta p ℚ K ^ m)⁻¹ := by
    have h_K : ((((η ^ m)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) : K) *
        (((η ^ m : (𝓞 K)ˣ) : 𝓞 K) : K) = 1 := by
      rw [← map_mul, h_pow_inv_mul, map_one]
    rw [h_pow_eq] at h_K
    exact eq_inv_of_mul_eq_one_left h_K
  -- Now h_unit says complexConj K (↑↑(η^m)) = ↑↑((η^m)⁻¹).
  -- Rewrite using h_pow_eq on LHS and h_inv_eq on RHS.
  rw [show IsCyclotomicExtension.zeta p ℚ K ^ m =
    (((η ^ m : (𝓞 K)ˣ) : 𝓞 K) : K) from h_pow_eq.symm]
  rw [h_unit]
  exact h_inv_eq

end BernoulliRegular

end
