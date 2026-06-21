import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.LDerivative.Part1

@[expose] public section

noncomputable section

open Real Complex
open scoped NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]

/-- **`LValueAtZeroFormula` is PROVEN**: for nontrivial even χ mod p (with
p > 1), `LFunction χ 0 = 0`. Direct from mathlib's
`ZMod.LFunction_apply_zero_of_even` since `χ 0 = 0` for nontrivial χ. -/
theorem lValueAtZeroFormula_proven (χ : DirichletCharacter ℂ p)
    [NeZero p] (hp_two : 2 ≤ p) : LValueAtZeroFormula p χ := by
  intro hχ_even hχ_ne_one
  unfold DirichletCharacter.LFunction
  rw [ZMod.LFunction_apply_zero_of_even hχ_even.to_fun]
  have h_p_neq_one : p ≠ 1 := by omega
  -- χ 0 = 0 for nontrivial χ.
  have h_zero : χ 0 = 0 := by
    have := ZMod.nontrivial_iff.mpr h_p_neq_one
    exact χ.map_zero
  rw [h_zero]
  simp

/-- **Sum of nontrivial χ values = 0 mod p**: classical orthogonality.

For non-trivial Dirichlet character χ mod p:
`∑_{a ∈ ZMod p} χ a = 0`. -/
theorem sum_nontrivial_dirichletCharacter_eq_zero
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) :
    ∑ a : ZMod p, χ a = 0 :=
  χ.sum_eq_zero_of_ne_one hχ

/-- **ZMod-sum bridge for vanishing-at-zero functions**: `∑ a : ZMod p, f a =
∑ a ∈ Finset.Ico 1 p, f ((a : ℕ) : ZMod p)` whenever `f 0 = 0`.

Concretely the bijection `Finset.Ico 1 p ≃ (ZMod p) \ {0}` via the natural-
number cast lets us drop the `a = 0` summand on the left. -/
private theorem sum_zmod_eq_sum_Ico_of_zero
    {f : ZMod p → ℂ} (h_zero : f (0 : ZMod p) = 0) :
    ∑ a : ZMod p, f a = ∑ a ∈ Finset.Ico 1 p, f ((a : ℕ) : ZMod p) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_pos : 0 < p := hp.out.pos
  rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ (0 : ZMod p)),
    h_zero, add_zero]
  symm
  refine Finset.sum_bij (fun k _ => ((k : ℕ) : ZMod p)) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_Ico] at hk
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro h_eq
    rw [ZMod.natCast_eq_zero_iff] at h_eq
    have := Nat.le_of_dvd (by omega) h_eq
    omega
  · intro k₁ hk₁ k₂ hk₂ heq
    rw [Finset.mem_Ico] at hk₁ hk₂
    have h_val1 : ((k₁ : ZMod p)).val = k₁ := ZMod.val_natCast_of_lt hk₁.2
    have h_val2 : ((k₂ : ZMod p)).val = k₂ := ZMod.val_natCast_of_lt hk₂.2
    have h := congrArg ZMod.val heq
    rw [h_val1, h_val2] at h
    exact h
  · intro x hx
    rw [Finset.mem_erase] at hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    rw [Finset.mem_Ico]
    refine ⟨?_, ZMod.val_lt x⟩
    rw [Nat.one_le_iff_ne_zero]
    intro h
    apply hx.1
    have h_val_eq : (x.val : ZMod p) = (0 : ZMod p) := by
      rw [h]; push_cast; rfl
    rw [← h_val_eq, ZMod.natCast_zmod_val]
  · intros; rfl

/-- **Bridge K-side ↔ K⁺-side log-sums**: for any Dirichlet character `χ` mod
`p`, the K⁺-side `evenLValueLogSum p χ` (sum over `ZMod p` with `χ⁻¹` and
`log‖1 - stdAddChar‖`) equals `-DirichletLogSum p χ⁻¹` (sum over
`Finset.Ico 1 p` with `χ⁻¹` and `log(2|sin(πa/p)|)`).

The cyclotomic norm identity `‖1 - stdAddChar a‖ = 2|sin(πa/p)|`
(`norm_one_sub_exp_two_pi_I_mul`) gives the pointwise equality; the
`a = 0` term in `ZMod p` vanishes via `χ⁻¹(0) = 0`.

This bridges the matrix-eigenvalue side of Sinnott's diagonalisation
(`dirichletCharacter_inv_matrix_eigenvalue_evenLValueLogSum`) to the
`L'(0, χ⁻¹)`-style `DirichletLogSum` formulation in LV-SIN-C. -/
theorem evenLValueLogSum_eq_neg_DirichletLogSum_inv
    (χ : DirichletCharacter ℂ p) :
    BernoulliRegular.evenLValueLogSum p χ = -DirichletLogSum p χ⁻¹ := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_pos : 0 < p := hp.out.pos
  unfold BernoulliRegular.evenLValueLogSum DirichletLogSum
  rw [neg_neg]
  set f : ZMod p → ℂ := fun a =>
    χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ)
  have h_zero : f (0 : ZMod p) = 0 := by
    simp [f, MulChar.map_zero]
  rw [show (∑ a : ZMod p,
      χ⁻¹ a * ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) a‖ : ℝ) : ℂ)) =
      ∑ a : ZMod p, f a from rfl]
  rw [sum_zmod_eq_sum_Ico_of_zero (p := p) h_zero]
  refine Finset.sum_congr rfl ?_
  intro a ha
  rw [Finset.mem_Ico] at ha
  have ha_pos : 0 < a := ha.1
  have ha_lt : a < p := ha.2
  change χ⁻¹ ((a : ℕ) : ZMod p) *
      ((Real.log ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ℕ) : ZMod p)‖ : ℝ) : ℂ) =
    χ⁻¹ ((a : ℕ) : ZMod p) *
      ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ)
  congr 2
  have h_std : ZMod.stdAddChar (N := p) ((a : ℕ) : ZMod p) =
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / p) := by
    have h := ZMod.stdAddChar_coe (N := p) (a : ℤ)
    simpa using h
  rw [h_std]
  have h_norm : ‖(1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / p)‖ =
      2 * |Real.sin (Real.pi * a / p)| := by
    have h_eq : (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / p) =
        ((2 * Real.pi * ((a : ℕ) / p : ℝ) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h_eq, norm_one_sub_exp_two_pi_I_mul]
    ring_nf
  rw [h_norm]

/-- **Cyclotomic product in `ℂ`**: `∏_{a ∈ Finset.Ico 1 p} (1 - stdAddChar a) = p`.
The roots `stdAddChar a = exp(2π·I·a/p)` for `a ∈ {1, …, p−1}` are exactly the
primitive `p`-th roots of unity in `ℂ`; mathlib's
`IsPrimitiveRoot.prod_one_sub_pow_eq_order` gives the product formula. -/
private theorem prod_one_sub_stdAddChar_eq_p :
    ∏ a ∈ Finset.Ico 1 p, ((1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ℕ) : ZMod p)) =
      (p : ℂ) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_pos : 0 < p := hp.out.pos
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p) with hζ_def
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p hp.out.ne_zero
  have hμ : IsPrimitiveRoot ζ ((p - 1) + 1) := by
    rw [show (p - 1) + 1 = p from Nat.succ_pred_eq_of_pos hp_pos]
    exact hζ
  have h_prod_pow : ∏ k ∈ Finset.range (p - 1), (1 - ζ ^ (k + 1)) =
      ((p - 1 : ℕ) : ℂ) + 1 := hμ.prod_one_sub_pow_eq_order
  have h_p_cast : ((p - 1 : ℕ) : ℂ) + 1 = (p : ℂ) := by
    have h_pe : (p - 1 : ℕ) + 1 = p := Nat.succ_pred_eq_of_pos hp_pos
    exact_mod_cast h_pe
  have h_Ico : Finset.Ico 1 p = (Finset.range (p - 1)).image (· + 1) := by
    ext a
    rw [Finset.mem_image, Finset.mem_Ico]
    refine ⟨fun ⟨ha1, ha2⟩ => ⟨a - 1, ?_, ?_⟩, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
    · rintro ⟨k, hk, rfl⟩
      rw [Finset.mem_range] at hk
      omega
  have h_inj : ∀ k₁ ∈ Finset.range (p - 1),
      ∀ k₂ ∈ Finset.range (p - 1), k₁ + 1 = k₂ + 1 → k₁ = k₂ :=
    fun _ _ _ _ h => by omega
  have h_eq_ζ : ∀ k ∈ Finset.range (p - 1),
      ZMod.stdAddChar (N := p) ((k + 1 : ℕ) : ZMod p) = ζ ^ (k + 1) := by
    intro k _
    rw [hζ_def, ← Complex.exp_nat_mul]
    have h := ZMod.stdAddChar_coe (N := p) ((k + 1 : ℕ) : ℤ)
    rw [show ((k + 1 : ℕ) : ZMod p) = (((k + 1 : ℕ) : ℤ) : ZMod p) from by push_cast; rfl, h]
    congr 1
    push_cast
    ring
  rw [h_Ico, Finset.prod_image h_inj]
  calc ∏ x ∈ Finset.range (p - 1),
        ((1 : ℂ) - ZMod.stdAddChar (N := p) ((x + 1 : ℕ) : ZMod p))
      = ∏ x ∈ Finset.range (p - 1), ((1 : ℂ) - ζ ^ (x + 1)) :=
        Finset.prod_congr rfl (fun k hk => by rw [h_eq_ζ k hk])
    _ = ((p - 1 : ℕ) : ℂ) + 1 := h_prod_pow
    _ = (p : ℂ) := h_p_cast

/-- **DirichletLogSum at the principal character** `χ = 1`: the sum collapses
to `-log p` via the classical cyclotomic-product identity
`∏_{a=1}^{p-1} 2|sin(πa/p)| = p`. -/
theorem DirichletLogSum_principal_eq_neg_log :
    DirichletLogSum p (1 : DirichletCharacter ℂ p) = -((Real.log p : ℝ) : ℂ) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_pos : 0 < p := hp.out.pos
  unfold DirichletLogSum
  -- Step 1: replace (1 : DirichletCharacter) a with 1 for a ∈ Ico 1 p.
  have h_eval : ∑ a ∈ Finset.Ico 1 p,
        ((1 : DirichletCharacter ℂ p) ((a : ℕ) : ZMod p)) *
        ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) =
      ∑ a ∈ Finset.Ico 1 p,
        ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) := by
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [Finset.mem_Ico] at ha
    have h_unit : IsUnit ((a : ℕ) : ZMod p) := by
      rw [isUnit_iff_ne_zero]
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd ha.1 h) (by omega)
    rw [MulChar.one_apply h_unit, one_mul]
  rw [h_eval]
  -- Step 2: each sin factor is positive on Ico 1 p.
  have h_pos : ∀ a ∈ Finset.Ico 1 p,
      (0 : ℝ) < 2 * |Real.sin (Real.pi * a / p)| := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    have hp_real : (0 : ℝ) < p := by positivity
    have h_arg_pos : 0 < Real.pi * a / p := by
      have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha.1
      positivity
    have h_arg_lt : Real.pi * a / p < Real.pi := by
      have h_a_lt : (a : ℝ) < p := by exact_mod_cast ha.2
      have h_div_lt : (a : ℝ) / p < 1 := (div_lt_one hp_real).mpr h_a_lt
      have hπ : Real.pi * ((a : ℝ) / p) < Real.pi * 1 :=
        mul_lt_mul_of_pos_left h_div_lt Real.pi_pos
      rw [mul_one] at hπ
      rw [mul_div_assoc]
      exact hπ
    have h_sin_pos : 0 < Real.sin (Real.pi * a / p) :=
      Real.sin_pos_of_pos_of_lt_pi h_arg_pos h_arg_lt
    rw [abs_of_pos h_sin_pos]
    positivity
  -- Step 3: cast the ℂ sum to a cast of an ℝ sum, then convert sum-of-logs
  -- to log-of-product.
  have h_real_sum : ∑ a ∈ Finset.Ico 1 p,
        ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) =
      ((∑ a ∈ Finset.Ico 1 p,
          Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [h_real_sum]
  have h_sum_log : (∑ a ∈ Finset.Ico 1 p,
        Real.log (2 * |Real.sin (Real.pi * a / p)|)) =
      Real.log (∏ a ∈ Finset.Ico 1 p,
        (2 * |Real.sin (Real.pi * a / p)| : ℝ)) :=
    (Real.log_prod (s := Finset.Ico 1 p)
      (f := fun a => 2 * |Real.sin (Real.pi * a / p)|)
      (fun a ha => (h_pos a ha).ne')).symm
  rw [h_sum_log]
  -- Step 4: the product equals p via the cyclotomic norm identity.
  have h_prod_eq : (∏ a ∈ Finset.Ico 1 p,
        (2 * |Real.sin (Real.pi * a / p)| : ℝ)) = (p : ℝ) := by
    have h_complex := prod_one_sub_stdAddChar_eq_p (p := p)
    have h_norm := congrArg (‖·‖) h_complex
    simp only [Complex.norm_prod] at h_norm
    rw [Complex.norm_natCast p] at h_norm
    have h_eq_each : ∀ a ∈ Finset.Ico 1 p,
        (2 * |Real.sin (Real.pi * a / p)| : ℝ) =
        ‖(1 : ℂ) - ZMod.stdAddChar (N := p) ((a : ℕ) : ZMod p)‖ := by
      intro a ha
      rw [Finset.mem_Ico] at ha
      have h_std : ZMod.stdAddChar (N := p) ((a : ℕ) : ZMod p) =
          Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / p) := by
        have h := ZMod.stdAddChar_coe (N := p) (a : ℤ)
        simpa using h
      rw [h_std]
      have h_eq : (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / p) =
          ((2 * Real.pi * ((a : ℕ) / p : ℝ) : ℝ) : ℂ) * Complex.I := by
        push_cast
        ring
      rw [h_eq, norm_one_sub_exp_two_pi_I_mul]
      ring_nf
    rw [Finset.prod_congr rfl h_eq_each]
    exact h_norm
  rw [h_prod_eq]

/-- **`evenLValueRhs` in `DirichletLogSum` form**: composing the definition
`evenLValueRhs p χ = -(gaussSum χ⁻¹)⁻¹ · evenLValueLogSum p χ` with the
bridge `evenLValueLogSum p χ = -DirichletLogSum p χ⁻¹` gives the cleaner
form

  `evenLValueRhs p χ = (gaussSum χ⁻¹)⁻¹ · DirichletLogSum p χ⁻¹`.

This identifies the analytic-CNF building block (`evenLValueRhs`) with the
K-side log-sum (`DirichletLogSum`) up to a Gauss-sum prefactor, which is the
form needed for the analytic CNF ↔ Sinnott regulator identity composition. -/
theorem evenLValueRhs_eq_gaussSum_inv_mul_DirichletLogSum
    (χ : DirichletCharacter ℂ p) :
    BernoulliRegular.evenLValueRhs p χ =
      (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ * DirichletLogSum p χ⁻¹ := by
  unfold BernoulliRegular.evenLValueRhs
  rw [evenLValueLogSum_eq_neg_DirichletLogSum_inv]
  ring

/-- **Cyclotomic half-sum identity**: for `p` an odd prime, the sum of
`log(2·|sin(π·a/p)|)` over the "half range" `Ico 1 ((p+1)/2)` equals
`(log p) / 2`. This is the cyclotomic-unit half-sum identity used in the
analytic prefactor matching for Sinnott's regulator determinant. -/
theorem half_sum_log_two_sin_eq_half_log_p (hp_odd : p ≠ 2) :
    ∑ a ∈ Finset.Ico 1 ((p + 1) / 2),
        Real.log (2 * |Real.sin (Real.pi * a / p)|) =
      Real.log p / 2 := by
  have h_p_odd : Odd p := hp.out.odd_of_ne_two hp_odd
  -- Cast the principal-character identity to a ℂ-equation.
  have h_principal : DirichletLogSum p (1 : DirichletCharacter ℂ p) =
      -((Real.log p : ℝ) : ℂ) := DirichletLogSum_principal_eq_neg_log p
  -- Apply the even-character full-half identity at χ = 1.
  have h_one_even : (1 : DirichletCharacter ℂ p).Even := by
    rw [DirichletCharacter.Even]
    rw [show (-1 : ZMod p) = ((-1 : ℤ) : ZMod p) from by push_cast; rfl]
    have h_unit : IsUnit ((-1 : ℤ) : ZMod p) := by
      rw [Int.cast_neg, Int.cast_one]
      exact (isUnit_one).neg
    rw [MulChar.one_apply h_unit]
  have h_full_half := dirichletCharacter_even_log_sin_full_eq_two_half
    (p := p) h_p_odd (1 : DirichletCharacter ℂ p) h_one_even
  -- Each (1 ↑a) factor in the sums is `1` for `a ∈ Ico 1 p` and
  -- `a ∈ Ico 1 ((p+1)/2)`.
  have h_one_apply : ∀ a : ℕ, 1 ≤ a → a < p →
      ((1 : DirichletCharacter ℂ p) ((a : ℕ) : ZMod p)) = 1 := by
    intro a ha1 ha2
    have h_unit : IsUnit ((a : ℕ) : ZMod p) := by
      rw [isUnit_iff_ne_zero]
      intro h
      rw [ZMod.natCast_eq_zero_iff] at h
      exact absurd (Nat.le_of_dvd ha1 h) (by omega)
    rw [MulChar.one_apply h_unit]
  -- Replace `1 (↑a)` with `1` in both sums of `h_full_half`.
  have h_lhs_simp : ∑ a ∈ Finset.Ico 1 p,
        ((1 : DirichletCharacter ℂ p) ((a : ℕ) : ZMod p)) *
          ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) =
      ((∑ a ∈ Finset.Ico 1 p,
          Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [Finset.mem_Ico] at ha
    rw [h_one_apply a ha.1 ha.2, one_mul]
  have h_rhs_simp : ∑ a ∈ Finset.Ico 1 ((p + 1) / 2),
        ((1 : DirichletCharacter ℂ p) ((a : ℕ) : ZMod p)) *
          ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) =
      ((∑ a ∈ Finset.Ico 1 ((p + 1) / 2),
          Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl ?_
    intro a ha
    rw [Finset.mem_Ico] at ha
    have ha_lt : a < p := by
      have : (p + 1) / 2 ≤ p := by omega
      omega
    rw [h_one_apply a ha.1 ha_lt, one_mul]
  rw [h_lhs_simp, h_rhs_simp] at h_full_half
  -- Now `h_full_half` says the full sum is twice the half sum.
  -- The LHS equals log p (from cyclotomic identity, via DirichletLogSum_principal).
  -- Unfold DirichletLogSum at 1 to get ↑(∑ ... log) = log p.
  have h_full_eq : ((∑ a ∈ Finset.Ico 1 p,
        Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) =
      ((Real.log p : ℝ) : ℂ) := by
    have h_unfold : DirichletLogSum p (1 : DirichletCharacter ℂ p) =
        -((∑ a ∈ Finset.Ico 1 p,
            ((1 : DirichletCharacter ℂ p) ((a : ℕ) : ZMod p)) *
              ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ))) := rfl
    rw [h_unfold] at h_principal
    rw [h_lhs_simp] at h_principal
    linear_combination -h_principal
  rw [h_full_eq] at h_full_half
  -- h_full_half : ↑(log p) = 2 * ↑(∑ half)
  -- Cast back to ℝ.
  have h_real : Real.log p = 2 * ∑ a ∈ Finset.Ico 1 ((p + 1) / 2),
      Real.log (2 * |Real.sin (Real.pi * a / p)|) := by
    exact_mod_cast h_full_half
  linarith

/-- **Cyclotomic half-product identity**: for `p` an odd prime,
`∏_{a=1}^{(p-1)/2} 2|sin(πa/p)| = √p`.

Proof: exp the half-sum identity `half_sum_log_two_sin_eq_half_log_p`,
which gives `∏_half 2|sin| = exp((log p)/2) = √p`. -/
theorem half_prod_two_sin_eq_sqrt_p (hp_odd : p ≠ 2) :
    ∏ a ∈ Finset.Ico 1 ((p + 1) / 2),
        (2 * |Real.sin (Real.pi * a / p)| : ℝ) = Real.sqrt p := by
  have hp_pos : 0 < p := hp.out.pos
  have hp_real : (0 : ℝ) < p := by positivity
  -- Each factor is positive (sin is positive in the half range).
  have h_pos : ∀ a ∈ Finset.Ico 1 ((p + 1) / 2),
      (0 : ℝ) < 2 * |Real.sin (Real.pi * a / p)| := by
    intro a ha
    rw [Finset.mem_Ico] at ha
    have ha_lt : a < p := by
      have : (p + 1) / 2 ≤ p := by omega
      omega
    have h_arg_pos : 0 < Real.pi * a / p := by
      have : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha.1
      positivity
    have h_arg_lt : Real.pi * a / p < Real.pi := by
      have h_a_lt : (a : ℝ) < p := by exact_mod_cast ha_lt
      have h_div_lt : (a : ℝ) / p < 1 := (div_lt_one hp_real).mpr h_a_lt
      have hπ : Real.pi * ((a : ℝ) / p) < Real.pi * 1 :=
        mul_lt_mul_of_pos_left h_div_lt Real.pi_pos
      rw [mul_one] at hπ
      rw [mul_div_assoc]
      exact hπ
    have h_sin_pos : 0 < Real.sin (Real.pi * a / p) :=
      Real.sin_pos_of_pos_of_lt_pi h_arg_pos h_arg_lt
    rw [abs_of_pos h_sin_pos]
    positivity
  -- The product is positive (each factor is).
  have h_prod_pos : (0 : ℝ) < ∏ a ∈ Finset.Ico 1 ((p + 1) / 2),
      (2 * |Real.sin (Real.pi * a / p)| : ℝ) :=
    Finset.prod_pos (fun a ha => h_pos a ha)
  have h_sqrt_pos : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr hp_real
  -- Compare via log: both positive, so log equality ⇒ equality.
  have h_log_eq : Real.log (∏ a ∈ Finset.Ico 1 ((p + 1) / 2),
        (2 * |Real.sin (Real.pi * a / p)| : ℝ)) =
      Real.log (Real.sqrt p) := by
    rw [Real.log_prod (s := Finset.Ico 1 ((p + 1) / 2))
        (f := fun a => 2 * |Real.sin (Real.pi * a / p)|)
        (fun a ha => (h_pos a ha).ne')]
    rw [half_sum_log_two_sin_eq_half_log_p (p := p) hp_odd]
    rw [Real.log_sqrt hp_real.le]
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr h_prod_pos)
    (Set.mem_Ioi.mpr h_sqrt_pos) h_log_eq

/-- **Gauss sum identity for even Dirichlet characters mod `p`**: for an
even nontrivial Dirichlet character `χ` mod a prime `p`,
`gaussSum χ stdAddChar · gaussSum χ⁻¹ stdAddChar = p`.

Composes mathlib's `gaussSum_mul_gaussSum_eq_card` (giving the product
with `ψ` and `ψ⁻¹` slots) with `mul_gaussSum_inv_eq_gaussSum` (converting
`gaussSum χ⁻¹ ψ⁻¹` to `gaussSum χ⁻¹ ψ` via the `χ(-1) = 1` even property). -/
theorem gaussSum_mul_gaussSum_inv_eq_p
    (χ : DirichletCharacter ℂ p) (hχ_ne : χ ≠ 1) (hχ_even : χ.Even) :
    gaussSum χ (ZMod.stdAddChar (N := p)) *
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) =
      (p : ℂ) := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have h_primitive : (ZMod.stdAddChar (N := p)).IsPrimitive :=
    ZMod.isPrimitive_stdAddChar p
  have h_card := gaussSum_mul_gaussSum_eq_card hχ_ne h_primitive
  -- h_card : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card (ZMod p)
  -- Use mul_gaussSum_inv_eq_gaussSum to relate gaussSum χ⁻¹ ψ⁻¹ to gaussSum χ⁻¹ ψ.
  have h_χinv_neg_one : χ⁻¹ ((-1 : ZMod p)) = 1 := by
    rw [MulChar.inv_apply_eq_inv']
    rw [DirichletCharacter.Even] at hχ_even
    rw [hχ_even]
    norm_num
  have h_convert :=
    mul_gaussSum_inv_eq_gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))
  rw [h_χinv_neg_one, one_mul] at h_convert
  rw [h_convert] at h_card
  rw [ZMod.card] at h_card
  exact_mod_cast h_card

/-- **Product of Gauss-sum pairs over even nontrivial characters**: for `p`
an odd prime, `∏_{χ even nontrivial} gaussSum χ · gaussSum χ⁻¹ = p^((p-3)/2)`.

Combines `gaussSum_mul_gaussSum_inv_eq_p` per term with the cardinality
`card_evenNontrivialCharacters` to get the product as `p^N` where
`N = card = (p-3)/2`. -/
theorem prod_gaussSum_mul_gaussSum_inv_eq_p_pow (hp_odd' : p ≠ 2) :
    ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
        (gaussSum χ (ZMod.stdAddChar (N := p)) *
          gaussSum χ⁻¹ (ZMod.stdAddChar (N := p))) =
      (p : ℂ) ^ ((p - 3) / 2) := by
  classical
  -- Each factor equals p.
  have h_per_χ : ∀ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
      gaussSum χ (ZMod.stdAddChar (N := p)) *
          gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) =
        (p : ℂ) := by
    intro χ hχ
    rw [BernoulliRegular.evenNontrivialCharacters, Finset.mem_filter] at hχ
    obtain ⟨_, hχ_even, hχ_ne⟩ := hχ
    exact gaussSum_mul_gaussSum_inv_eq_p p χ hχ_ne hχ_even
  rw [Finset.prod_congr rfl h_per_χ, Finset.prod_const,
    BernoulliRegular.card_evenNontrivialCharacters (p := p) hp_odd']

omit hp in
/-- **`evenNontrivialCharacters` is closed under inversion**: if χ is an
even nontrivial Dirichlet character mod p, so is χ⁻¹. -/
theorem inv_mem_evenNontrivialCharacters {χ : DirichletCharacter ℂ p}
    (hχ : χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p)) :
    χ⁻¹ ∈ BernoulliRegular.evenNontrivialCharacters (p := p) := by
  classical
  rw [BernoulliRegular.evenNontrivialCharacters, Finset.mem_filter] at hχ ⊢
  obtain ⟨_, hχ_even, hχ_ne⟩ := hχ
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · rw [DirichletCharacter.Even] at hχ_even ⊢
    rw [MulChar.inv_apply_eq_inv', hχ_even]
    norm_num
  · intro h_inv_eq_one
    apply hχ_ne
    have h_mul : χ⁻¹ * χ = 1 := MulChar.inv_mul χ
    rw [h_inv_eq_one, one_mul] at h_mul
    exact h_mul

/-- **Re-indexing identity**: `∏_{χ even nontrivial} gaussSum χ =
∏_{χ even nontrivial} gaussSum χ⁻¹`. Uses the involution χ ↔ χ⁻¹ on
`evenNontrivialCharacters`. -/
theorem prod_gaussSum_eq_prod_gaussSum_inv :
    ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
        gaussSum χ (ZMod.stdAddChar (N := p)) =
      ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)) := by
  classical
  refine (Finset.prod_bij (fun χ _ => χ⁻¹) ?_ ?_ ?_ ?_).symm
  · intro χ hχ
    exact inv_mem_evenNontrivialCharacters (p := p) hχ
  · intro χ₁ _ χ₂ _ heq
    have := congrArg (fun ψ => ψ⁻¹) heq
    simpa using this
  · intro χ hχ
    refine ⟨χ⁻¹, inv_mem_evenNontrivialCharacters (p := p) hχ, ?_⟩
    exact inv_inv χ
  · intro χ _; rfl

/-- **Square of the Gauss-sum product over even nontrivial characters**:
`(∏_{χ even nontrivial} gaussSum χ)² = p^((p-3)/2)`.

Combines:
* `prod_gaussSum_eq_prod_gaussSum_inv` (re-indexing via χ ↔ χ⁻¹).
* `prod_gaussSum_mul_gaussSum_inv_eq_p_pow`.

Then `(∏ g(χ))² = ∏ g(χ) · ∏ g(χ⁻¹) = ∏ g(χ)·g(χ⁻¹) = p^N`. -/
theorem prod_gaussSum_sq_eq_p_pow (hp_odd' : p ≠ 2) :
    (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
        gaussSum χ (ZMod.stdAddChar (N := p))) ^ 2 =
      (p : ℂ) ^ ((p - 3) / 2) := by
  classical
  rw [sq]
  nth_rewrite 2 [prod_gaussSum_eq_prod_gaussSum_inv (p := p)]
  rw [← Finset.prod_mul_distrib]
  exact prod_gaussSum_mul_gaussSum_inv_eq_p_pow (p := p) hp_odd'

/-- **hPlus in `DirichletLogSum` form**: composing `hPlus_formula_of_evenLValues`
with `evenLValueRhs_eq_gaussSum_inv_mul_DirichletLogSum` and the inverse-
reindexing identity `prod_gaussSum_eq_prod_gaussSum_inv` gives the analytic-side
`hPlus` formula entirely in terms of `cyclotomicHPlusFactor`, the inverse of
the product of `gaussSum` over even characters, and `∏ DirichletLogSum p χ⁻¹`:

  hPlus K =
    cyclotomicHPlusFactor · (∏ gaussSum χ)⁻¹ · ∏ DirichletLogSum p χ⁻¹

This is the analytic-side rewrite needed for the prefactor matching of
Sinnott's regulator-determinant identity. -/
theorem hPlus_eq_factor_gaussSum_inv_mul_prod_DirichletLogSum
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd' : p ≠ 2) :
    ((BernoulliRegular.hPlus K : ℕ) : ℂ) =
      BernoulliRegular.cyclotomicHPlusFactor (K := K) *
        (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
            gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ *
        ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ⁻¹ := by
  rw [BernoulliRegular.hPlus_formula_of_evenLValues (p := p) (K := K) hp_odd']
  -- ↑hPlus = cyclotomicHPlusFactor · ∏ evenLValueRhs
  have h_rhs : ∀ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
      BernoulliRegular.evenLValueRhs p χ =
        (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ * DirichletLogSum p χ⁻¹ :=
    fun χ _ => evenLValueRhs_eq_gaussSum_inv_mul_DirichletLogSum p χ
  rw [Finset.prod_congr rfl h_rhs]
  rw [Finset.prod_mul_distrib]
  rw [show (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
        (gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹) =
      (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
        gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))⁻¹ from
      Finset.prod_inv_distrib
        (fun χ : DirichletCharacter ℂ p => gaussSum χ⁻¹ (ZMod.stdAddChar (N := p)))]
  rw [← prod_gaussSum_eq_prod_gaussSum_inv (p := p)]
  ring

/-- **`cyclotomicHPlusFactor · regulator(K⁺) = 2·√(p^((p-3)/2)) / 2^((p-1)/2)`**:
the analytic prefactor for K⁺ in explicit closed form (cancelling the
`regulator` denominator inside `maximalRealSubfieldClassNumberFactor`).

Multiplying through `maximalRealSubfieldClassNumberFactor_eq_explicit` by
`regulator(K⁺)` (which is positive, hence non-zero) gives this clean
closed-form for the K⁺ analytic prefactor. -/
theorem cyclotomicHPlusFactor_mul_regulator_eq
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd' : p ≠ 2) :
    BernoulliRegular.cyclotomicHPlusFactor (K := K) *
        ((NumberField.Units.regulator (NumberField.maximalRealSubfield K) : ℝ) : ℂ) =
      ((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) / 2 ^ ((p - 1) / 2) : ℝ) : ℂ) := by
  have h_reg_pos : (0 : ℝ) < NumberField.Units.regulator
      (NumberField.maximalRealSubfield K) :=
    NumberField.Units.regulator_pos _
  have h_reg_ne : (NumberField.Units.regulator
      (NumberField.maximalRealSubfield K) : ℝ) ≠ 0 := h_reg_pos.ne'
  change BernoulliRegular.maximalRealSubfieldClassNumberFactor (K := K) * _ = _
  rw [BernoulliRegular.maximalRealSubfieldClassNumberFactor_eq_explicit
    (p := p) (K := K) hp_odd']
  push_cast
  have h_reg_C : ((NumberField.Units.regulator
      (NumberField.maximalRealSubfield K) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast h_reg_ne
  field_simp

/-- **`hPlus · regulator` in closed form**: composing the analytic
prefactor identity (`cyclotomicHPlusFactor_mul_regulator_eq`) with the
`DirichletLogSum`-form of `hPlus` (`hPlus_eq_factor_gaussSum_inv_mul_prod_DirichletLogSum`)
gives:

  ↑(hPlus K) · ↑(regulator K⁺) =
    (2·√(p^((p-3)/2)) / 2^((p-1)/2)) · (∏ gaussSum χ)⁻¹ ·
      ∏ DirichletLogSum p χ⁻¹

The LHS is the value identified by `KummerDirichletDeterminant` with
`regOfFamily(family)`. The RHS is the explicit analytic prefactor times
the Gauss-sum and DirichletLogSum products — the "analytic side" of the
prefactor matching for Sinnott's regulator determinant identity. -/
theorem hPlus_mul_regulator_eq_factor_gaussSum_inv_mul_prod_DirichletLogSum
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd' : p ≠ 2) :
    ((BernoulliRegular.hPlus K : ℕ) : ℂ) *
        ((NumberField.Units.regulator (NumberField.maximalRealSubfield K) : ℝ) : ℂ) =
      ((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) / 2 ^ ((p - 1) / 2) : ℝ) : ℂ) *
        (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
            gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ *
        ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ⁻¹ := by
  rw [hPlus_eq_factor_gaussSum_inv_mul_prod_DirichletLogSum (p := p) K hp_odd']
  rw [show
    BernoulliRegular.cyclotomicHPlusFactor (K := K) *
      (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
          gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ *
      (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
        DirichletLogSum p χ⁻¹) *
      ((NumberField.Units.regulator (NumberField.maximalRealSubfield K) : ℝ) : ℂ) =
    (BernoulliRegular.cyclotomicHPlusFactor (K := K) *
      ((NumberField.Units.regulator (NumberField.maximalRealSubfield K) : ℝ) : ℂ)) *
      (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
          gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ *
      ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
        DirichletLogSum p χ⁻¹ from by ring]
  rw [cyclotomicHPlusFactor_mul_regulator_eq (p := p) K hp_odd']

/-- **Prefactor squared identity**: the squared analytic prefactor combining
`2·√(p^((p-3)/2)) / 2^((p-1)/2)` with `(∏_{χ even nontriv} gaussSum χ)⁻¹`
satisfies a clean closed form:

  ((2·√(p^((p-3)/2)) / 2^((p-1)/2)) · (∏ gaussSum χ)⁻¹)² = 1 / 2^(p-3)

The `p^((p-3)/2)` in the numerator (from `√(p^((p-3)/2))²`) cancels exactly
with the `p^((p-3)/2)` in the denominator (from
`prod_gaussSum_sq_eq_p_pow`), leaving only the `2^(p-3)` factor in the
denominator. This is the analytic-side identity that allows the prefactor
matching with the Frobenius determinant evaluation. -/
theorem prefactor_sq_eq_inv_two_pow (hp_odd' : p ≠ 2) (hp_ge : 3 ≤ p) :
    (((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) / 2 ^ ((p - 1) / 2) : ℝ) : ℂ) *
        (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
            gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹) ^ 2 =
      ((2 : ℂ) ^ (p - 3))⁻¹ := by
  have hp_pos : 0 < p := hp.out.pos
  have hp_real : (0 : ℝ) ≤ p := by positivity
  have hp_pow_real : (0 : ℝ) ≤ (p : ℝ) ^ ((p - 1) / 2) := by positivity
  have hp_pow_nat : (0 : ℝ) ≤ (p : ℝ) ^ ((p - 3) / 2) := by positivity
  -- Step 1: expand the square.
  rw [mul_pow]
  -- Step 2: simplify the squared first factor:
  -- (2 · √(p^((p-3)/2)) / 2^((p-1)/2))^2 = 4 · p^((p-3)/2) / 2^(p-1)
  have h_first_sq : (((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) /
        2 ^ ((p - 1) / 2) : ℝ) : ℂ)) ^ 2 =
      ((4 * (p : ℝ) ^ ((p - 3) / 2) / 2 ^ (p - 1) : ℝ) : ℂ) := by
    push_cast
    rw [div_pow, mul_pow]
    rw [show ((2 : ℂ) : ℂ) ^ 2 = 4 from by norm_num]
    have h_sq_sqrt : (Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) : ℂ) ^ 2 =
        ((p : ℝ) ^ ((p - 3) / 2) : ℂ) := by
      push_cast
      exact_mod_cast Real.sq_sqrt hp_pow_nat
    rw [h_sq_sqrt]
    rw [show ((2 : ℂ) ^ ((p - 1) / 2)) ^ 2 = (2 : ℂ) ^ (p - 1) from by
      rw [← pow_mul]
      congr 1
      have h_even : Even (p - 1) := hp.out.even_sub_one hp_odd'
      obtain ⟨k, hk⟩ := h_even
      omega]
    push_cast
    ring
  rw [h_first_sq]
  -- Step 3: substitute the Gauss sum squared identity.
  rw [show (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
        gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ ^ 2 =
      ((∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
          gaussSum χ (ZMod.stdAddChar (N := p))) ^ 2)⁻¹ from
      inv_pow _ _]
  rw [prod_gaussSum_sq_eq_p_pow (p := p) hp_odd']
  -- Step 4: simplify `4 / 2^(p-1) = 1 / 2^(p-3)`.
  have h_p_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have h_p_pow_ne : (p : ℂ) ^ ((p - 3) / 2) ≠ 0 := pow_ne_zero _ h_p_ne
  have h_two_ne : (2 : ℂ) ≠ 0 := by norm_num
  rw [show ((4 * (p : ℝ) ^ ((p - 3) / 2) / 2 ^ (p - 1) : ℝ) : ℂ) =
      4 * (p : ℂ) ^ ((p - 3) / 2) / (2 : ℂ) ^ (p - 1) from by push_cast; ring]
  rw [show (2 : ℂ) ^ (p - 1) = (2 : ℂ) ^ ((p - 3) + 2) from by
    congr 1; omega]
  rw [pow_add, show (2 : ℂ) ^ 2 = 4 from by norm_num]
  field_simp

/-- **Sinnott's regulator identity squared in `DirichletLogSum` form**:
combining the analytic-side hPlus formula with the prefactor-squared identity
gives:

  (↑(hPlus K) · ↑(regulator K⁺))² =
    (∏_{χ even nontriv} DirichletLogSum p χ⁻¹)² / 2^(p-3)

This is the CLEAN squared form of `KummerDirichletDeterminant`. The
Frobenius determinant evaluation of the cyclotomic-unit log-embedding
matrix (the remaining PF-1 gap) needs to land on the same RHS — the
algebraic-side `|det M|²` must equal `(∏ DirichletLogSum)² / 2^(p-3)`. -/
theorem hPlus_mul_regulator_sq_eq
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    [NumberField.IsCMField K]
    (hp_odd' : p ≠ 2) (hp_ge : 3 ≤ p) :
    (((BernoulliRegular.hPlus K : ℕ) : ℂ) *
        ((NumberField.Units.regulator (NumberField.maximalRealSubfield K) : ℝ) : ℂ)) ^ 2 =
      (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ⁻¹) ^ 2 / (2 : ℂ) ^ (p - 3) := by
  rw [hPlus_mul_regulator_eq_factor_gaussSum_inv_mul_prod_DirichletLogSum
    (p := p) K hp_odd']
  rw [show
    (((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) / 2 ^ ((p - 1) / 2) : ℝ) : ℂ) *
        (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
            gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹ *
        ∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ⁻¹) ^ 2 =
      (((2 * Real.sqrt ((p : ℝ) ^ ((p - 3) / 2)) / 2 ^ ((p - 1) / 2) : ℝ) : ℂ) *
          (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
              gaussSum χ (ZMod.stdAddChar (N := p)))⁻¹) ^ 2 *
        (∏ χ ∈ BernoulliRegular.evenNontrivialCharacters (p := p),
          DirichletLogSum p χ⁻¹) ^ 2 from by ring]
  rw [prefactor_sq_eq_inv_two_pow (p := p) hp_odd' hp_ge]
  rw [inv_mul_eq_div]

end Sinnott

end FLT37

end BernoulliRegular

end
