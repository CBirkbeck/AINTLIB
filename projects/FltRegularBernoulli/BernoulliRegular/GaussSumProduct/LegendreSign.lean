module

public import BernoulliRegular.GaussSumProduct.RootNumberPairing

@[expose] public section

noncomputable section

namespace BernoulliRegular

open Complex

section LegendreRootNumberSign

variable (p : ℕ) [hp : Fact p.Prime]

/-- **Key identity** linking rootNumber, L(1, η), and B_{1, η} for the
Legendre-symbol character `η = legendreDirichlet p` with `p ≡ 3 mod 4`.

For the odd primitive quadratic `η`, applying `odd_LFunction_one_eq_oddLValueRhs`
(project, T021) to `η⁻¹ = η`:

`L(η, 1) = (π · I / p) · τ(η) · B_{1, η}`

Substituting `τ(η) = rootNumber η · I · √p`:

`L(η, 1) = -(π / √p) · rootNumber η · B_{1, η}`

Equivalently: `L(η, 1) · √p + π · rootNumber η · B_{1, η} = 0`. -/
theorem legendreDirichlet_L1_rootNumber_relation (hp_three_mod_four : p % 4 = 3) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    DirichletCharacter.LFunction (legendreDirichlet p) 1 * (p : ℂ) ^ (1 / 2 : ℂ) +
      (Real.pi : ℂ) *
        (DirichletCharacter.rootNumber (legendreDirichlet p)) *
        BernoulliGen (legendreDirichlet p) 1 = 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  have h_prim : (legendreDirichlet p).IsPrimitive := legendreDirichlet_isPrimitive p hp_odd
  have h_odd : (legendreDirichlet p).Odd := legendreDirichlet_odd p hp_three_mod_four
  have h_not_even : ¬ (legendreDirichlet p).Even := h_odd.not_even
  have h_ne_one : legendreDirichlet p ≠ 1 := legendreDirichlet_ne_one p hp_odd
  -- η⁻¹ = η for η quadratic.
  have h_inv_eq : (legendreDirichlet p)⁻¹ = legendreDirichlet p :=
    (legendreDirichlet_isQuadratic p).inv
  -- L(1, η) = oddLValueRhs p η via T021.
  have h_L1 : DirichletCharacter.LFunction (legendreDirichlet p) 1 =
      oddLValueRhs p (legendreDirichlet p) :=
    odd_LFunction_one_eq_oddLValueRhs (p := p) h_prim h_odd h_ne_one
  -- Expand oddLValueRhs: `(π·I / p) · τ(η) · B_{1, η⁻¹}`.
  unfold oddLValueRhs at h_L1
  rw [h_inv_eq] at h_L1
  -- rootNumber η = gaussSum η stdAddChar / I / √p  (from the definition for odd)
  have h_root_def : DirichletCharacter.rootNumber (legendreDirichlet p) =
      gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) /
        Complex.I / ((p : ℂ) ^ (1 / 2 : ℂ)) := by
    unfold DirichletCharacter.rootNumber
    rw [if_neg h_not_even, pow_one]
  -- Solve for gaussSum: gaussSum = rootNumber · I · √p.
  have hp_ne_zero : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hp_cpow_ne_zero : (p : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl hp_ne_zero)
  have h_I_ne_zero : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h_gs_eq : gaussSum (legendreDirichlet p) (ZMod.stdAddChar : AddChar (ZMod p) ℂ) =
      DirichletCharacter.rootNumber (legendreDirichlet p) *
        (Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ))) := by
    rw [h_root_def]; field_simp
  rw [h_gs_eq] at h_L1
  -- Now h_L1: L(1, η) = (π·I / p) · (rootNumber η · I · √p) · B_{1, η}.
  -- Simplify: = -π · rootNumber η · √p · B_{1, η} / p = -π · rootNumber η · B_{1, η} / √p
  have h_half_sq : ((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2 = (p : ℂ) := by
    rw [← Complex.cpow_mul_nat]
    norm_num
  -- Rearrange: L(1, η) · √p + π · rootNumber η · B_{1, η} = 0
  rw [h_L1]
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  -- Substitute (√p)² = p and simplify.
  -- After substitution:
  -- (π · I / p) · (rootNumber · I · √p) · B · √p + π · rootNumber · B
  -- = (π · I² · rootNumber · (√p)² · B) / p + π · rootNumber · B
  -- = (π · (-1) · rootNumber · p · B) / p + π · rootNumber · B
  -- = -π · rootNumber · B + π · rootNumber · B = 0
  have key : (Real.pi : ℂ) * Complex.I / (p : ℂ) *
        (DirichletCharacter.rootNumber (legendreDirichlet p) *
          (Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)))) *
      BernoulliGen (legendreDirichlet p) 1 * ((p : ℂ) ^ (1 / 2 : ℂ)) =
      -((Real.pi : ℂ) *
        (DirichletCharacter.rootNumber (legendreDirichlet p)) *
        BernoulliGen (legendreDirichlet p) 1) := by
    have expand : (Real.pi : ℂ) * Complex.I / (p : ℂ) *
          (DirichletCharacter.rootNumber (legendreDirichlet p) *
            (Complex.I * ((p : ℂ) ^ (1 / 2 : ℂ)))) *
        BernoulliGen (legendreDirichlet p) 1 * ((p : ℂ) ^ (1 / 2 : ℂ)) =
        (Real.pi : ℂ) * (Complex.I ^ 2) *
          (DirichletCharacter.rootNumber (legendreDirichlet p)) *
          (((p : ℂ) ^ (1 / 2 : ℂ)) ^ 2) *
          BernoulliGen (legendreDirichlet p) 1 / (p : ℂ) := by ring
    rw [expand, hI, h_half_sq]
    field_simp
  linear_combination key

/-- The product `rootNumber η · B_{1, η}` is a negative real number,
derived from the bridge identity combined with `L(η, 1) > 0`.

Since `rootNumber η ∈ {±1}` and `B_{1, η}` is real (η being real-valued),
this forces them to have **opposite signs**. The remaining step for
the Gauss sum sign theorem is to determine the sign of `B_{1, η}`
independently. -/
theorem rootNumber_B1_product_neg (hp_three_mod_four : p % 4 = 3) :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    let z := (DirichletCharacter.rootNumber (legendreDirichlet p)) *
      BernoulliGen (legendreDirichlet p) 1
    z.im = 0 ∧ z.re < 0 := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  have hp_odd : p ≠ 2 := by omega
  have h_ne_one : legendreDirichlet p ≠ 1 := legendreDirichlet_ne_one p hp_odd
  have h_quad : (legendreDirichlet p).IsQuadratic := legendreDirichlet_isQuadratic p
  have h_L_pos := LFunction_one_pos_of_real_quadratic h_quad h_ne_one
  have h_bridge := legendreDirichlet_L1_rootNumber_relation p hp_three_mod_four
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.out.pos
  have h_pi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  -- Cast (p : ℂ)^(1/2 : ℂ) to a positive real.
  have h_sqrtp_real : ((p : ℂ) ^ (1 / 2 : ℂ)).im = 0 ∧
      0 < ((p : ℂ) ^ (1 / 2 : ℂ)).re := by
    have hcast : ((p : ℂ) ^ (1 / 2 : ℂ)) = (((p : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) from by push_cast; ring,
        ← Complex.ofReal_natCast p]
      exact (Complex.ofReal_cpow hp_pos.le _).symm
    rw [hcast]
    refine ⟨Complex.ofReal_im _, ?_⟩
    simp only [Complex.ofReal_re]
    exact Real.rpow_pos_of_pos hp_pos _
  -- The bridge is a complex equation. Take real and imaginary parts.
  have h_L_im : (DirichletCharacter.LFunction (legendreDirichlet p) 1).im = 0 := h_L_pos.1
  have h_L_re : 0 < (DirichletCharacter.LFunction (legendreDirichlet p) 1).re := h_L_pos.2
  set L : ℝ := (DirichletCharacter.LFunction (legendreDirichlet p) 1).re
  set sq : ℝ := ((p : ℂ) ^ (1 / 2 : ℂ)).re
  have h_sq_pos : 0 < sq := h_sqrtp_real.2
  set z : ℂ := (DirichletCharacter.rootNumber (legendreDirichlet p)) *
    BernoulliGen (legendreDirichlet p) 1
  -- Bridge equation: L · sqrt p + π · z = 0 (in ℂ).
  -- Take real part:
  --   L.re · sq.re + π.re · z.re = L.re · sq (since L.im = sq.im = 0 and π is real)
  have h_bridge_re : L * sq + Real.pi * z.re = 0 := by
    have hre := congrArg Complex.re h_bridge
    simp only [Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re] at hre
    rw [h_L_im, h_sqrtp_real.1] at hre
    simp only [zero_mul, mul_zero, add_zero] at hre
    -- hre : L · sq + (π · rootNumber.re · B.re - π · rootNumber.im · B.im) = 0
    -- z.re = rootNumber.re · B.re - rootNumber.im · B.im
    -- So π · z.re = π · (rootNumber.re · B.re - rootNumber.im · B.im)
    --            = π · rootNumber.re · B.re - π · rootNumber.im · B.im
    have h_zre : z.re = (DirichletCharacter.rootNumber (legendreDirichlet p)).re *
        (BernoulliGen (legendreDirichlet p) 1).re -
      (DirichletCharacter.rootNumber (legendreDirichlet p)).im *
        (BernoulliGen (legendreDirichlet p) 1).im := by
      change ((DirichletCharacter.rootNumber (legendreDirichlet p)) *
        BernoulliGen (legendreDirichlet p) 1).re = _
      rw [Complex.mul_re]
    rw [h_zre]
    linarith [hre]
  have h_bridge_im : Real.pi * z.im = 0 := by
    have him := congrArg Complex.im h_bridge
    simp only [Complex.add_im, Complex.mul_im, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.zero_im,
      zero_mul, add_zero] at him
    rw [h_L_im, h_sqrtp_real.1] at him
    simp only [zero_mul, mul_zero, add_zero] at him
    have h_zim : z.im = (DirichletCharacter.rootNumber (legendreDirichlet p)).re *
        (BernoulliGen (legendreDirichlet p) 1).im +
      (DirichletCharacter.rootNumber (legendreDirichlet p)).im *
        (BernoulliGen (legendreDirichlet p) 1).re := by
      change ((DirichletCharacter.rootNumber (legendreDirichlet p)) *
        BernoulliGen (legendreDirichlet p) 1).im = _
      rw [Complex.mul_im]
    rw [h_zim]
    linarith [him]
  refine ⟨?_, ?_⟩
  · -- z.im = 0 from the imaginary part of the bridge.
    rcases mul_eq_zero.mp h_bridge_im with h | h
    · exact absurd h h_pi_pos.ne'
    · exact h
  · -- z.re < 0 from L · sq > 0 and L · sq + π · z.re = 0.
    have h_Lsq_pos : 0 < L * sq := mul_pos h_L_re h_sq_pos
    nlinarith [h_bridge_re, h_pi_pos, h_Lsq_pos]

end LegendreRootNumberSign

end BernoulliRegular
