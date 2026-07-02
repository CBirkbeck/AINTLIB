module

public import Mathlib

/-!
# Vertical behaviour of the Gamma function  (SP1-AC leaf A1)

Two-sided control of `‖Γ(σ+it)‖` on vertical strips, built WITHOUT Stirling asymptotics:
the moduli on the lines `Re = 1/2` and `Re = 1` are **exact** by the reflection formula,

* `norm_Gamma_half_add_mul_I_sq : ‖Γ(1/2+it)‖² = π / cosh(πt)`,
* `norm_Gamma_one_add_mul_I_sq  : ‖Γ(1+it)‖²  = πt / sinh(πt)`  (`t ≠ 0`),

and the strip bounds in between/beyond follow from these by the Hadamard three-lines
theorem, the recurrence `Γ(s+1) = sΓ(s)`, and `1/Γ(z) = Γ(1-z)·sin(πz)/π` (upcoming in
this file). These feed the convexity bounds for `ζ_K` (AC-A3) and the Jensen zero
counting (AC-A4); see `.mathlib-quality/decomposition-sp1ac.md`.
-/

namespace DedekindResidue

@[expose] public section

open Complex
open scoped Real

/-- Exact modulus of `Γ` on the critical line `Re = 1/2`:
`‖Γ(1/2+it)‖² = π/cosh(πt)`. -/
theorem norm_Gamma_half_add_mul_I_sq (t : ℝ) :
    ‖Complex.Gamma (1/2 + t * Complex.I)‖^2 = π / Real.cosh (π * t) := by
  have key := Complex.Gamma_mul_Gamma_one_sub (1/2 + t * Complex.I)
  have hconj : (1 : ℂ) - (1/2 + t * Complex.I)
      = (starRingEnd ℂ) (1/2 + t * Complex.I) := by
    apply Complex.ext <;> simp
    norm_num
  rw [hconj, Complex.Gamma_conj, Complex.mul_conj] at key
  have hsin : Complex.sin (π * (1/2 + t * Complex.I))
      = ((Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [show (π : ℂ) * (1/2 + t * Complex.I)
        = π/2 + ((π * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
      Complex.cos_mul_I]
    push_cast [Complex.ofReal_cosh]
    ring
  rw [hsin] at key
  -- key : ↑(normSq Γz) = ↑π / ↑cosh(πt); cast down
  have hcosh : Real.cosh (π * t) ≠ 0 := (Real.cosh_pos _).ne'
  have : ((Complex.normSq (Complex.Gamma (1/2 + t * Complex.I)) : ℝ) : ℂ)
      = ((π / Real.cosh (π * t) : ℝ) : ℂ) := by
    rw [key]
    push_cast
    ring
  have hreal := Complex.ofReal_injective this
  rw [← hreal, Complex.normSq_eq_norm_sq]

/-- Exact modulus of `Γ` on the line `Re = 1`: `‖Γ(1+it)‖² = πt/sinh(πt)` (`t ≠ 0`). -/
theorem norm_Gamma_one_add_mul_I_sq {t : ℝ} (ht : t ≠ 0) :
    ‖Complex.Gamma (1 + t * Complex.I)‖^2 = π * t / Real.sinh (π * t) := by
  have htI : (t : ℂ) * Complex.I ≠ 0 := by
    simp [Complex.ext_iff, ht]
  have key := Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * Complex.I)
  -- Γ(1+it) = it·Γ(it)
  have hrec : Complex.Gamma (1 + t * Complex.I)
      = (t : ℂ) * Complex.I * Complex.Gamma ((t : ℂ) * Complex.I) := by
    rw [add_comm, Complex.Gamma_add_one _ htI]
  have hconj : (1 : ℂ) - (t : ℂ) * Complex.I
      = (starRingEnd ℂ) (1 + t * Complex.I) := by
    apply Complex.ext <;> simp
  have hsin : Complex.sin (π * ((t : ℂ) * Complex.I))
      = ((Real.sinh (π * t) : ℝ) : ℂ) * Complex.I := by
    rw [show (π : ℂ) * ((t : ℂ) * Complex.I) = ((π * t : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.sin_mul_I]
    push_cast [Complex.ofReal_sinh]
    ring
  rw [hconj, Complex.Gamma_conj, hsin] at key
  -- key : Γ(it) · conj Γ(1+it) = π/(sinh(πt)·I)
  have hsinh : Real.sinh (π * t) ≠ 0 := by
    rw [ne_eq, Real.sinh_eq_zero]
    exact mul_ne_zero Real.pi_ne_zero ht
  have key2 : ((Complex.normSq (Complex.Gamma (1 + t * Complex.I)) : ℝ) : ℂ)
      = ((π * t / Real.sinh (π * t) : ℝ) : ℂ) := by
    calc ((Complex.normSq (Complex.Gamma (1 + t * Complex.I)) : ℝ) : ℂ)
        = Complex.Gamma (1 + t * Complex.I)
          * (starRingEnd ℂ) (Complex.Gamma (1 + t * Complex.I)) :=
          (Complex.mul_conj _).symm
      _ = ((t : ℂ) * Complex.I) * (Complex.Gamma ((t : ℂ) * Complex.I)
          * (starRingEnd ℂ) (Complex.Gamma (1 + t * Complex.I))) := by
          rw [hrec]; ring
      _ = ((t : ℂ) * Complex.I)
          * ((π : ℂ) / (((Real.sinh (π * t) : ℝ) : ℂ) * Complex.I)) := by rw [key]
      _ = ((π * t / Real.sinh (π * t) : ℝ) : ℂ) := by
          have hsc : ((Real.sinh (π * t) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsinh
          push_cast
          field_simp
  have hreal := Complex.ofReal_injective key2
  rw [← hreal, Complex.normSq_eq_norm_sq]

end

end DedekindResidue
