import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.LogEmbedding
import Mathlib.Analysis.SpecialFunctions.Complex.Circle


/-!
# LV-SIN-B: Vandermonde-style determinant evaluation

The Kummer-Dirichlet determinant identity for cyclotomic units.

For real cyclotomic units `realCyclotomicUnit k = (1-ζ^k)(1-ζ^{-k}) /
((1-ζ)(1-ζ^{-1}))`, applying a complex embedding `φ(ζ) = e^{2πi a/p}`:

  `|φ(realCyclotomicUnit k)| = sin²(πak/p) / sin²(πa/p)`

The log-embedding matrix has entries

  `log|φ_a(realCyclotomicUnit k)| = 2 log|sin(πak/p)| - 2 log|sin(πa/p)|`

Its determinant evaluates via character orthogonality + Dirichlet's
class number formula derivation to a product of L-values.

This is the analytic heart of Sinnott's formula.

## Foundational lemmas
-/

@[expose] public section

noncomputable section

open Complex Real

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

/-- **Norm-squared of `1 - e^{iθ}`**: `|1 - e^{iθ}|² = 2 - 2 cos θ`. -/
theorem normSq_one_sub_exp_I_mul (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) = 2 - 2 * Real.cos θ := by
  rw [Complex.exp_mul_I, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.cos_ofReal_re,
    Complex.mul_re, Complex.sin_ofReal_re, Complex.I_re, Complex.I_im,
    Complex.sin_ofReal_im, Complex.cos_ofReal_im, mul_zero,
    mul_one, sub_self, Complex.sub_im, Complex.one_im,
    Complex.add_im, Complex.mul_im, zero_sub]
  have h_pyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  nlinarith [h_pyth]

/-- **Norm-squared of `1 - e^{iθ}` as `4 sin²(θ/2)`**: half-angle form. -/
theorem normSq_one_sub_exp_I_mul_eq_four_sin_sq (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) =
      4 * Real.sin (θ / 2) ^ 2 := by
  rw [normSq_one_sub_exp_I_mul]
  -- 2 - 2 cos θ = 4 sin²(θ/2): use Real.cos_eq_one_sub_two_sin_sq via half-angle.
  -- cos(2x) = 1 - 2 sin²(x), so cos(θ) = 1 - 2 sin²(θ/2).
  have h_cos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have : Real.cos (2 * (θ / 2)) = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      rw [Real.cos_two_mul]
      have h_pyth : Real.sin (θ / 2) ^ 2 + Real.cos (θ / 2) ^ 2 = 1 :=
        Real.sin_sq_add_cos_sq _
      nlinarith [h_pyth]
    rw [show 2 * (θ / 2) = θ from by ring] at this
    exact this
  rw [h_cos]
  ring

/-- **Norm of `1 - e^{iθ}`**: `‖1 - e^{iθ}‖ = 2 |sin(θ/2)|`. -/
theorem norm_one_sub_exp_I_mul (θ : ℝ) :
    ‖(1 - Complex.exp (θ * Complex.I))‖ = 2 * |Real.sin (θ / 2)| := by
  have h_sq : ‖(1 - Complex.exp (θ * Complex.I))‖ ^ 2 =
      (2 * |Real.sin (θ / 2)|) ^ 2 := by
    rw [Complex.sq_norm, normSq_one_sub_exp_I_mul_eq_four_sin_sq]
    rw [mul_pow, sq_abs]; ring
  have h_nonneg : 0 ≤ ‖(1 - Complex.exp (θ * Complex.I))‖ := norm_nonneg _
  have h_pos : 0 ≤ 2 * |Real.sin (θ / 2)| := by positivity
  nlinarith [h_sq, h_nonneg, h_pos]

/-- **Specialised**: for `θ = 2π · q` with rational q, `‖1 - e^{2πi q}‖ = 2|sin(πq)|`. -/
theorem norm_one_sub_exp_two_pi_I_mul (q : ℝ) :
    ‖(1 - Complex.exp (((2 * Real.pi * q) : ℝ) * Complex.I))‖ =
      2 * |Real.sin (Real.pi * q)| := by
  rw [norm_one_sub_exp_I_mul]
  congr 2
  ring_nf

/-- **Cyclotomic case**: for an integer `n` mod `p`, the norm of `1 - e^{2πi n/p}`
in ℂ equals `2|sin(π n / p)|`. -/
theorem norm_one_sub_exp_two_pi_I_div_p (n : ℕ) (p : ℕ) (_hp : 0 < p) :
    ‖(1 - Complex.exp (((2 * Real.pi * (n / p : ℝ)) : ℝ) * Complex.I))‖ =
      2 * |Real.sin (Real.pi * n / p)| := by
  rw [norm_one_sub_exp_two_pi_I_mul]
  congr 2
  field_simp

/-- **Cyclotomic-unit log-embedding formula (abstract)**: for any field K
with a complex embedding `φ : K → ℂ` such that `φ(ζ) = e^{2πi a/p}`, the
absolute value `‖φ((1 - ζ^k)/(1 - ζ))‖` is the ratio of sines

  `‖φ((1 - ζ^k)/(1 - ζ))‖ = |sin(πak/p)| / |sin(πa/p)|`.

This is the cyclotomic-unit log evaluation that feeds the Kummer-Dirichlet
determinant. Stated for the abstract form; downstream code instantiates
with specific cyclotomic embeddings. -/
def CyclotomicUnitNormFormula (p : ℕ) : Prop :=
  ∀ (a k : ℕ) (_ : 0 < p) (_ : 1 ≤ a) (_ : a < p) (_ : 1 ≤ k) (_ : k < p),
    Real.sin (Real.pi * a / p) ≠ 0 →
    let φ_one_sub_zeta_k := (1 - Complex.exp ((2 * Real.pi * a * k / p) * Complex.I))
    let φ_one_sub_zeta := (1 - Complex.exp ((2 * Real.pi * a / p) * Complex.I))
    ‖φ_one_sub_zeta_k‖ / ‖φ_one_sub_zeta‖ =
      |Real.sin (Real.pi * a * k / p)| / |Real.sin (Real.pi * a / p)|

/-- **`CyclotomicUnitNormFormula` is PROVEN**: direct from the foundational
norm formulas. -/
theorem cyclotomicUnitNormFormula_proven (p : ℕ) :
    CyclotomicUnitNormFormula p := by
  intro a k _ _ _ _ _ h_sin_ne
  simp only []
  have h1 : ‖(1 - Complex.exp ((2 * Real.pi * a * k / p : ℂ) * Complex.I))‖ =
      2 * |Real.sin (Real.pi * a * k / p)| := by
    have h_eq : (2 * Real.pi * (a : ℂ) * k / p : ℂ) =
        ((2 * Real.pi * ((a * k : ℕ) / p : ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h_eq, norm_one_sub_exp_two_pi_I_mul]
    push_cast
    ring_nf
  have h2 : ‖(1 - Complex.exp ((2 * Real.pi * a / p : ℂ) * Complex.I))‖ =
      2 * |Real.sin (Real.pi * a / p)| := by
    have h_eq : (2 * Real.pi * (a : ℂ) / p : ℂ) =
        ((2 * Real.pi * ((a : ℕ) / p : ℝ) : ℝ) : ℂ) := by
      push_cast; ring
    rw [h_eq, norm_one_sub_exp_two_pi_I_mul]
    ring_nf
  rw [h1, h2]
  rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]

/-- **Log version of the cyclotomic-unit norm formula**: in additive form,
`log‖φ((1-ζ^k))‖ - log‖φ((1-ζ))‖ = log|sin(πak/p)| - log|sin(πa/p)|`. -/
theorem log_norm_one_sub_exp_diff (a k p : ℕ) (_hp : 0 < p)
    (h_sin_ne_ak : Real.sin (Real.pi * (a * k / p : ℝ)) ≠ 0)
    (h_sin_ne_a : Real.sin (Real.pi * (a / p : ℝ)) ≠ 0) :
    Real.log ‖(1 - Complex.exp (((2 * Real.pi * ((a * k : ℕ) / p : ℝ)) : ℝ)
        * Complex.I))‖ -
      Real.log ‖(1 - Complex.exp (((2 * Real.pi * ((a : ℕ) / p : ℝ)) : ℝ)
        * Complex.I))‖ =
    Real.log |Real.sin (Real.pi * (a * k / p : ℝ))| -
      Real.log |Real.sin (Real.pi * (a / p : ℝ))| := by
  rw [norm_one_sub_exp_two_pi_I_mul, norm_one_sub_exp_two_pi_I_mul]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by simp [h_sin_ne_ak])]
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by simp [h_sin_ne_a])]
  push_cast
  ring

/-- **k ↔ p-k symmetry**: `|sin(π(p-k)/p)| = |sin(πk/p)|`.

Direct from `sin(π - x) = sin(x)` since `π(p-k)/p = π - πk/p`. -/
theorem abs_sin_pi_sub_div (k p : ℕ) (hk : k ≤ p) :
    |Real.sin (Real.pi * ((p - k : ℕ) / p : ℝ))| =
      |Real.sin (Real.pi * (k / p : ℝ))| := by
  by_cases hp : p = 0
  · subst hp
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp
  have hp_pos : 0 < (p : ℝ) := by positivity
  have h_diff : (Real.pi * ((p - k : ℕ) / p : ℝ)) =
      Real.pi - Real.pi * (k / p : ℝ) := by
    rw [Nat.cast_sub hk]
    field_simp
  rw [h_diff, Real.sin_pi_sub]

/-- **Even-character `p − a` substitution**: for an even Dirichlet character
`χ` mod `p`, the cast `((p - a : ℕ) : ZMod p)` equals `-(a : ZMod p)` when
`a ≤ p`, and `χ` evaluated there equals `χ a`. -/
theorem dirichletCharacter_even_apply_pSub
    {p : ℕ} (χ : DirichletCharacter ℂ p) (hχ : χ.Even)
    {a : ℕ} (ha : a ≤ p) :
    χ ((p - a : ℕ) : ZMod p) = χ (a : ZMod p) := by
  have h_neg : ((p - a : ℕ) : ZMod p) = -((a : ZMod p)) := by
    rw [Nat.cast_sub ha, ZMod.natCast_self, zero_sub]
  rw [h_neg, hχ.eval_neg]

/-- **Character-substitution identity**: for `χ` a Dirichlet character mod `p`
and `k : (ZMod p)ˣ` a unit, character-weighted sums on `ZMod p` satisfy
`∑ a, χ(a) · g(a · k) = χ(k⁻¹) · ∑ a, χ(a) · g(a)`.

This is the eigenvalue identity that diagonalizes Sinnott's matrix in the
χ-basis: when `g(a) = log|2 sin(πa/p)|`, `(a · k)` corresponds to the
cyclotomic-unit shift `(1 - ζ^k) → (1 - ζ^{ak})`, and the χ-eigenvalue
becomes `χ(k⁻¹) · D_χ` where `D_χ := ∑ a, χ(a) g(a)`. -/
theorem dirichletCharacter_sum_mulRight_substitution
    {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (k : (ZMod p)ˣ) (g : ZMod p → ℂ) :
    ∑ a : ZMod p, χ a * g (a * (k : ZMod p)) =
      χ ((↑k⁻¹ : ZMod p)) * ∑ a : ZMod p, χ a * g a := by
  -- Substitute a ↦ a · k⁻¹ via Equiv.sum_comp.
  rw [← Equiv.sum_comp (Units.mulRight k⁻¹)
      (fun a : ZMod p => χ a * g (a * (↑k : ZMod p)))]
  -- After rewrite, goal: ∑ a, χ(a · k⁻¹) * g((a · k⁻¹) · k) = ...
  have h_simplify : ∀ a : ZMod p,
      χ ((Units.mulRight k⁻¹) a) * g (((Units.mulRight k⁻¹) a) * (↑k : ZMod p)) =
        χ (↑(k⁻¹ : (ZMod p)ˣ) : ZMod p) * (χ a * g a) := by
    intro a
    change χ (a * (↑k⁻¹ : ZMod p)) * g (a * (↑k⁻¹ : ZMod p) * (↑k : ZMod p)) =
        χ (↑(k⁻¹ : (ZMod p)ˣ) : ZMod p) * (χ a * g a)
    have h_can : (a * (↑k⁻¹ : ZMod p)) * (↑k : ZMod p) = a := by
      rw [mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    rw [h_can, map_mul χ]
    ring
  rw [Finset.sum_congr rfl (fun a _ => h_simplify a), ← Finset.mul_sum]

/-- **Matrix-eigenvalue identity**: for any Dirichlet character `χ` mod `p`,
unit `k : (ZMod p)ˣ`, and function `g : ZMod p → ℂ`, the χ-row of the
matrix `M[k, a] := g(a · k) − g(a)` (the "cyclotomic-unit log-difference"
shape) evaluates as

  `∑ a, χ(a) · M[k, a] = (χ(k⁻¹) − 1) · ∑ a, χ(a) · g(a)`.

Direct corollary of `dirichletCharacter_sum_mulRight_substitution`: split
the sum, apply substitution to the `g(a · k)` term, factor.

For the cyclotomic-unit specialisation `g(a) = log|2 sin(πa/p)|` and even
nontrivial χ, the sum on the right is `D_χ` (the DirichletLogSum), making
this the eigenvalue formula `(χ(k⁻¹) − 1) · D_χ` for column `k`. -/
theorem dirichletCharacter_sum_matrix_eigenvalue
    {p : ℕ} [Fact p.Prime]
    (χ : DirichletCharacter ℂ p) (k : (ZMod p)ˣ) (g : ZMod p → ℂ) :
    ∑ a : ZMod p, χ a * (g (a * (↑k : ZMod p)) - g a) =
      (χ (↑(k⁻¹ : (ZMod p)ˣ) : ZMod p) - 1) * ∑ a : ZMod p, χ a * g a := by
  have h_distrib : ∀ a : ZMod p,
      χ a * (g (a * (↑k : ZMod p)) - g a) =
        χ a * g (a * (↑k : ZMod p)) - χ a * g a := fun a => mul_sub _ _ _
  rw [Finset.sum_congr rfl (fun a _ => h_distrib a), Finset.sum_sub_distrib,
    dirichletCharacter_sum_mulRight_substitution χ k g]
  ring

/-- **Even-character full→half sum identity for `log|2 sin|`**: for an odd
prime `p` and an even Dirichlet character `χ` mod `p`, the full character-
weighted sum over `Finset.Ico 1 p` of `Real.log (2 · |sin (πa/p)|)` equals
twice the half sum over `Finset.Ico 1 ((p+1)/2)`.

This is the symmetry identity used in Sinnott's matrix-eigenvalue
computation: pair `a` with `p − a`; both `χ(a) = χ(p − a)` (even character)
and `|sin(πa/p)| = |sin(π(p−a)/p)|` (sin reflection) hold. -/
theorem dirichletCharacter_even_log_sin_full_eq_two_half
    {p : ℕ} (hp_odd : Odd p) (χ : DirichletCharacter ℂ p) (hχ : χ.Even) :
    ∑ a ∈ Finset.Ico 1 p,
        χ ((a : ℕ) : ZMod p) *
          ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) =
      2 * ∑ a ∈ Finset.Ico 1 ((p + 1) / 2),
        χ ((a : ℕ) : ZMod p) *
          ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) := by
  -- Split Ico 1 p = Ico 1 ((p+1)/2) ⊔ Ico ((p+1)/2) p.
  obtain ⟨n, hn⟩ := hp_odd
  -- For p = 2n+1, (p+1)/2 = n+1, and Ico 1 p splits at n+1.
  have h_split_idx : (p + 1) / 2 = n + 1 := by omega
  have h_p : p = 2 * n + 1 := hn
  have h_le : (p + 1) / 2 ≤ p := by omega
  rw [← Finset.sum_Ico_consecutive _ (by omega : 1 ≤ (p + 1) / 2) h_le]
  -- The high half = the low half by the substitution a ↦ p - a.
  -- Specifically: Ico ((p+1)/2) p ↔ Ico 1 ((p+1)/2) under a ↦ p-a.
  -- Use Finset.sum_nbij' with the involution.
  have h_high_eq_low :
      ∑ a ∈ Finset.Ico ((p + 1) / 2) p,
          χ ((a : ℕ) : ZMod p) *
            ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) =
        ∑ a ∈ Finset.Ico 1 ((p + 1) / 2),
          χ ((a : ℕ) : ZMod p) *
            ((Real.log (2 * |Real.sin (Real.pi * a / p)|) : ℝ) : ℂ) := by
    refine Finset.sum_nbij' (fun a => p - a) (fun a => p - a) ?_ ?_ ?_ ?_ ?_
    · -- maps Ico ((p+1)/2) p → Ico 1 ((p+1)/2)
      intro a ha
      rw [Finset.mem_Ico] at ha ⊢
      omega
    · -- maps Ico 1 ((p+1)/2) → Ico ((p+1)/2) p
      intro a ha
      rw [Finset.mem_Ico] at ha ⊢
      omega
    · -- left inverse: p - (p - a) = a (need a ≤ p)
      intro a ha
      rw [Finset.mem_Ico] at ha
      have : a ≤ p := by omega
      omega
    · -- right inverse: p - (p - a) = a (need a ≤ p)
      intro a ha
      rw [Finset.mem_Ico] at ha
      have : a ≤ p := by omega
      omega
    · -- pointwise equality of summands
      intro a ha
      rw [Finset.mem_Ico] at ha
      have ha_le : a ≤ p := by omega
      rw [dirichletCharacter_even_apply_pSub χ hχ ha_le]
      congr 1
      -- log argument: 2 * |sin (π(p-a)/p)| = 2 * |sin (πa/p)|
      have h_sin_eq :
          |Real.sin (Real.pi * ((p - a : ℕ) : ℝ) / (p : ℝ))| =
            |Real.sin (Real.pi * (a : ℝ) / (p : ℝ))| := by
        have hcast : (Real.pi * ((p - a : ℕ) : ℝ) / (p : ℝ)) =
            (Real.pi * (((p - a : ℕ) : ℝ) / (p : ℝ))) := by ring
        rw [hcast]
        have hcast2 : (Real.pi * (a : ℝ) / (p : ℝ)) =
            (Real.pi * ((a : ℝ) / (p : ℝ))) := by ring
        rw [hcast2]
        have h_div : (((p - a : ℕ) : ℝ) / (p : ℝ)) =
            (((p - a : ℕ) : ℕ) : ℝ) / ((p : ℕ) : ℝ) := by norm_cast
        have := abs_sin_pi_sub_div a p ha_le
        push_cast at this ⊢
        convert this using 2
      rw [h_sin_eq]
  rw [h_high_eq_low]
  ring

end Sinnott

end FLT37

end BernoulliRegular

end
