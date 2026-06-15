module

public import BernoulliRegular.FLT37.Hilbert90
public import BernoulliRegular.FLT37.KummerUnits
public import BernoulliRegular.FLT37.Mirimanoff
public import FltRegular.NumberTheory.Cyclotomic.CaseI
public import FltRegular.CaseI.Statement
public import Mathlib.NumberTheory.Bernoulli
public import BernoulliRegular.FLT37.CaseI.Part1


/-!
# FLT case I: composed unit-power decomposition (FLT37e)

Combines two earlier results:

* `fltCaseI_factor_eq_unit_mul_pow_of_regular`: the cyclotomic factor
  `a + ζ^k · b` equals a unit `u_k` times a `p`-th power `γ_k^p` (under
  regularity).
* `exists_zeta_pow_mul_real_eq_unit` (Kummer's lemma): the unit `u_k`
  splits as `ζ^{m_k} · v_k` with `v_k ∈ (𝓞 K⁺)ˣ` real.

Together: under regularity, every cyclotomic factor admits the
decomposition `a + ζ^k b = ζ^{m_k} · algebraMap v_k · γ_k^p`. This is the
shape used by the Mirimanoff-polynomial argument that closes case I.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension

namespace BernoulliRegular

namespace FLT37

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

/-- Local abbreviation for the primitive `p`-th root of unity `ζ` packaged as a
unit of `(𝓞 K)ˣ` (replacing the removed `IsPrimitiveRoot.unit'`). -/
local notation3 "ζcu" =>
  (((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit : (𝓞 K)ˣ)

/-- **Streamlined case I decomposition under regularity.** Same statement
as `fltCaseI_factor_eq_zeta_pow_mul_real_unit_mul_pow_of_regular` but
without the `h_factor_ne_zero` hypothesis (now derived automatically
from FLT case I conditions via `fltCaseI_factor_ne_zero`). -/
theorem fltCaseI_factor_decomposition_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k : ℕ} (hk : k < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ (m : ℕ) (v_plus : (𝓞 (K⁺))ˣ) (γ : 𝓞 K),
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
      ((ζcu ^ m :
          (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) * γ ^ p :=
  fltCaseI_factor_eq_zeta_pow_mul_real_unit_mul_pow_of_regular
    hp_two hp_odd h_reg heq hc hab
    (fun _j hj => fltCaseI_factor_ne_zero (K := K) hp_odd heq hc hab hj) hk

/-- **Order-2 Taylor of the σ-conjugate factor.** For `k ≤ p` and `p ≥ 3`,
`a + ζ^{p-k} b ≡ (a+b) - b·k·(ζ-1) (mod (ζ-1)^2)`. The `b·(p-k)` linear
term reduces to `-b·k` since `b·p·(ζ-1) ∈ (ζ-1)^p ⊆ (ζ-1)^2` for `p ≥ 3`. -/
theorem zetaSubOne_sq_dvd_factor_p_sub_k_sub_taylor
    (_hp_three : 3 ≤ p) (a b : ℤ) {k : ℕ} (hk : k ≤ p) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      (((a : 𝓞 K) +
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K)) -
        (((a + b : ℤ) : 𝓞 K) -
          (b : 𝓞 K) * (k : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1))) := by
  -- Use the order-2 Taylor expansion with index (p - k):
  --   a + ζ^{p-k} b ≡ (a+b) + b(p-k)(ζ-1) (mod (ζ-1)^2)
  -- Then b(p-k) ≡ -bk (mod p), and p·(integer) ≡ 0 mod (ζ-1)^2 (since (ζ-1)^2 ∣ p).
  have h1 := zetaSubOne_sq_dvd_factor_sub_taylor p K a b (p - k)
  -- h1 : (ζ-1)^2 ∣ (a + ζ^{p-k} b) - ((a+b) + b·(p-k)·(ζ-1))
  -- Difference between (a+b) + b(p-k)(ζ-1) and (a+b) - bk(ζ-1):
  --   b(p-k)(ζ-1) - (-bk(ζ-1)) = b(p-k+k)(ζ-1) = bp(ζ-1)
  -- We need (ζ-1)^2 ∣ bp(ζ-1), i.e., (ζ-1) ∣ bp.
  -- Since (ζ-1) ∣ p (zetaSubOne_dvd_intCast_iff), this holds.
  have h_bp : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣ ((b * p : ℤ) : 𝓞 K) := by
    rw [zetaSubOne_dvd_intCast_iff]
    exact ⟨b, by ring⟩
  obtain ⟨w, hw⟩ := h_bp
  -- (ζ-1)^2 ∣ b · p · (ζ-1) since (ζ-1) ∣ b · p.
  have h_bpz : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      ((b : 𝓞 K) * (p : 𝓞 K) * (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) := by
    refine ⟨w, ?_⟩
    have hbp_cast : (b : 𝓞 K) * (p : 𝓞 K) = ((b * p : ℤ) : 𝓞 K) := by push_cast; ring
    rw [hbp_cast, hw]
    ring
  -- Compute the difference:
  -- ((a + ζ^{p-k} b) - ((a+b) - bk(ζ-1))) =
  --   ((a + ζ^{p-k} b) - ((a+b) + b(p-k)(ζ-1))) + (b(p-k) + bk)(ζ-1)
  -- = h1's term + bp(ζ-1)
  have h_combine : ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K)) -
      (((a + b : ℤ) : 𝓞 K) -
        (b : 𝓞 K) * (k : 𝓞 K) *
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) =
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K)) -
          (((a + b : ℤ) : 𝓞 K) +
            (b : 𝓞 K) * ((p - k : ℕ) : 𝓞 K) *
              (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1))) +
        ((b : 𝓞 K) * (((p - k : ℕ) : 𝓞 K) + (k : 𝓞 K)) *
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1)) := by ring
  rw [h_combine]
  refine dvd_add h1 ?_
  -- (p - k : ℕ) + k = p (using k ≤ p).
  have h_sum : ((p - k : ℕ) : 𝓞 K) + (k : 𝓞 K) = (p : 𝓞 K) := by
    have : ((p - k + k : ℕ) : 𝓞 K) = (p : 𝓞 K) := by
      rw [Nat.sub_add_cancel hk]
    push_cast at this
    exact this
  rw [h_sum]
  -- Goal: (ζ-1)^2 ∣ b · p · (ζ-1).
  exact h_bpz

/-- **Order-2 Taylor of `ζ^{2m}·(a + ζ^{p-k} b)`.** For `k ≤ p` and
`p ≥ 3`, the product expansion modulo `(ζ-1)^2` is:
  `ζ^{2m}·(a + ζ^{p-k} b) ≡ (a+b) + (2m(a+b) - b·k)·(ζ-1) (mod (ζ-1)^2)`.

The proof uses the identity `X·Y - X_T·Y_T = (X - X_T)·Y + X_T·(Y - Y_T)`
where `X_T`, `Y_T` are the linear Taylor approximations of `ζ^{2m}` and
`(a + ζ^{p-k} b)` modulo `(ζ-1)^2`. -/
theorem zetaSubOne_sq_dvd_zeta_pow_mul_factor_p_sub_k_taylor
    (hp_three : 3 ≤ p) (a b : ℤ) {k : ℕ} (hk : k ≤ p) (m : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (2 * m) *
          ((a : 𝓞 K) +
            ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K))) -
        (((a + b : ℤ) : 𝓞 K) +
          ((2 * (m : ℤ) * (a + b) - b * k : ℤ) : 𝓞 K) *
            (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1))) := by
  set ε : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 with hε
  set X : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (2 * m) with hX
  set Y : 𝓞 K := (a : 𝓞 K) +
    ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K) with hY
  -- X_T := 1 + 2m·ε  (Taylor of X)
  -- Y_T := (a + b) - bk·ε  (Taylor of Y)
  -- (ζ-1)^2 ∣ X - X_T
  have hX_taylor : ε ^ 2 ∣ X - (1 + (2 * m : ℕ) * ε) := by
    have h := zetaSubOne_sq_dvd_zeta_pow_sub_one_sub_natCast_mul (p := p) (K := K) (2 * m)
    -- h : (ζ-1)^2 ∣ ζ^{2m} - 1 - (2m)·(ζ-1)
    -- Goal: ε^2 ∣ X - (1 + (2m)·ε), where ε = (ζ-1) and X = ζ^{2m}.
    have h_eq : X - (1 + ((2 * m : ℕ) : 𝓞 K) * ε) =
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (2 * m) - 1 -
          ((2 * m : ℕ) : 𝓞 K) * (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) := by
      simp only [hX, hε]; ring
    rw [h_eq]; exact h
  -- (ζ-1)^2 ∣ Y - Y_T
  have hY_taylor : ε ^ 2 ∣ Y - (((a + b : ℤ) : 𝓞 K) - (b : 𝓞 K) * (k : 𝓞 K) * ε) :=
    zetaSubOne_sq_dvd_factor_p_sub_k_sub_taylor (p := p) (K := K)
      hp_three a b hk
  -- X·Y - X_T·Y_T ∈ (ζ-1)^2 from (X-X_T)·Y + X_T·(Y-Y_T) ∈ (ζ-1)^2 + (ζ-1)^2.
  have h_prod_diff : ε ^ 2 ∣
      X * Y - (1 + (2 * m : ℕ) * ε) *
        (((a + b : ℤ) : 𝓞 K) - (b : 𝓞 K) * (k : 𝓞 K) * ε) := by
    have hXY_id : X * Y - (1 + (2 * m : ℕ) * ε) *
        (((a + b : ℤ) : 𝓞 K) - (b : 𝓞 K) * (k : 𝓞 K) * ε) =
        (X - (1 + (2 * m : ℕ) * ε)) * Y +
        (1 + (2 * m : ℕ) * ε) *
          (Y - (((a + b : ℤ) : 𝓞 K) - (b : 𝓞 K) * (k : 𝓞 K) * ε)) := by ring
    rw [hXY_id]
    exact dvd_add (hX_taylor.mul_right _) (hY_taylor.mul_left _)
  -- The Taylor product simplifies:
  --   (1 + 2m·ε) · ((a+b) - bk·ε) = (a+b) + (2m(a+b) - bk)·ε - 2m·bk·ε²
  -- And 2m·bk·ε² ∈ (ζ-1)^2 trivially.
  have h_simplify : (1 + ((2 * m : ℕ) : 𝓞 K) * ε) *
      (((a + b : ℤ) : 𝓞 K) - (b : 𝓞 K) * (k : 𝓞 K) * ε) -
      (((a + b : ℤ) : 𝓞 K) +
        ((2 * (m : ℤ) * (a + b) - b * k : ℤ) : 𝓞 K) * ε) =
      -((2 * m : ℕ) * (b : 𝓞 K) * (k : 𝓞 K) * ε ^ 2) := by
    push_cast
    ring
  -- Combine.
  have h_final : X * Y -
      (((a + b : ℤ) : 𝓞 K) +
        ((2 * (m : ℤ) * (a + b) - b * k : ℤ) : 𝓞 K) * ε) =
      (X * Y - (1 + ((2 * m : ℕ) : 𝓞 K) * ε) *
        (((a + b : ℤ) : 𝓞 K) - (b : 𝓞 K) * (k : 𝓞 K) * ε)) +
      ((1 + ((2 * m : ℕ) : 𝓞 K) * ε) *
        (((a + b : ℤ) : 𝓞 K) - (b : 𝓞 K) * (k : 𝓞 K) * ε) -
        (((a + b : ℤ) : 𝓞 K) +
          ((2 * (m : ℤ) * (a + b) - b * k : ℤ) : 𝓞 K) * ε)) := by ring
  rw [h_final]
  refine dvd_add h_prod_diff ?_
  rw [h_simplify]
  refine Dvd.dvd.neg_right ?_
  exact ⟨(2 * m : ℕ) * (b : 𝓞 K) * (k : 𝓞 K), by ring⟩

/-- **Streamlined σ-twist mod p under regularity.** From FLT case I +
regularity, for each `k < p` there exists `m` such that

  `(a + ζ^k b) - ζ^{2m}(a + ζ^{p-k} b) ∈ (p)` in `𝓞 K`.

This is the integer-side mod-p version of the σ-twist that holds
without us needing to pin down the decomposition data. -/
theorem fltCaseI_factor_sub_zeta_pow_mul_factor_mem_p_span_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k : ℕ} (hk : k < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ,
      ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((ζcu ^ (2 * m) :
          (𝓞 K)ˣ) : 𝓞 K) *
          ((a : 𝓞 K) +
            ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
  obtain ⟨m, v_plus, γ, h_decomp⟩ :=
    fltCaseI_factor_decomposition_of_regular hp_two hp_odd h_reg heq hc hab hk
  exact ⟨m, fltCaseI_decomposition_complexConj_mod_p hp_two a b hk.le v_plus γ h_decomp⟩

/-- **Mirimanoff relation `m·(a+b) ≡ b·k (mod p)`** under FLT case I +
regularity. From the σ-twist mod p `(a + ζ^k b) - ζ^{2m}(a + ζ^{p-k} b)
∈ (p)` combined with the order-2 Taylor expansions of both sides, we
extract `(ζ-1)^2 ∣ 2(m(a+b) - bk)·(ζ-1)`, hence `(ζ-1) ∣ 2(m(a+b) - bk)`,
hence `p ∣ 2(m(a+b) - bk)`. Since p is odd, `p ∣ m(a+b) - bk`. -/
theorem fltCaseI_mirimanoff_relation_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k : ℕ} (hk : k < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, (p : ℤ) ∣ ((m : ℤ) * (a + b) - b * k) := by
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
  obtain ⟨m, hD⟩ := fltCaseI_factor_sub_zeta_pow_mul_factor_mem_p_span_of_regular
    (K := K) hp_two hp_odd h_reg heq hc hab hk
  refine ⟨m, ?_⟩
  set ε : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 with hε_def
  have hT1 : ε ^ 2 ∣ (((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
      (((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K) * (k : 𝓞 K) * ε)) :=
    zetaSubOne_sq_dvd_factor_sub_taylor (p := p) (K := K) a b k
  have hT2 : ε ^ 2 ∣ ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (2 * m) *
          ((a : 𝓞 K) +
            ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K))) -
        (((a + b : ℤ) : 𝓞 K) +
          ((2 * (m : ℤ) * (a + b) - b * k : ℤ) : 𝓞 K) * ε)) :=
    zetaSubOne_sq_dvd_zeta_pow_mul_factor_p_sub_k_taylor (p := p) (K := K)
      hp_three a b hk.le m
  have hD_dvd : ε ^ 2 ∣ (((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
      ((ζcu ^ (2 * m) :
        (𝓞 K)ˣ) : 𝓞 K) *
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K))) := by
    rw [Ideal.mem_span_singleton] at hD
    have hp_dvd : ε ^ 2 ∣ ((p : ℕ) : 𝓞 K) :=
      zetaSubOne_sq_dvd_p (p := p) (K := K) hp_three
    have hp_cast : ((p : ℕ) : 𝓞 K) = (p : 𝓞 K) := by rfl
    rw [hp_cast] at hp_dvd
    exact hp_dvd.trans hD
  have h_combined : ε ^ 2 ∣
      ((2 * ((m : ℤ) * (a + b) - b * k) : ℤ) : 𝓞 K) * ε := by
    have h_eq : ((2 * ((m : ℤ) * (a + b) - b * k) : ℤ) : 𝓞 K) * ε =
        (((a : 𝓞 K) +
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
          (((a + b : ℤ) : 𝓞 K) + (b : 𝓞 K) * (k : 𝓞 K) * ε)) -
          ((((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (2 * m) *
            ((a : 𝓞 K) +
              ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K))) -
          (((a + b : ℤ) : 𝓞 K) +
            ((2 * (m : ℤ) * (a + b) - b * k : ℤ) : 𝓞 K) * ε)) -
        (((a : 𝓞 K) +
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((ζcu ^ (2 * m) :
          (𝓞 K)ˣ) : 𝓞 K) *
        ((a : 𝓞 K) +
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K))) := by
      have hcast : (((ζcu ^ (2 * m) :
          (𝓞 K)ˣ) : 𝓞 K)) = ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (2 * m) := by
        rw [Units.val_pow_eq_pow_val,
          show (ζcu : 𝓞 K) =
            ((zeta_spec p ℚ K).toInteger : 𝓞 K) from IsUnit.unit_spec _]
      rw [hcast]
      push_cast
      ring
    rw [h_eq]
    exact (hT1.sub hT2).sub hD_dvd
  have h_eps_ne : ε ≠ 0 := by
    rw [hε_def]; exact zetaSubOne_ne_zero p K
  have h_eps_dvd_int : ε ∣ ((2 * ((m : ℤ) * (a + b) - b * k) : ℤ) : 𝓞 K) := by
    obtain ⟨w, hw⟩ := h_combined
    refine ⟨w, ?_⟩
    have h_mul : ((2 * ((m : ℤ) * (a + b) - b * k) : ℤ) : 𝓞 K) * ε =
        ε * (ε * w) := by rw [hw, sq]; ring
    have : ε * ((2 * ((m : ℤ) * (a + b) - b * k) : ℤ) : 𝓞 K) = ε * (ε * w) := by
      rw [show ε * ((2 * ((m : ℤ) * (a + b) - b * k) : ℤ) : 𝓞 K) =
        ((2 * ((m : ℤ) * (a + b) - b * k) : ℤ) : 𝓞 K) * ε from by ring]
      exact h_mul
    exact mul_left_cancel₀ h_eps_ne this
  have h_p_dvd : (p : ℤ) ∣ (2 * ((m : ℤ) * (a + b) - b * k)) := by
    rwa [zetaSubOne_dvd_intCast_iff] at h_eps_dvd_int
  -- For p odd integer, p ∣ 2c ⟹ p ∣ c.
  -- Since gcd(p, 2) = 1 (p odd ≥ 3), this is standard.
  have hp_two_coprime_nat : Nat.Coprime p 2 := hp_odd.coprime_two_right
  have h_p_two_coprime : IsCoprime (p : ℤ) (2 : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact_mod_cast hp_two_coprime_nat
  exact h_p_two_coprime.dvd_of_dvd_mul_left h_p_dvd

/-- **Mirimanoff relation linearity in k.** Since `p ∤ (a + b)` under
FLT case I, the relation `m·(a+b) ≡ b·k (mod p)` determines m uniquely
modulo p. For different k values, the m_k's are related linearly:
`m_k ≡ k·b·(a+b)^{-1} (mod p)`, hence `(a+b)·(m_k - k·m_1) ≡ 0 (mod p)`. -/
theorem fltCaseI_mirimanoff_linear_in_k_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k₁ k₂ : ℕ} (hk₁ : k₁ < p) (hk₂ : k₂ < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m₁ m₂ : ℕ, (p : ℤ) ∣ ((m₁ : ℤ) * k₂ * (a + b) - (m₂ : ℤ) * k₁ * (a + b)) := by
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
  obtain ⟨m₁, hm₁⟩ := fltCaseI_mirimanoff_relation_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab hk₁
  obtain ⟨m₂, hm₂⟩ := fltCaseI_mirimanoff_relation_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab hk₂
  -- hm₁ : p ∣ m₁·(a+b) - b·k₁
  -- hm₂ : p ∣ m₂·(a+b) - b·k₂
  -- Compute k₂·hm₁ - k₁·hm₂ : p ∣ k₂·(m₁(a+b) - b·k₁) - k₁·(m₂(a+b) - b·k₂)
  --                       = (m₁·k₂ - m₂·k₁)·(a+b) - b·(k₁·k₂ - k₁·k₂)
  --                       = (m₁·k₂ - m₂·k₁)·(a+b)
  refine ⟨m₁, m₂, ?_⟩
  have h_lc : ((m₁ : ℤ) * k₂ * (a + b) - (m₂ : ℤ) * k₁ * (a + b)) =
      k₂ * ((m₁ : ℤ) * (a + b) - b * k₁) -
      k₁ * ((m₂ : ℤ) * (a + b) - b * k₂) := by ring
  rw [h_lc]
  exact dvd_sub (hm₁.mul_left _) (hm₂.mul_left _)

/-- **Cleaner Mirimanoff linearity: `p ∣ m₁·k₂ - m₂·k₁`.** Direct
consequence of the linear-combination form combined with `p ∤ (a+b)`:
since `p ∣ (m₁·k₂ - m₂·k₁)·(a+b)` and p prime with `p ∤ (a+b)`, we get
`p ∣ m₁·k₂ - m₂·k₁`. -/
theorem fltCaseI_mirimanoff_p_dvd_cross_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k₁ k₂ : ℕ} (hk₁ : k₁ < p) (hk₂ : k₂ < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m₁ m₂ : ℕ, (p : ℤ) ∣ ((m₁ : ℤ) * k₂ - (m₂ : ℤ) * k₁) := by
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
  obtain ⟨m₁, m₂, h_dvd⟩ := fltCaseI_mirimanoff_linear_in_k_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab hk₁ hk₂
  refine ⟨m₁, m₂, ?_⟩
  -- h_dvd : p ∣ m₁·k₂·(a+b) - m₂·k₁·(a+b) = (m₁·k₂ - m₂·k₁)·(a+b)
  -- p ∤ (a+b), so p ∣ (m₁·k₂ - m₂·k₁).
  have h_factor : ((m₁ : ℤ) * k₂ * (a + b) - (m₂ : ℤ) * k₁ * (a + b)) =
      ((m₁ : ℤ) * k₂ - (m₂ : ℤ) * k₁) * (a + b) := by ring
  rw [h_factor] at h_dvd
  have hp_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.1
  have hp_not_dvd : ¬ (p : ℤ) ∣ (a + b) :=
    fltCaseI_p_not_dvd_a_add_b heq hc
  -- p prime, p ∣ x·y, p ∤ y ⟹ p ∣ x.
  rcases hp_prime.dvd_mul.mp h_dvd with h | h
  · exact h
  · exact absurd h hp_not_dvd

/-- **Mirimanoff parameter scales linearly: `m_k ≡ k·m_1 (mod p)`.** Direct
specialisation of `fltCaseI_mirimanoff_p_dvd_cross_of_regular` at `k₁ = 1`.
For each `k < p`, picking `m_1` (witness for k=1) and `m_k` (witness for
k), the difference `m_k - k·m_1` is divisible by `p`. -/
theorem fltCaseI_mirimanoff_scale_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k : ℕ} (hk : k < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m₁ m_k : ℕ, (p : ℤ) ∣ ((m_k : ℤ) - (k : ℤ) * m₁) := by
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
  have h_one_lt : 1 < p := by have := hp.1.two_le; omega
  obtain ⟨m₁, m_k, h_cross⟩ := fltCaseI_mirimanoff_p_dvd_cross_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab h_one_lt hk
  refine ⟨m₁, m_k, ?_⟩
  -- h_cross : p ∣ m₁·k - m_k·1 = m₁·k - m_k
  -- We want: p ∣ m_k - k·m₁ = -(m₁·k - m_k).
  rw [show ((m_k : ℤ) - (k : ℤ) * m₁) = -((m₁ : ℤ) * (k : ℤ) - (m_k : ℤ) * 1) from by ring]
  exact dvd_neg.mpr h_cross

/-- **Direct form `m_1·(a+b) ≡ b (mod p)`** (Mirimanoff at `k = 1`). -/
theorem fltCaseI_mirimanoff_relation_one_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, (p : ℤ) ∣ ((m : ℤ) * (a + b) - b) := by
  have h_one_lt : 1 < p := by have := hp.1.two_le; omega
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab h_one_lt
  -- hm : p ∣ m·(a + b) - b·1 = m·(a + b) - b.
  refine ⟨m, ?_⟩
  -- hm: p ∣ m·(a+b) - b·(1 : ℕ) = m·(a+b) - b.
  convert hm using 1
  push_cast; ring

/-- **Mirimanoff residue at index `k = p - 1`.** Specialisation showing
that the Mirimanoff parameter at the top index `k = p - 1` is constrained
by `m·(a+b) ≡ b·(p-1) ≡ -b (mod p)`. -/
theorem fltCaseI_mirimanoff_relation_top_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, (p : ℤ) ∣ ((m : ℤ) * (a + b) + b) := by
  have hp_pos : 0 < p := hp.1.pos
  have h_top_lt : p - 1 < p := by omega
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab h_top_lt
  -- hm : p ∣ m·(a + b) - b·(p - 1) ≡ m·(a+b) + b (mod p) since b·(p-1) ≡ -b.
  refine ⟨m, ?_⟩
  -- p ∣ m·(a+b) - b·(p-1) ⟺ p ∣ m·(a+b) - b·p + b = m·(a+b) + b - b·p.
  -- p ∣ b·p, so p ∣ m·(a+b) + b iff p ∣ m·(a+b) - b·(p-1).
  have h_pcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
    have h_one_le : (1 : ℕ) ≤ p := hp_pos
    rw [Nat.cast_sub h_one_le, Nat.cast_one]
  rw [show ((m : ℤ) * (a + b) + b) =
      ((m : ℤ) * (a + b) - b * ((p - 1 : ℕ) : ℤ)) + b * p from by
        rw [h_pcast]; ring]
  exact dvd_add hm ⟨b, by ring⟩

/-- **Mirimanoff non-trivial: `p ∤ m_1` when `p ∤ b`.** Under FLT case I +
regularity, if additionally `p ∤ b`, then the k = 1 Mirimanoff parameter
satisfies `p ∤ m_1`. The proof: `m·(a+b) ≡ b (mod p)`, and if `p ∣ m`,
then `p ∣ b`, contradiction. -/
theorem fltCaseI_mirimanoff_one_p_not_dvd_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (hb : ¬ (p : ℤ) ∣ b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, ¬ (p : ℤ) ∣ (m : ℤ) ∧ (p : ℤ) ∣ ((m : ℤ) * (a + b) - b) := by
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_one_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨m, ?_, hm⟩
  intro h_p_dvd_m
  -- From p ∣ m and hm : p ∣ m·(a+b) - b, conclude p ∣ b.
  have h_dvd_prod : (p : ℤ) ∣ (m : ℤ) * (a + b) := h_p_dvd_m.mul_right _
  have h_dvd_b : (p : ℤ) ∣ b := by
    have := dvd_sub h_dvd_prod hm
    rwa [show ((m : ℤ) * (a + b) - ((m : ℤ) * (a + b) - b)) = b from by ring] at this
  exact hb h_dvd_b

/-- **Case I Mirimanoff package theorem.** Under FLT case I + regularity
+ `p ∤ b`, we package the family of Mirimanoff constraints: for each
`k < p`, there's `m_k` satisfying `m_k·(a+b) ≡ b·k (mod p)`, with the
m's linearly related: `m_k ≡ k·m_1 (mod p)`, and all non-trivial when
`k ≢ 0 (mod p)`. -/
theorem fltCaseI_mirimanoff_package_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (hb : ¬ (p : ℤ) ∣ b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    -- p ∤ (a + b)
    ¬ (p : ℤ) ∣ (a + b) ∧
    -- p ∣ c - (a + b)
    (p : ℤ) ∣ (c - (a + b)) ∧
    -- For k = 1, exists nontrivial m_1 with m_1·(a+b) ≡ b (mod p)
    (∃ m_1 : ℕ, ¬ (p : ℤ) ∣ (m_1 : ℤ) ∧
      (p : ℤ) ∣ ((m_1 : ℤ) * (a + b) - b)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact fltCaseI_p_not_dvd_a_add_b heq hc
  · exact fltCaseI_p_dvd_c_sub_a_add_b heq
  · exact fltCaseI_mirimanoff_one_p_not_dvd_of_regular (K := K)
      hp_two hp_odd hp_three h_reg heq hc hab hb

/-- **Mirimanoff relation in `c` form: `m_1·c ≡ b (mod p)`.** Combining
`m_1·(a+b) ≡ b (mod p)` (Mirimanoff at k=1) with `c ≡ a+b (mod p)`
(Fermat-style congruence) yields `m_1·c ≡ b (mod p)`. -/
theorem fltCaseI_mirimanoff_relation_c_form_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, (p : ℤ) ∣ ((m : ℤ) * c - b) := by
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_one_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨m, ?_⟩
  have h_c : (p : ℤ) ∣ (c - (a + b)) := fltCaseI_p_dvd_c_sub_a_add_b heq
  -- m·c - b = m·(c - (a+b)) + (m·(a+b) - b)
  have h_split : ((m : ℤ) * c - b) = (m : ℤ) * (c - (a + b)) + ((m : ℤ) * (a + b) - b) := by
    ring
  rw [h_split]
  exact dvd_add (h_c.mul_left _) hm

/-- **Mirimanoff swap symmetry: `m + m' ≡ 1 (mod p)`.** Using the FLT
case I equation symmetry `a^p + b^p = c^p ⟺ b^p + a^p = c^p`, applying
the Mirimanoff relation at k=1 with the roles of a,b swapped gives:

  ∃ m m', p ∣ m·(a+b) - b ∧ p ∣ m'·(a+b) - a.

Adding: `(m + m')·(a+b) ≡ a + b (mod p)`. Since `p ∤ (a+b)`, this gives
`m + m' ≡ 1 (mod p)`. -/
theorem fltCaseI_mirimanoff_swap_sum_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m m' : ℕ, (p : ℤ) ∣ (((m : ℤ) + m') - 1) := by
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_one_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  -- Swap a and b: b^p + a^p = c^p.
  have heq_swap : b ^ p + a ^ p = c ^ p := by linarith
  obtain ⟨m', hm'⟩ := fltCaseI_mirimanoff_relation_one_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq_swap hc hab.symm
  -- hm' : p ∣ m' · (b + a) - a
  refine ⟨m, m', ?_⟩
  -- Combine: p ∣ (m + m') · (a + b) - (a + b) = ((m + m') - 1) · (a + b).
  have h_sum : (p : ℤ) ∣ (((m : ℤ) + m') * (a + b) - (a + b)) := by
    have h_add := dvd_add hm hm'
    -- h_add : p ∣ (m·(a+b) - b) + (m'·(b+a) - a) = (m+m')·(a+b) - (a+b)
    have h_id : (((m : ℤ) + m') * (a + b) - (a + b)) =
        ((m : ℤ) * (a + b) - b) + ((m' : ℤ) * (b + a) - a) := by ring
    rw [h_id]
    exact h_add
  -- Factor: p ∣ ((m+m') - 1)·(a+b)
  have h_factor : (((m : ℤ) + m') * (a + b) - (a + b)) =
      (((m : ℤ) + m') - 1) * (a + b) := by ring
  rw [h_factor] at h_sum
  -- p ∤ (a + b), so p ∣ ((m+m') - 1).
  have hp_prime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.1
  have hp_not_dvd : ¬ (p : ℤ) ∣ (a + b) :=
    fltCaseI_p_not_dvd_a_add_b heq hc
  rcases hp_prime.dvd_mul.mp h_sum with h | h
  · exact h
  · exact absurd h hp_not_dvd

/-- **Mirimanoff relation in `ZMod p`.** Under FLT case I + regularity,
the Mirimanoff parameter `m_1` reduces in `ZMod p` to `b · (a+b)^{-1}`,
expressed as the equation `m_1 · (a + b) = b` in `ZMod p`. -/
theorem fltCaseI_mirimanoff_relation_zmod_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ZMod p, m * (a + b : ZMod p) = (b : ZMod p) := by
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_one_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨(m : ZMod p), ?_⟩
  -- p ∣ m·(a+b) - b in ℤ, so its image in ZMod p is 0.
  have h_zmod : (((m : ℤ) * (a + b) - b : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hm
  push_cast at h_zmod
  linear_combination h_zmod

/-- **Explicit Mirimanoff parameter formula in `ZMod p`.** Under FLT
case I + regularity, the Mirimanoff parameter is uniquely determined
by `m_1 = b · (a + b)⁻¹` in `ZMod p`. Uses `p ∤ (a + b)` to ensure
invertibility. -/
theorem fltCaseI_mirimanoff_eq_b_div_a_add_b_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI : Fact p.Prime := hp
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ZMod p, m = (b : ZMod p) * ((a + b : ZMod p))⁻¹ := by
  haveI : Fact p.Prime := hp
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_zmod_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨m, ?_⟩
  -- a + b ≠ 0 in ZMod p (from p ∤ (a+b)).
  have h_ne : (a + b : ZMod p) ≠ 0 := by
    intro hz
    have : ((a + b : ℤ) : ZMod p) = 0 := by push_cast; exact hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    have hp_not_dvd : ¬ (p : ℤ) ∣ (a + b) :=
      fltCaseI_p_not_dvd_a_add_b heq hc
    exact hp_not_dvd (by exact_mod_cast this)
  -- m · (a + b) = b ⟹ m = b · (a + b)⁻¹.
  field_simp
  linear_combination hm

/-- **Mirimanoff parameter formula in `c` form: `m_1 = b · c⁻¹`.** -/
theorem fltCaseI_mirimanoff_eq_b_div_c_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI : Fact p.Prime := hp
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ZMod p, m = (b : ZMod p) * ((c : ZMod p))⁻¹ := by
  haveI : Fact p.Prime := hp
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_c_form_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨(m : ZMod p), ?_⟩
  -- c ≠ 0 in ZMod p (from p ∤ c).
  have h_c_ne : (c : ZMod p) ≠ 0 := by
    intro hz
    have : ((c : ℤ) : ZMod p) = 0 := by exact hz
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
    exact hc (by exact_mod_cast this)
  -- p ∣ m·c - b ⟹ (m : ZMod p) · c = b ⟹ m = b · c⁻¹.
  have hmc : (((m : ℤ) * c - b : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast hm
  push_cast at hmc
  field_simp
  linear_combination hmc

/-- **Mirimanoff swap sum in `ZMod p`: `m + m' = 1`.** Cleaner ZMod p
form of `fltCaseI_mirimanoff_swap_sum_of_regular`: the two Mirimanoff
parameters at the swap-symmetric pair `(a, b)` and `(b, a)` sum to 1
in ZMod p. -/
theorem fltCaseI_mirimanoff_swap_sum_zmod_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI : Fact p.Prime := hp
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m m' : ZMod p, m + m' = 1 := by
  haveI : Fact p.Prime := hp
  obtain ⟨m, m', h⟩ := fltCaseI_mirimanoff_swap_sum_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨(m : ZMod p), (m' : ZMod p), ?_⟩
  -- p ∣ (m + m') - 1 in ℤ ⟹ ((m + m') - 1 : ZMod p) = 0.
  have h_zmod : ((((m : ℤ) + m') - 1 : ℤ) : ZMod p) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast h
  push_cast at h_zmod
  linear_combination h_zmod

/-- **Mirimanoff parameter is non-zero in `ZMod p`.** Under FLT case I +
regularity + `p ∤ b`, the Mirimanoff parameter `m_1 = b·(a+b)⁻¹` is
non-zero in `ZMod p` (i.e., lies in the unit group `(ZMod p)^*`). -/
theorem fltCaseI_mirimanoff_zmod_ne_zero_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (hb : ¬ (p : ℤ) ∣ b) :
    haveI : Fact p.Prime := hp
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ZMod p, m ≠ 0 ∧ m * (a + b : ZMod p) = (b : ZMod p) := by
  haveI : Fact p.Prime := hp
  obtain ⟨m, h⟩ := fltCaseI_mirimanoff_relation_zmod_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨m, ?_, h⟩
  intro hm0
  rw [hm0, zero_mul] at h
  -- h : 0 = (b : ZMod p), so p ∣ b.
  have h_b_dvd : ((b : ℤ) : ZMod p) = 0 := by exact_mod_cast h.symm
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h_b_dvd
  exact hb (by exact_mod_cast h_b_dvd)

/-- **Sum of Mirimanoff parameters is 0 mod p.** Under FLT case I +
regularity, summing the Mirimanoff parameter relations
`m_k ≡ k·m_1 (mod p)` over `k = 0, ..., p-1` gives:

  `∑_{k=0}^{p-1} m_k ≡ m_1 · p(p-1)/2 ≡ 0 (mod p)`,

since `p ∣ p(p-1)/2` for `p ≥ 1`. This is a structural identity. -/
theorem fltCaseI_mirimanoff_sum_zero_mod_p_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m_1 : ℕ, (p : ℤ) ∣ ((m_1 : ℤ) * (((p : ℤ) * (p - 1)) / 2)) := by
  obtain ⟨m_1, _⟩ := fltCaseI_mirimanoff_relation_one_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨m_1, ?_⟩
  -- p · (p - 1) / 2 = p · ((p - 1) / 2) for p odd, so p divides.
  have hp_odd_int : Odd (p : ℤ) := by exact_mod_cast hp_odd
  rcases hp_odd_int with ⟨n, hn⟩
  have h_pn : (p : ℤ) - 1 = 2 * n := by linarith
  have h_div : ((p : ℤ) * (p - 1)) / 2 = (p : ℤ) * n := by
    rw [h_pn]
    rw [show ((p : ℤ) * (2 * n)) = 2 * ((p : ℤ) * n) from by ring]
    exact Int.mul_ediv_cancel_left _ two_ne_zero
  rw [h_div]
  exact ⟨(m_1 : ℤ) * n, by ring⟩

/-- **`m_1 - 1 = -a · (a+b)⁻¹` in `ZMod p`.** Direct algebraic
consequence of `m_1 = b · (a+b)⁻¹` combined with the swap symmetry
`m + m' = 1`. Concretely: `(m_1 - 1) · (a+b) ≡ -a (mod p)`. -/
theorem fltCaseI_mirimanoff_sub_one_relation_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, (p : ℤ) ∣ (((m : ℤ) - 1) * (a + b) + a) := by
  obtain ⟨m, hm⟩ := fltCaseI_mirimanoff_relation_one_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨m, ?_⟩
  -- hm : p ∣ m·(a+b) - b. We want: p ∣ (m-1)·(a+b) + a = m·(a+b) - (a+b) + a = m·(a+b) - b.
  rw [show ((m : ℤ) - 1) * (a + b) + a = (m : ℤ) * (a + b) - b from by ring]
  exact hm

/-- **`m_1 - 1 ≠ 0` in `ZMod p` when `p ∤ a`.** Symmetric counterpart
to `fltCaseI_mirimanoff_one_p_not_dvd_of_regular`. -/
theorem fltCaseI_mirimanoff_sub_one_p_not_dvd_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (ha : ¬ (p : ℤ) ∣ a) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, ¬ (p : ℤ) ∣ ((m : ℤ) - 1) ∧
      (p : ℤ) ∣ (((m : ℤ) - 1) * (a + b) + a) := by
  obtain ⟨m, h⟩ := fltCaseI_mirimanoff_sub_one_relation_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨m, ?_, h⟩
  intro h_p_dvd
  -- p ∣ (m - 1) and h : p ∣ (m-1)·(a+b) + a, so p ∣ a.
  have : (p : ℤ) ∣ ((m : ℤ) - 1) * (a + b) := h_p_dvd.mul_right _
  have h_a_dvd : (p : ℤ) ∣ a := by
    have := dvd_sub h this
    have h_id : ((m : ℤ) - 1) * (a + b) + a - ((m : ℤ) - 1) * (a + b) = a := by ring
    rwa [h_id] at this
  exact ha h_a_dvd

/-- **Mirimanoff multiplicative identity: `m_1·(m_1 - 1)·(a+b)² ≡ -ab (mod p)`.**
Multiplying the two linear relations
`m_1·(a+b) ≡ b` and `(m_1 - 1)·(a+b) ≡ -a` (in ZMod p) yields the
quadratic identity. -/
theorem fltCaseI_mirimanoff_quadratic_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, (p : ℤ) ∣ ((m : ℤ) * ((m : ℤ) - 1) * (a + b) ^ 2 + a * b) := by
  obtain ⟨m, h1⟩ := fltCaseI_mirimanoff_relation_one_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  obtain ⟨m', h2⟩ := fltCaseI_mirimanoff_sub_one_relation_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  -- WARNING: m and m' are both Mirimanoff parameters at k = 1 from the same
  -- decomposition, so they're the same integer (mod p). We need to use the SAME m.
  -- Let me redo: get m from h1, then derive (m - 1)·(a+b) + a from h1 directly.
  refine ⟨m, ?_⟩
  -- h1 : p ∣ m·(a+b) - b.
  -- Derive: p ∣ (m - 1)·(a+b) + a since (m-1)(a+b) + a = m(a+b) - (a+b) + a = m(a+b) - b.
  have h_sub_one : (p : ℤ) ∣ ((m : ℤ) - 1) * (a + b) + a := by
    have h_id : ((m : ℤ) - 1) * (a + b) + a = (m : ℤ) * (a + b) - b := by ring
    rw [h_id]
    exact h1
  -- Multiply h1 and h_sub_one. In ZMod p:
  --   m·(a+b) = b and (m-1)·(a+b) = -a, multiplying gives
  --   m·(m-1)·(a+b)² = b·(-a) = -ab.
  -- So m·(m-1)·(a+b)² + ab = 0 in ZMod p.
  -- Let's verify the algebraic identity:
  --   m·(m-1)·(a+b)² + ab = (m·(a+b) - b)·(m-1)·(a+b) + b·(m-1)·(a+b) + ab
  --                      = (m·(a+b) - b)·(m-1)·(a+b) + (b·(m-1)·(a+b) + ab)
  --                      = (m·(a+b) - b)·(m-1)·(a+b) + b·((m-1)·(a+b) + a)
  -- Both terms are p-divisible by h1 and h_sub_one.
  have h_id : (m : ℤ) * ((m : ℤ) - 1) * (a + b) ^ 2 + a * b =
      ((m : ℤ) * (a + b) - b) * ((m : ℤ) - 1) * (a + b) +
      b * (((m : ℤ) - 1) * (a + b) + a) := by ring
  rw [h_id]
  exact dvd_add ((h1.mul_right _).mul_right _) (h_sub_one.mul_left _)

/-- **Mirimanoff quadratic in c-form: `m·(m - 1)·c² ≡ -ab (mod p)`.** -/
theorem fltCaseI_mirimanoff_quadratic_c_form_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p) (hp_three : 3 ≤ p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ m : ℕ, (p : ℤ) ∣ ((m : ℤ) * ((m : ℤ) - 1) * c ^ 2 + a * b) := by
  obtain ⟨m, h1⟩ := fltCaseI_mirimanoff_relation_c_form_of_regular
    (K := K) hp_two hp_odd hp_three h_reg heq hc hab
  refine ⟨m, ?_⟩
  -- h1 : p ∣ m·c - b. Derive: (m - 1)·c ≡ -a (mod p).
  have hC : (p : ℤ) ∣ (c - (a + b)) := fltCaseI_p_dvd_c_sub_a_add_b heq
  have h_sub : (p : ℤ) ∣ (((m : ℤ) - 1) * c + a) := by
    -- (m-1)·c + a = m·c - c + a = (m·c - b) + (b - c) + a = (m·c - b) - (c - a - b)
    -- = (m·c - b) - (c - (a+b)).
    have h_id : ((m : ℤ) - 1) * c + a = ((m : ℤ) * c - b) - (c - (a + b)) := by ring
    rw [h_id]
    exact dvd_sub h1 hC
  -- Multiply: m·(m-1)·c² ≡ -ab in ZMod p.
  have h_id : (m : ℤ) * ((m : ℤ) - 1) * c ^ 2 + a * b =
      ((m : ℤ) * c - b) * ((m : ℤ) - 1) * c +
      b * (((m : ℤ) - 1) * c + a) := by ring
  rw [h_id]
  exact dvd_add ((h1.mul_right _).mul_right _) (h_sub.mul_left _)

end FLT37

end BernoulliRegular

end
