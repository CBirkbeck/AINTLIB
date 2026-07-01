module

public import BernoulliRegular.FLT37.Hilbert90
public import BernoulliRegular.FLT37.KummerUnits
public import BernoulliRegular.FLT37.Mirimanoff
public import FltRegular.NumberTheory.Cyclotomic.CaseI
public import FltRegular.CaseI.Statement
public import Mathlib.NumberTheory.Bernoulli

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

/-- **FLT case I: full Kummer-style decomposition under regularity.**

Under the regular-prime hypothesis `p ∤ |Cl(𝓞 K)|`, each cyclotomic
factor `a + ζ^k · b` of `c^p - b^p` decomposes as
`a + ζ^k b = ζ^{m_k} · (algebraMap v_k) · γ_k^p`
with `v_k ∈ (𝓞 K⁺)ˣ` a real unit and `γ_k ∈ 𝓞 K`. -/
theorem fltCaseI_factor_eq_zeta_pow_mul_real_unit_mul_pow_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    (h_factor_ne_zero : ∀ k : ℕ, k < p →
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ≠ 0)
    {k : ℕ} (hk : k < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ (m : ℕ) (v_plus : (𝓞 (K⁺))ˣ) (γ : 𝓞 K),
      ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
      ((ζcu ^ m :
          (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) * γ ^ p := by
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
  -- Step 1: get the unit-times-pth-power decomposition.
  obtain ⟨u, γ, hu_eq⟩ :=
    fltCaseI_factor_eq_unit_mul_pow_of_regular p hp_odd K h_reg heq hc hab
      h_factor_ne_zero hk
  -- Step 2: decompose u into ζ^m * algebraMap v_plus.
  obtain ⟨m, v_plus, hu_decomp⟩ := exists_zeta_pow_mul_real_eq_unit hp_two u
  refine ⟨m, v_plus, γ, ?_⟩
  rw [hu_eq]
  -- Goal: u * γ^p = ζ^m * algebraMap v_plus * γ^p
  -- We have hu_decomp : u = ζ^m * Units.map (algebraMap _) v_plus (at unit level).
  congr 1
  -- u = ζ^m * algebraMap v_plus at value level
  have h_unit : (u : 𝓞 K) =
      (ζcu ^ m : (𝓞 K)ˣ) *
        (Units.map (algebraMap (𝓞 (K⁺)) (𝓞 K)).toMonoidHom v_plus :
          (𝓞 K)ˣ) := by
    exact_mod_cast congrArg (Units.val) hu_decomp
  rw [h_unit]
  push_cast
  rfl

/-- **Galois conjugate of the cyclotomic factor.** Complex conjugation
sends `a + ζ^k · b` to `a + ζ^{p-k} · b`, when `k ≤ p`. The proof uses
`σ(ζ) = ζ^{p-1}` and the cyclotomic relation `ζ^p = 1`. -/
theorem fltCaseI_factor_complexConj
    [IsCMField K] (a b : ℤ) {k : ℕ} (hk : k ≤ p) :
    ringOfIntegersComplexConj K
        ((a : 𝓞 K) +
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
      (a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K) := by
  -- σ acts on integer casts as identity, and σ(ζ^k) = ζ^(p-k) since
  -- σζ = ζ^(p-1) and ζ^p = 1.
  have h_int_cast : ringOfIntegersComplexConj K ((a : 𝓞 K)) = (a : 𝓞 K) := by
    change ringOfIntegersComplexConj K ((algebraMap ℤ (𝓞 K)) a) =
      (algebraMap ℤ (𝓞 K)) a
    rw [IsScalarTower.algebraMap_apply ℤ (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K),
      AlgEquiv.commutes]
  have h_int_cast_b : ringOfIntegersComplexConj K ((b : 𝓞 K)) = (b : 𝓞 K) := by
    change ringOfIntegersComplexConj K ((algebraMap ℤ (𝓞 K)) b) =
      (algebraMap ℤ (𝓞 K)) b
    rw [IsScalarTower.algebraMap_apply ℤ (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K),
      AlgEquiv.commutes]
  -- σ(ζ^k) = ζ^(p-k).
  have h_zeta_k : ringOfIntegersComplexConj K
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) := by
    rw [map_pow]
    -- σ(ζ) = ζ^(p-1)
    have h_conj_zeta : ringOfIntegersComplexConj K
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) := by
      exact complexConj_apply_zeta (p := p) (K := K)
    rw [h_conj_zeta, ← pow_mul]
    -- ζ^((p-1)*k) = ζ^(p-k) since ζ^p = 1.
    -- (p-1)*k ≡ -k ≡ p-k (mod p)
    have h_zeta_p : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
      zeta_toInteger_pow_eq_one p K
    have h_pow_eq : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((p - 1) * k) =
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) := by
      have hp_pos : 0 < p := hp.1.pos
      -- ζ^((p-1)*k) * ζ^k = ζ^(p*k) = 1 = ζ^(p-k) * ζ^k.
      have h1 : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((p - 1) * k) *
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k = 1 := by
        rw [← pow_add]
        have heq : (p - 1) * k + k = p * k := by
          have hpk : (p - 1) * k = p * k - k := by
            rcases Nat.eq_zero_or_pos k with hk0 | _
            · simp [hk0]
            · have : 1 ≤ p := hp_pos
              rw [Nat.sub_one_mul]
          rw [hpk]
          have hkp : k ≤ p * k := Nat.le_mul_of_pos_left k hp_pos
          omega
        rw [heq, pow_mul, h_zeta_p, one_pow]
      have h2 : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) *
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k = 1 := by
        rw [← pow_add, Nat.sub_add_cancel hk, h_zeta_p]
      -- From both equations, cancel ζ^k.
      have h_unit_pow : IsUnit (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k) :=
        ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).pow k
      exact mul_right_cancel₀ h_unit_pow.ne_zero (h1.trans h2.symm)
    exact h_pow_eq
  rw [map_add, map_mul, h_int_cast, h_zeta_k, h_int_cast_b]

/-- **Linear independence of `1` and `ζ^k`** in `K = ℚ(ζ_p)` over `ℚ`,
for `k ∈ [1, p-2]`. The proof uses the minimal polynomial of `ζ` over
`ℚ` being `cyclotomic p ℚ` of degree `p-1 > k`. -/
theorem zeta_pow_linearly_independent_lt (hp_odd : Odd p) {k : ℕ}
    (hk_pos : 1 ≤ k) (hk_lt : k ≤ p - 2)
    (a b : ℚ)
    (h : (a : K) + IsCyclotomicExtension.zeta p ℚ K ^ k * (b : K) = 0) :
    a = 0 ∧ b = 0 := by
  -- Define f(X) = a + b X^k.
  set f : Polynomial ℚ := Polynomial.C a + Polynomial.C b * Polynomial.X ^ k with hf_def
  have hp_pos : 0 < p := hp_odd.pos
  have hp_ge3 : 3 ≤ p := by
    rcases hp_odd with ⟨n, rfl⟩
    have := hp.1.two_le
    omega
  -- Aeval f at ζ equals 0.
  have h_aeval : Polynomial.aeval (IsCyclotomicExtension.zeta p ℚ K) f = 0 := by
    rw [hf_def]
    simp only [map_add, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow]
    rw [mul_comm]
    exact h
  -- minpoly of ζ over ℚ is cyclotomic p ℚ, of degree p - 1.
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta p ℚ K) p :=
    IsCyclotomicExtension.zeta_spec p ℚ K
  have h_irr : Irreducible (Polynomial.cyclotomic p ℚ) :=
    Polynomial.cyclotomic.irreducible_rat hp_pos
  have h_minpoly : minpoly ℚ (IsCyclotomicExtension.zeta p ℚ K) =
      Polynomial.cyclotomic p ℚ :=
    (hζ.minpoly_eq_cyclotomic_of_irreducible h_irr).symm
  -- minpoly | f.
  have h_dvd : minpoly ℚ (IsCyclotomicExtension.zeta p ℚ K) ∣ f :=
    minpoly.dvd ℚ _ h_aeval
  rw [h_minpoly] at h_dvd
  -- deg f ≤ k ≤ p - 2 < p - 1 = deg(cyclotomic p ℚ).
  have h_natDegree_cyc : (Polynomial.cyclotomic p ℚ).natDegree = p - 1 := by
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hp.1]
  have h_natDegree_f : f.natDegree ≤ k := by
    rw [hf_def]
    refine (Polynomial.natDegree_add_le _ _).trans ?_
    rw [Polynomial.natDegree_C, max_eq_right (Nat.zero_le _)]
    refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    rw [Polynomial.natDegree_pow, Polynomial.natDegree_X, mul_one]
  -- For dvd to hold with deg(f) < deg(cyclotomic), we need f = 0.
  have h_f_zero : f = 0 := by
    by_contra hf_ne
    have h_deg_le : (Polynomial.cyclotomic p ℚ).natDegree ≤ f.natDegree :=
      Polynomial.natDegree_le_of_dvd h_dvd hf_ne
    rw [h_natDegree_cyc] at h_deg_le
    omega
  -- f = 0 ⟹ a = 0 and b = 0 (via coefficient extraction).
  rw [hf_def] at h_f_zero
  -- Coefficients at 0 and k of f.
  have hk_ne : k ≠ 0 := Nat.pos_iff_ne_zero.mp hk_pos
  have h_a : a = 0 := by
    have h := congrArg (·.coeff 0) h_f_zero
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_zero, if_true,
      hk_ne.symm, if_false, mul_zero, add_zero] at h
    exact h
  have h_b : b = 0 := by
    have h := congrArg (·.coeff k) h_f_zero
    simp only [Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_zero, hk_ne, if_false,
      if_true, mul_one, zero_add] at h
    exact h
  exact ⟨h_a, h_b⟩

/-- **Case I: factor at index k ∈ [1, p-2] is non-zero**, given
`IsCoprime a b`. The argument: if `(a : 𝓞 K) + ζ^k · (b : 𝓞 K) = 0`,
lift to `K` and use `zeta_pow_linearly_independent_lt` to get `a = b = 0`
as rationals, hence as integers. But `IsCoprime 0 0` is false. -/
theorem fltCaseI_factor_lt_ne_zero (hp_odd : Odd p) {k : ℕ}
    (hk_pos : 1 ≤ k) (hk_lt : k ≤ p - 2)
    {a b : ℤ} (hab : IsCoprime a b) :
    ((a : 𝓞 K) +
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ≠ 0 := by
  intro h
  -- Lift to K via the inclusion 𝓞 K → K.
  have h_K : ((a : ℚ) : K) +
      IsCyclotomicExtension.zeta p ℚ K ^ k * ((b : ℚ) : K) = 0 := by
    have h_alg : (algebraMap (𝓞 K) K : 𝓞 K → K)
        ((a : 𝓞 K) +
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
        (algebraMap (𝓞 K) K) 0 := by
      rw [h]
    rw [map_add, map_mul, map_pow, map_zero] at h_alg
    -- algebraMap (𝓞 K) K (a : 𝓞 K) = (a : K)
    have h_a : (algebraMap (𝓞 K) K : 𝓞 K → K) (a : 𝓞 K) = ((a : ℚ) : K) := by
      simp
    have h_b : (algebraMap (𝓞 K) K : 𝓞 K → K) (b : 𝓞 K) = ((b : ℚ) : K) := by
      simp
    have h_zeta :
        (algebraMap (𝓞 K) K : 𝓞 K → K) ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
          IsCyclotomicExtension.zeta p ℚ K := by
      rfl
    rw [h_a, h_b, h_zeta] at h_alg
    exact h_alg
  -- Apply zeta_pow_linearly_independent_lt with rational a, b.
  obtain ⟨ha, hb⟩ :=
    zeta_pow_linearly_independent_lt (K := K) hp_odd hk_pos hk_lt (a : ℚ) (b : ℚ) h_K
  have ha_int : a = 0 := by exact_mod_cast ha
  have hb_int : b = 0 := by exact_mod_cast hb
  -- IsCoprime 0 0 is false (gcd 0 0 = 0).
  rw [ha_int, hb_int] at hab
  exact (not_isCoprime_zero_zero (R := ℤ)) hab

/-- **Case I integer congruence: `c ≡ a + b (mod p)`.** From FLT
`a^p + b^p = c^p` and Fermat's little theorem `x^p ≡ x (mod p)`,
we get `c ≡ c^p = a^p + b^p ≡ a + b (mod p)`. -/
theorem fltCaseI_p_dvd_c_sub_a_add_b
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p) :
    (p : ℤ) ∣ (c - (a + b)) := by
  -- Work in ZMod p. There, x^p = x, so a^p + b^p = a + b and c^p = c.
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  -- (c - (a + b) : ZMod p) = c - a - b
  -- From heq: (a : ZMod p)^p + (b : ZMod p)^p = (c : ZMod p)^p.
  have heq' : (a : ZMod p) ^ p + (b : ZMod p) ^ p = (c : ZMod p) ^ p := by
    exact_mod_cast congrArg ((↑·) : ℤ → ZMod p) heq
  haveI : Fact p.Prime := hp
  have ha : (a : ZMod p) ^ p = (a : ZMod p) := ZMod.pow_card _
  have hb : (b : ZMod p) ^ p = (b : ZMod p) := ZMod.pow_card _
  have hc : (c : ZMod p) ^ p = (c : ZMod p) := ZMod.pow_card _
  rw [ha, hb, hc] at heq'
  -- heq' : (a : ZMod p) + (b : ZMod p) = (c : ZMod p)
  rw [← heq']; ring

/-- **Case I corollary: `p ∤ (a + b)`.** From `c ≡ a + b (mod p)` and
`p ∤ c`, we get `p ∤ (a + b)`. -/
theorem fltCaseI_p_not_dvd_a_add_b
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) :
    ¬ (p : ℤ) ∣ (a + b) := by
  intro h_ab
  apply hc
  have h_eq := fltCaseI_p_dvd_c_sub_a_add_b heq
  -- p ∣ c - (a+b) and p ∣ a+b, so p ∣ c.
  have : (p : ℤ) ∣ (c - (a + b)) + (a + b) := dvd_add h_eq h_ab
  have h_simp : (c - (a + b)) + (a + b) = c := by ring
  rwa [h_simp] at this

/-- **Case I residue: `a + ζ^k b ≡ c (mod (ζ-1))`** in `𝓞 K`. From
`a + ζ^k b ≡ a + b (mod (ζ-1))` and `c ≡ a + b (mod p)` (so
`(ζ-1) ∣ c - (a+b)` since `(ζ-1) ∣ p`). -/
theorem fltCaseI_zetaSubOne_dvd_factor_sub_c
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (k : ℕ) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      (((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        (c : 𝓞 K)) := by
  -- (ζ-1) ∣ (a + ζ^k b) - (a + b)
  have h1 := zetaSubOne_dvd_factor_sub_sum p K a b k
  -- p ∣ c - (a + b)
  have h2 := fltCaseI_p_dvd_c_sub_a_add_b heq
  -- (ζ-1) ∣ p ∣ c - (a + b), so (ζ-1) ∣ (c - (a + b)) in 𝓞 K
  have h3 : (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      ((c - (a + b) : ℤ) : 𝓞 K) := by
    rw [zetaSubOne_dvd_intCast_iff]
    exact h2
  -- The factor a + ζ^k b - (a + b) plus (a + b) - c = -(c - (a+b)).
  -- Sum: (a + ζ^k b - (a + b)) - (c - (a + b)) = a + ζ^k b - c.
  have h_sum := dvd_sub h1 h3
  have h_eq :
      ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
          ((a + b : ℤ) : 𝓞 K) -
        ((c - (a + b) : ℤ) : 𝓞 K) =
      ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        (c : 𝓞 K) := by
    push_cast
    ring
  rwa [h_eq] at h_sum

/-- **Case I: `(ζ - 1) ∤ (a + ζ^k b)`.** Under FLT case I, no cyclotomic
factor of `c^p` is divisible by the prime `(ζ - 1)`. The proof:
`(ζ - 1) ∣ (a + ζ^k b)` would force `(ζ - 1) ∣ (a + b)`, hence
`p ∣ (a + b)`, contradicting `fltCaseI_p_not_dvd_a_add_b`. -/
theorem fltCaseI_zetaSubOne_not_dvd_factor
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (k : ℕ) :
    ¬ (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ∣
      ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) := by
  intro h_dvd
  rw [zetaSubOne_dvd_factor_iff_p_dvd] at h_dvd
  exact fltCaseI_p_not_dvd_a_add_b heq hc h_dvd

/-- **Case I: factor at index 0 is non-zero.** Under the FLT case-I
hypotheses (`a^p + b^p = c^p` with `¬ p ∣ c`), the trivial factor
`a + ζ^0 · b = a + b` is non-zero in `𝓞 K`. The argument: if `a + b = 0`
in `𝓞 K`, then `a + b = 0` in `ℤ` by injectivity, so `c^p = a^p + (-a)^p
= 0` (since p is odd), forcing `c = 0` and contradicting `¬ p ∣ c`. -/
theorem fltCaseI_factor_zero_ne_zero
    (hp_odd : Odd p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) :
    ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ 0 * (b : 𝓞 K)) ≠ 0 := by
  rw [pow_zero, one_mul]
  intro h
  -- (a : 𝓞 K) + (b : 𝓞 K) = 0; we want a + b = 0 in ℤ.
  have hsum : ((a + b : ℤ) : 𝓞 K) = 0 := by push_cast; exact h
  have hab_zero : (a + b : ℤ) = 0 := by
    have h_inj : Function.Injective (algebraMap ℤ (𝓞 K)) :=
      FaithfulSMul.algebraMap_injective ℤ (𝓞 K)
    have h_zero : algebraMap ℤ (𝓞 K) (a + b) = algebraMap ℤ (𝓞 K) 0 := by
      rw [map_zero]
      exact hsum
    exact h_inj h_zero
  -- a + b = 0 means b = -a; then c^p = 0 (since p odd), so c = 0.
  have hb : b = -a := by linarith
  rw [hb, hp_odd.neg_pow, ← sub_eq_add_neg, sub_self] at heq
  -- heq : 0 = c^p
  have hc_zero : c = 0 := by
    have hp_ne : p ≠ 0 := hp_odd.pos.ne'
    have h_pow_zero : c ^ p = 0 := heq.symm
    exact pow_eq_zero_iff hp_ne |>.mp h_pow_zero
  -- c = 0 contradicts ¬ p ∣ c.
  exact hc (hc_zero ▸ dvd_zero _)

/-- **Case I: factor at index `p-1` is non-zero**, given `IsCoprime a b`.
The trick: multiply `a + ζ^{p-1} b = 0` by `ζ` to get `b + ζ · a = 0`,
which is the `k = 1` case. -/
theorem fltCaseI_factor_top_ne_zero (hp_odd : Odd p)
    {a b : ℤ} (hab : IsCoprime a b) :
    ((a : 𝓞 K) +
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) * (b : 𝓞 K)) ≠ 0 := by
  intro h
  have hp_pos : 0 < p := hp_odd.pos
  have hp_ge3 : 3 ≤ p := by
    rcases hp_odd with ⟨n, rfl⟩
    have := hp.1.two_le
    omega
  -- ζ * (a + ζ^{p-1} b) = ζ·a + ζ^p · b = ζ·a + b in 𝓞 K.
  set ζU : 𝓞 K := ((zeta_spec p ℚ K).toInteger : 𝓞 K)
  have h_zeta_p : ζU ^ p = 1 := zeta_toInteger_pow_eq_one p K
  have h_mul_zero : ζU * ((a : 𝓞 K) + ζU ^ (p - 1) * (b : 𝓞 K)) = 0 := by
    rw [h, mul_zero]
  have h_swap : ζU * ((a : 𝓞 K) + ζU ^ (p - 1) * (b : 𝓞 K)) =
      (b : 𝓞 K) + ζU ^ 1 * (a : 𝓞 K) := by
    have h_pow : ζU * ζU ^ (p - 1) = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hp_pos, h_zeta_p]
    rw [pow_one, mul_add, ← mul_assoc, h_pow, one_mul, mul_comm (ζU) (a : 𝓞 K),
      add_comm]
  rw [h_swap] at h_mul_zero
  -- Apply fltCaseI_factor_lt_ne_zero with k = 1, a ↦ b, b ↦ a.
  exact fltCaseI_factor_lt_ne_zero (K := K) hp_odd (k := 1) (a := b) (b := a)
    (by omega) (by omega) hab.symm h_mul_zero

/-- **Case I: factor non-zero for any k < p.** Combines the three cases:
* `k = 0`: uses the FLT case I equation and `c ≠ 0`.
* `k ∈ [1, p-2]`: uses linear independence of `1, ζ^k` and IsCoprime.
* `k = p-1`: reduces to the `k = 1` case by multiplying by ζ. -/
theorem fltCaseI_factor_ne_zero (hp_odd : Odd p)
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k : ℕ} (hk : k < p) :
    ((a : 𝓞 K) +
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) ≠ 0 := by
  have hp_pos : 0 < p := hp_odd.pos
  have hp_ge3 : 3 ≤ p := by
    rcases hp_odd with ⟨n, rfl⟩
    have := hp.1.two_le
    omega
  rcases Nat.eq_zero_or_pos k with hk0 | hk_pos
  · subst hk0
    exact fltCaseI_factor_zero_ne_zero (K := K) hp_odd heq hc
  · rcases Nat.lt_or_ge k (p - 1) with hk_lt | hk_top
    · exact fltCaseI_factor_lt_ne_zero (K := K) hp_odd hk_pos (by omega) hab
    · -- k ∈ [p-1, p), i.e., k = p - 1.
      have hk_eq : k = p - 1 := by omega
      subst hk_eq
      exact fltCaseI_factor_top_ne_zero (K := K) hp_odd hab

/-- **σ-twist of the Kummer-style decomposition.** If we have a
decomposition
  `a + ζ^k b = ζ^m · algebraMap v · γ^p`
with `v ∈ (𝓞 K⁺)ˣ` real, then applying complex conjugation σ gives
  `a + ζ^{p-k} b = ζ^{(p-1)·m mod p} · algebraMap v · σ(γ)^p`,
since `σ(ζ) = ζ^{p-1}`, `σ(v) = v`, and `σ(γ^p) = σ(γ)^p`. -/
theorem fltCaseI_decomposition_complexConj
    [IsCMField K] (a b : ℤ) {k : ℕ} (hk : k ≤ p) {m : ℕ}
    (v_plus : (𝓞 (K⁺))ˣ) (γ : 𝓞 K)
    (h_decomp : ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
      ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) * γ ^ p) :
    ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K)) =
      ((ζcu ^ ((p - 1) * m) :
          (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) *
        (ringOfIntegersComplexConj K γ) ^ p := by
  -- Apply σ to both sides of h_decomp.
  have h_apply : ringOfIntegersComplexConj K
      ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
    ringOfIntegersComplexConj K
      (((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) * γ ^ p) := by
    rw [h_decomp]
  -- LHS = a + ζ^{p-k} b.
  rw [fltCaseI_factor_complexConj a b hk] at h_apply
  -- RHS: σ(ζ^m · algebraMap v · γ^p) = σ(ζ^m) · σ(algebraMap v) · σ(γ^p).
  rw [map_mul, map_mul, map_pow] at h_apply
  -- σ(ζ^m) at unit-cast level = ζ^{(p-1)*m} as in fltCaseI_factor_complexConj.
  have h_sigma_zeta_m :
      ringOfIntegersComplexConj K
        (((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K)) =
      ((ζcu ^ ((p - 1) * m) :
        (𝓞 K)ˣ) : 𝓞 K) := by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      show (ζcu : 𝓞 K) =
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) from IsUnit.unit_spec _,
      map_pow]
    -- σ(ζ) = ζ^(p-1), so σ(ζ)^m = (ζ^(p-1))^m = ζ^{(p-1)*m}.
    rw [complexConj_apply_zeta (p := p) (K := K), ← pow_mul]
  rw [h_sigma_zeta_m] at h_apply
  -- σ(algebraMap v) = algebraMap v (since v is in K⁺).
  have h_sigma_v : ringOfIntegersComplexConj K
      (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) =
      algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus := by
    apply RingOfIntegers.ext
    rw [coe_ringOfIntegersComplexConj, RingOfIntegers.complexConj_eq_self_iff]
    exact ⟨_, rfl⟩
  rw [h_sigma_v] at h_apply
  exact h_apply

/-- **Case I σ-twist mod p (Vandiver / flt-regular form).** From the
case I decomposition `a + ζ^k b = ζ^m · algebraMap v · γ^p`, we have

  `(a + ζ^k b) - ζ^{2m} · (a + ζ^{p-k} b) ∈ (p)`

in `𝓞 K`. The proof: σ-twist gives `a + ζ^{p-k} b = ζ^{(p-1)m} · v · σ(γ)^p`.
Multiplying by `ζ^{2m}`, the ζ-power becomes `ζ^{(p+1)m} = ζ^m`. So
the difference is `ζ^m · v · (γ^p - σ(γ)^p)`, and `γ^p - σ(γ^p) ∈ (p)`
by `pow_sub_intGalConj_mem` from flt-regular. -/
theorem fltCaseI_decomposition_complexConj_mod_p
    [IsCMField K] (hp_two : 2 < p) (a b : ℤ) {k : ℕ} (hk : k ≤ p) {m : ℕ}
    (v_plus : (𝓞 (K⁺))ˣ) (γ : 𝓞 K)
    (h_decomp : ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
      ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) * γ ^ p) :
    ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) -
        ((ζcu ^ (2 * m) :
          (𝓞 K)ˣ) : 𝓞 K) *
          ((a : 𝓞 K) +
            ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K)) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) := by
  -- Use the σ-twist of the decomposition.
  have h_conj := fltCaseI_decomposition_complexConj a b hk v_plus γ h_decomp
  -- LHS = a + ζ^k b = decomp at k.
  -- ζ^{2m} · (a + ζ^{p-k} b) = ζ^{2m} · ζ^{(p-1)m} · v · σ(γ)^p
  --                          = ζ^{m·(p+1)} · v · σ(γ)^p
  --                          = ζ^m · v · σ(γ)^p   (since ζ^p = 1, so ζ^{m(p+1)} = ζ^{m·p+m} = ζ^m)
  have h_zeta_p : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
    zeta_toInteger_pow_eq_one p K
  have h_zeta_pow_collapse :
      ((ζcu ^ (2 * m) : (𝓞 K)ˣ) : 𝓞 K) *
      ((ζcu ^ ((p - 1) * m) : (𝓞 K)ˣ) : 𝓞 K) =
      ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) := by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val,
      show (ζcu : 𝓞 K) =
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) from IsUnit.unit_spec _,
      ← pow_add]
    -- 2*m + (p-1)*m = (p+1)*m. We want to show ζ^{(p+1)*m} = ζ^m.
    -- (p+1)*m = p*m + m. ζ^{p*m + m} = (ζ^p)^m · ζ^m = ζ^m.
    have heq : 2 * m + (p - 1) * m = m + p * m := by
      have hp_pos : 0 < p := hp.1.pos
      have hpk : (p - 1) * m = p * m - m := by
        rcases Nat.eq_zero_or_pos m with hm0 | _
        · simp [hm0]
        · rw [Nat.sub_one_mul]
      rw [hpk]
      have : m ≤ p * m := Nat.le_mul_of_pos_left m hp_pos
      omega
    rw [heq, pow_add, pow_mul, h_zeta_p, one_pow, mul_one]
  -- Now multiply h_conj by ζ^{2m}:
  have h_step : ((ζcu ^ (2 * m) :
        (𝓞 K)ˣ) : 𝓞 K) *
      ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K)) =
      ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) *
        (ringOfIntegersComplexConj K γ) ^ p := by
    rw [h_conj]
    rw [show ((ζcu ^ (2 * m) : (𝓞 K)ˣ) : 𝓞 K) *
        (((ζcu ^ ((p - 1) * m) : (𝓞 K)ˣ) : 𝓞 K) *
          (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) *
          (ringOfIntegersComplexConj K γ) ^ p) =
        (((ζcu ^ (2 * m) : (𝓞 K)ˣ) : 𝓞 K) *
          ((ζcu ^ ((p - 1) * m) : (𝓞 K)ˣ) : 𝓞 K)) *
          (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) *
          (ringOfIntegersComplexConj K γ) ^ p by ring,
      h_zeta_pow_collapse]
  rw [h_step, h_decomp]
  -- Goal: ζ^m · v · γ^p - ζ^m · v · σ(γ)^p ∈ (p).
  rw [show
      ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) * γ ^ p -
      ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) *
        (ringOfIntegersComplexConj K γ) ^ p =
      ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) *
        (γ ^ p - (ringOfIntegersComplexConj K γ) ^ p) by ring]
  refine Ideal.mul_mem_left _ _ ?_
  -- γ^p - σ(γ^p) ∈ (p) by pow_sub_intGalConj_mem.
  have h_apply : γ ^ p - ringOfIntegersComplexConj K (γ ^ p) ∈
      Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K)) :=
    FltRegular.CaseI.pow_sub_intGalConj_mem (p := p) (K := K) γ hp_two
  rw [map_pow] at h_apply
  exact h_apply

/-- **Factor-conjugate product expansion.** The product of the
cyclotomic factor at index `k` with its `σ`-conjugate (which is the
factor at index `p - k`) expands to
  `a^2 + a·b·(ζ^k + ζ^{p-k}) + b^2`,
all of whose terms lie in `K⁺` since `ζ^k + ζ^{p-k}` is `σ`-fixed.

This expression equals `algebraMap K⁺→K (intNorm(a + ζ^k b))` by
`algebraMap_intNorm_eq_self_mul_complexConj`. -/
theorem fltCaseI_factor_mul_complexConj
    [IsCMField K] (a b : ℤ) {k : ℕ} (_hk : k ≤ p) :
    ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) *
        ((a : 𝓞 K) +
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K)) =
      (a : 𝓞 K) ^ 2 +
        (a : 𝓞 K) * (b : 𝓞 K) *
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k +
            ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k)) +
        (b : 𝓞 K) ^ 2 *
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k *
            ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k)) := by
  ring

/-- **Cancellation form: the product simplifies modulo `ζ^p = 1`.** Using
`ζ^k · ζ^{p-k} = ζ^p = 1`, the product expansion yields
  `(a + ζ^k b)·(a + ζ^{p-k} b) = a^2 + a·b·(ζ^k + ζ^{p-k}) + b^2`. -/
theorem fltCaseI_factor_mul_complexConj' [IsCMField K]
    (a b : ℤ) {k : ℕ} (hk : k ≤ p) :
    ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) *
        ((a : 𝓞 K) +
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) * (b : 𝓞 K)) =
      (a : 𝓞 K) ^ 2 +
        (a : 𝓞 K) * (b : 𝓞 K) *
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k +
            ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k)) +
        (b : 𝓞 K) ^ 2 := by
  rw [fltCaseI_factor_mul_complexConj a b hk]
  -- ζ^k · ζ^(p-k) = ζ^p = 1
  have h_zeta_p : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
    zeta_toInteger_pow_eq_one p K
  rw [← pow_add, Nat.add_sub_cancel' hk, h_zeta_p, mul_one]

/-- **Combined: factor-product equals real-unit-squared times pth-power.**
Combining the case I decomposition with the σ-twist and the factor
product expansion, we get the K⁺-side identity expressed in `𝓞 K`:

  `a^2 + ab·(ζ^k + ζ^{p-k}) + b^2 = (algebraMap v)^2 · (γ · σ(γ))^p`

Both sides are σ-fixed (so lie in the image of `𝓞 K⁺ → 𝓞 K`), and
the LHS is the product `(a + ζ^k b) · (a + ζ^{p-k} b)`. -/
theorem fltCaseI_factor_product_eq_realUnit_sq_mul_pow
    [IsCMField K] (a b : ℤ) {k : ℕ} (hk : k ≤ p) {m : ℕ}
    (v_plus : (𝓞 (K⁺))ˣ) (γ : 𝓞 K)
    (h_decomp : ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
      ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) * γ ^ p) :
    (a : 𝓞 K) ^ 2 +
        (a : 𝓞 K) * (b : 𝓞 K) *
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k +
            ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k)) +
        (b : 𝓞 K) ^ 2 =
      (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) ^ 2 *
        (γ * ringOfIntegersComplexConj K γ) ^ p := by
  -- LHS = (a + ζ^k b)·(a + ζ^{p-k} b) by the product expansion.
  rw [← fltCaseI_factor_mul_complexConj' a b hk]
  -- Substitute the decomposition for both factors.
  have h_decomp_conj :=
    fltCaseI_decomposition_complexConj (p := p) (K := K) a b hk v_plus γ h_decomp
  rw [h_decomp, h_decomp_conj]
  -- Now expand: (ζ^m · v · γ^p) · (ζ^{(p-1)m} · v · σ(γ)^p)
  --           = ζ^{m + (p-1)m} · v^2 · γ^p · σ(γ)^p
  --           = ζ^{p·m} · v^2 · (γ · σ(γ))^p
  --           = v^2 · (γ · σ(γ))^p   (since ζ^{p·m} = (ζ^p)^m = 1)
  have h_zeta_p : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
    zeta_toInteger_pow_eq_one p K
  have h_zeta_pm : ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) *
      ((ζcu ^ ((p - 1) * m) :
        (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
      show (ζcu : 𝓞 K) =
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) from IsUnit.unit_spec _,
      ← pow_add]
    have heq : m + (p - 1) * m = p * m := by
      have hp_pos : 0 < p := hp.1.pos
      have hpk : (p - 1) * m = p * m - m := by
        rcases Nat.eq_zero_or_pos m with hm0 | _
        · simp [hm0]
        · rw [Nat.sub_one_mul]
      rw [hpk]
      have : m ≤ p * m := Nat.le_mul_of_pos_left m hp_pos
      omega
    rw [heq, pow_mul, h_zeta_p, one_pow]
  linear_combination
    ((algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) ^ 2 *
      (γ * ringOfIntegersComplexConj K γ) ^ p) * h_zeta_pm

/-- **The element `ζ^k + ζ^{p-k}` is σ-fixed in 𝓞 K** (hence lies in
the image of `algebraMap (𝓞 K⁺) (𝓞 K)`). This is the trace of
`ζ^k` from `K` to `K⁺`. -/
theorem zeta_pow_add_complexConj_zeta_pow [IsCMField K] {k : ℕ} (hk : k ≤ p) :
    ringOfIntegersComplexConj K
        (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k +
          ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k)) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) := by
  rw [map_add]
  -- σ(ζ^k) = ζ^{p-k} (already proved as part of fltCaseI_factor_complexConj's body).
  have h_sigma_k : ringOfIntegersComplexConj K
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) := by
    rw [map_pow]
    have h_conj_zeta : ringOfIntegersComplexConj K
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) := by
      exact complexConj_apply_zeta (p := p) (K := K)
    rw [h_conj_zeta, ← pow_mul]
    -- ζ^{(p-1)*k} = ζ^(p-k) by the same argument as in fltCaseI_factor_complexConj.
    have h_zeta_p : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
      zeta_toInteger_pow_eq_one p K
    have hp_pos : 0 < p := hp.1.pos
    have h1 : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((p - 1) * k) *
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k = 1 := by
      rw [← pow_add]
      have heq : (p - 1) * k + k = p * k := by
        have hpk : (p - 1) * k = p * k - k := by
          rcases Nat.eq_zero_or_pos k with hk0 | _
          · simp [hk0]
          · rw [Nat.sub_one_mul]
        rw [hpk]
        have hkp : k ≤ p * k := Nat.le_mul_of_pos_left k hp_pos
        omega
      rw [heq, pow_mul, h_zeta_p, one_pow]
    have h2 : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) *
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k = 1 := by
      rw [← pow_add, Nat.sub_add_cancel hk, h_zeta_p]
    have h_unit_pow : IsUnit (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k) :=
      ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).pow k
    exact mul_right_cancel₀ h_unit_pow.ne_zero (h1.trans h2.symm)
  -- σ(ζ^{p-k}) = ζ^{p-(p-k)} = ζ^k by symmetry.
  have h_sigma_pk : ringOfIntegersComplexConj K
      (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k)) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k := by
    rw [map_pow]
    have h_conj_zeta : ringOfIntegersComplexConj K
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) =
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) := by
      exact complexConj_apply_zeta (p := p) (K := K)
    rw [h_conj_zeta, ← pow_mul]
    have h_zeta_p : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ p = 1 :=
      zeta_toInteger_pow_eq_one p K
    have hp_pos : 0 < p := hp.1.pos
    have hpk_le : p - k ≤ p := Nat.sub_le _ _
    have h1 : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ ((p - 1) * (p - k)) *
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) = 1 := by
      rw [← pow_add]
      have heq : (p - 1) * (p - k) + (p - k) = p * (p - k) := by
        have hpk : (p - 1) * (p - k) = p * (p - k) - (p - k) := by
          rcases Nat.eq_zero_or_pos (p - k) with hpk0 | _
          · simp [hpk0]
          · rw [Nat.sub_one_mul]
        rw [hpk]
        have hkp : (p - k) ≤ p * (p - k) := Nat.le_mul_of_pos_left _ hp_pos
        omega
      rw [heq, pow_mul, h_zeta_p, one_pow]
    -- Want σ(ζ^{p-k}) = ζ^{p - (p-k)} = ζ^k.
    -- We have σ(ζ^{p-k}) = ζ^{(p-1)(p-k)} and want to show this equals ζ^k.
    -- Strategy: ζ^{(p-1)(p-k)} · ζ^{p-k} = 1 = ζ^k · ζ^{p-k}, cancel ζ^{p-k}.
    have h2 : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k *
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k) = 1 := by
      rw [← pow_add, Nat.add_sub_cancel' hk, h_zeta_p]
    have h_unit_pow : IsUnit (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k)) :=
      ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).pow (p - k)
    exact mul_right_cancel₀ h_unit_pow.ne_zero (h1.trans h2.symm)
  rw [h_sigma_k, h_sigma_pk, add_comm]

/-- **K⁺-side relation from the case I decomposition.** Taking the
relative integer norm of `a + ζ^k b = ζ^m · algebraMap v · γ^p` gives
the K⁺-side identity
  `intNorm(a + ζ^k b) = v^2 · intNorm(γ)^p`,
since `intNorm(ζ^m) = 1` and `intNorm(algebraMap v) = v^2`.

This is the input to descending the Mirimanoff polynomial argument from
`K` to `K⁺`. -/
theorem fltCaseI_intNorm_decomposition
    [IsCMField K] (a b : ℤ) {k : ℕ} {m : ℕ}
    (v_plus : (𝓞 (K⁺))ˣ) (γ : 𝓞 K)
    (h_decomp : ((a : 𝓞 K) +
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
      ((ζcu ^ m : (𝓞 K)ˣ) : 𝓞 K) *
        (algebraMap (𝓞 (K⁺)) (𝓞 K) v_plus) * γ ^ p) :
    Algebra.intNorm (𝓞 (K⁺)) (𝓞 K)
        ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
      (v_plus : 𝓞 (K⁺)) ^ 2 *
        Algebra.intNorm (𝓞 (K⁺)) (𝓞 K) γ ^ p := by
  rw [h_decomp, map_mul, map_mul, map_pow]
  -- intNorm(ζ^m) = 1.
  rw [zeta_pow_intNorm_eq_one (p := p) (K := K), one_mul]
  -- intNorm(algebraMap v) = v^2 (relative norm of K⁺ → K of degree 2).
  congr 1
  -- Goal: intNorm (algebraMap v) = v^2.
  apply FaithfulSMul.algebraMap_injective (𝓞 (K⁺)) (𝓞 K)
  rw [algebraMap_intNorm_eq_self_mul_complexConj (K := K),
    IsPrimaryUnit.complexConj_algebraMap_eq v_plus, map_pow, sq]

/-- **K-level expansion of intNorm(a + ζ^k b).** The relative integer
norm `intNorm (𝓞 K⁺) (𝓞 K) (a + ζ^k b)` lifted via `algebraMap` equals
the explicit polynomial expression
  `a^2 + ab·(ζ^k + ζ^{p-k}) + b^2`
in `𝓞 K`. This combines `algebraMap_intNorm_eq_self_mul_complexConj`
(from Hilbert90) with the σ-conjugate factor identity. -/
theorem algebraMap_intNorm_factor_eq [IsCMField K]
    (a b : ℤ) {k : ℕ} (hk : k ≤ p) :
    algebraMap (𝓞 K⁺) (𝓞 K)
        (Algebra.intNorm (𝓞 K⁺) (𝓞 K)
          ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K))) =
      (a : 𝓞 K) ^ 2 +
        (a : 𝓞 K) * (b : 𝓞 K) *
          (((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k +
            ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - k)) +
        (b : 𝓞 K) ^ 2 := by
  rw [algebraMap_intNorm_eq_self_mul_complexConj (K := K),
    fltCaseI_factor_complexConj a b hk]
  exact fltCaseI_factor_mul_complexConj' a b hk

/-- **`intNorm(a + ζ^k b) ≡ (a+b)^2 (mod (ζ-1)^2)`** in `𝓞 K`. The
algebraMap lift of `intNorm(a + ζ^k b)` differs from `(a+b)^2` by
`a·b·(ζ^k + ζ^{p-k} - 2)`, and `(ζ-1)^2` divides `ζ^k + ζ^{p-k} - 2`. -/
theorem zetaSubOne_sq_dvd_algebraMap_intNorm_factor_sub_sum_sq
    [IsCMField K] (a b : ℤ) {k : ℕ} (hk : k ≤ p) :
    (((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1) ^ 2 ∣
      (algebraMap (𝓞 K⁺) (𝓞 K)
        (Algebra.intNorm (𝓞 K⁺) (𝓞 K)
          ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K))) -
        ((a + b : ℤ) : 𝓞 K) ^ 2) := by
  rw [algebraMap_intNorm_factor_eq a b hk]
  -- Goal: (ζ-1)^2 ∣ (a^2 + ab(ζ^k + ζ^{p-k}) + b^2) - (a+b)^2
  --              = ab(ζ^k + ζ^{p-k} - 2)
  have h_dvd := zetaSubOne_sq_dvd_zeta_pow_add_zeta_pow_sub_two p K hk
  obtain ⟨w, hw⟩ := h_dvd
  refine ⟨(a : 𝓞 K) * (b : 𝓞 K) * w, ?_⟩
  have h_cast : ((a + b : ℤ) : 𝓞 K) = (a : 𝓞 K) + (b : 𝓞 K) := by push_cast; rfl
  rw [h_cast]
  linear_combination (a : 𝓞 K) * (b : 𝓞 K) * hw

/-- **Streamlined K⁺-norm relation under regularity.** Direct
specialisation: under FLT case I + regularity, for each `k < p` there
exist a real unit `v_k` and an element `γ_k` such that
  `intNorm(a + ζ^k b) = v_k^2 · intNorm(γ_k)^p` in `𝓞 K⁺`. -/
theorem fltCaseI_intNorm_eq_realUnit_sq_mul_pow_of_regular
    (hp_two : 2 < p) (hp_odd : Odd p)
    [Fintype (ClassGroup (𝓞 K))]
    (h_reg : p.Coprime (Fintype.card (ClassGroup (𝓞 K))))
    {a b c : ℤ} (heq : a ^ p + b ^ p = c ^ p)
    (hc : ¬ (p : ℤ) ∣ c) (hab : IsCoprime a b)
    {k : ℕ} (hk : k < p) :
    haveI := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
    ∃ (v_plus : (𝓞 (K⁺))ˣ) (γ : 𝓞 K),
      Algebra.intNorm (𝓞 (K⁺)) (𝓞 K)
          ((a : 𝓞 K) + ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ k * (b : 𝓞 K)) =
        (v_plus : 𝓞 (K⁺)) ^ 2 *
          Algebra.intNorm (𝓞 (K⁺)) (𝓞 K) γ ^ p := by
  haveI : IsCMField K := IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_two⟩
  obtain ⟨m, v_plus, γ, h_decomp⟩ := fltCaseI_factor_eq_zeta_pow_mul_real_unit_mul_pow_of_regular
    hp_two hp_odd h_reg heq hc hab
    (fun j hj ↦ fltCaseI_factor_ne_zero (K := K) hp_odd heq hc hab hj) hk
  exact ⟨v_plus, γ, fltCaseI_intNorm_decomposition (K := K) a b v_plus γ h_decomp⟩

end FLT37

end BernoulliRegular

end
