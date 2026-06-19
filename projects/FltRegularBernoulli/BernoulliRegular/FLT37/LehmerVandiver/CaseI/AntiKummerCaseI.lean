import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummerL3
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.Stage2Interface

/-!
# Case-I FLT data → AK chain inputs

This file builds the bridge from FLT case-I data (a, b, c, ζ, I) to the
σ-anti Kummer chain inputs (α₀ ≠ 0, α₀ ^ 2 ≠ 1, …) needed by AK-4.

The main ingredient is K-arithmetic of cyclotomic primitive roots: when
`ζ ∈ K` is primitive `p`-th root and `b ≠ 0` in ℤ, no ℚ-linear relation
of the form `a + ζ · b = 0` holds (because `ζ` has minimal polynomial of
degree `p - 1 ≥ 2` over ℚ when `p` is an odd prime).
-/

@[expose] public section

noncomputable section

open NumberField Polynomial

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseI

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type} [Field K] [NumberField K]
  [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **K-level complex conjugation sends any primitive `p`-th root to its inverse**,
for `p` odd prime in a CM cyclotomic K. This is the K-level statement of
the well-known fact that the σ-anti property holds for every root of
unity in the CM cyclotomic field.

Proof: ζ is a unit in `𝓞 K` (root of unity); membership in `torsion K`;
apply `unitsComplexConj_torsion` then map back to K via
`coe_ringOfIntegersComplexConj`. -/
theorem complexConj_K_apply_primRoot_eq_inv
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) :
    NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K ζ) =
      (algebraMap (𝓞 K) K ζ)⁻¹ := by
  have hp_prime : p.Prime := Fact.out
  have hζ_unit : IsUnit ζ := hζ.isUnit hp_prime.ne_zero
  have hζ_torsion : hζ_unit.unit ∈ NumberField.Units.torsion K := by
    refine (CommGroup.mem_torsion _).2 (isOfFinOrder_iff_pow_eq_one.2 ⟨p, hp_prime.pos, ?_⟩)
    apply Units.ext
    simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]
    exact hζ.pow_eq_one
  have h_units :=
    NumberField.IsCMField.unitsComplexConj_torsion (K := K) ⟨hζ_unit.unit, hζ_torsion⟩
  have h_OK : NumberField.IsCMField.ringOfIntegersComplexConj K
      ((hζ_unit.unit : (𝓞 K)ˣ) : 𝓞 K) =
      (((hζ_unit.unit)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) :=
    Units.ext_iff.mp h_units
  have h_unit_val : ((hζ_unit.unit : (𝓞 K)ˣ) : 𝓞 K) = ζ := hζ_unit.unit_spec
  rw [h_unit_val] at h_OK
  have h_inv_val : (((hζ_unit.unit)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ζ = 1 := by
    have h_one : ((hζ_unit.unit)⁻¹ * hζ_unit.unit : (𝓞 K)ˣ) = 1 := inv_mul_cancel _
    have h_cast := Units.ext_iff.mp h_one
    rw [Units.val_mul, Units.val_one, h_unit_val] at h_cast
    exact h_cast
  have h_inv_K :
      algebraMap (𝓞 K) K (((hζ_unit.unit)⁻¹ : (𝓞 K)ˣ) : 𝓞 K) =
      (algebraMap (𝓞 K) K ζ)⁻¹ := by
    have h_mul := congrArg (algebraMap (𝓞 K) K) h_inv_val
    rw [map_mul, map_one] at h_mul
    exact eq_inv_of_mul_eq_one_left h_mul
  have h_conj_OK_K :
      algebraMap (𝓞 K) K (NumberField.IsCMField.ringOfIntegersComplexConj K ζ) =
      NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K ζ) :=
    NumberField.IsCMField.coe_ringOfIntegersComplexConj (K := K) ζ
  rw [← h_conj_OK_K, h_OK, h_inv_K]

omit [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **`a + ζ · b ≠ 0` in K** for `ζ` a primitive `p`-th root with `p` odd prime
and `b ≠ 0` an integer.

The minimal polynomial of `ζ` over ℚ is the `p`-th cyclotomic polynomial,
which has degree `p - 1 ≥ 2` for `p` odd prime. If `a + ζ b = 0`, then
`ζ` is a root of `b · X + a ∈ ℚ[X]` (a degree-1 polynomial), so the
minimal polynomial divides this degree-1 polynomial, contradicting
`natDegree (minpoly) = p - 1 ≥ 2`. -/
theorem intCast_add_zeta_mul_intCast_ne_zero
    (hp_odd : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a b : ℤ} (hb : b ≠ 0) :
    (a : K) + ζ * (b : K) ≠ 0 := by
  intro h
  have hp_prime : p.Prime := Fact.out
  haveI : NeZero (p : ℕ) := ⟨hp_prime.ne_zero⟩
  -- ζ is a root of f := C b * X + C a.
  set f : Polynomial ℚ := C ((b : ℚ)) * X + C ((a : ℚ)) with hf_def
  have hb_rat : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  -- f ≠ 0 since leading coefficient b ≠ 0.
  have hf_ne : f ≠ 0 := by
    rw [hf_def]
    intro h0
    have : (C ((b : ℚ)) * X + C ((a : ℚ))).coeff 1 = 0 := by rw [h0]; simp
    rw [coeff_add, coeff_C_mul, coeff_X_one, mul_one, coeff_C, if_neg (by decide : (1 : ℕ) ≠ 0),
        add_zero] at this
    exact hb_rat this
  -- f.natDegree = 1.
  have hf_natDeg : f.natDegree = 1 := by
    rw [hf_def]
    exact natDegree_linear hb_rat
  -- aeval ζ f = 0.
  have hf_eval : aeval ζ f = 0 := by
    rw [hf_def]
    simp only [map_add, map_mul, aeval_X, aeval_C]
    -- Goal: (algebraMap ℚ K) ↑b * ζ + (algebraMap ℚ K) ↑a = 0 in K.
    have hb_K : (algebraMap ℚ K) ((b : ℚ)) = (b : K) := by
      have : (algebraMap ℚ K) ((b : ℚ)) = ((b : ℚ) : K) := by
        rw [IsScalarTower.algebraMap_apply ℚ ℚ K]; simp
      rw [this]; push_cast; rfl
    have ha_K : (algebraMap ℚ K) ((a : ℚ)) = (a : K) := by
      have : (algebraMap ℚ K) ((a : ℚ)) = ((a : ℚ) : K) := by
        rw [IsScalarTower.algebraMap_apply ℚ ℚ K]; simp
      rw [this]; push_cast; rfl
    rw [hb_K, ha_K]
    linear_combination h
  -- minpoly ζ over ℚ divides f.
  have h_minpoly_dvd : minpoly ℚ ζ ∣ f := minpoly.dvd ℚ ζ hf_eval
  -- natDegree minpoly ≤ natDegree f = 1.
  have h_minpoly_le : (minpoly ℚ ζ).natDegree ≤ f.natDegree :=
    natDegree_le_of_dvd h_minpoly_dvd hf_ne
  -- minpoly ζ = cyclotomic p ℚ (since cyclotomic_p irreducible over ℚ).
  have h_irr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp_prime.pos
  have h_minpoly_eq : minpoly ℚ ζ = cyclotomic p ℚ :=
    (hζ.minpoly_eq_cyclotomic_of_irreducible h_irr).symm
  have h_minpoly_natDeg : (minpoly ℚ ζ).natDegree = p - 1 := by
    rw [h_minpoly_eq, natDegree_cyclotomic, Nat.totient_prime hp_prime]
  -- Combine: p - 1 ≤ 1.
  rw [h_minpoly_natDeg, hf_natDeg] at h_minpoly_le
  -- But p ≥ 3 (odd prime), so p - 1 ≥ 2. Contradiction.
  have hp_ge_3 : 3 ≤ p := by
    rcases hp_prime.two_le.lt_or_eq with h | h
    · omega
    · exfalso; exact hp_odd h.symm
  omega

omit [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **`a + ζ * b ≠ 0` in `𝓞 K`** for `ζ` primitive `p`-th root, `p` odd prime,
`b ≠ 0`. Follows from the K-level version by injectivity of `𝓞 K → K`. -/
theorem ringOfInt_intCast_add_zeta_mul_intCast_ne_zero
    (hp_odd : p ≠ 2)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    {a b : ℤ} (hb : b ≠ 0) :
    ((a : 𝓞 K) + ζ * (b : 𝓞 K)) ≠ 0 := by
  intro h0
  -- Apply algebraMap to K.
  have h_K : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) = 0 := by
    rw [h0]; simp
  -- Image in K: a + ζ_K · b where ζ_K = algebraMap ζ in K.
  have h_K_expand : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) =
      (a : K) + algebraMap (𝓞 K) K ζ * (b : K) := by
    rw [map_add, map_mul]
    have h_a : algebraMap (𝓞 K) K (a : 𝓞 K) = (a : K) := by rfl
    have h_b : algebraMap (𝓞 K) K (b : 𝓞 K) = (b : K) := by rfl
    rw [h_a, h_b]
  rw [h_K_expand] at h_K
  have hζ_K : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p :=
    hζ.map_of_injective (RingOfIntegers.coe_injective)
  exact intCast_add_zeta_mul_intCast_ne_zero (K := K) hp_odd hζ_K hb h_K

omit [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **`a + ζ * b ≠ 0` (K-image) from case-I FLT data**: under the case-I
non-divisibility `¬ p ∣ abc` (which forces `b ≠ 0`), the K-image of the
case-I factor `(a + ζ b)` is nonzero. -/
theorem caseI_factor_K_ne_zero
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) :
    algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) ≠ 0 := by
  have hb_ne_zero : b ≠ 0 := by
    intro hb0
    apply hcaseI
    rw [hb0]; ring_nf; exact ⟨0, rfl⟩
  intro h_K
  -- Use the 𝓞 K-level lemma plus algebraMap injectivity.
  have h_oK : ((a : 𝓞 K) + ζ * (b : 𝓞 K)) = 0 := by
    apply RingOfIntegers.coe_injective
    rw [h_K]
    simp
  exact ringOfInt_intCast_add_zeta_mul_intCast_ne_zero (K := K) hp_odd hζ hb_ne_zero h_oK

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **σ-anti radical denominator nonzero** under case-I hypotheses. -/
theorem caseI_antiRadical_denom_K_ne_zero
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p) :
    NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0 := by
  intro h0
  -- Apply complexConj to get back original.
  have h_inv : NumberField.IsCMField.complexConj K
      (NumberField.IsCMField.complexConj K
        (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)))) =
      algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) :=
    NumberField.IsCMField.complexConj_apply_apply K _
  rw [h0, map_zero] at h_inv
  exact caseI_factor_K_ne_zero (K := K) hp_odd hcaseI hζ h_inv.symm

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **σ-anti radical nonzero** under case-I hypotheses. -/
theorem caseI_antiRadical_ne_zero
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0)) :
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab ≠ 0 := by
  unfold BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
  exact div_ne_zero
    (caseI_factor_K_ne_zero (K := K) hp_odd hcaseI hζ)
    (caseI_antiRadical_denom_K_ne_zero (K := K) hp_odd hcaseI hζ)

omit [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **`a + ζ b = a + ζ⁻¹ b` in K ⟹ b = 0** (when `p` is odd prime, `ζ` a primitive
`p`-th root in K).

This is the K-arithmetic content of the α₀ = 1 case: the equation forces `b(ζ - ζ⁻¹) = 0`
in K, and ζ - ζ⁻¹ ≠ 0 for p odd, so b = 0. -/
theorem intCast_b_eq_zero_of_zeta_pair_eq
    (hp_odd : p ≠ 2)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a b : ℤ}
    (h : (a : K) + ζ * (b : K) = (a : K) + ζ⁻¹ * (b : K)) :
    (b : K) = 0 := by
  -- Subtract: ζ b - ζ⁻¹ b = 0, i.e., b(ζ - ζ⁻¹) = 0.
  have h_diff : (ζ - ζ⁻¹) * (b : K) = 0 := by linear_combination h
  have hζ_ne : ζ ≠ 0 := hζ.ne_zero (Fact.out : p.Prime).ne_zero
  -- ζ - ζ⁻¹ = (ζ² - 1) / ζ, so (ζ - ζ⁻¹) * b = 0 ⟹ (ζ² - 1) * b = 0 (multiply by ζ).
  have h_eq2 : (ζ^2 - 1) * (b : K) = 0 := by
    have : ζ * ((ζ - ζ⁻¹) * (b : K)) = ζ * 0 := by rw [h_diff]
    field_simp at this
    linear_combination this
  -- ζ² ≠ 1 for p odd ≥ 3 (since order of ζ is p > 2).
  have hp_prime : p.Prime := Fact.out
  have hζ_sq_ne : ζ^2 ≠ 1 := by
    intro h_sq
    have h_order : p ∣ 2 := hζ.dvd_of_pow_eq_one 2 h_sq
    have hp_ge_3 : 3 ≤ p := by
      rcases hp_prime.two_le.lt_or_eq with h | h
      · omega
      · exfalso; exact hp_odd h.symm
    -- p ≥ 3 and p ∣ 2 ⟹ p ≤ 2, contradiction.
    have : p ≤ 2 := Nat.le_of_dvd two_pos h_order
    omega
  -- ζ² - 1 ≠ 0.
  have hζ2_minus_one_ne : ζ^2 - 1 ≠ 0 := sub_ne_zero.mpr hζ_sq_ne
  -- From (ζ² - 1) * b = 0 with ζ² - 1 ≠ 0 in K, get b = 0.
  exact (mul_eq_zero.mp h_eq2).resolve_left hζ2_minus_one_ne

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`α₀ ≠ 1` from case-I FLT data** for `p` odd prime.

If α₀ = 1, then (a + ζ b) = σ(a + ζ b) = (a + ζ⁻¹ b), which forces `b · (ζ - ζ⁻¹) = 0`.
Since `ζ - ζ⁻¹ ≠ 0` (because `ζ² ≠ 1` for `p` odd), this forces `b = 0`, contradicting
the case-I assumption `¬ p ∣ abc` (which forces `b ≠ 0`). -/
theorem caseI_antiRadical_ne_one
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0)) :
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab ≠ 1 := by
  intro h_eq_one
  unfold BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical at h_eq_one
  have h_denom_ne : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0 :=
    caseI_antiRadical_denom_K_ne_zero (K := K) hp_odd hcaseI hζ
  -- ℤ ⊂ K⁺ ⊂ K, complex conj fixes K⁺.
  have h_int_fixed : ∀ (n : ℤ), NumberField.IsCMField.complexConj K (n : K) = (n : K) := by
    intro n
    have h_n : (n : K) =
        algebraMap (NumberField.maximalRealSubfield K) K
          (algebraMap ℤ (NumberField.maximalRealSubfield K) n) := by
      rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.maximalRealSubfield K) K]
      rfl
    rw [h_n]
    exact (NumberField.IsCMField.complexConj K).commutes _
  -- α₀ = 1 ⟹ numer = denom.
  have h_eq : (a : K) + algebraMap (𝓞 K) K ζ * (b : K) =
      (a : K) + NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K ζ) * (b : K) := by
    have h_alpha_eq : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) =
        NumberField.IsCMField.complexConj K
          (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) := by
      field_simp at h_eq_one
      exact h_eq_one
    -- Expand both sides via push_cast + map_mul.
    simp only [map_add, map_mul] at h_alpha_eq
    -- algMap (𝓞 K) K (a : 𝓞 K) = (a : K) and similarly for b.
    have h_a_K : algebraMap (𝓞 K) K ((a : 𝓞 K)) = (a : K) := by rfl
    have h_b_K : algebraMap (𝓞 K) K ((b : 𝓞 K)) = (b : K) := by rfl
    rw [h_a_K, h_b_K] at h_alpha_eq
    rw [h_int_fixed a, h_int_fixed b] at h_alpha_eq
    exact h_alpha_eq
  -- σ(ζ) = ζ⁻¹ for any primitive p-th root ζ in K (CM cyclotomic field).
  have hζ_K : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p :=
    hζ.map_of_injective RingOfIntegers.coe_injective
  have h_conj_ζ : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K ζ) =
      (algebraMap (𝓞 K) K ζ)⁻¹ :=
    complexConj_K_apply_primRoot_eq_inv (K := K) hζ
  -- Substitute σ(ζ) = ζ⁻¹ and get b(ζ - ζ⁻¹) = 0 ⟹ b = 0.
  rw [h_conj_ζ] at h_eq
  have h_b_eq_zero : (b : K) = 0 :=
    intCast_b_eq_zero_of_zeta_pair_eq (K := K) hp_odd hζ_K h_eq
  have h_b_ne_zero : (b : K) ≠ 0 := by
    have hb_ne_int : b ≠ 0 := fun hb => hcaseI (by rw [hb]; ring_nf; exact ⟨0, rfl⟩)
    exact_mod_cast hb_ne_int
  exact h_b_ne_zero h_b_eq_zero

omit [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **`b·ζ² + 2a·ζ + b = 0` in K with `p ≥ 5` (odd prime, ≠ 3) and `b ≠ 0` is impossible**.

Implies `ζ` satisfies the quadratic `b·X² + 2a·X + b ∈ ℚ[X]`. Then minpoly of ζ over ℚ
(degree `p − 1 ≥ 4`) divides this degree-2 polynomial, contradiction. -/
theorem intCast_quad_ne_zero_of_p_ge_five
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    {a b : ℤ} (hb : b ≠ 0) :
    (b : K) * ζ ^ 2 + (2 * a : ℤ) * ζ + (b : K) ≠ 0 := by
  intro h
  have hp_prime : p.Prime := Fact.out
  have hp_ge_5 : 5 ≤ p := by
    have h2_le := hp_prime.two_le
    -- p ≥ 2 and p ≠ 2 ⟹ p ≥ 3.
    -- p ≥ 3 and p ≠ 3 ⟹ p ≥ 4.
    -- p ≥ 4 and p prime ⟹ p ≠ 4 (since 4 = 2·2 not prime) ⟹ p ≥ 5.
    rcases hp_prime.eq_two_or_odd' with h_two | ⟨k, h_k⟩
    · exfalso; exact hp_odd h_two
    -- p = 2k + 1, p ≠ 2 (so k ≥ 1), p ≠ 3 (so k ≥ 2), so p ≥ 5.
    omega
  -- Define f := C b * X² + C (2a) * X + C b.
  set f : Polynomial ℚ := C ((b : ℚ)) * X ^ 2 + C ((2 * a : ℤ) : ℚ) * X + C ((b : ℚ)) with hf_def
  have hb_rat : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  -- f.natDegree = 2 via natDegree_quadratic (since leading coefficient b ≠ 0).
  have hf_natDeg : f.natDegree = 2 := by
    rw [hf_def]; exact natDegree_quadratic hb_rat
  -- f ≠ 0 from natDegree being defined.
  have hf_ne : f ≠ 0 := fun h0 => by
    rw [h0, natDegree_zero] at hf_natDeg; omega
  have hf_natDeg_le : f.natDegree ≤ 2 := by rw [hf_natDeg]
  -- aeval ζ f = 0.
  have hf_eval : aeval ζ f = 0 := by
    rw [hf_def]
    simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
    have h_b_K : (algebraMap ℚ K) ((b : ℚ)) = (b : K) := by
      have h_iso : (algebraMap ℚ K) ((b : ℚ)) = ((b : ℚ) : K) := by
        rw [IsScalarTower.algebraMap_apply ℚ ℚ K]; simp
      rw [h_iso]; push_cast; rfl
    have h_2a_K : (algebraMap ℚ K) (((2 * a : ℤ) : ℚ)) = ((2 * a : ℤ) : K) := by
      have h_iso : (algebraMap ℚ K) (((2 * a : ℤ) : ℚ)) = (((2 * a : ℤ) : ℚ) : K) := by
        rw [IsScalarTower.algebraMap_apply ℚ ℚ K]; simp
      rw [h_iso]; push_cast; rfl
    rw [h_b_K, h_2a_K]
    linear_combination h
  -- minpoly ζ over ℚ divides f.
  have h_minpoly_dvd : minpoly ℚ ζ ∣ f := minpoly.dvd ℚ ζ hf_eval
  -- natDegree minpoly ≤ natDegree f ≤ 2.
  have h_minpoly_le : (minpoly ℚ ζ).natDegree ≤ f.natDegree :=
    natDegree_le_of_dvd h_minpoly_dvd hf_ne
  -- But minpoly degree = p - 1 ≥ 4.
  have h_irr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hp_prime.pos
  have h_minpoly_eq : minpoly ℚ ζ = cyclotomic p ℚ :=
    (hζ.minpoly_eq_cyclotomic_of_irreducible h_irr).symm
  have h_minpoly_natDeg : (minpoly ℚ ζ).natDegree = p - 1 := by
    rw [h_minpoly_eq, natDegree_cyclotomic, Nat.totient_prime hp_prime]
  rw [h_minpoly_natDeg] at h_minpoly_le
  -- p - 1 ≤ f.natDegree ≤ 2, but p ≥ 5 so p - 1 ≥ 4. Contradiction.
  omega

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`α₀ ≠ -1` from case-I FLT data** for `p ≥ 5` prime.

If α₀ = -1, then (a + ζ b) = -σ(a + ζ b) = -(a + ζ⁻¹ b), so 2a + b(ζ + ζ⁻¹) = 0 in K.
Multiplying by ζ: bζ² + 2aζ + b = 0, so ζ satisfies a degree-2 polynomial over ℚ.
But ζ has minpoly cyclotomic_p with degree p − 1 ≥ 4, contradiction. -/
theorem caseI_antiRadical_ne_neg_one
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0)) :
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab ≠ -1 := by
  intro h_eq_neg_one
  unfold BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical at h_eq_neg_one
  have h_denom_ne : NumberField.IsCMField.complexConj K
      (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) ≠ 0 :=
    caseI_antiRadical_denom_K_ne_zero (K := K) hp_odd hcaseI hζ
  -- ℤ ⊂ K⁺ ⊂ K, complex conj fixes K⁺.
  have h_int_fixed : ∀ (n : ℤ), NumberField.IsCMField.complexConj K (n : K) = (n : K) := by
    intro n
    have h_n : (n : K) =
        algebraMap (NumberField.maximalRealSubfield K) K
          (algebraMap ℤ (NumberField.maximalRealSubfield K) n) := by
      rw [← IsScalarTower.algebraMap_apply ℤ (NumberField.maximalRealSubfield K) K]
      rfl
    rw [h_n]; exact (NumberField.IsCMField.complexConj K).commutes _
  -- σ(ζ_K) = ζ_K⁻¹ (via shipped helper complexConj_K_apply_primRoot_eq_inv).
  have hζ_K : IsPrimitiveRoot (algebraMap (𝓞 K) K ζ) p :=
    hζ.map_of_injective RingOfIntegers.coe_injective
  have h_conj_ζ : NumberField.IsCMField.complexConj K (algebraMap (𝓞 K) K ζ) =
      (algebraMap (𝓞 K) K ζ)⁻¹ :=
    complexConj_K_apply_primRoot_eq_inv (K := K) hζ
  -- α₀ = -1 ⟹ numer = -denom ⟹ numer + denom = 0.
  -- Rearrange to 2a + b(ζ + σ(ζ)) = 0 in K.
  have h_eq : (a : K) + algebraMap (𝓞 K) K ζ * (b : K) +
      ((a : K) + (algebraMap (𝓞 K) K ζ)⁻¹ * (b : K)) = 0 := by
    have h_alpha_eq : algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K)) =
        - NumberField.IsCMField.complexConj K
            (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) := by
      rw [div_eq_iff h_denom_ne] at h_eq_neg_one
      linear_combination h_eq_neg_one
    simp only [map_add, map_mul] at h_alpha_eq
    have h_a_K : algebraMap (𝓞 K) K ((a : 𝓞 K)) = (a : K) := by rfl
    have h_b_K : algebraMap (𝓞 K) K ((b : 𝓞 K)) = (b : K) := by rfl
    rw [h_a_K, h_b_K, h_int_fixed a, h_int_fixed b, h_conj_ζ] at h_alpha_eq
    linear_combination h_alpha_eq
  -- Multiply by algMap ζ (nonzero) and rearrange to quadratic.
  have hζ_K_ne : algebraMap (𝓞 K) K ζ ≠ 0 :=
    hζ_K.ne_zero (Fact.out : p.Prime).ne_zero
  -- Multiply both sides by algMap ζ.
  have h_quad : (b : K) * (algebraMap (𝓞 K) K ζ) ^ 2 +
      ((2 * a : ℤ) : K) * algebraMap (𝓞 K) K ζ + (b : K) = 0 := by
    have h_mul := congrArg (· * algebraMap (𝓞 K) K ζ) h_eq
    have h_inv : (algebraMap (𝓞 K) K ζ)⁻¹ * algebraMap (𝓞 K) K ζ = 1 :=
      inv_mul_cancel₀ hζ_K_ne
    field_simp at h_mul
    push_cast
    linear_combination h_mul
  -- Apply intCast_quad_ne_zero_of_p_ge_five.
  have hb_ne_int : b ≠ 0 := fun hb => hcaseI (by rw [hb]; ring_nf; exact ⟨0, rfl⟩)
  exact intCast_quad_ne_zero_of_p_ge_five (K := K) hp_odd hp_ne_three hζ_K hb_ne_int h_quad

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`α₀² ≠ 1` from case-I FLT data** for `p ≥ 5` prime.

Combines `caseI_antiRadical_ne_one` and `caseI_antiRadical_ne_neg_one`:
α₀² = 1 in a field ⟺ α₀ = 1 ∨ α₀ = -1. Both are ruled out. -/
theorem caseI_antiRadical_sq_ne_one
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0)) :
    (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab) ^ 2 ≠ 1 := by
  intro h_sq
  -- α₀² = 1 in field ⟺ (α₀ - 1)(α₀ + 1) = 0 ⟺ α₀ = 1 ∨ α₀ = -1.
  have h_factor : (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
        K a b ζ hab - 1) *
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
        K a b ζ hab + 1) = 0 := by
    have : (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
        K a b ζ hab) ^ 2 - 1 = 0 := by rw [h_sq]; ring
    linear_combination this
  rcases mul_eq_zero.mp h_factor with h_one | h_neg_one
  · have := sub_eq_zero.mp h_one
    exact caseI_antiRadical_ne_one (K := K) hp_odd hcaseI hζ hab this
  · have h_eq_neg : (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
        K a b ζ hab) = -1 := by linear_combination h_neg_one
    exact caseI_antiRadical_ne_neg_one (K := K) hp_odd hp_ne_three hcaseI hζ hab h_eq_neg

/-! ## K/K⁺ ramification bound (towards IsUnramified L⁺/K⁺)

For any prime `𝔓` of `𝓞 K` lying over a prime `𝔭` of `𝓞 K⁺`, the
ramification index `e(𝔓 | 𝔭)` is at most `[K : K⁺] = 2`. This bound
is part of the tower argument that establishes `IsUnramified L⁺/K⁺`
under the K-side primary case-I conditions.
-/

/-- **NoZeroSMulDivisors `𝓞 K⁺ → 𝓞 K`** (helper for ramification lemmas). -/
instance noZeroSMulDivisors_OK_Kplus_OK :
    NoZeroSMulDivisors (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) := by
  constructor
  intro c x h
  rw [Algebra.smul_def] at h
  rcases mul_eq_zero.mp h with hc | hx
  · left
    have h_inj : Function.Injective
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) :=
      FaithfulSMul.algebraMap_injective _ _
    have h0 : algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) 0 = 0 := map_zero _
    exact h_inj (hc.trans h0.symm)
  · right; exact hx

/-- **`ramificationIdx(K/K⁺) ≤ 2` at every prime**. -/
theorem ramificationIdx_K_over_Kplus_le_two
    (𝔭 : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    [hpm : 𝔭.IsMaximal]
    (𝔓 : Ideal (𝓞 K)) [h𝔓_prime : 𝔓.IsPrime] [h𝔓_over : 𝔓.LiesOver 𝔭] :
    𝔭.ramificationIdx 𝔓 ≤ 2 := by
  have h_le_finrank : 𝔭.ramificationIdx 𝔓 ≤
      Module.finrank (NumberField.maximalRealSubfield K) K :=
    Ideal.ramificationIdx_le_finrank
      (R := 𝓞 (NumberField.maximalRealSubfield K)) (S := 𝓞 K)
      (K := NumberField.maximalRealSubfield K) (L := K) (p := 𝔭) 𝔓
  have h_eq_two : Module.finrank (NumberField.maximalRealSubfield K) K = 2 :=
    finrank_K_over_Kplus K
  omega

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **`ramificationIdx(L/K⁺) ≤ 2`** for any prime `𝔓_L` of L = antiKummerLift α₀
lying over a maximal prime `𝔭` of K⁺, given the K-side unramified hypothesis.

Combines `ramificationIdx_K_over_Kplus_le_two` with `Ideal.ramificationIdx_algebra_tower'`
for the K⁺ ⊂ K ⊂ L tower. -/
theorem ramificationIdx_L_over_Kplus_le_two
    {α₀ : K} {hα₀ : α₀ ≠ 0}
    (𝔭 : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    [hpm : 𝔭.IsMaximal]
    (𝔭_K : Ideal (𝓞 K))
    [h𝔭_K_prime : 𝔭_K.IsPrime] [h𝔭_K_over : 𝔭_K.LiesOver 𝔭]
    (𝔓_L : Ideal (𝓞
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := p) K α₀ hα₀)))
    [h𝔓_L_prime : 𝔓_L.IsPrime] [h𝔓_L_over : 𝔓_L.LiesOver 𝔭_K]
    (h_LK_unram : 𝔭_K.ramificationIdx 𝔓_L = 1) :
    𝔭.ramificationIdx 𝔓_L ≤ 2 := by
  -- Tower formula K⁺ ⊂ K ⊂ L.
  have h_tower : Ideal.ramificationIdx 𝔭 𝔓_L =
      Ideal.ramificationIdx 𝔭 𝔭_K * Ideal.ramificationIdx 𝔭_K 𝔓_L :=
    Ideal.ramificationIdx_algebra_tower' 𝔭 𝔭_K 𝔓_L
  rw [h_tower, h_LK_unram, mul_one]
  exact ramificationIdx_K_over_Kplus_le_two (K := K) 𝔭 𝔭_K

/-- **`ramificationIdx(L⁺/K⁺)` divides `ramificationIdx(L/K⁺)`** via the
L⁺ ⊂ L tower formula (since L/L⁺ is degree 2, this gives e(L⁺/K⁺) ≤ e(L/K⁺)).

Combined with `ramificationIdx_L_over_Kplus_le_two`, this gives e(L⁺/K⁺) ≤ 2.
The final IsUnramified step combines this with the Galois cyclic divisibility
e(L⁺/K⁺) | p to conclude e(L⁺/K⁺) | gcd(2, p) = 1. -/
theorem ramificationIdx_Lplus_dvd_L_over_Kplus
    {α₀ : K} {hα₀ : α₀ ≠ 0}
    {h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹}
    {h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)}
    {h_irr_g : Irreducible (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
      (p := p) K α₀ hα₀ h_anti)}
    {h_alpha_sq_ne : α₀ ^ 2 ≠ 1}
    (𝔭 : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (𝔓 : Ideal (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
      (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
        (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))))
    (𝔓_L : Ideal (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
      (p := p) K α₀ hα₀)))
    [𝔓.IsPrime] [𝔓_L.IsPrime]
    [𝔓.LiesOver 𝔭] [𝔓_L.LiesOver 𝔓] :
    Ideal.ramificationIdx 𝔭 𝔓 ∣ Ideal.ramificationIdx 𝔭 𝔓_L := by
  -- Tower formula: e(𝔭 | 𝔓_L) = e(𝔭 | 𝔓) · e(𝔓 | 𝔓_L).
  have h_tower := Ideal.ramificationIdx_algebra_tower' 𝔭 𝔓 𝔓_L
  rw [h_tower]
  exact ⟨_, rfl⟩

/-- **`ramificationIdx(L⁺/K⁺) ≤ 2`** at every prime, combining the L/K⁺
upper bound with the L⁺ ⊂ L tower divisibility. -/
theorem ramificationIdx_Lplus_over_Kplus_le_two_of_LK_unram
    {α₀ : K} {hα₀ : α₀ ≠ 0}
    {h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹}
    {h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)}
    {h_irr_g : Irreducible (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
      (p := p) K α₀ hα₀ h_anti)}
    {h_alpha_sq_ne : α₀ ^ 2 ≠ 1}
    (𝔭 : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    [hpm : 𝔭.IsMaximal]
    (𝔓 : Ideal (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
      (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
        (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))))
    [h𝔓_prime : 𝔓.IsPrime] [h𝔓_over : 𝔓.LiesOver 𝔭]
    (𝔓_L : Ideal (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
      (p := p) K α₀ hα₀)))
    [h𝔓_L_prime : 𝔓_L.IsPrime] [h𝔓_L_over : 𝔓_L.LiesOver 𝔓]
    (𝔭_K : Ideal (𝓞 K))
    [h𝔭_K_prime : 𝔭_K.IsPrime] [h𝔭_K_over : 𝔭_K.LiesOver 𝔭]
    [h𝔓_L_over_K : 𝔓_L.LiesOver 𝔭_K]
    (h𝔭_ne_bot : 𝔭 ≠ ⊥)
    (h_LK_unram : 𝔭_K.ramificationIdx 𝔓_L = 1) :
    𝔭.ramificationIdx 𝔓 ≤ 2 := by
  have h_dvd : 𝔭.ramificationIdx 𝔓 ∣ 𝔭.ramificationIdx 𝔓_L :=
    ramificationIdx_Lplus_dvd_L_over_Kplus 𝔭 𝔓 𝔓_L
  have h_le : 𝔭.ramificationIdx 𝔓_L ≤ 2 :=
    ramificationIdx_L_over_Kplus_le_two 𝔭 𝔭_K 𝔓_L h_LK_unram
  -- ramificationIdx is positive for primes-over a nonzero prime.
  haveI : 𝔓_L.LiesOver 𝔭 := Ideal.LiesOver.trans 𝔓_L 𝔓 𝔭
  have h_pos : 0 < 𝔭.ramificationIdx 𝔓_L :=
    Nat.pos_of_ne_zero <| Ideal.IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver _ h𝔭_ne_bot
  exact (Nat.le_of_dvd h_pos h_dvd).trans h_le

/-- **Galois divisibility for L⁺/K⁺**: ramificationIdx divides [L⁺ : K⁺] = p.

For Galois L⁺/K⁺ of order p (cyclic prime degree), `ramificationIdxIn 𝔭 (𝓞 L⁺)`
divides `Nat.card Gal(L⁺/K⁺) = p` via the fundamental identity
`r * (e * f) = Nat.card G`. -/
theorem ramificationIdx_Lplus_over_Kplus_dvd_p
    (hp_odd : p ≠ 2)
    {α₀ : K} {hα₀ : α₀ ≠ 0}
    {h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹}
    {h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)}
    {h_irr_g : Irreducible (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
      (p := p) K α₀ hα₀ h_anti)}
    {h_alpha_sq_ne : α₀ ^ 2 ≠ 1}
    (𝔭 : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    [hpm : 𝔭.IsMaximal] (h𝔭_ne_bot : 𝔭 ≠ ⊥)
    (𝔓 : Ideal (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
      (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
        (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))))
    [h𝔓_prime : 𝔓.IsPrime] [h𝔓_over : 𝔓.LiesOver 𝔭] :
    𝔭.ramificationIdx 𝔓 ∣ p := by
  -- Set up the Galois group.
  haveI hg : IsGalois (NumberField.maximalRealSubfield K)
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
        (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
          (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)) :=
    antiKummerRealSubfield_isGalois (p := p) hp_odd α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne
  -- ramificationIdxIn = ramificationIdx for any prime, in Galois case.
  have h_eqIn : Ideal.ramificationIdxIn 𝔭
      (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
        (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
          (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))) =
      𝔭.ramificationIdx 𝔓 := by
    rw [Ideal.ramificationIdx_eq_ramificationIdx' 𝔭 𝔓 h𝔭_ne_bot]
    exact Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭 𝔓
      Gal((BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
        (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
          (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))/
        (NumberField.maximalRealSubfield K))
  rw [← h_eqIn]
  -- Fundamental identity gives ramificationIdxIn divides Nat.card Gal = p.
  have h_fund := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (p := 𝔭) (B := 𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
        (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
          (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)))
    (G := Gal((BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
        (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
          (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))/
        (NumberField.maximalRealSubfield K)))
  -- Nat.card Gal(L⁺/K⁺) = [L⁺ : K⁺] = p.
  have h_card_eq_p : Nat.card Gal((BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
        (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
          (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))/
        (NumberField.maximalRealSubfield K)) = p := by
    rw [IsGalois.card_aut_eq_finrank]
    exact antiKummerRealSubfield_finrank_eq_p
      (p := p) α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne
  rw [h_card_eq_p] at h_fund
  -- h_fund : r * (e * f) = p, so e | p (extracting e = ramificationIdx from the product).
  set Lplus_OK := 𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
      (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
        (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne)) with hLplus_OK
  refine ⟨(Ideal.primesOver 𝔭 Lplus_OK).ncard *
    Ideal.inertiaDegIn 𝔭 Lplus_OK, ?_⟩
  linarith [h_fund]

/-- **`ramificationIdx(L⁺/K⁺) = 1` at every nonzero prime**, under `L/K` unramified.

Combines:
- `ramificationIdx_Lplus_over_Kplus_le_two_of_LK_unram`: e ≤ 2.
- `ramificationIdx_Lplus_over_Kplus_dvd_p`: e ∣ p.
- For p odd prime ≥ 3, gcd(p, 2) = 1, hence e = 1. -/
theorem ramificationIdx_Lplus_over_Kplus_eq_one
    (hp_odd : p ≠ 2)
    {α₀ : K} {hα₀ : α₀ ≠ 0}
    {h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹}
    {h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)}
    {h_irr_g : Irreducible (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
      (p := p) K α₀ hα₀ h_anti)}
    {h_alpha_sq_ne : α₀ ^ 2 ≠ 1}
    (𝔭 : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    [hpm : 𝔭.IsMaximal] (h𝔭_ne_bot : 𝔭 ≠ ⊥)
    (𝔓 : Ideal (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
      (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
        (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))))
    [h𝔓_prime : 𝔓.IsPrime] [h𝔓_over : 𝔓.LiesOver 𝔭]
    (𝔓_L : Ideal (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
      (p := p) K α₀ hα₀)))
    [h𝔓_L_prime : 𝔓_L.IsPrime] [h𝔓_L_over : 𝔓_L.LiesOver 𝔓]
    (𝔭_K : Ideal (𝓞 K))
    [h𝔭_K_prime : 𝔭_K.IsPrime] [h𝔭_K_over : 𝔭_K.LiesOver 𝔭]
    [h𝔓_L_over_K : 𝔓_L.LiesOver 𝔭_K]
    (h_LK_unram : 𝔭_K.ramificationIdx 𝔓_L = 1) :
    𝔭.ramificationIdx 𝔓 = 1 := by
  have h_le : 𝔭.ramificationIdx 𝔓 ≤ 2 :=
    ramificationIdx_Lplus_over_Kplus_le_two_of_LK_unram 𝔭 𝔓 𝔓_L 𝔭_K h𝔭_ne_bot h_LK_unram
  have h_dvd : 𝔭.ramificationIdx 𝔓 ∣ p :=
    ramificationIdx_Lplus_over_Kplus_dvd_p hp_odd 𝔭 h𝔭_ne_bot 𝔓
  -- p odd prime ≥ 3, so divisors of p are {1, p}. Combined with ≤ 2, must be 1.
  have hp_prime : p.Prime := Fact.out
  have hp_ge_3 : 3 ≤ p := by
    rcases hp_prime.two_le.lt_or_eq with h | h
    · omega
    · exfalso; exact hp_odd h.symm
  -- e ∣ p prime ⟹ e ∈ {1, p}. Combined with e ≤ 2 and p ≥ 3, e = 1.
  rcases (Nat.dvd_prime hp_prime).mp h_dvd with he1 | hep
  · exact he1
  · omega

/-- **Global IsUnramified L⁺/K⁺**, under `IsUnramified (𝓞 K) (𝓞 L)`.

Wires `ramificationIdx_Lplus_over_Kplus_eq_one` (per-prime fact) into
`antiKummerRealSubfield_isUnramified_of_ram_bound` to produce the full
IsUnramified instance. The K-side unramified hypothesis comes from
primarity of α₀ via `antiKummerLift_isUnramified_K_of_primary`. -/
theorem antiKummerRealSubfield_isUnramified_from_K_unramified
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K))
    (h_irr_g : Irreducible (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
      (p := p) K α₀ hα₀ h_anti))
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1)
    (h_LK_unram : Algebra.Unramified (𝓞 K)
      (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := p) K α₀ hα₀))) :
    Algebra.Unramified (𝓞 (NumberField.maximalRealSubfield K))
      (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerRealSubfield
        (p := p) (K := K) (α₀ := α₀) (hα₀ := hα₀) (h_irr := h_irr)
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
          (p := p) K α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne))) := by
  apply antiKummerRealSubfield_isUnramified_of_ram_bound
    (p := p) hp_odd α₀ hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne
  intro 𝔭 𝔓 hp_prime h𝔓_prime hp_bot h𝔓_over
  haveI := hp_prime
  haveI := h𝔓_prime
  haveI := h𝔓_over
  -- 𝔭 prime + nonzero in 𝓞 K⁺ ⟹ maximal (since 𝓞 K⁺ Dedekind dim 1).
  haveI hpm : 𝔭.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hp_bot hp_prime
  -- Lift 𝔓 ⊂ 𝓞 L⁺ to 𝔓_L ⊂ 𝓞 L over 𝔓.
  obtain ⟨𝔓_L, _, h𝔓_L_prime, h𝔓_L_over_𝔓⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
      (p := p) K α₀ hα₀)) 𝔓 (⊥ : Ideal (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
      (p := p) K α₀ hα₀))) (by simp)
  haveI : 𝔓_L.IsPrime := h𝔓_L_prime
  haveI : 𝔓_L.LiesOver 𝔓 := ⟨h𝔓_L_over_𝔓.symm⟩
  -- 𝔓_L lies over 𝔭_K = 𝔓_L ∩ 𝓞 K.
  set 𝔭_K : Ideal (𝓞 K) := 𝔓_L.under (𝓞 K) with h𝔭_K_def
  haveI h𝔭_K_prime : 𝔭_K.IsPrime := Ideal.IsPrime.under (𝓞 K) 𝔓_L
  haveI h𝔓_L_over_K : 𝔓_L.LiesOver 𝔭_K := ⟨rfl⟩
  -- 𝔓_L lies over 𝔭 (transitively).
  haveI h𝔓_L_over_𝔭 : 𝔓_L.LiesOver 𝔭 := Ideal.LiesOver.trans 𝔓_L 𝔓 𝔭
  -- Hence 𝔭_K lies over 𝔭 (by tower_bot).
  haveI h𝔭_K_over : 𝔭_K.LiesOver 𝔭 := Ideal.LiesOver.tower_bot (𝔓 := 𝔓_L) (P := 𝔭_K) (p := 𝔭)
  -- 𝔭_K ≠ ⊥: from 𝔭_K LiesOver 𝔭 with 𝔭 ≠ ⊥ in injective tower.
  have h𝔭_K_ne_bot : 𝔭_K ≠ ⊥ := by
    intro h
    apply hp_bot
    have h_under : 𝔭 = 𝔭_K.under (𝓞 (NumberField.maximalRealSubfield K)) :=
      h𝔭_K_over.over
    rw [h_under, h, Ideal.under_bot]
  -- Apply per-prime ramificationIdx = 1.
  haveI h_unram_at : Algebra.IsUnramifiedAt (𝓞 K) 𝔓_L :=
    (Algebra.unramified_iff_forall (R := 𝓞 K)
      (A := 𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := p) K α₀ hα₀))).mp h_LK_unram ⟨𝔓_L, h𝔓_L_prime⟩
  have h𝔓_L_ne_bot : 𝔓_L ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭_K_ne_bot 𝔓_L
  have h_LK_unram_at : 𝔭_K.ramificationIdx 𝔓_L = 1 := by
    have h := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K) (S := 𝓞
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := p) K α₀ hα₀)) (p := 𝔓_L) h𝔓_L_ne_bot
    rwa [← h𝔭_K_def] at h
  exact ramificationIdx_Lplus_over_Kplus_eq_one hp_odd 𝔭 hp_bot 𝔓 𝔓_L 𝔭_K h_LK_unram_at

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **`X^p - C α₀` irreducible ⟺ `α₀` is not a p-th power in K**, for `p` odd prime.

Specializes mathlib's `Polynomial.X_pow_sub_C_irreducible_iff_of_prime_pow` to n = 1
(so we're at `X^p - C α₀` directly, not `X^(p^n) - C α₀`). -/
theorem X_pow_sub_C_irreducible_iff_not_pth_power
    (hp_odd : p ≠ 2) (α₀ : K) :
    Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K) ↔
      ∀ β : K, β ^ p ≠ α₀ := by
  have hp_prime : p.Prime := Fact.out
  have h_iff := X_pow_sub_C_irreducible_iff_of_prime_pow
    (p := p) (n := 1) hp_prime hp_odd (a := α₀) (by decide : 1 ≠ 0)
  simpa using h_iff

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **Stage2 conclusion witness when α₀ is a p-th power**.

If the σ-anti radical α₀ = (a + ζb)/σ(a + ζb) is a p-th power in K, then
Stage2KummerRatioK's conclusion holds directly with k = 0 and the same β. -/
theorem stage2_conclusion_of_antiRadical_is_pth_power
    (hp_odd : p ≠ 2)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0))
    {β : K} (hβ_pow : β ^ p =
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) :
    ∃ k : ℕ, k < p ∧ ∃ β' : K, β' ≠ 0 ∧
      (algebraMap (𝓞 K) K
        (ζ ^ k * ((a : 𝓞 K) + ζ * (b : 𝓞 K)))) /
      (algebraMap (𝓞 K) K
        (NumberField.IsCMField.ringOfIntegersComplexConj K
          (ζ ^ k * ((a : 𝓞 K) + ζ * (b : 𝓞 K))))) = β' ^ p := by
  have hp_prime : p.Prime := Fact.out
  have hα_ne : BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab ≠ 0 :=
    caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab
  refine ⟨0, hp_prime.pos, β, ?_, ?_⟩
  · -- β ≠ 0: from β^p = α₀ ≠ 0.
    intro hβ0
    apply hα_ne
    rw [← hβ_pow, hβ0]
    exact zero_pow hp_prime.ne_zero
  · -- The ratio at k = 0 equals α₀ = β^p.
    -- ζ^0 = 1, so numerator = algMap (a + ζb)_𝓞K = (a + ζb)_K.
    -- Denominator = algMap σ_𝓞K (a + ζb) = σ_K (a + ζb)_K = denom of antiRadical.
    -- Hence ratio = antiRadical = β^p.
    simp only [pow_zero, one_mul]
    have h_conj_eq : algebraMap (𝓞 K) K
        (NumberField.IsCMField.ringOfIntegersComplexConj K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) =
        NumberField.IsCMField.complexConj K
          (algebraMap (𝓞 K) K ((a : 𝓞 K) + ζ * (b : 𝓞 K))) :=
      NumberField.IsCMField.coe_ringOfIntegersComplexConj (K := K)
        ((a : 𝓞 K) + ζ * (b : 𝓞 K))
    rw [h_conj_eq]
    -- Goal: (algMap (a + ζb)) / σ(algMap (a + ζb)) = β ^ p.
    -- The LHS is precisely antiRadical K a b ζ hab.
    show BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical
      K a b ζ hab = β ^ p
    exact hβ_pow.symm

/-- **σ-anti α₀ with α₀² ≠ 1 implies α₀ ∉ K⁺**.

If α₀ ∈ K⁺ then σ(α₀) = α₀ (K⁺ is σ-fixed). Combined with σ(α₀) = α₀⁻¹ (σ-anti),
α₀ = α₀⁻¹, hence α₀² = 1. Contrapositive: α₀² ≠ 1 ⟹ α₀ ∉ K⁺. -/
theorem antiRadical_not_mem_Kplus_of_sq_ne_one
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    α₀ ∉ NumberField.maximalRealSubfield K := by
  intro h_mem
  apply h_alpha_sq_ne
  have h_fixed : NumberField.IsCMField.complexConj K α₀ = α₀ := by
    rw [NumberField.IsCMField.complexConj_eq_self_iff]
    exact h_mem
  rw [h_anti] at h_fixed
  -- h_fixed : α₀⁻¹ = α₀. So α₀ * α₀⁻¹ = α₀^2, and α₀ * α₀⁻¹ = 1.
  have : α₀ * α₀⁻¹ = 1 := mul_inv_cancel₀ hα₀
  rw [h_fixed] at this
  rw [pow_two]
  exact this

/-- **σ-anti α₀⁻¹ with α₀² ≠ 1 implies α₀⁻¹ ∉ K⁺**, by symmetry with `α₀`. -/
theorem antiRadical_inv_not_mem_Kplus_of_sq_ne_one
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    α₀⁻¹ ∉ NumberField.maximalRealSubfield K := by
  intro h_mem
  apply antiRadical_not_mem_Kplus_of_sq_ne_one (K := K) α₀ hα₀ h_anti h_alpha_sq_ne
  -- α₀⁻¹ ∈ K⁺ ⟹ α₀ ∈ K⁺ (K⁺ is a subfield, closed under inverse).
  have h_inv : (α₀⁻¹)⁻¹ ∈ NumberField.maximalRealSubfield K :=
    Subfield.inv_mem _ h_mem
  rwa [inv_inv] at h_inv

omit [NumberField K] [NumberField.IsCMField K] in
/-- **`α₀ ≠ α₀⁻¹` for σ-anti α₀ with α₀² ≠ 1**. -/
theorem antiRadical_ne_inv_of_sq_ne_one
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    α₀ ≠ α₀⁻¹ := by
  intro h_eq
  apply h_alpha_sq_ne
  have : α₀ * α₀⁻¹ = 1 := mul_inv_cancel₀ hα₀
  rw [← h_eq] at this
  rw [pow_two]
  exact this

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **`X^p - C α₀⁻¹` is irreducible** when `X^p - C α₀` is, for nonzero α₀.

If β^p = α₀⁻¹, then (β⁻¹)^p = α₀, contradicting irreducibility of X^p - C α₀.
Uses `X_pow_sub_C_irreducible_iff_not_pth_power`. -/
theorem X_pow_sub_C_inv_irreducible
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)) :
    Irreducible (Polynomial.X ^ p - Polynomial.C α₀⁻¹ : Polynomial K) := by
  rw [X_pow_sub_C_irreducible_iff_not_pth_power hp_odd]
  intro β hβ_pow
  rw [X_pow_sub_C_irreducible_iff_not_pth_power hp_odd] at h_irr
  apply h_irr β⁻¹
  rw [inv_pow, hβ_pow, inv_inv]

omit [NumberField K] [IsCyclotomicExtension {p} ℚ K] [NumberField.IsCMField K] in
/-- **`X^p - α₀` and `X^p - α₀⁻¹` are distinct polynomials** when α₀² ≠ 1. -/
theorem X_pow_sub_C_ne_X_pow_sub_C_inv_of_sq_ne
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1) :
    (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K) ≠
      Polynomial.X ^ p - Polynomial.C α₀⁻¹ := by
  intro h_eq
  apply antiRadical_ne_inv_of_sq_ne_one (K := K) α₀ hα₀ h_alpha_sq_ne
  -- Compare coefficient at X^0: both polynomials have constant term -α₀ and -α₀⁻¹.
  have h_coeff : (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K).coeff 0 =
      (Polynomial.X ^ p - Polynomial.C α₀⁻¹ : Polynomial K).coeff 0 := by
    rw [h_eq]
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
    Polynomial.coeff_C_zero, zero_sub, neg_inj] at h_coeff
  rw [if_neg (Ne.symm hp_pos.ne'), zero_sub, zero_sub, neg_inj] at h_coeff
  exact h_coeff

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`antiKummerKplusPoly` has natDegree `2p`** — useful for polynomial-UFD reasoning. -/
theorem antiKummerKplusPoly_natDegree
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
      (p := p) K α₀ hα₀ h_anti).natDegree = 2 * p := by
  have h_monic := BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly_monic
    (p := p) K α₀ hα₀ h_anti
  -- antiKummerKplusPoly maps to (X^p - α₀)(X^p - α₀⁻¹), which has natDegree 2p.
  -- And map preserves natDegree for monic polys.
  have h_map_eq := BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly_map_eq_factor_product
    (p := p) K α₀ hα₀ h_anti
  have h_natDeg_map :
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
        (p := p) K α₀ hα₀ h_anti).natDegree =
      ((BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
        (p := p) K α₀ hα₀ h_anti).map
          (algebraMap (NumberField.maximalRealSubfield K) K)).natDegree :=
    (Polynomial.natDegree_map_eq_of_injective
      (RingHom.injective (algebraMap (NumberField.maximalRealSubfield K) K))
      _).symm
  rw [h_natDeg_map, h_map_eq]
  -- (X^p - α₀)(X^p - α₀⁻¹).natDegree = p + p = 2p.
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  rw [Polynomial.natDegree_mul, Polynomial.natDegree_X_pow_sub_C,
      Polynomial.natDegree_X_pow_sub_C]
  · ring
  · exact Polynomial.X_pow_sub_C_ne_zero hp_pos α₀
  · exact Polynomial.X_pow_sub_C_ne_zero hp_pos α₀⁻¹

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`antiKummerKplusPoly` has degree `2p`** (as a `WithBot ℕ`) — corollary of monic + natDegree. -/
theorem antiKummerKplusPoly_degree
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
      (p := p) K α₀ hα₀ h_anti).degree = 2 * p := by
  have h_monic := BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly_monic
    (p := p) K α₀ hα₀ h_anti
  rw [Polynomial.degree_eq_natDegree h_monic.ne_zero]
  exact_mod_cast antiKummerKplusPoly_natDegree (K := K) α₀ hα₀ h_anti

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`antiKummerKplusPoly` is nonzero** — immediate from monic. -/
theorem antiKummerKplusPoly_ne_zero
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
      (p := p) K α₀ hα₀ h_anti ≠ 0 :=
  (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly_monic
    (p := p) K α₀ hα₀ h_anti).ne_zero

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **The constant coefficient of `antiKummerKplusPoly mapped to K[X]` divided by some
factor gives -α₀ or -α₀⁻¹** — extracted as a structural helper for the irreducibility
argument. The constant coefficient of the K[X]-map equals `((-α₀) * (-α₀⁻¹) + 1) = 0`?
No, let's actually compute: `(X^p - α₀)(X^p - α₀⁻¹) = X^{2p} - (α₀+α₀⁻¹) X^p + α₀ · α₀⁻¹ = X^{2p} - (α₀+α₀⁻¹) X^p + 1`.
So constant coefficient is `1`. -/
theorem antiKummerKplusPoly_K_map_coeff_zero
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    ((BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
      (p := p) K α₀ hα₀ h_anti).map
        (algebraMap (NumberField.maximalRealSubfield K) K)).coeff 0 = 1 := by
  rw [BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly_map_eq_factor_product]
  -- (X^p - α₀)(X^p - α₀⁻¹).coeff 0 = (-α₀) * (-α₀⁻¹) = α₀ * α₀⁻¹ = 1.
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  rw [Polynomial.mul_coeff_zero]
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      if_neg (Ne.symm hp_pos.ne'), Polynomial.coeff_C_zero, zero_sub]
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      if_neg (Ne.symm hp_pos.ne'), Polynomial.coeff_C_zero, zero_sub]
  rw [neg_mul_neg, mul_inv_cancel₀ hα₀]

omit [NumberField K] [NumberField.IsCMField K] in
/-- **Polynomial.map preserves natDegree** under injective algebraMap. Convenience wrapper. -/
theorem natDegree_map_OK_eq
    (f : Polynomial (NumberField.maximalRealSubfield K)) :
    (f.map (algebraMap (NumberField.maximalRealSubfield K) K)).natDegree = f.natDegree :=
  Polynomial.natDegree_map_eq_of_injective
    (RingHom.injective (algebraMap (NumberField.maximalRealSubfield K) K)) f

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`antiKummerKplusPoly ≠ 1`** — used in `Monic.irreducible_iff_natDegree`. -/
theorem antiKummerKplusPoly_ne_one
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
      (p := p) K α₀ hα₀ h_anti ≠ 1 := by
  intro h
  have hp_pos : 0 < p := hp.out.pos
  have h_natDeg := antiKummerKplusPoly_natDegree (p := p) (K := K) α₀ hα₀ h_anti
  rw [h, Polynomial.natDegree_one] at h_natDeg
  omega

/-- **σ-invariance of K⁺-polynomials mapped to K[X]**: if `f ∈ K⁺[X]`, then
`σ_poly (f.map (algMap K⁺ K)) = f.map (algMap K⁺ K)` where `σ_poly` denotes
`Polynomial.map (complexConj K).toRingHom`. -/
theorem K_plus_poly_map_sigma_invariant
    (f : Polynomial (NumberField.maximalRealSubfield K)) :
    (f.map (algebraMap (NumberField.maximalRealSubfield K) K)).map
      (NumberField.IsCMField.complexConj K).toAlgHom.toRingHom =
    f.map (algebraMap (NumberField.maximalRealSubfield K) K) := by
  rw [Polynomial.map_map]
  congr 1
  ext x
  -- (complexConj K).toRingHom ∘ algMap K⁺ K = algMap K⁺ K (σ fixes K⁺).
  simp [NumberField.IsCMField.complexConj]

omit hp [IsCyclotomicExtension {p} ℚ K] in
/-- **`σ_poly(X^p - C α₀) = X^p - C α₀⁻¹`** for σ-anti α₀. -/
theorem sigma_poly_X_pow_sub_C_alpha
    (α₀ : K) (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹) :
    (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K).map
      (NumberField.IsCMField.complexConj K).toAlgHom.toRingHom =
    Polynomial.X ^ p - Polynomial.C α₀⁻¹ := by
  rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
  rw [show (NumberField.IsCMField.complexConj K).toAlgHom.toRingHom α₀ =
    NumberField.IsCMField.complexConj K α₀ from rfl, h_anti]

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **No K⁺-polynomial maps to `X^p - C α₀` in K[X]** when α₀² ≠ 1.

Combines `K_plus_poly_map_sigma_invariant` (K⁺-polys are σ-invariant) with
`sigma_poly_X_pow_sub_C_alpha` (σ_poly swaps X^p - α₀ ↔ X^p - α₀⁻¹). -/
theorem no_K_plus_poly_maps_to_X_pow_sub_C_alpha
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1)
    (f : Polynomial (NumberField.maximalRealSubfield K))
    (hf : f.map (algebraMap (NumberField.maximalRealSubfield K) K) =
      Polynomial.X ^ p - Polynomial.C α₀) :
    False := by
  have h_inv := K_plus_poly_map_sigma_invariant (K := K) f
  -- h_inv : (f.map (algMap K⁺ K)).map (complexConj K).toAlgHom.toRingHom = f.map (algMap K⁺ K)
  rw [hf] at h_inv
  -- h_inv : σ_poly(X^p - α₀) = X^p - α₀.
  rw [sigma_poly_X_pow_sub_C_alpha (K := K) α₀ h_anti] at h_inv
  -- h_inv : X^p - C α₀⁻¹ = X^p - C α₀.
  -- Extract α₀⁻¹ = α₀ from constant coefficient.
  have h_coeff : (Polynomial.X ^ p - Polynomial.C α₀⁻¹ : Polynomial K).coeff 0 =
      (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K).coeff 0 := by rw [h_inv]
  have hp_pos : 0 < p := (Fact.out : p.Prime).pos
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      if_neg (Ne.symm hp_pos.ne'), Polynomial.coeff_C_zero, zero_sub] at h_coeff
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow,
      if_neg (Ne.symm hp_pos.ne'), Polynomial.coeff_C_zero, zero_sub] at h_coeff
  -- h_coeff : -α₀⁻¹ = -α₀. So α₀⁻¹ = α₀, hence α₀² = 1.
  apply h_alpha_sq_ne
  have h_eq' : α₀ = α₀⁻¹ := (neg_inj.mp h_coeff).symm
  have h_mul : α₀ * α₀⁻¹ = 1 := mul_inv_cancel₀ hα₀
  rw [← h_eq'] at h_mul
  rw [pow_two]; exact h_mul

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **No K⁺-polynomial maps to `X^p - C α₀⁻¹` in K[X]** — symmetric to the above. -/
theorem no_K_plus_poly_maps_to_X_pow_sub_C_alpha_inv
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1)
    (f : Polynomial (NumberField.maximalRealSubfield K))
    (hf : f.map (algebraMap (NumberField.maximalRealSubfield K) K) =
      Polynomial.X ^ p - Polynomial.C α₀⁻¹) :
    False := by
  -- Apply no_K_plus_poly_maps_to_X_pow_sub_C_alpha with α₀⁻¹ as the new α₀.
  -- Need h_anti' : complexConj K α₀⁻¹ = (α₀⁻¹)⁻¹ = α₀.
  have h_anti' : NumberField.IsCMField.complexConj K α₀⁻¹ = (α₀⁻¹)⁻¹ := by
    rw [map_inv₀, h_anti]
  have h_alpha_sq_ne' : (α₀⁻¹) ^ 2 ≠ 1 := by
    intro h_sq
    apply h_alpha_sq_ne
    have : α₀ ^ 2 * α₀⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hα₀, one_pow]
    rw [h_sq, mul_one] at this
    exact this
  have hα₀_inv_ne : α₀⁻¹ ≠ 0 := inv_ne_zero hα₀
  exact no_K_plus_poly_maps_to_X_pow_sub_C_alpha (K := K) α₀⁻¹ hα₀_inv_ne h_anti' h_alpha_sq_ne' f hf

omit [IsCyclotomicExtension {p} ℚ K] in
/-- **`antiKummerKplusPoly` is irreducible** in K⁺[X] — main result.

Strategy: any factorization f * g = antiKummerKplusPoly with both monic gives via
the K[X]-map (X^p - α₀)(X^p - α₀⁻¹) = f.map * g.map. Since X^p - α₀ is irreducible
in the UFD K[X], it's prime, hence divides f.map or g.map (Euclid). Case analysis
combined with σ-invariance argument (`no_K_plus_poly_maps_to_X_pow_sub_C_alpha`)
shows one of f, g must be a unit, giving natDegree = 0. -/
theorem antiKummerKplusPoly_irreducible
    (hp_odd : p ≠ 2)
    (α₀ : K) (hα₀ : α₀ ≠ 0)
    (h_anti : NumberField.IsCMField.complexConj K α₀ = α₀⁻¹)
    (h_alpha_sq_ne : α₀ ^ 2 ≠ 1)
    (h_X_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K)) :
    Irreducible
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly
        (p := p) K α₀ hα₀ h_anti) := by
  have h_monic := BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly_monic
    (p := p) K α₀ hα₀ h_anti
  rw [h_monic.irreducible_iff_natDegree]
  refine ⟨antiKummerKplusPoly_ne_one (K := K) α₀ hα₀ h_anti, ?_⟩
  intro f g hf_monic hg_monic h_eq
  have h_K_prod : f.map (algebraMap (NumberField.maximalRealSubfield K) K) *
      g.map (algebraMap (NumberField.maximalRealSubfield K) K) =
      (Polynomial.X ^ p - Polynomial.C α₀) *
      (Polynomial.X ^ p - Polynomial.C α₀⁻¹) := by
    rw [← Polynomial.map_mul, h_eq,
      BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerKplusPoly_map_eq_factor_product]
  have h_X_prime : Prime (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K) :=
    h_X_irr.prime
  have hX_ne : (Polynomial.X ^ p - Polynomial.C α₀ : Polynomial K) ≠ 0 :=
    h_X_irr.ne_zero
  have h_X_inv_irr : Irreducible (Polynomial.X ^ p - Polynomial.C α₀⁻¹ : Polynomial K) :=
    X_pow_sub_C_inv_irreducible (K := K) hp_odd α₀ hα₀ h_X_irr
  have h_X_dvd : (Polynomial.X ^ p - Polynomial.C α₀) ∣
      f.map (algebraMap _ K) * g.map (algebraMap _ K) := by
    rw [h_K_prod]; exact dvd_mul_right _ _
  rcases h_X_prime.dvd_or_dvd h_X_dvd with h_dvd_f | h_dvd_g
  · obtain ⟨fq, hfq⟩ := h_dvd_f
    have h_cancel : fq * g.map (algebraMap _ K) =
        Polynomial.X ^ p - Polynomial.C α₀⁻¹ := by
      have key : (Polynomial.X ^ p - Polynomial.C α₀) * (fq * g.map (algebraMap _ K)) =
          (Polynomial.X ^ p - Polynomial.C α₀) * (Polynomial.X ^ p - Polynomial.C α₀⁻¹) := by
        have := h_K_prod
        calc
          (Polynomial.X ^ p - Polynomial.C α₀) * (fq * g.map (algebraMap _ K))
              = ((Polynomial.X ^ p - Polynomial.C α₀) * fq) * g.map (algebraMap _ K) := by ring
            _ = f.map (algebraMap _ K) * g.map (algebraMap _ K) := by rw [← hfq]
            _ = _ := this
      exact mul_left_cancel₀ hX_ne key
    rcases h_X_inv_irr.isUnit_or_isUnit h_cancel.symm with hu_fq | hu_g
    · have h_fq_natDeg : fq.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu_fq
      have h_fq_C : fq = Polynomial.C (fq.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero h_fq_natDeg
      have hg_monic_K : (g.map (algebraMap _ K)).Monic := hg_monic.map _
      have h_lead : fq.coeff 0 = 1 := by
        have hh : (fq * g.map (algebraMap _ K)).leadingCoeff =
            (Polynomial.X ^ p - Polynomial.C α₀⁻¹ : Polynomial K).leadingCoeff := by
          rw [h_cancel]
        rw [Polynomial.leadingCoeff_mul, hg_monic_K, mul_one] at hh
        rw [h_fq_C, Polynomial.leadingCoeff_C] at hh
        rw [Polynomial.Monic.leadingCoeff
          (Polynomial.monic_X_pow_sub_C α₀⁻¹ (Fact.out : p.Prime).ne_zero)] at hh
        exact hh
      have h_fq_eq_one : fq = 1 := by rw [h_fq_C, h_lead]; rfl
      rw [h_fq_eq_one, mul_one] at hfq
      exfalso
      exact no_K_plus_poly_maps_to_X_pow_sub_C_alpha (K := K)
        α₀ hα₀ h_anti h_alpha_sq_ne f hfq
    · right
      have h_natDeg : (g.map (algebraMap _ K)).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit hu_g
      rw [natDegree_map_OK_eq] at h_natDeg
      exact h_natDeg
  · obtain ⟨gq, hgq⟩ := h_dvd_g
    have h_cancel : gq * f.map (algebraMap _ K) =
        Polynomial.X ^ p - Polynomial.C α₀⁻¹ := by
      have key : (Polynomial.X ^ p - Polynomial.C α₀) * (gq * f.map (algebraMap _ K)) =
          (Polynomial.X ^ p - Polynomial.C α₀) * (Polynomial.X ^ p - Polynomial.C α₀⁻¹) := by
        have := h_K_prod
        calc
          (Polynomial.X ^ p - Polynomial.C α₀) * (gq * f.map (algebraMap _ K))
              = f.map (algebraMap _ K) * ((Polynomial.X ^ p - Polynomial.C α₀) * gq) := by ring
            _ = f.map (algebraMap _ K) * g.map (algebraMap _ K) := by rw [← hgq]
            _ = _ := this
      exact mul_left_cancel₀ hX_ne key
    rcases h_X_inv_irr.isUnit_or_isUnit h_cancel.symm with hu_gq | hu_f
    · have h_gq_natDeg : gq.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu_gq
      have h_gq_C : gq = Polynomial.C (gq.coeff 0) :=
        Polynomial.eq_C_of_natDegree_eq_zero h_gq_natDeg
      have hf_monic_K : (f.map (algebraMap _ K)).Monic := hf_monic.map _
      have h_lead : gq.coeff 0 = 1 := by
        have hh : (gq * f.map (algebraMap _ K)).leadingCoeff =
            (Polynomial.X ^ p - Polynomial.C α₀⁻¹ : Polynomial K).leadingCoeff := by
          rw [h_cancel]
        rw [Polynomial.leadingCoeff_mul, hf_monic_K, mul_one] at hh
        rw [h_gq_C, Polynomial.leadingCoeff_C] at hh
        rw [Polynomial.Monic.leadingCoeff
          (Polynomial.monic_X_pow_sub_C α₀⁻¹ (Fact.out : p.Prime).ne_zero)] at hh
        exact hh
      have h_gq_eq_one : gq = 1 := by rw [h_gq_C, h_lead]; rfl
      rw [h_gq_eq_one, mul_one] at hgq
      exfalso
      exact no_K_plus_poly_maps_to_X_pow_sub_C_alpha (K := K)
        α₀ hα₀ h_anti h_alpha_sq_ne g hgq
    · left
      have h_natDeg : (f.map (algebraMap _ K)).natDegree = 0 :=
        Polynomial.natDegree_eq_zero_of_isUnit hu_f
      rw [natDegree_map_OK_eq] at h_natDeg
      exact h_natDeg

/-- **Case-I → σ-anti Kummer extension package**: bundles α₀ ≠ 0, σ-anti, α₀² ≠ 1,
and h_irr_g (the just-shipped antiKummerKplusPoly irreducibility) into the
`SigmaAntiKummerExtension` package via `antiKummerSigmaTildePkg`.

Takes h_irr (X^p - α₀ irreducible) as hypothesis since that's the substantive
remaining content beyond the building blocks. -/
noncomputable def caseI_sigma_anti_pkg
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0))
    (h_irr : Irreducible (Polynomial.X ^ p -
      Polynomial.C
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        : Polynomial K)) :
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.SigmaAntiKummerExtension
      (p := p) K
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
      (caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab)
      h_irr := by
  -- Construct h_anti, h_alpha_sq_ne, h_irr_g, then apply antiKummerSigmaTildePkg.
  have h_denom_ne :=
    caseI_antiRadical_denom_K_ne_zero (K := K) hp_odd hcaseI hζ (a := a) (b := b)
  have h_anti :
      NumberField.IsCMField.complexConj K
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab) =
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)⁻¹ :=
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical_sigma_inv
      K a b ζ hab h_denom_ne
  have h_alpha_sq_ne :=
    caseI_antiRadical_sq_ne_one (K := K) hp_odd hp_ne_three hcaseI hζ hab
  have hα₀ := caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab
  have h_irr_g :=
    antiKummerKplusPoly_irreducible (K := K) hp_odd
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
      hα₀ h_anti h_alpha_sq_ne h_irr
  exact BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerSigmaTildePkg
    (p := p) K
    (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
    hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne

/-- **Case-I FLT data → AntiKummerRealSubfieldH94Inputs**: bundles the full structural
inputs needed by `ak_caseI_false_under_VC_and_inputs`.

Takes h_irr (X^p - α₀ irreducible) and h_LK_unram (IsUnramified L/K from primarity)
as the substantive remaining hypotheses. All other inputs derive from shipped lemmas. -/
noncomputable def caseI_AK_inputs_of_h_irr_and_h_LK_unram
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0))
    (h_irr : Irreducible (Polynomial.X ^ p -
      Polynomial.C
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        : Polynomial K))
    (h_LK_unram : Algebra.Unramified (𝓞 K)
      (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := p) K
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        (caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab)))) :
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.AntiKummerRealSubfieldH94Inputs
      (p := p) (K := K)
      (caseI_sigma_anti_pkg (K := K) hp_odd hp_ne_three hcaseI hζ hab h_irr) := by
  -- Derive the four shipped fields + IsUnramified from h_LK_unram.
  have h_denom_ne :=
    caseI_antiRadical_denom_K_ne_zero (K := K) hp_odd hcaseI hζ (a := a) (b := b)
  have h_anti :=
    BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical_sigma_inv
      K a b ζ hab h_denom_ne
  have h_alpha_sq_ne :=
    caseI_antiRadical_sq_ne_one (K := K) hp_odd hp_ne_three hcaseI hζ hab
  have hα₀ := caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab
  have h_irr_g :=
    antiKummerKplusPoly_irreducible (K := K) hp_odd
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
      hα₀ h_anti h_alpha_sq_ne h_irr
  -- IsUnramified L⁺/K⁺ from L/K unramified.
  have h_isUnramified :=
    antiKummerRealSubfield_isUnramified_from_K_unramified (K := K) hp_odd
      (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
      hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne h_LK_unram
  -- Apply mkAntiKummerRealSubfieldH94Inputs.
  exact mkAntiKummerRealSubfieldH94Inputs (K := K) hp_odd
    (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
    hα₀ h_anti h_irr h_irr_g h_alpha_sq_ne h_isUnramified

/-- **Case-I FLT data + VC + h_irr + h_LK_unram ⟹ False** — the FULL AK chain
discharge composition. Combines `caseI_AK_inputs_of_h_irr_and_h_LK_unram` with
`ak_caseI_false_under_VC_and_inputs`. -/
theorem caseI_FLT_false_of_h_irr_h_LK_unram_VC
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    (h_VC : ¬ (p : ℕ) ∣ hPlus K)
    {a b c : ℤ} (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
    {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
    (hab : ¬ (a = 0 ∧ b = 0))
    (h_irr : Irreducible (Polynomial.X ^ p -
      Polynomial.C
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        : Polynomial K))
    (h_LK_unram : Algebra.Unramified (𝓞 K)
      (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
        (p := p) K
        (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
        (caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab)))) :
    False :=
  BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.ak_caseI_false_under_VC_and_inputs
    (p := p) (K := K) hp_odd
    (caseI_sigma_anti_pkg (K := K) hp_odd hp_ne_three hcaseI hζ hab h_irr)
    (caseI_AK_inputs_of_h_irr_and_h_LK_unram
      (K := K) hp_odd hp_ne_three hcaseI hζ hab h_irr h_LK_unram)
    h_VC

/-- **Stage2 placeholder discharge under VC + universal h_LK_unram**: the full
case-by-case discharge of `Stage2KummerRatioK` for p ≥ 5 prime under VC, with the
universal "L/K unramified at each case-I α₀" as the residual hypothesis.

Case split: α₀ either is or isn't a p-th power.
- Is: directly satisfy Stage2 conclusion via `stage2_conclusion_of_antiRadical_is_pth_power`.
- Isn't: X^p - α₀ irreducible (via `X_pow_sub_C_irreducible_iff_not_pth_power`),
  apply `caseI_FLT_false_of_h_irr_h_LK_unram_VC` to derive False, use `False.elim`. -/
theorem flt37_stage2_via_AK_chain
    (hp_odd : p ≠ 2) (hp_ne_three : p ≠ 3)
    (h_VC : ¬ (p : ℕ) ∣ hPlus K)
    (h_LK_unram_per_case : ∀ {a b c : ℤ}
      (heq : a ^ p + b ^ p = c ^ p)
      (hcaseI : ¬ (p : ℤ) ∣ a * b * c)
      {ζ : 𝓞 K} (hζ : IsPrimitiveRoot ζ p)
      (hab : ¬ (a = 0 ∧ b = 0)),
      Algebra.Unramified (𝓞 K)
        (𝓞 (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiKummerLift
          (p := p) K
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
          (caseI_antiRadical_ne_zero (K := K) hp_odd hcaseI hζ hab)))) :
    FLT37.LehmerVandiver.CaseI.Stage2KummerRatioK p K := by
  intro a b c _hgcd hcaseI heq ζ hζ I _hI_nz _hI_pow
  -- a, b nonzero from case-I (p ∤ abc).
  have hab : ¬ (a = 0 ∧ b = 0) := by
    intro ⟨ha, _hb⟩
    apply hcaseI
    rw [ha]; ring_nf; exact ⟨0, rfl⟩
  -- Case split on α₀ being a p-th power.
  by_cases h_pow :
      ∃ β : K, β ^ p =
        BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab
  · -- α₀ is a p-th power → directly satisfy Stage2 conclusion.
    obtain ⟨β, hβ⟩ := h_pow
    exact stage2_conclusion_of_antiRadical_is_pth_power
      (K := K) hp_odd hcaseI hζ hab hβ
  · -- α₀ NOT a p-th power → X^p - α₀ irreducible.
    have h_irr : Irreducible (Polynomial.X ^ p -
        Polynomial.C
          (BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiKummer.antiRadical K a b ζ hab)
          : Polynomial K) := by
      rw [X_pow_sub_C_irreducible_iff_not_pth_power (K := K) hp_odd]
      intro β hβ
      exact h_pow ⟨β, hβ⟩
    -- Apply AK chain.
    exfalso
    exact caseI_FLT_false_of_h_irr_h_LK_unram_VC
      (K := K) hp_odd hp_ne_three h_VC hcaseI hζ hab h_irr
      (h_LK_unram_per_case heq hcaseI hζ hab)

/-! ## Irreducibility of antiKummerKplusPoly: outline for next session

The remaining piece (antiKummerKplusPoly irreducibility) admits two natural paths:

**Path A (UFD argument):** Use `Polynomial.Monic.irreducible_iff_natDegree` + UFD-based
enumeration of divisors. f * g = antiKummerKplusPoly with both monic ⟹ K[X]-images give
f.map * g.map = (X^p - α₀)(X^p - α₀⁻¹). Both K-factors are monic irreducible distinct
(shipped: `X_pow_sub_C_inv_irreducible`, `X_pow_sub_C_ne_X_pow_sub_C_inv_of_sq_ne`).
By unique factorization in K[X], f.map ∈ {1, X^p - α₀, X^p - α₀⁻¹, product}. For
deg f.map = p (the only nontrivial case from the natDegree analysis), f.map = X^p - α₀
or X^p - α₀⁻¹. But then -α₀ or -α₀⁻¹ ∈ image(algMap K⁺ K), forcing α₀ or α₀⁻¹ ∈ K⁺.
Contradicts `antiRadical_not_mem_Kplus_of_sq_ne_one` / `antiRadical_inv_not_mem_Kplus_of_sq_ne_one`.

**Path B (minpoly argument):** Construct a root ρ ∈ L of `X^p - α₀_L` (exists in splitting
field). Show K⁺(ρ) = L (primitive element argument via Galois subfield enumeration).
Then minpoly(ρ over K⁺) has degree [L:K⁺] = 2p. Show antiKummerKplusPoly.aeval ρ = 0
(both `X^p - α₀_L` factor and itself contain ρ as root). Apply `minpoly.unique` to
conclude antiKummerKplusPoly = minpoly(ρ over K⁺), which is always irreducible.

Path B is cleaner mathematically; Path A is more direct but needs UFD divisor enumeration
which is heavy in Lean. Either path is a focused next-session effort.
-/

end BernoulliRegular.FLT37.LehmerVandiver.CaseI

end
