module

public import BernoulliRegular.FLT37.Primary

/-!
# Complex conjugation preserves primarity (ticket FLT37b2b)

For a CM cyclotomic field `K = ℚ(ζ_p)`, complex conjugation `σ` sends `ζ` to
`ζ^{p-1}`. Hence `σ(ζ - 1) = ζ^{p-1} - 1 = -ζ^{p-1}(ζ - 1)`, and `σ(ζ - 1)`
is associated to `ζ - 1`. Divisibility by `(ζ - 1)^k` is therefore preserved
by `σ`, and primarity is `σ`-invariant.

The arithmetic input
`(ζ - 1)^{2p} ∣ α - σ(α)` (`zetaSubOne_pow_dvd_sub_complexConj`) is the entry
point for showing `[(α)] = [(σ(α))]` in `Cl(K)`, the Galois descent step
toward Vandiver Lemma 1.

## References

* Washington, *Introduction to Cyclotomic Fields*, §6.4.
* `BernoulliRegular.TotallyRealSubfield.Conjugation`
  (`complexConj_apply_zeta`).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular

namespace FLT37

section ConjSetup

variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The unit `-ζ^{p-1} ∈ (𝓞 K)ˣ` realising the associated relation
`σ(ζ - 1) = (-ζ^{p-1}) (ζ - 1)`. -/
noncomputable def zetaSubOneConjUnit : (𝓞 K)ˣ :=
  (-1 : (𝓞 K)ˣ) *
    ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^ (p - 1)

omit [NumberField K] in
/-- Helper: `((-1 : (𝓞 K)ˣ) : 𝓞 K) = -1`. -/
private theorem coe_neg_one_unit : ((-1 : (𝓞 K)ˣ) : 𝓞 K) = -1 := rfl

/-- Helper: the coercion of the chosen `ζ`-unit to `𝓞 K` is
`(zeta_spec p ℚ K).toInteger`. -/
private theorem coe_unit'_eq_toInteger :
    (((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit : 𝓞 K) =
      (zeta_spec p ℚ K).toInteger :=
  IsUnit.unit_spec _

/-- Complex conjugation multiplies `ζ - 1` by `-ζ^{p-1}`. -/
theorem complexConj_zetaSubOne_eq [IsCMField K] :
    ringOfIntegersComplexConj K (zetaSubOne p K) =
      ((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) * zetaSubOne p K := by
  have hζ_pow : (zeta_spec p ℚ K).toInteger ^ p = 1 := zeta_toInteger_pow_eq_one p K
  have hconj_zeta : (ringOfIntegersComplexConj K (zeta_spec p ℚ K).toInteger : 𝓞 K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) :=
    complexConj_apply_zeta (p := p) (K := K)
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel hp.1.one_lt.le
  have key : ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) *
      (zeta_spec p ℚ K).toInteger = 1 := by
    rw [← pow_succ, hp1]; exact hζ_pow
  -- Compute LHS: σ(ζ - 1) = ζ^(p-1) - 1
  have lhs_eq : ringOfIntegersComplexConj K (zetaSubOne p K) =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) - 1 := by
    change ringOfIntegersComplexConj K ((zeta_spec p ℚ K).toInteger - 1) = _
    rw [map_sub, map_one, hconj_zeta]
  -- Compute RHS: (-ζ^(p-1)) · (ζ - 1) = ζ^(p-1) - 1 (using ζ · ζ^(p-1) = 1)
  have rhs_eq : ((zetaSubOneConjUnit p K : (𝓞 K)ˣ) : 𝓞 K) * zetaSubOne p K =
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) - 1 := by
    change (((-1 : (𝓞 K)ˣ) *
        ((zeta_spec p ℚ K).toInteger_isPrimitiveRoot.isUnit hp.1.ne_zero).unit ^ (p - 1) :
          (𝓞 K)ˣ) : 𝓞 K) *
        ((zeta_spec p ℚ K).toInteger - 1) = _
    rw [Units.val_mul, Units.val_pow_eq_pow_val, coe_neg_one_unit, coe_unit'_eq_toInteger]
    linear_combination -key
  rw [lhs_eq, rhs_eq]

/-- `σ(ζ - 1)` is associated to `ζ - 1` in `𝓞 K`. -/
theorem associated_complexConj_zetaSubOne [IsCMField K] :
    Associated (zetaSubOne p K) (ringOfIntegersComplexConj K (zetaSubOne p K)) :=
  ⟨zetaSubOneConjUnit p K, by rw [complexConj_zetaSubOne_eq]; ring⟩

/-- Powered form: `σ((ζ - 1)^k) = (-ζ^{p-1})^k · (ζ - 1)^k` in `𝓞 K`. -/
theorem complexConj_zetaSubOne_pow_eq [IsCMField K] (k : ℕ) :
    ringOfIntegersComplexConj K (zetaSubOne p K ^ k) =
      ((zetaSubOneConjUnit p K ^ k : (𝓞 K)ˣ) : 𝓞 K) * zetaSubOne p K ^ k := by
  rw [map_pow, complexConj_zetaSubOne_eq, mul_pow, Units.val_pow_eq_pow_val]

/-- `σ((ζ - 1)^k)` is associated to `(ζ - 1)^k` for any `k`. -/
theorem associated_complexConj_zetaSubOne_pow [IsCMField K] (k : ℕ) :
    Associated (zetaSubOne p K ^ k)
      (ringOfIntegersComplexConj K (zetaSubOne p K ^ k)) := by
  rw [map_pow]
  exact (associated_complexConj_zetaSubOne p K).pow_pow

/-- Divisibility by `(ζ - 1)^k` is preserved by complex conjugation. -/
theorem zetaSubOne_pow_dvd_complexConj_iff [IsCMField K] (k : ℕ) (x : 𝓞 K) :
    zetaSubOne p K ^ k ∣ ringOfIntegersComplexConj K x ↔
      zetaSubOne p K ^ k ∣ x := by
  have hxx (y : 𝓞 K) : ringOfIntegersComplexConj K (ringOfIntegersComplexConj K y) = y := by
    apply RingOfIntegers.ext
    simp
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h_apply : ringOfIntegersComplexConj K (zetaSubOne p K ^ k) ∣
        ringOfIntegersComplexConj K (ringOfIntegersComplexConj K x) :=
      map_dvd (ringOfIntegersComplexConj K).toRingEquiv.toRingHom h
    rw [hxx] at h_apply
    exact (associated_complexConj_zetaSubOne_pow p K k).dvd.trans h_apply
  · have h_apply : ringOfIntegersComplexConj K (zetaSubOne p K ^ k) ∣
        ringOfIntegersComplexConj K x :=
      map_dvd (ringOfIntegersComplexConj K).toRingEquiv.toRingHom h
    exact (associated_complexConj_zetaSubOne_pow p K k).dvd.trans h_apply

end ConjSetup

/-- Complex conjugation preserves primarity: if `α` is primary, so is `σ(α)`,
with the same integer witness `a`. -/
theorem IsPrimary.complexConj
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} (hα : IsPrimary p α) :
    IsPrimary p (K := K) (ringOfIntegersComplexConj K α) := by
  obtain ⟨a, ha⟩ := hα
  refine ⟨a, ?_⟩
  have ha_int : ringOfIntegersComplexConj K ((a : ℤ) : 𝓞 K) = ((a : ℤ) : 𝓞 K) := by
    change ringOfIntegersComplexConj K ((algebraMap ℤ (𝓞 K)) a) = (algebraMap ℤ (𝓞 K)) a
    rw [IsScalarTower.algebraMap_apply ℤ (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K),
      AlgEquiv.commutes]
  have hsub : ringOfIntegersComplexConj K α - ((a : ℤ) : 𝓞 K) =
      ringOfIntegersComplexConj K (α - ((a : ℤ) : 𝓞 K)) := by
    rw [map_sub, ha_int]
  rw [hsub, zetaSubOne_pow_dvd_complexConj_iff]
  exact ha

/-- IsPrimary is invariant under complex conjugation (biconditional). -/
@[simp]
theorem IsPrimary.complexConj_iff
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} :
    IsPrimary p (K := K) (ringOfIntegersComplexConj K α) ↔ IsPrimary p α := by
  refine ⟨fun h => ?_, IsPrimary.complexConj⟩
  have h2 : IsPrimary p (K := K)
      (ringOfIntegersComplexConj K (ringOfIntegersComplexConj K α)) :=
    h.complexConj
  have heq : ringOfIntegersComplexConj K (ringOfIntegersComplexConj K α) = α := by
    apply RingOfIntegers.ext
    simp
  rw [heq] at h2
  exact h2

/-- For a primary element `α`, `(ζ - 1)^{2p}` divides `α - σ(α)`. -/
theorem zetaSubOne_pow_dvd_sub_complexConj
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} (hα : IsPrimary p α) :
    zetaSubOne p K ^ (2 * p) ∣ α - ringOfIntegersComplexConj K α := by
  obtain ⟨a, ha⟩ := hα
  have ha_int : ringOfIntegersComplexConj K ((a : ℤ) : 𝓞 K) = ((a : ℤ) : 𝓞 K) := by
    change ringOfIntegersComplexConj K ((algebraMap ℤ (𝓞 K)) a) = (algebraMap ℤ (𝓞 K)) a
    rw [IsScalarTower.algebraMap_apply ℤ (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K),
      AlgEquiv.commutes]
  have ha_conj : zetaSubOne p K ^ (2 * p) ∣
      ringOfIntegersComplexConj K α - ((a : ℤ) : 𝓞 K) := by
    have hsub : ringOfIntegersComplexConj K α - ((a : ℤ) : 𝓞 K) =
        ringOfIntegersComplexConj K (α - ((a : ℤ) : 𝓞 K)) := by
      rw [map_sub, ha_int]
    rw [hsub, zetaSubOne_pow_dvd_complexConj_iff]
    exact ha
  have heq : α - ringOfIntegersComplexConj K α =
      (α - ((a : ℤ) : 𝓞 K)) - (ringOfIntegersComplexConj K α - ((a : ℤ) : 𝓞 K)) := by
    ring
  rw [heq]
  exact dvd_sub ha ha_conj

/-- For a primary element `α` and any natural number `k`, `(ζ - 1)^{2p}`
divides `α^k - σ(α^k)`. Direct corollary of `IsPrimary.pow` and
`zetaSubOne_pow_dvd_sub_complexConj`. -/
theorem zetaSubOne_pow_dvd_pow_sub_complexConj_pow
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} (hα : IsPrimary p α) (k : ℕ) :
    zetaSubOne p K ^ (2 * p) ∣ α ^ k - ringOfIntegersComplexConj K (α ^ k) :=
  zetaSubOne_pow_dvd_sub_complexConj (hα.pow k)

/-- Primarity is preserved by `α ↦ α · σα`: if `α` is primary, so is its
norm-product (with witness `a²`). -/
theorem IsPrimary.mul_complexConj
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} (hα : IsPrimary p α) :
    IsPrimary p (α * ringOfIntegersComplexConj K α) :=
  hα.mul hα.complexConj

/-- Primarity is preserved by `α ↦ α + σα` (the trace-like sum). -/
theorem IsPrimary.add_complexConj
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} (hα : IsPrimary p α) :
    IsPrimary p (α + ringOfIntegersComplexConj K α) :=
  hα.add hα.complexConj

/-- Primarity is preserved by `α ↦ α - σα`: the σ-skew difference. -/
theorem IsPrimary.sub_complexConj
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} (hα : IsPrimary p α) :
    IsPrimary p (α - ringOfIntegersComplexConj K α) :=
  hα.sub hα.complexConj

/-- IsHyperprimary is invariant under complex conjugation. The witness for
`σ α` is `σ β`, and `(ζ-1)^{p+1} | α - β^p` transports through `σ` (which
preserves the ideal `(ζ-1)`-power up to a unit). -/
theorem IsHyperprimary.complexConj
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} (hα : IsHyperprimary p α) :
    IsHyperprimary p (K := K) (ringOfIntegersComplexConj K α) := by
  obtain ⟨β, hβ⟩ := hα
  refine ⟨ringOfIntegersComplexConj K β, ?_⟩
  -- σ(α) - σ(β)^p = σ(α - β^p)
  rw [show ringOfIntegersComplexConj K α -
      (ringOfIntegersComplexConj K β) ^ p =
      ringOfIntegersComplexConj K (α - β ^ p) from by
    rw [map_sub, map_pow]]
  rw [zetaSubOne_pow_dvd_complexConj_iff]
  exact hβ

/-- IsHyperprimary is invariant under complex conjugation (biconditional). -/
@[simp]
theorem IsHyperprimary.complexConj_iff
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} :
    IsHyperprimary p (K := K) (ringOfIntegersComplexConj K α) ↔
      IsHyperprimary p α := by
  refine ⟨fun h => ?_, IsHyperprimary.complexConj⟩
  have h2 := h.complexConj
  have heq : ringOfIntegersComplexConj K (ringOfIntegersComplexConj K α) = α := by
    apply RingOfIntegers.ext
    simp
  rw [heq] at h2
  exact h2

/-- The norm-form `α · σ α` is hyperprimary when α is. -/
theorem IsHyperprimary.mul_complexConj
    {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {α : 𝓞 K} (hα : IsHyperprimary p α) :
    IsHyperprimary p (α * ringOfIntegersComplexConj K α) :=
  IsHyperprimary.mul (p := p) (K := K) hα hα.complexConj

end FLT37

end BernoulliRegular

end
