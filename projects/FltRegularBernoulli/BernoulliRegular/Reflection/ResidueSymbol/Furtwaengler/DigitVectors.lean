module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.TraceCoefficientValuation
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.MinimalWeight


/-!
# Digit vectors and the digit denominator (REF-18c2c4-L2c3d-3)

This file packages the shared digit-vector notation used by the Route-D
proof of the digit-sum Stickelberger congruence (`L2c3d-1..7`,
`L2c3e-1..5`):

* `digitVec ℓ f`: vectors `(m_0, …, m_{f-1})` with `m_i ∈ [0, ℓ)`;
* `digitWeight m = ∑ m_i`, `digitValue m = ∑ m_i · ℓ^i`;
* `digitDen ℓ f := ∏_{i < f} ∏_{r < ℓ} r!`, the common denominator;
* `digitCoeff m := digitDen / ∏ m_i!`, the integral multinomial coefficient.

The identity `digitCoeff m · ∏ m_i! = digitDen` is the multinomial
denominator-cleared form originally planned for L2c3d-4. That digit-bounded
expansion turned out to be mathematically incorrect; the correct
expansion is the Dwork splitting expansion in `DworkAssembly.lean`
(`gaussSumIntRec_dwork_expansion`), and `digitCoeff` / `digitDen` here
remain useful as multinomial-arithmetic helpers consumed by other
files.

This file proves the **L2c3d-3 deliverables**:

* `digitDen_not_mem_Q` — the digit denominator is a `Q`-unit;
* `mem_Q_pow_of_digitDen_mul_mem` — cancel the digit denominator from a
  `Q`-power membership.

Both follow from the factorial-not-in-`Q` lemmas already proved in
`TraceCoefficientValuation.lean` plus the primality of `Q`.
-/

@[expose] public section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

/-- Digit vector of base `ℓ` and length `f`: a function `Fin f → ℕ` with
each entry strictly less than `ℓ`. -/
def digitVec (ℓ f : ℕ) : Type :=
  { m : Fin f → ℕ // ∀ i, m i < ℓ }

namespace digitVec

variable {ℓ f : ℕ}

/-- Underlying `Fin f → ℕ` function. -/
def toFun (m : digitVec ℓ f) : Fin f → ℕ := m.1

/-- All entries are strictly less than `ℓ`. -/
theorem entry_lt (m : digitVec ℓ f) (i : Fin f) : m.1 i < ℓ := m.2 i

/-- Equivalence between `digitVec ℓ f` and `Fin f → Fin ℓ`. -/
def equivFinFun {ℓ f : ℕ} : digitVec ℓ f ≃ (Fin f → Fin ℓ) where
  toFun m := fun i => ⟨m.1 i, m.2 i⟩
  invFun g := ⟨fun i => (g i).val, fun i => (g i).isLt⟩
  left_inv m := by
    apply Subtype.ext
    funext i
    rfl
  right_inv g := by
    funext i
    apply Fin.ext
    rfl

/-- `Fintype` instance for digit vectors. -/
instance fintype (ℓ f : ℕ) : Fintype (digitVec ℓ f) :=
  Fintype.ofEquiv _ digitVec.equivFinFun.symm

/-- Decidable equality on `digitVec ℓ f`. -/
instance decidableEq (ℓ f : ℕ) : DecidableEq (digitVec ℓ f) :=
  fun m m' => decidable_of_iff (m.1 = m'.1) Subtype.ext_iff.symm

end digitVec

/-- Total weight of a digit vector: sum of digits. -/
def digitWeight {ℓ f : ℕ} (m : digitVec ℓ f) : ℕ :=
  ∑ i : Fin f, m.1 i

/-- Numerical value of a digit vector: `∑ m_i · ℓ^i`. -/
def digitValue {ℓ f : ℕ} (m : digitVec ℓ f) : ℕ :=
  ∑ i : Fin f, m.1 i * ℓ ^ (i : ℕ)

/-- Total weight of an unbounded multi-index `m : Fin f → ℕ`. -/
def multiIndexWeight {f : ℕ} (m : Fin f → ℕ) : ℕ :=
  ∑ i : Fin f, m i

/-- Numerical value of an unbounded multi-index `m : Fin f → ℕ`,
relative to base `ℓ`. -/
def multiIndexValue {f : ℕ} (ℓ : ℕ) (m : Fin f → ℕ) : ℕ :=
  ∑ i : Fin f, m i * ℓ ^ (i : ℕ)

/-- Finset of unbounded multi-indices `m : Fin f → ℕ` of total weight at
most `N`. Used by the Dwork-splitting expansion (REF-18c2c4-L2c3d-4b). -/
def multiIndexLE (f N : ℕ) : Finset (Fin f → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : Fin f => Finset.range (N + 1))).filter
    (fun m => multiIndexWeight m ≤ N)

@[simp]
theorem mem_multiIndexLE {f N : ℕ} (m : Fin f → ℕ) :
    m ∈ multiIndexLE f N ↔ (∀ i, m i ≤ N) ∧ multiIndexWeight m ≤ N := by
  classical
  unfold multiIndexLE
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => Nat.le_of_lt_succ (h1 i), h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i => Nat.lt_succ_of_le (h1 i), h2⟩

/-- Each entry of a member of `multiIndexLE f N` is bounded by the total
weight bound. (Bookkeeping helper.) -/
theorem multiIndexLE_entry_le {f N : ℕ} (m : Fin f → ℕ)
    (hm : m ∈ multiIndexLE f N) (i : Fin f) : m i ≤ N :=
  ((mem_multiIndexLE m).mp hm).1 i

/-- Finset of digit vectors of length `f` and base `ℓ` with total weight
at most `N`. -/
def digitVecsLE (ℓ f N : ℕ) : Finset (digitVec ℓ f) := by
  classical
  exact Finset.univ.filter (fun m => digitWeight m ≤ N)

@[simp]
theorem mem_digitVecsLE {ℓ f N : ℕ} (m : digitVec ℓ f) :
    m ∈ digitVecsLE ℓ f N ↔ digitWeight m ≤ N := by
  classical
  unfold digitVecsLE
  simp

/-- Common denominator for the digit-vector multinomial coefficients:
`digitDen ℓ f = ∏_{i < f} ∏_{r < ℓ} r! = (∏_{r<ℓ} r!)^f`. -/
def digitDen (ℓ f : ℕ) : ℕ :=
  ∏ _i : Fin f, ∏ r ∈ Finset.range ℓ, Nat.factorial r

/-- Integral multinomial coefficient associated to a digit vector:
`digitCoeff m = digitDen / ∏ m_i!`. The division is exact because each
`m_i < ℓ` ensures `m_i! ∣ ∏_{r<ℓ} r!`. -/
def digitCoeff {ℓ f : ℕ} (m : digitVec ℓ f) : ℕ :=
  digitDen ℓ f / ∏ i : Fin f, Nat.factorial (m.1 i)

/-- For `r < ℓ`, the factorial `r!` divides the single-block denominator
`∏_{s < ℓ} s!`. -/
theorem factorial_dvd_block {ℓ r : ℕ} (hr : r < ℓ) :
    Nat.factorial r ∣ ∏ s ∈ Finset.range ℓ, Nat.factorial s := by
  refine Finset.dvd_prod_of_mem _ ?_
  exact Finset.mem_range.mpr hr

/-- For each `i`, the factorial `m_i!` divides `digitDen ℓ f`. -/
theorem factorial_entry_dvd_digitDen {ℓ f : ℕ} (m : digitVec ℓ f) (i : Fin f) :
    Nat.factorial (m.1 i) ∣ digitDen ℓ f := by
  unfold digitDen
  refine (factorial_dvd_block (m.entry_lt i)).trans ?_
  exact Finset.dvd_prod_of_mem
    (fun _ : Fin f => ∏ r ∈ Finset.range ℓ, Nat.factorial r) (Finset.mem_univ i)

/-- The product of the entry factorials divides the digit denominator.
This is the integrality witness for `digitCoeff`. -/
theorem factorial_prod_dvd_digitDen {ℓ f : ℕ} (m : digitVec ℓ f) :
    (∏ i : Fin f, Nat.factorial (m.1 i)) ∣ digitDen ℓ f := by
  unfold digitDen
  refine Finset.prod_dvd_prod_of_dvd _ _ ?_
  intro i _
  exact factorial_dvd_block (m.entry_lt i)

/-- **Denominator-cleared multinomial identity** for digit vectors:
`digitCoeff m * ∏ m_i! = digitDen ℓ f`. -/
theorem digitCoeff_mul_prod_factorial_eq {ℓ f : ℕ} (m : digitVec ℓ f) :
    digitCoeff m * (∏ i : Fin f, Nat.factorial (m.1 i)) = digitDen ℓ f := by
  unfold digitCoeff
  exact Nat.div_mul_cancel (factorial_prod_dvd_digitDen m)

/-- Extension of a digit vector to `ℕ → ℕ` by zero outside `[0, f)`. -/
def digitVec.extend {ℓ f : ℕ} (m : digitVec ℓ f) : ℕ → ℕ :=
  fun i => if h : i < f then m.1 ⟨i, h⟩ else 0

@[simp]
theorem digitVec.extend_of_lt {ℓ f : ℕ} (m : digitVec ℓ f) {i : ℕ} (hi : i < f) :
    m.extend i = m.1 ⟨i, hi⟩ := by
  unfold digitVec.extend
  rw [dif_pos hi]

theorem digitVec.extend_of_not_lt {ℓ f : ℕ} (m : digitVec ℓ f) {i : ℕ} (hi : ¬ i < f) :
    m.extend i = 0 := by
  unfold digitVec.extend
  rw [dif_neg hi]

/-- The digit weight equals the `Finset.range`-form sum of the extended
sequence. -/
theorem digitWeight_eq_sum_range {ℓ f : ℕ} (m : digitVec ℓ f) :
    digitWeight m = ∑ i ∈ Finset.range f, m.extend i := by
  unfold digitWeight
  rw [← Fin.sum_univ_eq_sum_range (fun i => m.extend i) f]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (digitVec.extend_of_lt m i.is_lt).symm

/-- The digit value equals the `Finset.range`-form sum of the extended
sequence weighted by powers of `ℓ`. -/
theorem digitValue_eq_sum_range {ℓ f : ℕ} (m : digitVec ℓ f) :
    digitValue m = ∑ i ∈ Finset.range f, m.extend i * ℓ ^ i := by
  unfold digitValue
  rw [← Fin.sum_univ_eq_sum_range (fun i => m.extend i * ℓ ^ i) f]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [digitVec.extend_of_lt m i.is_lt]

/-- **Minimal-weight bound for digit vectors.** The base-`ℓ` digit sum of
`digitValue m` is at most the digit weight of `m`. This is the digit-vector
specialisation of `decomp_weight_ge_digitSum` (L1b). -/
theorem digitSum_digitValue_le_digitWeight {ℓ f : ℕ} (hℓ : 2 ≤ ℓ) (m : digitVec ℓ f) :
    digitSum ℓ (digitValue m) ≤ digitWeight m := by
  rw [digitValue_eq_sum_range, digitWeight_eq_sum_range]
  exact decomp_weight_ge_digitSum hℓ f m.extend

/-- For a bounded digit vector, the base-`ℓ` digit sum of its value is
exactly its digit weight. -/
theorem digitSum_digitValue_eq_digitWeight {ℓ f : ℕ} (hℓ : 1 < ℓ) (m : digitVec ℓ f) :
    digitSum ℓ (digitValue m) = digitWeight m := by
  rw [digitValue_eq_sum_range, digitWeight_eq_sum_range]
  exact digitSum_eq_sum_of_all_lt hℓ f m.extend fun i hi => by
    rw [m.extend_of_lt hi]
    exact m.entry_lt _

/-- Residue orbit used in the arbitrary-degree digit/carry calculation:
`r_i = A * ℓ^i mod p`. -/
def residueOrbit (ℓ p A : ℕ) (i : ℕ) : ℕ :=
  (A * ℓ ^ i) % p

/-- Carry digits for the arbitrary-degree Stickelberger digit formula. The
`j`-th digit is the carry in
`ℓ * r_{f-1-j} = p * q_j + r_{f-j}`. -/
def dworkCarryDigitVec {ℓ p : ℕ} (hℓ : 0 < ℓ) (hp : 0 < p)
    (A f : ℕ) : digitVec ℓ f :=
  ⟨fun j : Fin f => (ℓ * residueOrbit ℓ p A (f - 1 - (j : ℕ))) / p, fun j => by
    have hr : residueOrbit ℓ p A (f - 1 - (j : ℕ)) < p := Nat.mod_lt _ hp
    have hmul : ℓ * residueOrbit ℓ p A (f - 1 - (j : ℕ)) < ℓ * p :=
      Nat.mul_lt_mul_of_pos_left hr hℓ
    exact (Nat.div_lt_iff_lt_mul hp).2 hmul⟩

@[simp]
theorem dworkCarryDigitVec_apply {ℓ p : ℕ} (hℓ : 0 < ℓ) (hp : 0 < p)
    (A f : ℕ) (j : Fin f) :
    (dworkCarryDigitVec hℓ hp A f).1 j =
      (ℓ * residueOrbit ℓ p A (f - 1 - (j : ℕ))) / p :=
  rfl

/-- Multiplying a residue by `ℓ` advances the residue orbit. -/
theorem residueOrbit_mul_ell_mod_eq_next {ℓ p A i : ℕ} :
    (ℓ * residueOrbit ℓ p A i) % p = residueOrbit ℓ p A (i + 1) := by
  unfold residueOrbit
  change ℓ * ((A * ℓ ^ i) % p) ≡ A * ℓ ^ (i + 1) [MOD p]
  have h1 : (A * ℓ ^ i) % p ≡ A * ℓ ^ i [MOD p] := Nat.mod_modEq _ _
  have h2 : ℓ * ((A * ℓ ^ i) % p) ≡ ℓ * (A * ℓ ^ i) [MOD p] :=
    Nat.ModEq.mul_left ℓ h1
  have h3 : ℓ * (A * ℓ ^ i) = A * ℓ ^ (i + 1) := by
    rw [pow_succ]
    ring
  rwa [h3] at h2

/-- Carry recurrence for the residue orbit:
`p * q_i + r_{i+1} = ℓ * r_i`. -/
theorem carryDigit_mul_p_add_next {ℓ p A i : ℕ} :
    p * ((ℓ * residueOrbit ℓ p A i) / p) + residueOrbit ℓ p A (i + 1) =
      ℓ * residueOrbit ℓ p A i := by
  have hmod := residueOrbit_mul_ell_mod_eq_next (ℓ := ℓ) (p := p) (A := A) (i := i)
  have h := Nat.mod_add_div (ℓ * residueOrbit ℓ p A i) p
  rw [hmod] at h
  omega

/-- If `ℓ ^ f ≡ 1 mod p`, then the residue orbit has period `f`. -/
theorem residueOrbit_period_of_pow_modEq_one {ℓ p A f : ℕ}
    (hpow : ℓ ^ f ≡ 1 [MOD p]) :
    residueOrbit ℓ p A f = residueOrbit ℓ p A 0 := by
  unfold residueOrbit
  change A * ℓ ^ f ≡ A * ℓ ^ 0 [MOD p]
  simpa using Nat.ModEq.mul_left A hpow

/-- The cyclic shift `∑ r_{f-j}` has the same sum as `∑ r_j`, provided
the orbit has period `f`. -/
theorem sum_residueOrbit_shift_eq (ℓ p A : ℕ) {f : ℕ}
    (hper : residueOrbit ℓ p A f = residueOrbit ℓ p A 0) :
    (∑ j ∈ Finset.range f, residueOrbit ℓ p A (f - j)) =
      ∑ j ∈ Finset.range f, residueOrbit ℓ p A j := by
  cases f with
  | zero =>
      rw [Finset.range_zero, Finset.sum_empty, Finset.sum_empty]
  | succ n =>
      rw [Finset.sum_range_succ']
      have hrev0 :
          (∑ k ∈ Finset.range n, residueOrbit ℓ p A (n + 1 - (k + 1))) =
            ∑ k ∈ Finset.range n, residueOrbit ℓ p A (n - 1 - k + 1) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        have hklt : k < n := Finset.mem_range.mp hk
        congr 1
        omega
      have hrev1 :
          (∑ k ∈ Finset.range n, residueOrbit ℓ p A (n - 1 - k + 1)) =
            ∑ k ∈ Finset.range n, residueOrbit ℓ p A (k + 1) :=
        Finset.sum_range_reflect (fun i => residueOrbit ℓ p A (i + 1)) n
      rw [hrev0, hrev1]
      rw [show residueOrbit ℓ p A (n + 1 - 0) = residueOrbit ℓ p A 0 by
        simpa using hper]
      rw [Finset.sum_range_succ']

/-- Reflection of the reversed residue orbit. -/
theorem sum_residueOrbit_reflect_eq (ℓ p A f : ℕ) :
    (∑ j ∈ Finset.range f, residueOrbit ℓ p A (f - 1 - j)) =
      ∑ j ∈ Finset.range f, residueOrbit ℓ p A j :=
  Finset.sum_range_reflect (fun i => residueOrbit ℓ p A i) f

/-- Weighted carry recurrence summed over one period. -/
theorem p_mul_dworkCarryDigitWeight_add_shift_eq
    {ℓ p A f : ℕ} (hℓ : 0 < ℓ) (hp : 0 < p) :
    p * digitWeight (dworkCarryDigitVec hℓ hp A f) +
        (∑ j ∈ Finset.range f, residueOrbit ℓ p A (f - j)) =
      ℓ * (∑ j ∈ Finset.range f, residueOrbit ℓ p A j) := by
  rw [digitWeight_eq_sum_range]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  have hterm :
      (∑ x ∈ Finset.range f,
          (p * (dworkCarryDigitVec hℓ hp A f).extend x + residueOrbit ℓ p A (f - x))) =
        ∑ x ∈ Finset.range f, ℓ * residueOrbit ℓ p A (f - 1 - x) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxlt : x < f := Finset.mem_range.mp hx
    rw [(dworkCarryDigitVec hℓ hp A f).extend_of_lt hxlt]
    have hsucc : f - 1 - x + 1 = f - x := by omega
    simpa [hsucc] using
      (carryDigit_mul_p_add_next (ℓ := ℓ) (p := p) (A := A) (i := f - 1 - x))
  rw [hterm]
  rw [← Finset.mul_sum]
  rw [sum_residueOrbit_reflect_eq]

/-- The carry digit weight is the Frobenius-orbit residue sum after the
normalizing factor `p / (ℓ - 1)`. This is the core arbitrary-degree
digit/carry identity; it has no split or order-one hypothesis. -/
theorem p_mul_dworkCarryDigitWeight_eq_ell_sub_one_mul_residueOrbitSum
    {ℓ p A f : ℕ} (hℓ : 0 < ℓ) (hp : 0 < p)
    (hper : residueOrbit ℓ p A f = residueOrbit ℓ p A 0) :
    p * digitWeight (dworkCarryDigitVec hℓ hp A f) =
      (ℓ - 1) * (∑ j ∈ Finset.range f, residueOrbit ℓ p A j) := by
  let T := ∑ j ∈ Finset.range f, residueOrbit ℓ p A j
  have h :=
    p_mul_dworkCarryDigitWeight_add_shift_eq (ℓ := ℓ) (p := p) (A := A) (f := f) hℓ hp
  rw [sum_residueOrbit_shift_eq ℓ p A hper] at h
  change p * digitWeight (dworkCarryDigitVec hℓ hp A f) = (ℓ - 1) * T
  change p * digitWeight (dworkCarryDigitVec hℓ hp A f) + T = ℓ * T at h
  have hmul : ℓ * T = (ℓ - 1) * T + T := by
    calc
      ℓ * T = ((ℓ - 1) + 1) * T := by
        have : ℓ - 1 + 1 = ℓ := by omega
        rw [this]
      _ = (ℓ - 1) * T + 1 * T := by rw [Nat.add_mul]
      _ = (ℓ - 1) * T + T := by rw [one_mul]
  rw [hmul] at h
  omega

/-- Recursive value formula for the carry digit vector. -/
theorem digitValue_dworkCarryDigitVec_succ {ℓ p A f : ℕ}
    (hℓ : 0 < ℓ) (hp : 0 < p) :
    digitValue (dworkCarryDigitVec hℓ hp A (f + 1)) =
      (ℓ * residueOrbit ℓ p A f) / p +
        ℓ * digitValue (dworkCarryDigitVec hℓ hp A f) := by
  unfold digitValue
  rw [Fin.sum_univ_succ]
  simp only [dworkCarryDigitVec_apply, Fin.val_zero, tsub_zero, Fin.val_succ]
  rw [show f + 1 - 1 = f by omega, pow_zero, mul_one]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hidx : f - ((i : ℕ) + 1) = f - 1 - (i : ℕ) := by
    have hi : (i : ℕ) < f := i.isLt
    omega
  rw [hidx, pow_succ]
  ring

/-- Telescoped value identity for the carry digit vector. -/
theorem p_mul_digitValue_dworkCarryDigitVec_add_last_eq
    {ℓ p A f : ℕ} (hℓ : 0 < ℓ) (hp : 0 < p) :
    p * digitValue (dworkCarryDigitVec hℓ hp A f) + residueOrbit ℓ p A f =
      residueOrbit ℓ p A 0 * ℓ ^ f := by
  induction f with
  | zero =>
      simp [digitValue]
  | succ f ih =>
      rw [digitValue_dworkCarryDigitVec_succ hℓ hp]
      have hcarry := carryDigit_mul_p_add_next (ℓ := ℓ) (p := p) (A := A) (i := f)
      rw [pow_succ]
      nlinarith

/-- The carry digit vector is the standard length-`f` digit vector of
`A * ((ℓ ^ f - 1) / p)` under the expected period and divisibility
hypotheses. -/
theorem digitValue_dworkCarryDigitVec_eq_mul_div
    {ℓ p A f : ℕ} (hℓ : 0 < ℓ) (hp : 0 < p)
    (hA_lt : A < p) (hpow : ℓ ^ f ≡ 1 [MOD p])
    (hdiv : p ∣ ℓ ^ f - 1) :
    digitValue (dworkCarryDigitVec hℓ hp A f) = A * ((ℓ ^ f - 1) / p) := by
  have hmain :=
    p_mul_digitValue_dworkCarryDigitVec_add_last_eq
      (ℓ := ℓ) (p := p) (A := A) (f := f) hℓ hp
  have hr0 : residueOrbit ℓ p A 0 = A := by
    unfold residueOrbit
    rw [pow_zero, mul_one, Nat.mod_eq_of_lt hA_lt]
  have hrf : residueOrbit ℓ p A f = A := by
    rw [residueOrbit_period_of_pow_modEq_one (A := A) hpow, hr0]
  rw [hr0, hrf] at hmain
  have hmulV : p * digitValue (dworkCarryDigitVec hℓ hp A f) = A * (ℓ ^ f - 1) := by
    have hpow_ge : 1 ≤ ℓ ^ f := Nat.one_le_pow f ℓ hℓ
    have hsplit : A * ℓ ^ f = A * (ℓ ^ f - 1) + A := by
      calc
        A * ℓ ^ f = A * ((ℓ ^ f - 1) + 1) := by rw [Nat.sub_add_cancel hpow_ge]
        _ = A * (ℓ ^ f - 1) + A := by ring
    rw [hsplit] at hmain
    omega
  have hmulR : p * (A * ((ℓ ^ f - 1) / p)) = A * (ℓ ^ f - 1) := by
    calc
      p * (A * ((ℓ ^ f - 1) / p)) = A * (p * ((ℓ ^ f - 1) / p)) := by ring
      _ = A * (ℓ ^ f - 1) := by
        rw [Nat.mul_comm p ((ℓ ^ f - 1) / p), Nat.div_mul_cancel hdiv]
  exact Nat.mul_left_cancel hp (by rw [hmulV, hmulR])

/-- The digit sum of `A * ((ℓ ^ f - 1) / p)` is the carry digit weight. -/
theorem digitSum_mul_div_eq_dworkCarryDigitWeight
    {ℓ p A f : ℕ} (hℓ : 1 < ℓ) (hp : 0 < p)
    (hA_lt : A < p) (hpow : ℓ ^ f ≡ 1 [MOD p])
    (hdiv : p ∣ ℓ ^ f - 1) :
    digitSum ℓ (A * ((ℓ ^ f - 1) / p)) =
      digitWeight (dworkCarryDigitVec (Nat.zero_lt_of_lt hℓ) hp A f) := by
  rw [← digitValue_dworkCarryDigitVec_eq_mul_div
    (Nat.zero_lt_of_lt hℓ) hp hA_lt hpow hdiv]
  exact digitSum_digitValue_eq_digitWeight hℓ _

/-- Pure arbitrary-degree digit/carry quotient formula. The right side is
the sum of the least residues in the Frobenius orbit
`A, Aℓ, ..., Aℓ^(f-1)` modulo `p`. -/
theorem p_mul_digitSum_mul_div_eq_ell_sub_one_mul_residueOrbitSum
    {ℓ p A f : ℕ} (hℓ : 1 < ℓ) (hp : 0 < p)
    (hA_lt : A < p) (hpow : ℓ ^ f ≡ 1 [MOD p])
    (hdiv : p ∣ ℓ ^ f - 1) :
    p * digitSum ℓ (A * ((ℓ ^ f - 1) / p)) =
      (ℓ - 1) * (∑ j ∈ Finset.range f, residueOrbit ℓ p A j) := by
  rw [digitSum_mul_div_eq_dworkCarryDigitWeight hℓ hp hA_lt hpow hdiv]
  exact p_mul_dworkCarryDigitWeight_eq_ell_sub_one_mul_residueOrbitSum
    (Nat.zero_lt_of_lt hℓ) hp (residueOrbit_period_of_pow_modEq_one (A := A) hpow)

/-- The digit value is strictly bounded by `ℓ ^ f`: classical place-value
inequality. -/
theorem digitValue_lt {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {f : ℕ} (m : digitVec ℓ f) :
    digitValue m < ℓ ^ f := by
  unfold digitValue
  induction f with
  | zero => simp
  | succ n ih =>
    -- ∑_{i:Fin (n+1)} m_i * ℓ^i = (∑_{i:Fin n} m_i * ℓ^i) + m_n * ℓ^n.
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    -- Trim to a digit vector of length n.
    let m' : digitVec ℓ n :=
      ⟨fun i : Fin n => m.1 i.castSucc, fun i => m.entry_lt i.castSucc⟩
    have hsum_eq :
        (∑ i : Fin n, m.1 i.castSucc * ℓ ^ (i : ℕ)) =
          (∑ i : Fin n, m'.1 i * ℓ ^ (i : ℕ)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rfl
    rw [hsum_eq]
    have hih : (∑ i : Fin n, m'.1 i * ℓ ^ (i : ℕ)) < ℓ ^ n := ih m'
    have hmn : m.1 (Fin.last n) < ℓ := m.entry_lt _
    -- (sum) + m_n * ℓ^n < ℓ^n + (ℓ-1) * ℓ^n = ℓ * ℓ^n = ℓ^(n+1).
    have hbnd : m.1 (Fin.last n) * ℓ ^ n ≤ (ℓ - 1) * ℓ ^ n :=
      Nat.mul_le_mul_right _ (by omega)
    have hℓ_pow : (ℓ - 1) * ℓ ^ n + ℓ ^ n = ℓ * ℓ ^ n := by
      have : ((ℓ - 1) + 1) * ℓ ^ n = ℓ * ℓ ^ n := by
        congr 1; omega
      linarith [this, Nat.add_mul (ℓ - 1) 1 (ℓ^n)]
    rw [pow_succ]
    -- Combine: (sum) + m_n * ℓ^n < ℓ^n + (ℓ-1) * ℓ^n = ℓ^n * ℓ.
    have : (∑ i : Fin n, m'.1 i * ℓ ^ (i : ℕ)) + m.1 (Fin.last n) * ℓ ^ n
        < ℓ ^ n + (ℓ - 1) * ℓ ^ n := by
      have h1 : (∑ i : Fin n, m'.1 i * ℓ ^ (i : ℕ)) < ℓ ^ n := hih
      omega
    have heq : ℓ ^ n + (ℓ - 1) * ℓ ^ n = ℓ ^ n * ℓ := by
      have : ℓ ^ n + (ℓ - 1) * ℓ ^ n = (1 + (ℓ - 1)) * ℓ ^ n := by ring
      rw [this]
      have h_one_add : 1 + (ℓ - 1) = ℓ := by omega
      rw [h_one_add, mul_comm]
    omega

/-- Inclusive form of `digitValue_lt`. -/
theorem digitValue_le_pred {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {f : ℕ} (m : digitVec ℓ f) :
    digitValue m ≤ ℓ ^ f - 1 := by
  have h := digitValue_lt hℓ m
  omega

/-- Standard base-`ℓ` digit decomposition of `a` as a digit vector of
length `f`: the `i`-th entry is `(a / ℓ^i) % ℓ`. The bound `< ℓ` is
immediate. -/
def standardDigitVec {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (f a : ℕ) : digitVec ℓ f :=
  ⟨fun i : Fin f => (a / ℓ ^ (i : ℕ)) % ℓ, fun _ => Nat.mod_lt _ (by omega)⟩

@[simp]
theorem standardDigitVec_apply {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (f a : ℕ) (i : Fin f) :
    (standardDigitVec hℓ f a).1 i = (a / ℓ ^ (i : ℕ)) % ℓ := rfl

/-- The standard digit decomposition recovers `a` whenever `a < ℓ ^ f`. -/
theorem digitValue_standardDigitVec_of_lt
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∀ {f a : ℕ}, a < ℓ ^ f →
      digitValue (standardDigitVec hℓ f a) = a := by
  intro f
  induction f with
  | zero =>
    intro a h
    rw [pow_zero] at h
    have : a = 0 := by omega
    simp [digitValue, standardDigitVec, this]
  | succ n ih =>
    intro a h
    unfold digitValue
    rw [Fin.sum_univ_succ]
    simp only [standardDigitVec_apply, Fin.val_succ, Fin.val_zero, pow_zero, Nat.div_one,
      pow_succ]
    have hdiv_lt : a / ℓ < ℓ ^ n := by
      rw [pow_succ] at h
      exact Nat.div_lt_iff_lt_mul (by omega) |>.mpr h
    have hih := ih hdiv_lt
    unfold digitValue at hih
    have hkey :
        (∑ i : Fin n,
            (a / (ℓ ^ (i : ℕ) * ℓ) % ℓ) * (ℓ ^ (i : ℕ) * ℓ)) =
          ℓ * (∑ i : Fin n,
            (standardDigitVec hℓ n (a / ℓ)).1 i * ℓ ^ (i : ℕ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [standardDigitVec_apply]
      have hdivdiv : a / (ℓ ^ (i : ℕ) * ℓ) = a / ℓ / ℓ ^ (i : ℕ) := by
        rw [mul_comm (ℓ ^ (i : ℕ)) ℓ, ← Nat.div_div_eq_div_mul]
      rw [hdivdiv]
      ring
    rw [hkey, hih]
    have := Nat.mod_add_div a ℓ
    omega

/-- **Uniqueness of digit-vector representation.** Any digit vector
whose value is `a` (with `a < ℓ ^ f`) equals the standard digit
decomposition. -/
theorem digitVec_eq_standardDigitVec_of_value
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {f a : ℕ} (h_lt : a < ℓ ^ f)
    (m : digitVec ℓ f) (hm : digitValue m = a) :
    m = standardDigitVec hℓ f a := by
  obtain ⟨k_uniq, _, h_unique⟩ :=
    digitSum_decomp_unique_at_minimum hℓ f a h_lt
  -- m.extend satisfies the three conditions.
  have h_m_ext : m.extend = k_uniq := by
    apply h_unique
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact m.extend_of_not_lt (by omega)
    · intro i
      by_cases h : i < f
      · rw [m.extend_of_lt h]; exact m.entry_lt _
      · rw [m.extend_of_not_lt h]; omega
    · rw [← digitValue_eq_sum_range]; exact hm
  -- standardDigitVec satisfies the same.
  have h_s_ext : (standardDigitVec hℓ f a).extend = k_uniq := by
    apply h_unique
    refine ⟨?_, ?_, ?_⟩
    · intro i hi
      exact (standardDigitVec hℓ f a).extend_of_not_lt (by omega)
    · intro i
      by_cases h : i < f
      · rw [(standardDigitVec hℓ f a).extend_of_lt h]
        exact (standardDigitVec hℓ f a).entry_lt _
      · rw [(standardDigitVec hℓ f a).extend_of_not_lt h]; omega
    · rw [← digitValue_eq_sum_range]
      exact digitValue_standardDigitVec_of_lt hℓ h_lt
  -- m.extend = standardDigitVec.extend ⇒ m.1 = standardDigitVec.1.
  have h_eq_ext : m.extend = (standardDigitVec hℓ f a).extend := by
    rw [h_m_ext, ← h_s_ext]
  apply Subtype.ext
  funext i
  have hi_lt : (i : ℕ) < f := i.isLt
  have h := congrArg (fun k => k (i : ℕ)) h_eq_ext
  simp only [m.extend_of_lt hi_lt,
    (standardDigitVec hℓ f a).extend_of_lt hi_lt] at h
  exact h

/-- The digit weight of the standard decomposition recovers `digitSum ℓ a`
whenever `a < ℓ ^ f`. -/
theorem digitWeight_standardDigitVec_of_lt
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    ∀ {f a : ℕ}, a < ℓ ^ f →
      digitWeight (standardDigitVec hℓ f a) = digitSum ℓ a := by
  intro f
  induction f with
  | zero =>
    intro a h
    rw [pow_zero] at h
    have : a = 0 := by omega
    simp [digitWeight, standardDigitVec, this, digitSum]
  | succ n ih =>
    intro a h
    unfold digitWeight
    rw [Fin.sum_univ_succ]
    simp only [standardDigitVec_apply, Fin.val_succ, Fin.val_zero, pow_zero, Nat.div_one]
    have hdiv_lt : a / ℓ < ℓ ^ n := by
      rw [pow_succ] at h
      exact Nat.div_lt_iff_lt_mul (by omega) |>.mpr h
    have hih := ih hdiv_lt
    unfold digitWeight at hih
    -- After simp the goal has `∑ x, a / ℓ ^ (↑x + 1) % ℓ`. Rewrite it.
    have hkey :
        (∑ i : Fin n, a / ℓ ^ ((i : ℕ) + 1) % ℓ) =
          digitSum ℓ (a / ℓ) := by
      rw [← hih]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [standardDigitVec_apply]
      congr 1
      rw [pow_succ, mul_comm (ℓ ^ (i : ℕ)) ℓ, ← Nat.div_div_eq_div_mul]
    rw [hkey]
    rcases Nat.eq_zero_or_pos a with ha | ha
    · simp [ha, digitSum]
    · -- digitSum ℓ a = (a%ℓ) + digitSum ℓ (a/ℓ).
      have hdigit : digitSum ℓ a = a % ℓ + digitSum ℓ (a / ℓ) := by
        unfold digitSum
        rw [Nat.digits_def' hℓ ha]
        simp
      omega

namespace TraceFormStickelbergerSetup

universe u v w

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (S : TraceFormStickelbergerSetup ℓ p k K R')

/-- Each factor `∏_{r < ℓ} r!` of `digitDen` is a `Q`-unit, because every
`r! ∉ Q` for `r < ℓ`. -/
theorem block_factorial_prod_not_mem_Q :
    ((∏ r ∈ Finset.range ℓ, Nat.factorial r : ℕ) : 𝓞 R') ∉ S.Q := by
  classical
  intro hmem
  rw [Nat.cast_prod] at hmem
  obtain ⟨r, hr_mem, hr_in_Q⟩ := (Ideal.IsPrime.prod_mem_iff (p := S.Q)).mp hmem
  have hr_lt : r < ℓ := Finset.mem_range.mp hr_mem
  exact S.natCast_factorial_not_mem_Q_of_lt_ell hr_lt hr_in_Q

/-- **L2c3d-3 (first half).** The digit denominator `digitDen ℓ f`
is a `Q`-unit. -/
theorem digitDen_not_mem_Q :
    (digitDen ℓ S.f : 𝓞 R') ∉ S.Q := by
  classical
  intro hmem
  unfold digitDen at hmem
  rw [Nat.cast_prod] at hmem
  obtain ⟨i, _, hi_in_Q⟩ := (Ideal.IsPrime.prod_mem_iff (p := S.Q)).mp hmem
  exact S.block_factorial_prod_not_mem_Q hi_in_Q

/-- **L2c3d-3 (second half).** Cancel the digit denominator from a
`Q`-power membership: `digitDen · x ∈ Q^n` implies `x ∈ Q^n`. -/
theorem mem_Q_pow_of_digitDen_mul_mem
    {x : 𝓞 R'} {n : ℕ}
    (h : (digitDen ℓ S.f : 𝓞 R') * x ∈ S.Q ^ n) :
    x ∈ S.Q ^ n := by
  have hunit := S.digitDen_not_mem_Q
  rcases Ideal.IsPrime.mul_mem_pow S.Q h with hdQ | hxQ
  · exact (hunit hdQ).elim
  · exact hxQ

/-- The digit coefficient is a `Q`-unit: `digitCoeff m ∉ Q`. Used by
`leadingCoeff_not_mem_Q` (L2c3e-3). -/
theorem digitCoeff_not_mem_Q (m : digitVec ℓ S.f) :
    (digitCoeff m : 𝓞 R') ∉ S.Q := by
  classical
  intro hmem
  -- digitCoeff m * ∏ m_i! = digitDen, so digitDen ∈ Q ∨ ∏ m_i! ∈ Q.
  have hkey :
      (digitCoeff m : 𝓞 R') * ((∏ i : Fin S.f, Nat.factorial (m.1 i) : ℕ) : 𝓞 R') =
        (digitDen ℓ S.f : 𝓞 R') := by
    have h := digitCoeff_mul_prod_factorial_eq m
    exact_mod_cast congrArg (Nat.cast : ℕ → 𝓞 R') h
  -- multiply hmem by the product of factorials and rewrite to get digitDen ∈ Q.
  have hprod_in : (digitDen ℓ S.f : 𝓞 R') ∈ S.Q := by
    rw [← hkey]
    exact Ideal.mul_mem_right _ _ hmem
  exact S.digitDen_not_mem_Q hprod_in

/-- **L2c3d-6 (raw form).** No digit vector of weight strictly less than
`s_ℓ(a · d)` survives the divisibility test
`(q-1) ∣ (p-a) · d + digitValue m`, where `d = (q-1)/p` and `q = #k`.
This is the orthogonality-coupled minimal-weight pruning step.

Stated using the raw `(Fintype.card k - 1) / p` rather than the
`stickOrd`/`stickD` aliases so that this file does not depend on
`LeadingTerm.lean`; the `stickOrd`-form wrapper
`no_survivor_of_weight_lt_stickOrd` is provided in `LeadingTerm.lean`.
-/
theorem no_survivor_of_weight_lt
    (a : ℕ) (ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1)
    (m : digitVec ℓ S.f)
    (hm :
      digitWeight m <
        digitSum ℓ (a * ((Fintype.card k - 1) / p))) :
    ¬ (Fintype.card k - 1) ∣
        ((p - a) * ((Fintype.card k - 1) / p) + digitValue m) := by
  intro hdiv
  -- Setup arithmetic.
  set q : ℕ := Fintype.card k with hq_def
  set d : ℕ := (q - 1) / p with hd_def
  set A : ℕ := a * d with hA_def
  set M : ℕ := digitValue m with hM_def
  -- Key identity q - 1 = p * d.
  have hpd : p * d = q - 1 := by
    have h := S.toConcreteStickelbergerSetup.hdiv
    rw [hd_def, mul_comm]
    exact Nat.div_mul_cancel h
  have hℓ_prime : Nat.Prime ℓ := Fact.out
  have hp_prime : Nat.Prime p := Fact.out
  have hℓ_ge_two : 2 ≤ ℓ := hℓ_prime.two_le
  have hp_ge_two : 2 ≤ p := hp_prime.two_le
  -- q = ℓ ^ S.f, hence q ≥ 2.
  have hq_eq : q = ℓ ^ S.f := S.card_k
  have hq_pos : 1 ≤ q := by
    rw [hq_eq]
    exact Nat.one_le_pow _ _ (by omega)
  -- Show q ≥ 2: there is at least one nonzero element since k is a field.
  have hq_ge_two : 2 ≤ q := Fintype.one_lt_card
  -- d ≥ 1: from p ∣ q-1, q-1 ≥ 1, p ≥ 2, so q-1 ≥ p ≥ 2.
  have hd_pos : 1 ≤ d := by
    have hq_sub : 1 ≤ q - 1 := by omega
    have hp_dvd : p ∣ q - 1 := S.toConcreteStickelbergerSetup.hdiv
    have : p ≤ q - 1 := Nat.le_of_dvd hq_sub hp_dvd
    rw [hd_def]
    exact Nat.one_le_div_iff (by omega) |>.mpr this
  -- M = digitValue m < q = ℓ ^ f.
  have hM_lt : M < q := by
    rw [hM_def, hq_eq]
    exact digitValue_lt hℓ_ge_two m
  -- M ≤ q - 1.
  have hM_le : M ≤ q - 1 := by omega
  -- A = a * d ≤ (p-1) * d = q - 1 - d.
  have hA_le : A ≤ q - 1 - d := by
    rw [hA_def]
    have h_a_le : a ≤ p - 1 := ha₂
    have : a * d ≤ (p - 1) * d := Nat.mul_le_mul_right _ h_a_le
    have : (p - 1) * d = p * d - d := by
      have : (p - 1) * d = p * d - 1 * d := by
        rw [Nat.sub_mul]
      simp [this]
    omega
  -- A ≥ d ≥ 1.
  have hA_pos : 1 ≤ A := by
    rw [hA_def]
    exact Nat.one_le_iff_ne_zero.mpr (fun h => by
      rcases Nat.mul_eq_zero.mp h with h1 | h2
      · omega
      · omega)
  -- (p-a) * d ≥ d (since p-a ≥ 1).
  have hpa_d_ge : d ≤ (p - a) * d := by
    have h_pa : 1 ≤ p - a := by omega
    have : 1 * d ≤ (p - a) * d := Nat.mul_le_mul_right _ h_pa
    simpa using this
  -- (p-a)*d + M ≥ d ≥ 1 > 0.
  have h_lhs_pos : 1 ≤ (p - a) * d + M := by omega
  -- (p-a)*d ≤ (p-1)*d = q-1-d.
  have hpa_d_le : (p - a) * d ≤ q - 1 - d := by
    have h1 : (p - a) * d ≤ (p - 1) * d := by
      have : p - a ≤ p - 1 := by omega
      exact Nat.mul_le_mul_right _ this
    have h2 : (p - 1) * d = p * d - d := by
      have : (p - 1) * d = p * d - 1 * d := by rw [Nat.sub_mul]
      simp [this]
    omega
  -- (p-a)*d + M ≤ (q-1-d) + (q-1) = 2(q-1) - d ≤ 2(q-1) - 1 < 2(q-1).
  have h_lhs_lt : (p - a) * d + M < 2 * (q - 1) := by omega
  -- (q-1) ∣ ((p-a)*d + M) and 0 < (p-a)*d + M < 2(q-1) ⇒ (p-a)*d + M = q-1.
  have h_lhs_eq : (p - a) * d + M = q - 1 := by
    obtain ⟨c, hc⟩ := hdiv
    -- (p-a)*d + M = (q-1) * c.
    have : (q - 1) * c = (p - a) * d + M := by
      change (q - 1) * c = _
      rw [show (Fintype.card k - 1) * c = (q - 1) * c from rfl] at hc
      exact hc.symm
    -- c = 1 because 0 < (q-1)*c < 2(q-1) and q-1 ≥ 1.
    have hq_sub : 1 ≤ q - 1 := by omega
    have hc_pos : 1 ≤ c := by
      rcases Nat.eq_zero_or_pos c with hc0 | hcp
      · rw [hc0, Nat.mul_zero] at this; omega
      · exact hcp
    have hc_lt : c < 2 := by
      have : (q - 1) * c < (q - 1) * 2 := by
        rw [this]; rw [show (q - 1) * 2 = 2 * (q - 1) by ring]; exact h_lhs_lt
      exact Nat.lt_of_mul_lt_mul_left this
    have hc_eq : c = 1 := by omega
    rw [hc_eq, Nat.mul_one] at this
    exact this.symm
  -- From h_lhs_eq and hpd: (p-a)*d + M = p*d, so M = a*d = A.
  have hM_eq_A : M = A := by
    rw [hA_def]
    have h1 : (p - a) * d + M = p * d := by rw [h_lhs_eq]; exact hpd.symm
    have h2 : (p - a) * d + a * d = p * d := by
      rw [show (p - a) * d + a * d = ((p - a) + a) * d by ring]
      congr 1
      omega
    omega
  -- Now digitSum ℓ M ≤ digitWeight m < digitSum ℓ A = digitSum ℓ M. Contradiction.
  have hbound : digitSum ℓ M ≤ digitWeight m := by
    rw [hM_def]
    exact digitSum_digitValue_le_digitWeight hℓ_ge_two m
  rw [← hM_eq_A] at hm
  omega

/-- Bundle accessor for the standard digit vector at length `S.f`. -/
def standardDigitVec (a : ℕ) : digitVec ℓ S.f :=
  Furtwaengler.standardDigitVec (Fact.out : Nat.Prime ℓ).two_le S.f a

/-- Bundle accessor for the finset of digit vectors of weight at most
`N`. -/
def digitVecsLE (N : ℕ) : Finset (digitVec ℓ S.f) :=
  Furtwaengler.digitVecsLE ℓ S.f N

/-- The standard digit vector of `a * S.stickD` for `1 ≤ a ≤ p - 1` has
weight `S.stickOrd a` (= `digitSum ℓ (a · d)`) and value `a * S.stickD`. -/
theorem standardDigitVec_weight_value
    (a : ℕ) (_ha₁ : 1 ≤ a) (ha₂ : a ≤ p - 1) :
    digitWeight (S.standardDigitVec (a * ((Fintype.card k - 1) / p))) =
        digitSum ℓ (a * ((Fintype.card k - 1) / p)) ∧
      digitValue (S.standardDigitVec (a * ((Fintype.card k - 1) / p))) =
        a * ((Fintype.card k - 1) / p) := by
  -- Set up arithmetic to bound a · d < ℓ ^ f.
  set q : ℕ := Fintype.card k with hq_def
  set d : ℕ := (q - 1) / p
  set A : ℕ := a * d with hA_def
  have hℓ_prime : Nat.Prime ℓ := Fact.out
  have hp_prime : Nat.Prime p := Fact.out
  have hℓ_ge_two : 2 ≤ ℓ := hℓ_prime.two_le
  have hp_ge_two : 2 ≤ p := hp_prime.two_le
  have hq_eq : q = ℓ ^ S.f := S.card_k
  have hq_ge_two : 2 ≤ q := Fintype.one_lt_card
  have hpd : p * d = q - 1 := by
    have h := S.toConcreteStickelbergerSetup.hdiv
    rw [mul_comm]
    exact Nat.div_mul_cancel h
  have hd_pos : 1 ≤ d := by
    have hq_sub : 1 ≤ q - 1 := by omega
    have hp_dvd : p ∣ q - 1 := S.toConcreteStickelbergerSetup.hdiv
    have : p ≤ q - 1 := Nat.le_of_dvd hq_sub hp_dvd
    exact Nat.one_le_div_iff (by omega) |>.mpr this
  -- A < ℓ ^ f: from A ≤ (p-1)*d = pd - d = q-1-d < q.
  have hA_lt : A < ℓ ^ S.f := by
    have : A ≤ (p - 1) * d := Nat.mul_le_mul_right _ ha₂
    have h_pd : (p - 1) * d = p * d - d := by
      have : (p - 1) * d = p * d - 1 * d := by rw [Nat.sub_mul]
      simp [this]
    rw [← hq_eq]
    omega
  refine ⟨?_, ?_⟩
  · -- digitWeight = digitSum.
    exact digitWeight_standardDigitVec_of_lt hℓ_ge_two hA_lt
  · -- digitValue = A.
    exact digitValue_standardDigitVec_of_lt hℓ_ge_two hA_lt

end TraceFormStickelbergerSetup

end Furtwaengler

end BernoulliRegular
