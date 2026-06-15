module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.WittCarry

/-!
# Basic Q-adic and inverse-boundary lemmas for the finite Dwork telescope.

Split from `DworkFactorization/Telescope.lean`.
-/

@[expose] public section

noncomputable section

open scoped NumberField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace FullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']

variable (F : FullTeichStickelbergerSetup ℓ p k K R')

/-- Powers of the rational residue characteristic have exactly the expected
`Q`-adic order coming from `ℓ ~ (ζ_ℓ - 1)^(ℓ-1)`. -/
theorem natCast_ell_pow_not_mem_Q_pow_mul_pred_succ (m : ℕ) :
    ((ℓ : 𝓞 R') ^ m) ∉ F.Q ^ (m * (ℓ - 1) + 1) := by
  have hassoc :
      Associated ((ℓ : 𝓞 R') ^ m) (F.π ^ (m * (ℓ - 1))) := by
    have h :=
      (associated_ell_zeta_sub_one_pow
        F.toConcreteStickelbergerSetup.zeta_ell_int_isPrimitiveRoot).pow_pow (n := m)
    have hπpow :
        Associated (((F.zeta_ell_int - 1) ^ (ℓ - 1)) ^ m)
          (F.π ^ (m * (ℓ - 1))) := by
      rw [F.toConcreteStickelbergerSetup.hπ, ← pow_mul]
      rw [Nat.mul_comm (ℓ - 1) m]
    exact h.trans hπpow
  intro hmem
  have hpi_mem : F.π ^ (m * (ℓ - 1)) ∈ F.Q ^ (m * (ℓ - 1) + 1) :=
    (associated_mem_ideal_iff hassoc).1 hmem
  exact
    F.toTraceFormStickelbergerSetup.pi_pow_not_mem_Q_pow_succ_of_not_mem_sq
      F.toTraceFormStickelbergerSetup.pi_ne_zero
      F.toTraceFormStickelbergerSetup.pi_not_mem_Q_sq
      (m * (ℓ - 1)) hpi_mem

/-- Exact `Q`-adic cancellation for powers of the rational residue
characteristic.  Since `(ℓ)^m` has exact `Q`-adic order `m*(ℓ-1)`, a product
`(ℓ)^m * x` lying in `Q^(m*(ℓ-1)+n)` forces `x` to lie in `Q^n`. -/
theorem mem_Q_pow_of_natCast_ell_pow_mul_mem_Q_pow_add_mul_pred
    {m n : ℕ} {x : 𝓞 R'}
    (h : (ℓ : 𝓞 R') ^ m * x ∈ F.Q ^ (m * (ℓ - 1) + n)) :
    x ∈ F.Q ^ n := by
  classical
  by_cases hx : x = 0
  · subst x
    simp
  let r : ℕ := m * (ℓ - 1)
  let I : Ideal (𝓞 R') := Ideal.span ({(ℓ : 𝓞 R') ^ m} : Set (𝓞 R'))
  let J : Ideal (𝓞 R') := Ideal.span ({x} : Set (𝓞 R'))
  have hI_le : I ≤ F.Q ^ r := by
    change Ideal.span ({(ℓ : 𝓞 R') ^ m} : Set (𝓞 R')) ≤ F.Q ^ r
    rw [Ideal.span_singleton_le_iff_mem]
    simpa [r] using
      F.toTraceFormStickelbergerSetup.natCast_ell_pow_mem_Q_pow_mul_pred m
  have hI_not_le : ¬ I ≤ F.Q ^ (r + 1) := fun hle =>
    F.natCast_ell_pow_not_mem_Q_pow_mul_pred_succ m <|
      by
        have hmem : (ℓ : 𝓞 R') ^ m ∈ F.Q ^ (r + 1) :=
          hle (Ideal.mem_span_singleton_self ((ℓ : 𝓞 R') ^ m))
        simpa [r, Nat.add_comm] using hmem
  have hI_count :
      Multiset.count F.Q (UniqueFactorizationMonoid.normalizedFactors I) = r :=
    Ideal.count_normalizedFactors_eq hI_le hI_not_le
  have hI_ne : I ≠ ⊥ := by
    change Ideal.span ({(ℓ : 𝓞 R') ^ m} : Set (𝓞 R')) ≠ ⊥
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact pow_ne_zero m (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero)
  have hJ_ne : J ≠ ⊥ := by
    change Ideal.span ({x} : Set (𝓞 R')) ≠ ⊥
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hx
  have hIJ_ne : I * J ≠ ⊥ := mul_ne_zero hI_ne hJ_ne
  have hprod_le : I * J ≤ F.Q ^ (r + n) := by
    change
      Ideal.span ({(ℓ : 𝓞 R') ^ m} : Set (𝓞 R')) *
          Ideal.span ({x} : Set (𝓞 R')) ≤ F.Q ^ (r + n)
    rw [Ideal.span_singleton_mul_span_singleton,
      Ideal.span_singleton_le_iff_mem]
    simpa [r, mul_assoc] using h
  have hQ_irr : Irreducible F.Q := by
    have hQp : Prime F.Q :=
      Ideal.prime_of_isPrime F.toTraceFormStickelbergerSetup.Q_ne_bot
        F.toTraceFormStickelbergerSetup.Q_isPrime
    exact hQp.irreducible
  have hQpow_count :
      Multiset.count F.Q
          (UniqueFactorizationMonoid.normalizedFactors (F.Q ^ (r + n))) =
        r + n := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hQ_irr,
      normalize_eq, Multiset.count_nsmul, Multiset.count_singleton_self, mul_one]
  have hprod_count_ge :
      r + n ≤ Multiset.count F.Q
          (UniqueFactorizationMonoid.normalizedFactors (I * J)) := by
    have hcount := Ideal.count_le_of_ideal_ge hprod_le hIJ_ne F.Q
    rw [hQpow_count] at hcount
    exact hcount
  have hprod_count :
      Multiset.count F.Q (UniqueFactorizationMonoid.normalizedFactors (I * J)) =
        r + Multiset.count F.Q (UniqueFactorizationMonoid.normalizedFactors J) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_mul hI_ne hJ_ne,
      Multiset.count_add, hI_count]
  have hJ_count_ge :
      n ≤ Multiset.count F.Q (UniqueFactorizationMonoid.normalizedFactors J) := by
    omega
  have hQpow_ne : F.Q ^ n ≠ ⊥ :=
    pow_ne_zero n F.toTraceFormStickelbergerSetup.Q_ne_bot
  have hJ_le : J ≤ F.Q ^ n := by
    rw [← Ideal.dvd_iff_le]
    rw [UniqueFactorizationMonoid.dvd_iff_normalizedFactors_le_normalizedFactors
      hQpow_ne hJ_ne]
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      UniqueFactorizationMonoid.normalizedFactors_irreducible hQ_irr,
      normalize_eq, Multiset.nsmul_singleton]
    rw [Multiset.le_iff_count]
    intro P
    by_cases hP : P = F.Q
    · subst P
      simpa using hJ_count_ge
    · rw [Multiset.count_replicate]
      simp [hP, eq_comm]
  exact hJ_le (Ideal.mem_span_singleton_self x)

/-- `Q`-adic form of the standard binomial valuation for
`Nat.choose (ℓ^m) s`.  The rational `ℓ`-divisibility supplied by Kummer's
theorem is translated to the selected prime `Q` above `ℓ`. -/
theorem natCast_choose_ell_pow_mem_Q_pow_factorization
    {m s : ℕ} (hs0 : s ≠ 0) (hsle : s ≤ ℓ ^ m) :
    ((Nat.choose (ℓ ^ m) s : ℕ) : 𝓞 R') ∈
      F.Q ^ ((m - s.factorization ℓ) * (ℓ - 1)) := by
  have hp : Nat.Prime ℓ := Fact.out
  have hchoose_ne : Nat.choose (ℓ ^ m) s ≠ 0 :=
    (Nat.choose_pos hsle).ne'
  have hfac :
      (Nat.choose (ℓ ^ m) s).factorization ℓ = m - s.factorization ℓ :=
    Nat.factorization_choose_prime_pow hp hsle hs0
  have hdvd : ℓ ^ (m - s.factorization ℓ) ∣ Nat.choose (ℓ ^ m) s :=
    (hp.pow_dvd_iff_le_factorization hchoose_ne).2
        (by rw [hfac])
  exact
    F.toTraceFormStickelbergerSetup.natCast_mem_Q_pow_mul_pred_of_ell_pow_dvd hdvd

private theorem nat_mul_pred_le_pow_sub_one (a n : ℕ) (ha : 1 ≤ a) :
    n * (a - 1) ≤ a ^ n - 1 := by
  have ha_pos : 0 < a := Nat.lt_of_lt_of_le Nat.zero_lt_one ha
  have hpow_one : 1 ≤ a ^ n := Nat.one_le_pow n a ha_pos
  have hbern :
      (1 : ℤ) + (n : ℤ) * ((a : ℤ) - 1) ≤ (a : ℤ) ^ n :=
    one_add_mul_sub_le_pow (by omega) n
  have hcast :
      ((n * (a - 1) : ℕ) : ℤ) ≤ ((a ^ n - 1 : ℕ) : ℤ) := by
    have hpow_cast : ((a ^ n : ℕ) : ℤ) = (a : ℤ) ^ n :=
      Nat.cast_pow a n
    rw [Nat.cast_mul, Nat.cast_sub ha, Nat.cast_sub hpow_one, hpow_cast,
      Nat.cast_one]
    change (n : ℤ) * ((a : ℤ) - 1) ≤ (a : ℤ) ^ n - 1
    omega
  exact_mod_cast hcast

private theorem factorization_mul_pred_le_pred
    {s : ℕ} (hs0 : s ≠ 0) :
    s.factorization ℓ * (ℓ - 1) ≤ s - 1 := by
  have hp : Nat.Prime ℓ := Fact.out
  let f : ℕ := s.factorization ℓ
  have hdvd : ℓ ^ f ∣ s :=
    (hp.pow_dvd_iff_le_factorization hs0).2 le_rfl
  have hpow_le : ℓ ^ f ≤ s :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hs0) hdvd
  have hmul_le : f * (ℓ - 1) ≤ ℓ ^ f - 1 :=
    nat_mul_pred_le_pow_sub_one ℓ f hp.pos
  exact hmul_le.trans (Nat.sub_le_sub_right hpow_le 1)

/-- High-precision linearization of the `ℓ^m`-power map on principal
`Q`-units.  For `x ∈ Q^n`, `n ≥ 2`, all nonlinear binomial terms have
`Q`-adic order at least `m*(ℓ-1)+n+1`. -/
theorem one_add_pow_ell_pow_sub_one_sub_natCast_ell_pow_mul_mem_Q_pow
    {m n : ℕ} (hn : 2 ≤ n) {x : 𝓞 R'} (hx : x ∈ F.Q ^ n) :
    (1 + x) ^ (ℓ ^ m) - 1 - ((ℓ : 𝓞 R') ^ m) * x ∈
      F.Q ^ (m * (ℓ - 1) + n + 1) := by
  classical
  let L : ℕ := ℓ ^ m
  let term : ℕ → 𝓞 R' := fun s => x ^ s * (Nat.choose L s : 𝓞 R')
  have hL_pos : 0 < L := pow_pos (Fact.out : Nat.Prime ℓ).pos m
  have htwo_le : 2 ≤ L + 1 := by omega
  have hfull : (1 + x) ^ L = ∑ s ∈ Finset.range (L + 1), term s := by
    rw [show (1 + x : 𝓞 R') = x + 1 by ring, add_pow]
    simp [term]
  have hsplit := Finset.sum_range_add_sum_Ico term htwo_le
  have htail_mem :
      ∑ s ∈ Finset.Ico 2 (L + 1), term s ∈
        F.Q ^ (m * (ℓ - 1) + n + 1) := by
    refine Ideal.sum_mem _ fun s hs => ?_
    have hs_bounds := Finset.mem_Ico.mp hs
    have hs2 : 2 ≤ s := hs_bounds.1
    have hsle : s ≤ ℓ ^ m := by
      dsimp [L] at hs_bounds
      omega
    have hs0 : s ≠ 0 := by omega
    have hf_le_m : s.factorization ℓ ≤ m := by
      simpa using Nat.factorization_le_of_le_pow hsle
    have hfac_le : s.factorization ℓ * (ℓ - 1) ≤ s - 1 :=
      factorization_mul_pred_le_pred (ℓ := ℓ) hs0
    have hfac_plus :
        s.factorization ℓ * (ℓ - 1) + 1 ≤ n * (s - 1) := by
      have hs_pred_pos : 1 ≤ s - 1 := by omega
      calc
        s.factorization ℓ * (ℓ - 1) + 1
            ≤ (s - 1) + 1 := Nat.add_le_add_right hfac_le 1
        _ ≤ n * (s - 1) := by
          nlinarith [hn, hs_pred_pos]
    have horder :
        m * (ℓ - 1) + n + 1 ≤
          n * s + (m - s.factorization ℓ) * (ℓ - 1) := by
      have hsplit_m :
          m * (ℓ - 1) =
            (m - s.factorization ℓ) * (ℓ - 1) +
              s.factorization ℓ * (ℓ - 1) := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hf_le_m]
      have hlinear :
          s.factorization ℓ * (ℓ - 1) + n + 1 ≤ n * s := by
        calc
          s.factorization ℓ * (ℓ - 1) + n + 1
              = (s.factorization ℓ * (ℓ - 1) + 1) + n := by omega
          _ ≤ n * (s - 1) + n := Nat.add_le_add_right hfac_plus n
          _ = n * s := by
            have hs_pos : 0 < s := by omega
            rw [← Nat.mul_succ, Nat.succ_eq_add_one,
              Nat.sub_add_cancel (Nat.succ_le_of_lt hs_pos)]
      calc
        m * (ℓ - 1) + n + 1
            =
              (m - s.factorization ℓ) * (ℓ - 1) +
                (s.factorization ℓ * (ℓ - 1) + n + 1) := by
              rw [hsplit_m]
              omega
        _ ≤ (m - s.factorization ℓ) * (ℓ - 1) + n * s :=
              Nat.add_le_add_left hlinear _
        _ = n * s + (m - s.factorization ℓ) * (ℓ - 1) := by omega
    have hxpow : x ^ s ∈ F.Q ^ (n * s) := by
      have hpow : x ^ s ∈ (F.Q ^ n) ^ s := Ideal.pow_mem_pow hx s
      rw [← pow_mul] at hpow
      simpa [Nat.mul_comm] using hpow
    have hcoeff :
        ((Nat.choose L s : ℕ) : 𝓞 R') ∈
          F.Q ^ ((m - s.factorization ℓ) * (ℓ - 1)) := by
      simpa [L] using
        F.natCast_choose_ell_pow_mem_Q_pow_factorization hs0 hsle
    have hmul :
        term s ∈ F.Q ^ (n * s + (m - s.factorization ℓ) * (ℓ - 1)) := by
      have hmul' :
          x ^ s * ((Nat.choose L s : ℕ) : 𝓞 R') ∈
            F.Q ^ (n * s) * F.Q ^ ((m - s.factorization ℓ) * (ℓ - 1)) :=
        Ideal.mul_mem_mul hxpow hcoeff
      simpa [term, pow_add] using hmul'
    exact Ideal.pow_le_pow_right horder hmul
  have hsum_range_two :
      ∑ s ∈ Finset.range 2, term s = 1 + ((ℓ : 𝓞 R') ^ m) * x := by
    have hsum :
        ∑ s ∈ Finset.range 2, term s = 1 + x * ((ℓ : 𝓞 R') ^ m) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp [term, L, Nat.choose_one_right]
    simpa [mul_comm] using hsum
  rw [show (1 + x) ^ (ℓ ^ m) - 1 - ((ℓ : 𝓞 R') ^ m) * x =
      ∑ s ∈ Finset.Ico 2 (L + 1), term s by
    dsimp [L] at hfull ⊢
    rw [hfull, ← hsplit, hsum_range_two]
    ring]
  exact htail_mem

/-- High-precision linearization of the `ℓ^m`-power map at any element
congruent to `1` modulo `Q`.  The same leading term `(ℓ)^m*x` controls
`(a+x)^(ℓ^m) - a^(ℓ^m)` because the extra factor `a^(ℓ^m-1)-1` contributes
one more `Q`. -/
theorem add_pow_ell_pow_sub_pow_sub_natCast_ell_pow_mul_mem_Q_pow
    {m n : ℕ} (hn : 2 ≤ n) {a x : 𝓞 R'} (ha : a - 1 ∈ F.Q)
    (hx : x ∈ F.Q ^ n) :
    (a + x) ^ (ℓ ^ m) - a ^ (ℓ ^ m) - ((ℓ : 𝓞 R') ^ m) * x ∈
      F.Q ^ (m * (ℓ - 1) + n + 1) := by
  classical
  let L : ℕ := ℓ ^ m
  let term : ℕ → 𝓞 R' := fun s =>
    x ^ s * ((Nat.choose L s : ℕ) : 𝓞 R') * a ^ (L - s)
  have hL_pos : 0 < L := pow_pos (Fact.out : Nat.Prime ℓ).pos m
  have htwo_le : 2 ≤ L + 1 := by omega
  have hfull : (a + x) ^ L = ∑ s ∈ Finset.range (L + 1), term s := by
    rw [show (a + x : 𝓞 R') = x + a by ring, add_pow]
    simp [term, mul_assoc, mul_comm]
  have hsplit := Finset.sum_range_add_sum_Ico term htwo_le
  have htail_mem :
      ∑ s ∈ Finset.Ico 2 (L + 1), term s ∈
        F.Q ^ (m * (ℓ - 1) + n + 1) := by
    refine Ideal.sum_mem _ fun s hs => ?_
    have hs_bounds := Finset.mem_Ico.mp hs
    have hs2 : 2 ≤ s := hs_bounds.1
    have hsle : s ≤ ℓ ^ m := by
      dsimp [L] at hs_bounds
      omega
    have hs0 : s ≠ 0 := by omega
    have hf_le_m : s.factorization ℓ ≤ m := by
      simpa using Nat.factorization_le_of_le_pow hsle
    have hfac_le : s.factorization ℓ * (ℓ - 1) ≤ s - 1 :=
      factorization_mul_pred_le_pred (ℓ := ℓ) hs0
    have hfac_plus :
        s.factorization ℓ * (ℓ - 1) + 1 ≤ n * (s - 1) := by
      have hs_pred_pos : 1 ≤ s - 1 := by omega
      calc
        s.factorization ℓ * (ℓ - 1) + 1
            ≤ (s - 1) + 1 := Nat.add_le_add_right hfac_le 1
        _ ≤ n * (s - 1) := by
          nlinarith [hn, hs_pred_pos]
    have horder :
        m * (ℓ - 1) + n + 1 ≤
          n * s + (m - s.factorization ℓ) * (ℓ - 1) := by
      have hsplit_m :
          m * (ℓ - 1) =
            (m - s.factorization ℓ) * (ℓ - 1) +
              s.factorization ℓ * (ℓ - 1) := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hf_le_m]
      have hlinear :
          s.factorization ℓ * (ℓ - 1) + n + 1 ≤ n * s := by
        calc
          s.factorization ℓ * (ℓ - 1) + n + 1
              = (s.factorization ℓ * (ℓ - 1) + 1) + n := by omega
          _ ≤ n * (s - 1) + n := Nat.add_le_add_right hfac_plus n
          _ = n * s := by
            have hs_pos : 0 < s := by omega
            rw [← Nat.mul_succ, Nat.succ_eq_add_one,
              Nat.sub_add_cancel (Nat.succ_le_of_lt hs_pos)]
      calc
        m * (ℓ - 1) + n + 1
            =
              (m - s.factorization ℓ) * (ℓ - 1) +
                (s.factorization ℓ * (ℓ - 1) + n + 1) := by
              rw [hsplit_m]
              omega
        _ ≤ (m - s.factorization ℓ) * (ℓ - 1) + n * s :=
              Nat.add_le_add_left hlinear _
        _ = n * s + (m - s.factorization ℓ) * (ℓ - 1) := by omega
    have hxpow : x ^ s ∈ F.Q ^ (n * s) := by
      have hpow : x ^ s ∈ (F.Q ^ n) ^ s := Ideal.pow_mem_pow hx s
      rw [← pow_mul] at hpow
      simpa [Nat.mul_comm] using hpow
    have hcoeff :
        ((Nat.choose L s : ℕ) : 𝓞 R') ∈
          F.Q ^ ((m - s.factorization ℓ) * (ℓ - 1)) := by
      simpa [L] using
        F.natCast_choose_ell_pow_mem_Q_pow_factorization hs0 hsle
    have hmul :
        x ^ s * ((Nat.choose L s : ℕ) : 𝓞 R') ∈
          F.Q ^ (n * s + (m - s.factorization ℓ) * (ℓ - 1)) := by
      have hmul' :
          x ^ s * ((Nat.choose L s : ℕ) : 𝓞 R') ∈
            F.Q ^ (n * s) * F.Q ^ ((m - s.factorization ℓ) * (ℓ - 1)) :=
        Ideal.mul_mem_mul hxpow hcoeff
      simpa [pow_add] using hmul'
    have hterm :
        term s ∈ F.Q ^ (n * s + (m - s.factorization ℓ) * (ℓ - 1)) := by
      have hterm' :
          a ^ (L - s) * (x ^ s * ((Nat.choose L s : ℕ) : 𝓞 R')) ∈
            F.Q ^ (n * s + (m - s.factorization ℓ) * (ℓ - 1)) :=
        Ideal.mul_mem_left _ _ hmul
      simpa [term, mul_assoc, mul_comm, mul_left_comm] using hterm'
    exact Ideal.pow_le_pow_right horder hterm
  have hsum_range_two :
      ∑ s ∈ Finset.range 2, term s =
        a ^ L + x * ((ℓ : 𝓞 R') ^ m) * a ^ (L - 1) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    simp [term, L, Nat.choose_one_right]
  have hell_mem :
      ((ℓ : 𝓞 R') ^ m) ∈ F.Q ^ (m * (ℓ - 1)) :=
    F.toTraceFormStickelbergerSetup.natCast_ell_pow_mem_Q_pow_mul_pred m
  have hell_x_mem :
      ((ℓ : 𝓞 R') ^ m) * x ∈ F.Q ^ (m * (ℓ - 1) + n) :=
    mul_mem_ideal_pow_add F.Q hell_mem hx
  have ha_pow_sub_one :
      a ^ (L - 1) - 1 ∈ F.Q :=
    pow_sub_one_mem_of_sub_one_mem a (L - 1) ha
  have hlinear_mem :
      ((ℓ : 𝓞 R') ^ m) * x * (a ^ (L - 1) - 1) ∈
        F.Q ^ (m * (ℓ - 1) + n + 1) := by
    have hmul :
        (((ℓ : 𝓞 R') ^ m) * x) * (a ^ (L - 1) - 1) ∈
          F.Q ^ (m * (ℓ - 1) + n) * F.Q :=
      Ideal.mul_mem_mul hell_x_mem ha_pow_sub_one
    simpa [pow_add] using hmul
  rw [show (a + x) ^ (ℓ ^ m) - a ^ (ℓ ^ m) - ((ℓ : 𝓞 R') ^ m) * x =
      (∑ s ∈ Finset.Ico 2 (L + 1), term s) +
        ((ℓ : 𝓞 R') ^ m) * x * (a ^ (L - 1) - 1) by
    dsimp [L] at hfull ⊢
    rw [hfull, ← hsplit, hsum_range_two]
    ring]
  exact (F.Q ^ (m * (ℓ - 1) + n + 1)).add_mem htail_mem hlinear_mem

/-- One-step Q-adic descent from an `ℓ^m`-power comparison.  If `a` is a
principal `Q`-unit, `x` is already in `Q^n`, and the powered difference
`(a+x)^(ℓ^m)-a^(ℓ^m)` vanishes to the precision predicted after the linear
term, then exact valuation of `(ℓ)^m` raises `x` from `Q^n` to `Q^(n+1)`. -/
theorem mem_Q_pow_succ_of_add_pow_ell_pow_sub_pow_mem_Q_pow_add
    {m n : ℕ} (hn : 2 ≤ n) {a x : 𝓞 R'} (ha : a - 1 ∈ F.Q)
    (hx : x ∈ F.Q ^ n)
    (hpow : (a + x) ^ (ℓ ^ m) - a ^ (ℓ ^ m) ∈
      F.Q ^ (m * (ℓ - 1) + n + 1)) :
    x ∈ F.Q ^ (n + 1) := by
  have hlin :
      (a + x) ^ (ℓ ^ m) - a ^ (ℓ ^ m) - ((ℓ : 𝓞 R') ^ m) * x ∈
        F.Q ^ (m * (ℓ - 1) + n + 1) :=
    F.add_pow_ell_pow_sub_pow_sub_natCast_ell_pow_mul_mem_Q_pow hn ha hx
  have hellx :
      ((ℓ : 𝓞 R') ^ m) * x ∈ F.Q ^ (m * (ℓ - 1) + n + 1) := by
    have hsub := (F.Q ^ (m * (ℓ - 1) + n + 1)).sub_mem hpow hlin
    convert hsub using 1
    ring
  simpa [Nat.add_assoc] using
    F.mem_Q_pow_of_natCast_ell_pow_mul_mem_Q_pow_add_mul_pred
      (m := m) (n := n + 1) hellx

/-- REF-18 theta-product version of one-step descent.  Once the powered
theta/base difference is known at the predicted precision, an existing
`Q^n` congruence between `ψ` and the corrected theta product upgrades to
`Q^(n+1)`. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_approx_mem_Q_pow_succ_of_mem_Q_pow_of_pow_sub_mem
    {m n N : ℕ} (hn : 2 ≤ n) (y : kˣ)
    (hmem :
      F.psiInt (y : k) -
          artinHasseThetaTruncProductAtTo F
            (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
        F.Q ^ n)
    (hpow :
      (artinHasseThetaTruncProductAtTo F
            (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y) ^
            (ℓ ^ m) -
          (F.psiInt (y : k)) ^ (ℓ ^ m) ∈
        F.Q ^ (m * (ℓ - 1) + n + 1)) :
    F.psiInt (y : k) -
        artinHasseThetaTruncProductAtTo F
          (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y ∈
      F.Q ^ (n + 1) := by
  let theta : 𝓞 R' :=
    artinHasseThetaTruncProductAtTo F
      (artinHasseDworkParameterApproxTo F.toConcreteStickelbergerSetup N) N y
  have hpsi_Q : F.psiInt (y : k) - 1 ∈ F.Q :=
    F.toConcreteStickelbergerSetup.psiInt_sub_one_mem_Q (y : k)
  have htheta_sub : theta - F.psiInt (y : k) ∈ F.Q ^ n := by
    have hneg := (F.Q ^ n).neg_mem hmem
    convert hneg using 1
    dsimp [theta]
    ring
  have hpow' :
      (F.psiInt (y : k) + (theta - F.psiInt (y : k))) ^ (ℓ ^ m) -
          (F.psiInt (y : k)) ^ (ℓ ^ m) ∈
        F.Q ^ (m * (ℓ - 1) + n + 1) := by
    convert hpow using 1
    dsimp [theta]
    ring
  have htheta_sub_succ :
      theta - F.psiInt (y : k) ∈ F.Q ^ (n + 1) :=
    F.mem_Q_pow_succ_of_add_pow_ell_pow_sub_pow_mem_Q_pow_add
      (m := m) (n := n) hn hpsi_Q htheta_sub hpow'
  have hneg := (F.Q ^ (n + 1)).neg_mem htheta_sub_succ
  convert hneg using 1
  dsimp [theta]
  ring

/-- Boundary value for the finite Artin-Hasse exponential in the quotient:
evaluation at the zero parameter is `1`. -/
theorem artinHasseExp_trunc_eval_zero (N : ℕ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0 = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let hE : DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) :=
    fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n
  let Eps : PowerSeries A := hE.mapTo
    (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  rw [Finset.sum_eq_single 0]
  · simp only [RingHom.id_apply, pow_zero, mul_one,
      DieudonneDwork.IsRIntegralPS.coeff_mapTo]
    change (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
        (⟨(PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries ℓ), hE 0⟩ :
          DieudonneDwork.rIntegralRatSubring ℓ) = 1
    have hcoeff0 :
        (⟨(PowerSeries.coeff (R := ℚ) 0) (artinHasseExpSeries ℓ), hE 0⟩ :
          DieudonneDwork.rIntegralRatSubring ℓ) = 1 := by
      ext
      simp [artinHasseExpSeries_constantCoeff]
    rw [hcoeff0]
    exact map_one _
  · intro n _hn hn0
    simp [hn0]
  · simp

/-- The finite Artin-Hasse exponential in the quotient evaluates to a unit
at every Frobenius iterate of a nilpotent parameter, after multiplication by
an arbitrary quotient element. -/
theorem artinHasseExp_trunc_eval_pow_iterate_mul_isUnit_of_pow_succ_eq_zero
    (N j : ℕ) (ε u : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    IsUnit ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
      (ε ^ (ℓ ^ j) * u)) := by
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  have hεj : (ε ^ (ℓ ^ j)) ^ (N + 1) = 0 := by
    rw [← pow_mul, Nat.mul_comm]
    exact pow_eq_zero_of_le
      (Nat.le_mul_of_pos_right (N + 1) (Nat.pow_pos (Fact.out : Nat.Prime ℓ).pos))
      hε
  have harg : (ε ^ (ℓ ^ j) * u) ^ (N + 1) = 0 := by
    rw [mul_pow, hεj, zero_mul]
  simpa [A, Eps] using
    artinHasseExp_mapTo_trunc_eval_isUnit_of_pow_eq_zero ℓ
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N) N harg

/-- Boundary value for the finite Frobenius theta product at the zero
parameter. -/
theorem artinHasseExp_frobenius_product_zero (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    ∏ i : Fin F.toConcreteStickelbergerSetup.f,
      (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (0 * zbar ^ (ℓ ^ (i : ℕ))) = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  have hzero := F.artinHasseExp_trunc_eval_zero N
  simp [hzero]

/-- Boundary value for the normalized base side at the zero parameter. -/
theorem artinHasseExp_base_zero (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) 0) ^ t = 1 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hzero := F.artinHasseExp_trunc_eval_zero N
  simp [hzero]

/-- Iterating `ε ↦ ε^ℓ` preserves the nilpotence bound needed to reapply the
Dwork recursions in `𝓞 R'/Q^(N+1)`. -/
theorem parameter_pow_iterate_pow_succ_eq_zero
    (N m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) :
    (ε ^ (ℓ ^ m)) ^ (N + 1) = 0 := by
  rw [← pow_mul]
  exact pow_eq_zero_of_le (a := ε)
    (m := N + 1)
    (n := ℓ ^ m * (N + 1))
    (Nat.le_mul_of_pos_left _ (Nat.pow_pos (Fact.out : Nat.Prime ℓ).pos))
    hε

/-- After sufficiently many `ℓ`-power iterations, any parameter with
`ε^(N+1)=0` becomes zero in `𝓞 R'/Q^(N+1)`. -/
theorem parameter_pow_iterate_eq_zero_of_le
    (N m : ℕ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hm : N + 1 ≤ ℓ ^ m) :
    ε ^ (ℓ ^ m) = 0 :=
  pow_eq_zero_of_le (a := ε) (m := N + 1) (n := ℓ ^ m) hm hε

/-- The inverse-series Artin-Hasse parameter has zero sufficiently far along
the `δ ↦ δ^ℓ` iteration. -/
theorem artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    δ ^ (ℓ ^ m) = 0 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  exact F.parameter_pow_iterate_eq_zero_of_le N m δ hδ hm

/-- Product-side iterated recursion after the parameter has reached the zero
boundary. -/
theorem artinHasseExp_frobenius_product_pow_prime_iterate_eq_iterCorrection_of_zero_iterate
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) =
      F.artinHasseExpFrobeniusProductIterCorrection N y ε m := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  have hiter :=
    F.artinHasseExp_frobenius_product_pow_prime_iterate_eq_iterCorrection_mul
      N m y ε hε
  have htail :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ)))) = 1 := by
    rw [hzero]
    simpa [A, Eps, zbar] using F.artinHasseExp_frobenius_product_zero N y
  calc
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (ε * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m)
        =
          F.artinHasseExpFrobeniusProductIterCorrection N y ε m *
            ∏ i : Fin F.toConcreteStickelbergerSetup.f,
              (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
                (ε ^ (ℓ ^ m) * zbar ^ (ℓ ^ (i : ℕ))) := by
          simpa [A, Eps, zbar] using hiter
    _ = F.artinHasseExpFrobeniusProductIterCorrection N y ε m := by
          rw [htail, mul_one]

/-- Base-side iterated recursion after the parameter has reached the zero
boundary. -/
theorem artinHasseExp_base_trace_pow_prime_iterate_eq_iterCorrection_of_zero_iterate
    (N m : ℕ) (y : kˣ) (ε : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hε : ε ^ (N + 1) = 0) (hzero : ε ^ (ℓ ^ m) = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ (ℓ ^ m) =
      (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hiter :=
    F.artinHasseExp_base_trace_pow_prime_iterate_eq_iterCorrection_mul
      N m y ε hε
  have htail :
      ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
        (ε ^ (ℓ ^ m))) ^ t = 1 := by
    rw [hzero]
    simpa [A, Eps, t] using F.artinHasseExp_base_zero N y
  calc
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) ε) ^ t) ^ (ℓ ^ m)
        =
          (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t *
            ((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
              (ε ^ (ℓ ^ m))) ^ t := by
          simpa [A, Eps, t] using hiter
    _ = (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N ε m) ^ t := by
          rw [htail, mul_one]

/-- Product-side zero-boundary specialization for the actual inverse-series
Dwork parameter. -/
theorem artinHasseExp_inverse_frobenius_product_pow_prime_iterate_eq_iterCorrection_of_le
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ (ℓ ^ m) =
      F.artinHasseExpFrobeniusProductIterCorrection N y δ m := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have hzero :
      δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  simpa [A, Ips, πbar, δ] using
    F.artinHasseExp_frobenius_product_pow_prime_iterate_eq_iterCorrection_of_zero_iterate
      N m y δ hδ hzero

/-- Base-side zero-boundary specialization for the actual inverse-series
Dwork parameter. -/
theorem artinHasseExp_inverse_base_trace_pow_prime_iterate_eq_iterCorrection_of_le
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (((PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A) δ) ^ t) ^ (ℓ ^ m) =
      (F.toConcreteStickelbergerSetup.artinHasseExpIterCorrection N δ m) ^ t := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have hzero :
      δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  simpa [A, Ips, πbar, δ] using
    F.artinHasseExp_base_trace_pow_prime_iterate_eq_iterCorrection_of_zero_iterate
      N m y δ hδ hzero

/-- Inverse-parameter specialization of the fixed-carry adjusted recursion.
The ordinary carry correction is already rewritten as a finite product over
the chosen prime-field coordinates of `traceCarry y`; the displayed exponents
are the `ℓ`-divisible ones needed by the next cancellation step. -/
theorem artinHasseExp_inverse_adjusted_product_pow_prime_mul_zmod_product_eq_trace_recursion_of_le
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N m : ℕ) (hm : N + 1 ≤ ℓ ^ m) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let θ : WittVector ℓ k →+* A :=
      F.toConcreteStickelbergerSetup.wittThetaModQPow N
    let Eps : PowerSeries A :=
      (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
        fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
          (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Rps : PowerSeries A :=
      (rescale_exp_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let Ips : PowerSeries A :=
      (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
    let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
    let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    (∏ i : Fin F.toConcreteStickelbergerSetup.f,
        (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
          (δ * zbar ^ (ℓ ^ (i : ℕ)))) ^ ℓ *
      (∏ r ∈ Finset.Iic N,
        ((PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A)
          (δ *
            θ (WittVector.teichmuller ℓ
              (algebraMap (ZMod ℓ) k (F.traceCarryCoeffZMod y r))))) ^
          (ℓ ^ (r + 1))) =
      (PowerSeries.trunc (N + 1) Rps).eval₂ (RingHom.id A) (δ * (t : A)) *
        ∏ i : Fin F.toConcreteStickelbergerSetup.f,
          (PowerSeries.trunc (N + 1) Eps).eval₂ (RingHom.id A)
            (δ ^ ℓ * zbar ^ (ℓ ^ (i : ℕ))) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A :=
    F.toConcreteStickelbergerSetup.wittThetaModQPow N
  let Eps : PowerSeries A :=
    (show DieudonneDwork.IsRIntegralPS ℓ (artinHasseExpSeries ℓ) from
      fun n => artinHasseExpSeries_coeff_isRIntegral ℓ n).mapTo
        (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Rps : PowerSeries A :=
    (rescale_exp_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let Ips : PowerSeries A :=
    (artinHasseExpInverseSeries_isRIntegral ℓ).mapTo
      (F.toConcreteStickelbergerSetup.rIntegralRatToQuotient N)
  let πbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) F.π
  let δ : A := (PowerSeries.trunc (N + 1) Ips).eval₂ (RingHom.id A) πbar
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  have hδ :
      δ ^ (N + 1) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.toConcreteStickelbergerSetup.artinHasseExp_inverse_trunc_eval_pow_succ_eq_zero N
  have _hzero :
      δ ^ (ℓ ^ m) = 0 := by
    simpa [A, Ips, πbar, δ] using
      F.artinHasseExp_inverse_parameter_pow_iterate_eq_zero_of_le N m hm
  simpa [A, θ, Eps, Rps, Ips, πbar, δ, zbar, t] using
    F.adjusted_product_pow_prime_mul_zmod_product_eq_trace_recursion_of_parameter
      N y δ hδ

/-- Teichmüller lifts are fixed by the `ℓ ^ f` Frobenius power attached to the
residue field cardinality. -/
theorem teichUnitFullVal_pow_ell_f_eq_self (x : kˣ) :
    F.teichUnitFullVal x ^ (ℓ ^ F.toConcreteStickelbergerSetup.f) =
      F.teichUnitFullVal x := by
  let z : 𝓞 R' := F.teichUnitFullVal x
  have hcard_pos : 0 < Fintype.card k := Fintype.card_pos
  have hcard : z ^ Fintype.card k = z := by
    rw [show Fintype.card k = (Fintype.card k - 1) + 1 by omega]
    rw [pow_succ]
    have hunit := F.teichUnitFullVal_pow_card_sub_one x
    simpa [z] using congrArg (fun a : 𝓞 R' => a * z) hunit
  rw [← F.toConcreteStickelbergerSetup.card_k_eq]
  exact hcard

/-- The Teichmüller Frobenius trace sum is unchanged by any cyclic shift of
the Frobenius orbit. -/
theorem teichFrobeniusSum_shift_iterate_eq
    (N m : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        zbar ^ (ℓ ^ ((i : ℕ) + m))) =
      ∑ i : Fin F.toConcreteStickelbergerSetup.f,
        zbar ^ (ℓ ^ (i : ℕ)) := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) z
  let f : ℕ := F.toConcreteStickelbergerSetup.f
  let g : ℕ → A := fun n => zbar ^ (ℓ ^ n)
  have hzperiod : zbar ^ (ℓ ^ f) = zbar := by
    simpa [z, zbar, f, map_pow] using
      congrArg (Ideal.Quotient.mk (F.Q ^ (N + 1)))
        (F.teichUnitFullVal_pow_ell_f_eq_self (F.traceScale * y))
  have hperiod : ∀ n : ℕ, g (n + f) = g n := by
    intro n
    have hpow_nf : ℓ ^ (n + f) = ℓ ^ f * ℓ ^ n := by
      rw [pow_add, Nat.mul_comm]
    calc
      g (n + f) = zbar ^ (ℓ ^ f * ℓ ^ n) := by
        simp [g, hpow_nf]
      _ = (zbar ^ (ℓ ^ f)) ^ (ℓ ^ n) := by
        rw [← pow_mul]
      _ = g n := by
        rw [hzperiod]
  have hshift := sum_range_shift_iterate_eq_of_period g f m hperiod
  have hleft :
      (∑ i : Fin f, zbar ^ (ℓ ^ ((i : ℕ) + m))) =
        ∑ i ∈ Finset.range f, g (i + m) :=
    (Finset.sum_range (f := fun i : ℕ => zbar ^ (ℓ ^ (i + m)))).symm
  have hright :
      (∑ i : Fin f, zbar ^ (ℓ ^ (i : ℕ))) =
        ∑ i ∈ Finset.range f, g i :=
    (Finset.sum_range (f := fun i : ℕ => zbar ^ (ℓ ^ i))).symm
  rw [show F.toConcreteStickelbergerSetup.f = f from rfl]
  rw [hleft, hright]
  exact hshift

/-- Scalar-right form of `teichFrobeniusSum_shift_iterate_eq`, matching the
inner sums that appear after factoring an Artin-Hasse logarithm term. -/
theorem teichFrobeniusSum_shift_iterate_mul_eq
    (N m : ℕ) (y : kˣ) (h : 𝓞 R' ⧸ F.Q ^ (N + 1)) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        zbar ^ (ℓ ^ ((i : ℕ) + m)) * h) =
      (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        zbar ^ (ℓ ^ (i : ℕ))) * h := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  calc
    (∑ i : Fin F.toConcreteStickelbergerSetup.f,
        zbar ^ (ℓ ^ ((i : ℕ) + m)) * h)
        =
          (∑ i : Fin F.toConcreteStickelbergerSetup.f,
            zbar ^ (ℓ ^ ((i : ℕ) + m))) * h := by
          rw [Finset.sum_mul]
    _ =
          (∑ i : Fin F.toConcreteStickelbergerSetup.f,
            zbar ^ (ℓ ^ (i : ℕ))) * h := by
          rw [F.teichFrobeniusSum_shift_iterate_eq N m y]

end FullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular

end
