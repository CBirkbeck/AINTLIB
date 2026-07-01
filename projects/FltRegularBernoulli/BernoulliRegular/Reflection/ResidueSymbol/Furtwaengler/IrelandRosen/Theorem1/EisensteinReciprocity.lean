module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IrelandRosen.Theorem1.CanonicalPrimeSourceData

@[expose] public section

noncomputable section

open scoped NumberField
open UniqueFactorizationMonoid
open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace IrelandRosen

/-- The canonical integral `p`-th root upstairs, without any exact
pair-cyclotomic hypothesis on `R'`. -/
noncomputable def canonicalZetaPIntFlexible
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type v) [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] : 𝓞 R' :=
  algebraMap (𝓞 K) (𝓞 R') (cyclotomicZetaInteger (p := p) K)

/-- The flexible canonical upstairs integral root is primitive. -/
theorem canonicalZetaPIntFlexible_isPrimitiveRoot
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type v) [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] :
    IsPrimitiveRoot (canonicalZetaPIntFlexible p K R') p := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  haveI : FaithfulSMul (𝓞 K) (𝓞 R') :=
    FaithfulSMul.of_field_isFractionRing (𝓞 K) (𝓞 R') K R'
  unfold canonicalZetaPIntFlexible
  exact (cyclotomicZetaInteger_isPrimitiveRoot (p := p) (K := K)).map_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 K) (𝓞 R'))

/-- Unit-valued flexible canonical upstairs `p`-th root. -/
noncomputable def canonicalZetaPFlexible
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type v) [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] : R'ˣ :=
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  (((canonicalZetaPIntFlexible_isPrimitiveRoot p K R').map_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 R') R')).isUnit
    (Fact.out : Nat.Prime p).ne_zero).unit

@[simp]
theorem algebraMap_canonicalZetaPIntFlexible
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type v) [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] :
    algebraMap (𝓞 R') R' (canonicalZetaPIntFlexible p K R') =
      (canonicalZetaPFlexible p K R' : R'ˣ) := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  rfl

/-- The unit-valued flexible canonical upstairs `p`-th root is primitive. -/
theorem canonicalZetaPFlexible_isPrimitiveRoot
    (p : ℕ) [Fact p.Prime]
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type v) [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R'] :
    IsPrimitiveRoot (canonicalZetaPFlexible p K R') p := by
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  refine (IsPrimitiveRoot.coe_units_iff (k := p)
    (ζ := canonicalZetaPFlexible p K R')).mp ?_
  rw [← algebraMap_canonicalZetaPIntFlexible]
  exact (canonicalZetaPIntFlexible_isPrimitiveRoot p K R').map_of_injective
    (FaithfulSMul.algebraMap_injective (𝓞 R') R')

/-- Flexible canonical zeta residue compatibility under a compatible splitting
isomorphism. -/
theorem canonicalZetaPIntFlexible_residue_of_kAlgebraCompat
    (p : ℕ) [Fact p.Prime]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R']
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    (Q : Ideal (𝓞 R')) [Q.IsPrime]
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (h_compat : CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso
      (K₀ := K) Q P iso) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    CyclotomicLocalSetup.residueMap_of_split (K₀ := K) Q P iso
        (canonicalZetaPIntFlexible p K R') =
      ((canonicalResidueZetaP (p := p) (K := K) P :
          (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) := by
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  unfold canonicalZetaPIntFlexible
  rw [CyclotomicLocalSetup.residueMap_of_split_algebraMap
    (K₀ := K) Q P iso h_compat]
  rfl

/-- Flexible trace-form split-prime constructor with canonical `ζ_p` and an
explicit primitive integral `ζ_ℓ`. -/
noncomputable def flexibleTraceFormOfSplitPrimeCanonical
    {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {R' : Type v} [Field R'] [NumberField R'] [Algebra K R']
    [IsScalarTower ℚ K R']
    (P : Ideal (𝓞 K)) [hP_max : P.IsMaximal]
    (hℓ_in_P : (ℓ : 𝓞 K) ∈ P)
    (hp_notin_P : (p : 𝓞 K) ∉ P)
    (hP_ne_bot : P ≠ ⊥)
    (hℓ_ne_p : ℓ ≠ p)
    (Q : Ideal (𝓞 R')) [hQ_prime : Q.IsPrime]
    (hQ_in : (ℓ : 𝓞 R') ∈ Q)
    (iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P))
    (h_compat : CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso
      (K₀ := K) Q P iso)
    (zeta_ell_int : 𝓞 R')
    (hzeta_ell_int : IsPrimitiveRoot zeta_ell_int ℓ)
    (h_pi_not_mem_Q_sq : zeta_ell_int - 1 ∉ Q ^ 2) :
    letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
    letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
      CyclotomicLocalSetup.algebra_zmod_residueField
        (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
    ConductorFlexibleTraceFormStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R' :=
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField
      (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : P.IsPrime := hP_max.isPrime
  let zeta_ell : R' := algebraMap (𝓞 R') R' zeta_ell_int
  have hzeta_ell : IsPrimitiveRoot zeta_ell ℓ :=
    hzeta_ell_int.map_of_injective (FaithfulSMul.algebraMap_injective (𝓞 R') R')
  have card_k :
      Fintype.card (𝓞 K ⧸ P) =
        ℓ ^ ((Ideal.span ({(ℓ : ℤ)} : Set ℤ)).inertiaDeg P) :=
    CyclotomicLocalSetup.cardResidueField_eq_pow_ell_inertiaDeg P hℓ_in_P
  have hdiv : p ∣ Fintype.card (𝓞 K ⧸ P) - 1 :=
    CyclotomicLocalSetup.p_dvd_card_residueField_sub_one P hP_ne_bot hp_notin_P
  have h_ringChar : ringChar (𝓞 K ⧸ P) = ℓ :=
    CyclotomicLocalSetup.ringChar_residueField_eq_ell P hℓ_in_P
  let zeta_k_unit : (𝓞 K ⧸ P)ˣ :=
    canonicalResidueZetaP (p := p) (K := K) P
  have hzeta_k : IsPrimitiveRoot zeta_k_unit p :=
    canonicalResidueZetaP_isPrimitiveRoot hP_ne_bot hp_notin_P
  let S₀ : ConductorFlexibleConcreteStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R' :=
    ConductorFlexibleConcreteStickelbergerSetup.mkFromTrace
      (K := K) (R' := R') hℓ_ne_p _ card_k
      zeta_k_unit hzeta_k hdiv
      (canonicalZetaPFlexible p K R')
      (canonicalZetaPFlexible_isPrimitiveRoot p K R')
      (canonicalZetaPIntFlexible p K R')
      (algebraMap_canonicalZetaPIntFlexible p K R')
      zeta_ell hzeta_ell zeta_ell_int rfl
      (zeta_ell_int - 1) rfl Q hQ_prime hQ_in
      (CyclotomicLocalSetup.residueMap_of_split (K₀ := K) Q P iso)
      (CyclotomicLocalSetup.residueMap_of_split_surjective (K₀ := K) Q P iso)
      (CyclotomicLocalSetup.residueMap_of_split_ker (K₀ := K) Q P iso)
      (canonicalZetaPIntFlexible_residue_of_kAlgebraCompat
        (K := K) (R' := R') p P Q iso h_compat)
      h_ringChar
  { toConductorFlexibleConcreteStickelbergerSetup := S₀
    traceScale := 1
    psiExponent_trace := by
      intro x
      change BundleConstruction.psiTraceFormExponent ℓ (𝓞 K ⧸ P) x =
        (Algebra.trace (ZMod ℓ) (𝓞 K ⧸ P)
          (((1 : (𝓞 K ⧸ P)ˣ) : 𝓞 K ⧸ P) * x)).val
      rw [BundleConstruction.psiTraceFormExponent_apply, Units.val_one, one_mul]
    pi_not_mem_Q_sq := h_pi_not_mem_Q_sq }

/-- A prime `ℓ` coprime to `m` does not divide `m`. -/
theorem prime_not_dvd_of_coprime
    {ℓ m : ℕ} (hℓ_prime : ℓ.Prime) (hcop : ℓ.Coprime m) :
    ¬ ℓ ∣ m :=
  hℓ_prime.coprime_iff_not_dvd.mp hcop

/-- Passing from the unit `ℓ mod p` to its underlying element does not change
the order. -/
theorem orderOf_unitOfCoprime_eq_orderOf
    {ℓ p : ℕ} [Fact (Nat.Prime p)] (hℓp : ℓ.Coprime p) :
    orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p) =
      orderOf (ℓ : ZMod p) := by
  rw [← orderOf_injective (Units.coeHom _) Units.val_injective
    (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)]
  simp [ZMod.coe_unitOfCoprime]

/-- Canonical conductor-flexible source data for one normalized prime factor
of `(α)`.  The conductor is `ℓ · (#(𝓞 K/P) - 1)`, exactly as in
Ireland--Rosen's proof: the second factor makes the chosen upstairs prime have
relative residue degree one over `P`, while the first factor supplies
`ζ_ℓ - 1` as a uniformizer. -/
noncomputable def canonicalPrimeSourceData
    {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]
    {K : Type u} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
      [IsGalois ℚ K] [NumberField.IsCMField K]
    {α : 𝓞 K}
    (hp_gt_two : 2 < p)
    (hα_prime_to_p : IsPrimeToP (p := p) (K := K) α)
    (P : Ideal (𝓞 K)) [P.IsMaximal]
    (hP : P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K)))) :
    PrimeSourceData.{u, u} (p := p) (K := K) P := by
  classical
  obtain ⟨hα_ne, hαp_top⟩ := hα_prime_to_p
  have hP_facts := isPrime_of_mem_normalizedFactors hP
  have hP_prime : P.IsPrime := hP_facts.1
  have hP_ne : P ≠ ⊥ := hP_facts.2.1
  letI : P.IsPrime := hP_prime
  letI : NeZero P := ⟨hP_ne⟩
  let ℓ : ℕ := Ideal.absNorm (P.under ℤ)
  have hℓ_prime_nat : ℓ.Prime := Nat.absNorm_under_prime P
  letI : Fact (Nat.Prime ℓ) := ⟨hℓ_prime_nat⟩
  have hℓ_in_P : (ℓ : 𝓞 K) ∈ P := by
    simpa [ℓ] using
      (Int.absNorm_under_mem (I := P) : (Ideal.absNorm (P.under ℤ) : 𝓞 K) ∈ P)
  have hp_notin_P : (p : 𝓞 K) ∉ P := by
    intro hp_mem
    have hI_le_P : Ideal.span ({α} : Set (𝓞 K)) ≤ P := by
      rw [← Ideal.dvd_iff_le]
      exact UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP
    have hα_mem : α ∈ P :=
      hI_le_P (Ideal.mem_span_singleton_self α)
    have hspan_le :
        Ideal.span ({α, (p : 𝓞 K)} : Set (𝓞 K)) ≤ P := by
      rw [Ideal.span_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hα_mem
      · exact hp_mem
    exact hP_prime.ne_top (by
      rw [hαp_top] at hspan_le
      exact top_le_iff.mp hspan_le)
  have hℓ_ne_p : ℓ ≠ p := fun h =>
    hp_notin_P (by simpa [ℓ, h] using hℓ_in_P)
  have hℓp : ℓ.Coprime p :=
    (prime_coprime_of_ne (p := p) (ℓ := ℓ) hℓ_ne_p).symm
  let q : Ideal ℤ := Ideal.span ({(ℓ : ℤ)} : Set ℤ)
  have hP_under : P.under ℤ = q :=
    CyclotomicLocalSetup.under_eq_span_of_natCast_mem
      (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  letI : P.LiesOver q := ⟨hP_under.symm⟩
  have h_card :
      Fintype.card (𝓞 K ⧸ P) = ℓ ^ q.inertiaDeg P := by
    simpa [q] using
      CyclotomicLocalSetup.cardResidueField_eq_pow_ell_inertiaDeg
        (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  have hf_pos : 0 < q.inertiaDeg P :=
    Ideal.inertiaDeg_pos q P
  let m : ℕ := Fintype.card (𝓞 K ⧸ P) - 1
  have hm_coprime : ℓ.Coprime m := by
    simpa [m] using
      prime_coprime_card_sub_one_of_card_eq_pow
        (ℓ := ℓ) (q := Fintype.card (𝓞 K ⧸ P))
        (f := q.inertiaDeg P) hℓ_prime_nat hf_pos h_card
  have hm_not_dvd_ell : ¬ ℓ ∣ m :=
    prime_not_dvd_of_coprime hℓ_prime_nat hm_coprime
  have hp_dvd_m : p ∣ m := by
    simpa [m] using
      CyclotomicLocalSetup.p_dvd_card_residueField_sub_one
        (p₀ := p) (K₀ := K) P hP_ne hp_notin_P
  have h_card_ge_two : 2 ≤ Fintype.card (𝓞 K ⧸ P) :=
    Fintype.one_lt_card
  have hm_pos : 0 < m := by
    dsimp [m]
    omega
  have hm_ne_zero : m ≠ 0 := by omega
  have hN_ne : ℓ * m ≠ 0 :=
    Nat.mul_ne_zero hℓ_prime_nat.ne_zero hm_ne_zero
  letI : NeZero (ℓ * m) := ⟨hN_ne⟩
  let R' : Type u := CyclotomicField (ℓ * m) K
  letI : Field R' := inferInstance
  letI : NumberField R' := inferInstance
  letI : Algebra K R' := inferInstance
  letI : IsScalarTower ℚ K R' := inferInstance
  have hp_dvd_N : p ∣ ℓ * m := Nat.dvd_mul_left_of_dvd hp_dvd_m ℓ
  have hcycl_Q_R'_raw :
      IsCyclotomicExtension ({p} ∪ {ℓ * m} : Set ℕ) ℚ R' :=
    IsCyclotomicExtension.trans
      (A := ℚ) (B := K) (S := ({p} : Set ℕ)) (T := ({ℓ * m} : Set ℕ)) R'
      (FaithfulSMul.algebraMap_injective K R')
  have hcycl_Q_R'_swap :
      IsCyclotomicExtension ({ℓ * m} ∪ {p} : Set ℕ) ℚ R' := by
    simpa [Set.union_comm] using hcycl_Q_R'_raw
  have hcycl_Q_R' :
      IsCyclotomicExtension ({ℓ * m} : Set ℕ) ℚ R' :=
    (IsCyclotomicExtension.iff_union_of_dvd
      (A := ℚ) (B := R') (S := ({ℓ * m} : Set ℕ)) (n := p)
      ⟨ℓ * m, by simp, hN_ne, hp_dvd_N⟩).2 hcycl_Q_R'_swap
  letI : IsCyclotomicExtension ({ℓ * m} : Set ℕ) ℚ R' := hcycl_Q_R'
  letI : IsCyclotomicExtension ({ℓ * m} : Set ℕ) K R' := inferInstance
  letI : IsGalois K R' := IsCyclotomicExtension.isGalois ({ℓ * m} : Set ℕ) K R'
  letI : FiniteDimensional K R' :=
    IsCyclotomicExtension.finiteDimensional ({ℓ * m} : Set ℕ) K R'
  letI : IsScalarTower ℤ (𝓞 K) (𝓞 R') := inferInstance
  letI : FaithfulSMul (𝓞 K) (𝓞 R') :=
    FaithfulSMul.of_field_isFractionRing (𝓞 K) (𝓞 R') K R'
  letI : Module.IsTorsionFree (𝓞 K) (𝓞 R') := inferInstance
  have h_exists := exists_maximal_over_of_finite_extension (K := K) (R' := R') P
  let Q : Ideal (𝓞 R') := Classical.choose h_exists
  have hQ_spec :
      Q.IsMaximal ∧ Q.comap (algebraMap (𝓞 K) (𝓞 R')) = P :=
    Classical.choose_spec h_exists
  have hQ_max : Q.IsMaximal := hQ_spec.1
  letI : Q.IsMaximal := hQ_max
  letI : Q.IsPrime := hQ_max.isPrime
  have h_lies : Q.under (𝓞 K) = P := hQ_spec.2
  letI : Q.LiesOver P := ⟨h_lies.symm⟩
  have hQ_ne : Q ≠ ⊥ := by
    intro hQ_bot
    have h_under_bot : Q.under (𝓞 K) = (⊥ : Ideal (𝓞 K)) := by
      simp [hQ_bot]
    exact hP_ne (h_lies ▸ h_under_bot)
  have hQ_in : (ℓ : 𝓞 R') ∈ Q :=
    CyclotomicLocalSetup.natCast_mem_of_under_eq
      (ℓ₀ := ℓ) (K₀ := K) (R' := R') P Q h_lies hℓ_in_P
  letI : Q.LiesOver q := Ideal.LiesOver.trans Q P q
  haveI hq_max : q.IsMaximal := Int.ideal_span_isMaximal_of_prime ℓ
  have hq_ne : q ≠ ⊥ := by simp [q, hℓ_prime_nat.ne_zero]
  haveI hP_max : P.IsMaximal := inferInstance
  have h_abs_inertia :
      q.inertiaDeg Q = orderOf (ℓ : ZMod m) := by
    have hn : ℓ * m = ℓ ^ (0 + 1) * m := by
      simp
    rw [Ideal.inertiaDeg_eq_inertiaDeg']
    simpa [q] using
      (IsCyclotomicExtension.Rat.inertiaDeg_eq
        (n := ℓ * m) (p := ℓ) (k := 0) (m := m)
        (K := R') (P := Q) hn hm_not_dvd_ell)
  have h_order_m :
      orderOf (ℓ : ZMod m) = q.inertiaDeg P := by
    have hm_eq : m = ℓ ^ q.inertiaDeg P - 1 := by
      simp [m, h_card]
    rw [hm_eq]
    exact orderOf_natCast_zmod_pow_sub_one
      (ℓ := ℓ) (f := q.inertiaDeg P) hℓ_prime_nat.two_le hf_pos
  have h_inertia_tower :
      q.inertiaDeg Q = q.inertiaDeg P * P.inertiaDeg Q :=
    Ideal.inertiaDeg_algebra_tower q P Q
  have h_inertia_one : P.inertiaDeg Q = 1 := by
    have hmul : q.inertiaDeg P * P.inertiaDeg Q = q.inertiaDeg P * 1 := by
      rw [← h_inertia_tower, h_abs_inertia, h_order_m, mul_one]
    exact Nat.eq_of_mul_eq_mul_left hf_pos hmul
  have h_abs_ram :
      q.ramificationIdx Q = ℓ - 1 := by
    have hn : ℓ * m = ℓ ^ (0 + 1) * m := by
      simp
    rw [Ideal.ramificationIdx_eq_ramificationIdx' q Q hq_ne]
    simpa [q] using
      (IsCyclotomicExtension.Rat.ramificationIdx_eq
        (n := ℓ * m) (p := ℓ) (k := 0) (m := m)
        (K := R') (P := Q) hn hm_not_dvd_ell)
  have h_base_ram :
      q.ramificationIdx P = 1 := by
    rw [Ideal.ramificationIdx_eq_ramificationIdx' q P hq_ne]
    simpa [q] using
      (IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd
        (p := ℓ) (m := p) (K := K) (P := P)
        (prime_not_dvd_of_coprime hℓ_prime_nat hℓp))
  have h_ram_tower :
      q.ramificationIdx Q = q.ramificationIdx P * P.ramificationIdx Q :=
    Ideal.ramificationIdx_algebra_tower' (p := q) (P := P) (Q := Q)
  have h_rel_ram : P.ramificationIdx Q = ℓ - 1 := by
    rw [h_base_ram, one_mul] at h_ram_tower
    rw [← h_ram_tower, h_abs_ram]
  have h_base_inertia :
      q.inertiaDeg P = orderOf (ℓ : ZMod p) := by
    rw [Ideal.inertiaDeg_eq_inertiaDeg']
    simpa [q] using
      (IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd
        (p := ℓ) (m := p) (K := K) (P := P)
        (prime_not_dvd_of_coprime hℓ_prime_nat hℓp))
  have h_surj :
      Function.Surjective
        (CyclotomicLocalSetup.canonicalQuotientMap
          (K₀ := K) (R' := R') P Q h_lies) :=
    CyclotomicLocalSetup.canonicalQuotientMap_surjective_of_inertiaDeg_eq_one
      (K₀ := K) (R' := R') P Q h_lies h_inertia_one
  let iso : (𝓞 R' ⧸ Q) ≃+* (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.canonicalSplittingIso
      (K₀ := K) (R' := R') P Q h_lies h_surj
  have h_compat :
      CyclotomicLocalSetup.IsKAlgebraCompatibleSplittingIso
        (K₀ := K) Q P iso :=
    CyclotomicLocalSetup.canonicalSplittingIso_isKAlgebraCompatible
      (K₀ := K) (R' := R') P Q h_lies h_surj
  have hℓ_dvd_N : ℓ ∣ ℓ * m := Nat.dvd_mul_right ℓ m
  let zeta_ell_exists :=
    TraceFormStickelbergerSetup.exists_integer_isPrimitiveRoot_dvd_of_isCyclotomicExtension
      (N := ℓ * m) (m := ℓ) (R' := R')
      hℓ_prime_nat.ne_zero hℓ_dvd_N
  let zeta_ell_int : 𝓞 R' := Classical.choose zeta_ell_exists
  have hzeta_ell_int : IsPrimitiveRoot zeta_ell_int ℓ :=
    Classical.choose_spec zeta_ell_exists
  have hm_dvd_N : m ∣ ℓ * m := Nat.dvd_mul_left m ℓ
  let zeta_m_exists :=
    TraceFormStickelbergerSetup.exists_integer_isPrimitiveRoot_dvd_of_isCyclotomicExtension
      (N := ℓ * m) (m := m) (R' := R') hm_ne_zero hm_dvd_N
  let zeta_m_int : 𝓞 R' := Classical.choose zeta_m_exists
  have hzeta_m_int : IsPrimitiveRoot zeta_m_int m :=
    Classical.choose_spec zeta_m_exists
  have h_pi_not_mem_Q_sq : zeta_ell_int - 1 ∉ Q ^ 2 :=
    pi_not_mem_Q_sq_of_ramificationIdx_eq
      (ℓ := ℓ) zeta_ell_int hzeta_ell_int Q hQ_ne (by
        simpa [q] using h_abs_ram)
  letI : Field (𝓞 K ⧸ P) := Ideal.Quotient.field P
  letI : Algebra (ZMod ℓ) (𝓞 K ⧸ P) :=
    CyclotomicLocalSetup.algebra_zmod_residueField
      (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
  let T : ConductorFlexibleTraceFormStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R' :=
    flexibleTraceFormOfSplitPrimeCanonical
      (p := p) (ℓ := ℓ) (K := K) (R' := R')
      P hℓ_in_P hp_notin_P hP_ne hℓ_ne_p
      Q hQ_in iso h_compat zeta_ell_int hzeta_ell_int h_pi_not_mem_Q_sq
  let F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p (𝓞 K ⧸ P) K R' :=
    T.mkFullTeich_of_isPrimitiveRoot hzeta_m_int
  let S : ConductorFlexibleFullTeichDworkSetup ℓ p (𝓞 K ⧸ P) K R' :=
    F.toConductorFlexibleFullTeichDworkSetupArtinHasseApproxToOfFiniteLog
  have h_psi : S.concrete.IsGalPsiShiftCompatible :=
    T.isGalPsiShiftCompatible
  have h_descentPrime : S.concrete.descentPrime = P := by
    change Q.under (𝓞 K) = P
    exact h_lies
  have h_zeta_k_eq : S.zeta_k = canonicalResidueZetaP (p := p) (K := K) P := by
    rfl
  have h_zeta_p_int_eq :
      S.zeta_p_int =
        (algebraMap (𝓞 K) (𝓞 R'))
          (cyclotomicZetaInteger (p := p) K) := by
    rfl
  have h_gauss_not_mem :
      S.gaussSumInt (p - 1) ∉ S.Q ^ (S.stickOrdOrd (p - 1) + 1) :=
    (S.gaussSumInt_qadic_ord_at_prime_ord_dwork
      (p - 1) (one_le_p_sub_one_of_prime (p := p)) (le_refl (p - 1))).2
  have h_gauss_ne_zero : S.gaussSumInt (p - 1) ^ p ≠ 0 :=
    S.concrete.gaussSumInt_pow_p_ne_zero_of_ne_zero
      (S.concrete.gaussSumInt_ne_zero_of_not_mem_Q_pow_succ
        (a := p - 1) (d := S.stickOrdOrd (p - 1)) h_gauss_not_mem)
  have hf : S.f = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p) := by
    change q.inertiaDeg P = orderOf (ZMod.unitOfCoprime ℓ hℓp : CyclotomicUnitDelta p)
    rw [orderOf_unitOfCoprime_eq_orderOf hℓp, h_base_inertia]
  have he : S.concrete.descentRamificationIdx = ℓ - 1 := by
    rw [ConductorFlexibleConcreteStickelbergerSetup.descentRamificationIdx,
      h_descentPrime]
    exact h_rel_ram
  have hm_ge_p : p ≤ m :=
    Nat.le_of_dvd hm_pos hp_dvd_m
  have hN_gt_two : 2 < ℓ * m := by
    have hℓ_two : 2 ≤ ℓ := hℓ_prime_nat.two_le
    nlinarith [hℓ_two, hp_gt_two, hm_ge_p]
  letI : NumberField.IsCMField R' :=
    IsCyclotomicExtension.Rat.isCMField (S := {ℓ * m}) R' ⟨ℓ * m, rfl, hN_gt_two⟩
  let conjLift : 𝓞 R' →+* 𝓞 R' :=
    NumberField.IsCMField.ringOfIntegersComplexConj R'
  have h_conj_lifts :
      ∀ x : 𝓞 K,
        conjLift (algebraMap (𝓞 K) (𝓞 R') x) =
          algebraMap (𝓞 K) (𝓞 R')
            (NumberField.IsCMField.ringOfIntegersComplexConj K x) := fun x =>
    upstairsComplexConj_lifts_downstairs_of_isCMField
        (p := p) hp_gt_two (K := K) (R' := R') x
  have h_conj_zeta_ell :
      conjLift S.concrete.zeta_ell_int =
        S.concrete.zeta_ell_int ^ (ℓ - 1) :=
    ringOfIntegersComplexConj_primitiveRoot hℓ_prime_nat.pos hzeta_ell_int
  exact
    { ℓ := ℓ
      hℓ_prime := ⟨hℓ_prime_nat⟩
      algZMod :=
        CyclotomicLocalSetup.algebra_zmod_residueField
          (ℓ₀ := ℓ) (K₀ := K) P hℓ_in_P
      R' := R'
      field_R' := inferInstance
      numberField_R' := inferInstance
      algebra_K_R' := inferInstance
      scalarTower_Q_K_R' := inferInstance
      cyclotomic_R' := hcycl_Q_R'
      scalarTower_Z_OK_OR' := inferInstance
      isGalois_K_R' := inferInstance
      finiteDimensional_K_R' := inferInstance
      faithfulSMul_OK_OR' := inferInstance
      torsionFree_OK_OR' := inferInstance
      hP_bot := hP_ne
      hℓ_in_P := hℓ_in_P
      hp_notin_P := hp_notin_P
      S := S
      h_psi := h_psi
      h_descentPrime := h_descentPrime
      h_source_coprime := hm_coprime
      h_zeta_k_eq := h_zeta_k_eq
      h_zeta_p_int_eq := h_zeta_p_int_eq
      h_ne_zero := h_gauss_ne_zero
      hℓp := hℓp
      hf := hf
      he := he
      conjLift := conjLift
      conjLift_lifts := h_conj_lifts
      conjLift_zeta_ell := h_conj_zeta_ell }

/-- Ireland--Rosen, Chapter 14, Section 5, Proposition 14.5.4, in the
canonical project residue-symbol notation.

Dictionary with Ireland--Rosen:
* `p`, `[Fact p.Prime]`, and `hp_odd` are the odd rational prime `l`.
* `K` with `[IsCyclotomicExtension {p} ℚ K]` is the cyclotomic field
  `ℚ(ζ_l)`; its ring of integers `𝓞 K` is Ireland--Rosen's `D_l`.
* `α : 𝓞 K` is the element `α ∈ D_l`.
* `hα_primary` and `hα_prime_to_p` together encode Ireland--Rosen's
  hypothesis that `α` is primary: in this project `FLT37.IsPrimary` is the
  congruence part, while `IsPrimeToP` records `α ≠ 0` and primeness to `l`.
* `B : Ideal (𝓞 K)` is the ideal `B`.
* `hB_ne` is the nonzero-ideal convention implicit in the classical notation.
* `hB_prime_to_p` is the assumption that `B` is prime to `l`.
* `hNB_prime_to_alpha` is the assumption that `NB` is prime to `α`, expressed
  as coprimality between `(NB)` and `(α)`.

The conclusion is exactly `(α / NB)_l = (NB / α)_l`.  The left denominator
`NB` is `idealNormPrincipalIdeal B`, and the right numerator is the rational
integer `B.absNorm` mapped into `𝓞 K`. -/
theorem eisensteinReciprocity_proposition14_5_4
    (p : ℕ) [Fact p.Prime] (hp_odd : Odd p)
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {α : 𝓞 K}
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (hα_prime_to_p : IsPrimeToP (p := p) (K := K) α)
    (B : Ideal (𝓞 K))
    (hB_ne : B ≠ ⊥)
    (hB_prime_to_p :
      IsCoprime B (Ideal.span ({(p : 𝓞 K)} : Set (𝓞 K))))
    (hNB_prime_to_alpha :
      IsCoprime (idealNormPrincipalIdeal (K := K) B)
        (Ideal.span ({α} : Set (𝓞 K)))) :
    pthSymbolAtIdeal_canonical (p := p) (K := K) α
        (idealNormPrincipalIdeal (K := K) B) =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (algebraMap ℤ (𝓞 K) (B.absNorm : ℤ))
        (Ideal.span ({α} : Set (𝓞 K))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : Nat.Prime p).ne_zero⟩
  have hp_ne_two : p ≠ 2 := by
    intro hp_eq
    rw [hp_eq] at hp_odd
    rcases hp_odd with ⟨k, hk⟩
    omega
  have hp_gt_two : 2 < p := by
    have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    omega
  have hp_three : 3 ≤ p := by omega
  haveI : IsGalois ℚ K :=
    IsCyclotomicExtension.isGalois ({p} : Set ℕ) ℚ K
  haveI : NumberField.IsCMField K :=
    IsCyclotomicExtension.Rat.isCMField (S := {p}) K ⟨p, rfl, hp_gt_two⟩
  have hB_prime_to_alpha :
      IsCoprime B (Ideal.span ({α} : Set (𝓞 K))) := by
    rw [Ideal.isCoprime_iff_sup_eq] at hNB_prime_to_alpha ⊢
    refine le_antisymm le_top ?_
    rw [← hNB_prime_to_alpha]
    refine sup_le_sup ?_ le_rfl
    rw [idealNormPrincipalIdeal, Ideal.span_singleton_le_iff_mem]
    change ((Ideal.absNorm B : ℤ) : 𝓞 K) ∈ B
    exact_mod_cast (Ideal.absNorm_mem B)
  let source :
      ∀ P : Ideal (𝓞 K), [P.IsMaximal] →
        P ∈ normalizedFactors (Ideal.span ({α} : Set (𝓞 K))) →
          PrimeSourceData.{u, u} (p := p) (K := K) P :=
    fun P _ hP =>
      canonicalPrimeSourceData
        (p := p) (K := K) (α := α)
        hp_gt_two hα_prime_to_p P hP
  let primePhi :=
    primePhiFamilyOfSourceData (p := p) (K := K) (α := α) source
  have hfacts :=
    primePhiFamilyFactsOfSourceData
      (p := p) (K := K) (α := α) hp_three source
  exact idealNormReciprocity_of_primePhiFamilyFacts
    (p := p) (K := K) hp_odd hα_primary hα_prime_to_p
    primePhi hfacts.1 hfacts.2.1 hfacts.2.2 B
    ⟨hB_ne, hB_prime_to_alpha, hB_prime_to_p, hNB_prime_to_alpha⟩

/-- Ireland--Rosen, Chapter 14, Section 2, Theorem 1, in the canonical
project residue-symbol notation.

Dictionary with the statement in Ireland--Rosen:
* `p`, `[Fact p.Prime]`, and `hp_odd` are the odd rational prime `p`.
* `K` with `[IsCyclotomicExtension {p} ℚ K]` is the cyclotomic field
  containing the `p`-th roots of unity; in Ireland--Rosen this is
  `ℚ(ζ_p)`.
* `α : 𝓞 K` is Ireland--Rosen's algebraic integer `α`.
* `hα_primary` is the primary hypothesis on `α`.
* `hα_prime_to_p` says `α` is nonzero and prime to the rational prime `p`.
* `a : ℤ` is Ireland--Rosen's rational integer denominator.
* `ha` says `a ≠ 0` and the ideal `(a)` is prime both to `(α)` and to `(p)`.

The conclusion is the equality `(α / a)_p = (a / α)_p`; the right-hand side is
written in project notation as the canonical ideal symbol with numerator
`a : 𝓞 K` and denominator the principal ideal `(α)`. -/
theorem eisensteinReciprocity_theorem1
    (p : ℕ) [Fact p.Prime] (hp_odd : Odd p)
    (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    {α : 𝓞 K} (a : ℤ)
    (hα_primary : FLT37.IsPrimary p (K := K) α)
    (hα_prime_to_p : IsPrimeToP (p := p) (K := K) α)
    (ha : IsCoprimeToPAndAlphaInt (p := p) (K := K) a α) :
    pthSymbolAtInt_canonical (p := p) (K := K) α a =
      pthSymbolAtIdeal_canonical (p := p) (K := K)
        (algebraMap ℤ (𝓞 K) a) (Ideal.span ({α} : Set (𝓞 K))) := by
  have hp_ne_two : p ≠ 2 := by
    intro hp_eq
    rw [hp_eq] at hp_odd
    rcases hp_odd with ⟨k, hk⟩
    omega
  have hp_gt_two : 2 < p := by
    have hp_two : 2 ≤ p := (Fact.out : Nat.Prime p).two_le
    omega
  refine eisensteinReciprocityInt_of_idealNormReciprocity
    (p := p) (K := K) ?_ hp_gt_two ha
  intro B hB
  exact eisensteinReciprocity_proposition14_5_4
    (p := p) hp_odd (K := K) hα_primary hα_prime_to_p
    B hB.1 hB.2.2.1 hB.2.2.2

end IrelandRosen

end Furtwaengler

end BernoulliRegular

end
