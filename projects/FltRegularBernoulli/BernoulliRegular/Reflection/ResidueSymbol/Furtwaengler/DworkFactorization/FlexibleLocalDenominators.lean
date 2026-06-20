module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Flexible
public import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Local denominator estimates for the finite Dwork telescope

This file connects the exact `Q`-adic order of powers of the rational
residue characteristic with the quotient-local fraction evaluator from
`ConcreteSetup`.  The denominator `ℓ^m` is not invertible at `Q`, so the API
uses an actual local representation `ℓ^m * y = d * x` with
`d ∉ Q`; then `y / d` is the `Q`-local value of `x / ℓ^m`.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open WithZero Multiplicative IsDedekindDomain

namespace BernoulliRegular

namespace Furtwaengler

universe u v w

namespace ConductorFlexibleConcreteStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')

/-- The selected prime `Q` is nonzero. -/
theorem Q_ne_bot : S.Q ≠ ⊥ := by
  intro hQ_bot
  have hℓ_zero : (ℓ : 𝓞 R') = 0 := by
    rw [← Ideal.mem_bot, ← hQ_bot]
    exact S.hQ
  exact (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero) hℓ_zero

/-- The quotient map sends every local denominator away from `Q` to a unit. -/
theorem quotient_mk_isUnit_primeCompl
    (N : ℕ) (s : S.Q.primeCompl) :
    IsUnit (Ideal.Quotient.mk (S.Q ^ (N + 1)) (s : 𝓞 R')) :=
  S.quotient_mk_isUnit_of_not_mem_Q N s.property

/-- The canonical map from the localization of `𝓞 R'` away from `Q` to the
finite quotient `𝓞 R' / Q^(N+1)`. -/
noncomputable def quotientLocalizationAwayQMap (N : ℕ) :
    Localization S.Q.primeCompl →+* (𝓞 R' ⧸ S.Q ^ (N + 1)) :=
  IsLocalization.lift
    (M := S.Q.primeCompl)
    (S := Localization S.Q.primeCompl)
    (P := 𝓞 R' ⧸ S.Q ^ (N + 1))
    (g := Ideal.Quotient.mk (S.Q ^ (N + 1)))
    (fun s => S.quotient_mk_isUnit_primeCompl N s)

@[simp]
theorem quotientLocalizationAwayQMap_algebraMap
    (N : ℕ) (x : 𝓞 R') :
    S.quotientLocalizationAwayQMap N
        (algebraMap (𝓞 R') (Localization S.Q.primeCompl) x) =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  simp [quotientLocalizationAwayQMap,
    (IsLocalization.lift_eq
      (M := S.Q.primeCompl)
      (S := Localization S.Q.primeCompl)
      (P := 𝓞 R' ⧸ S.Q ^ (N + 1))
      (g := Ideal.Quotient.mk (S.Q ^ (N + 1)))
      (fun s => S.quotient_mk_isUnit_primeCompl N s)
      x)]

/-- Evaluate a local fraction with denominator away from `Q` in the finite
quotient. -/
noncomputable def quotientFractionEvalPrimeCompl
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) :
    𝓞 R' ⧸ S.Q ^ (N + 1) :=
  S.quotientLocalizationAwayQMap N
    (IsLocalization.mk' (Localization S.Q.primeCompl) x s)

/-- Evaluate a local fraction with an explicit proof that the denominator is
outside `Q`. -/
noncomputable def quotientFractionEval
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ S.Q) :
    𝓞 R' ⧸ S.Q ^ (N + 1) :=
  S.quotientFractionEvalPrimeCompl N x ⟨s, hs⟩

@[simp]
theorem quotientFractionEvalPrimeCompl_one
    (N : ℕ) (x : 𝓞 R') :
    S.quotientFractionEvalPrimeCompl N x 1 =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  simpa [quotientFractionEvalPrimeCompl] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_one
        (S := Localization S.Q.primeCompl)
        x)

theorem quotientFractionEvalPrimeCompl_den_mul
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) (s : 𝓞 R') *
        S.quotientFractionEvalPrimeCompl N x s =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  have h :
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x =
        Ideal.Quotient.mk (S.Q ^ (N + 1)) (s : 𝓞 R') *
          S.quotientFractionEvalPrimeCompl N x s :=
    (IsLocalization.lift_mk'_spec
        (M := S.Q.primeCompl)
        (S := Localization S.Q.primeCompl)
        (P := 𝓞 R' ⧸ S.Q ^ (N + 1))
        (g := Ideal.Quotient.mk (S.Q ^ (N + 1)))
        (hg := fun t => S.quotient_mk_isUnit_primeCompl N t)
        x
        (S.quotientFractionEvalPrimeCompl N x s)
        s).1 (by
          simp [quotientFractionEvalPrimeCompl, quotientLocalizationAwayQMap])
  exact h.symm

theorem quotientFractionEval_den_mul
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ S.Q) :
    Ideal.Quotient.mk (S.Q ^ (N + 1)) s *
        S.quotientFractionEval N x s hs =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x := by
  simpa [quotientFractionEval] using
    S.quotientFractionEvalPrimeCompl_den_mul N x ⟨s, hs⟩

theorem quotientFractionEval_eq_mk_mul_inv
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ S.Q) :
    S.quotientFractionEval N x s hs =
      Ideal.Quotient.mk (S.Q ^ (N + 1)) x *
        S.quotientInvOfNotMemQ N s hs := by
  apply (S.quotient_mk_isUnit_of_not_mem_Q N hs).mul_left_inj.mp
  rw [mul_comm (S.quotientFractionEval N x s hs),
    S.quotientFractionEval_den_mul N x s hs]
  rw [mul_assoc, S.quotientInvOfNotMemQ_mul_quotient_mk N s hs, mul_one]

theorem quotientFractionEvalPrimeCompl_add
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N
        (x₁ * (s₂ : 𝓞 R') + x₂ * (s₁ : 𝓞 R')) (s₁ * s₂) =
      S.quotientFractionEvalPrimeCompl N x₁ s₁ +
        S.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_add] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_add
        (S := Localization S.Q.primeCompl)
        x₁ x₂ s₁ s₂)

theorem quotientFractionEvalPrimeCompl_mul
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N (x₁ * x₂) (s₁ * s₂) =
      S.quotientFractionEvalPrimeCompl N x₁ s₁ *
        S.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_mul] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_mul
        (S := Localization S.Q.primeCompl)
        x₁ x₂ s₁ s₂)

theorem quotientFractionEvalPrimeCompl_neg
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N (-x) s =
      -S.quotientFractionEvalPrimeCompl N x s := by
  simpa [quotientFractionEvalPrimeCompl, map_neg] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_neg
        (S := Localization S.Q.primeCompl)
        x s)

theorem quotientFractionEvalPrimeCompl_sub
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : S.Q.primeCompl) :
    S.quotientFractionEvalPrimeCompl N
        (x₁ * (s₂ : 𝓞 R') - x₂ * (s₁ : 𝓞 R')) (s₁ * s₂) =
      S.quotientFractionEvalPrimeCompl N x₁ s₁ -
        S.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_sub] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_sub
        (S := Localization S.Q.primeCompl)
        x₁ x₂ s₁ s₂)

theorem quotientFractionEvalPrimeCompl_pow
    (N : ℕ) (x : 𝓞 R') (s : S.Q.primeCompl) (m : ℕ) :
    S.quotientFractionEvalPrimeCompl N (x ^ m) (s ^ m) =
      S.quotientFractionEvalPrimeCompl N x s ^ m := by
  simpa [quotientFractionEvalPrimeCompl, map_pow] using
    congrArg (S.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_pow
        (S := Localization S.Q.primeCompl)
        x s m)

theorem quotientFractionEvalPrimeCompl_eq_zero_of_mem
    (N : ℕ) {x : 𝓞 R'} (s : S.Q.primeCompl)
    (hx : x ∈ S.Q ^ (N + 1)) :
    S.quotientFractionEvalPrimeCompl N x s = 0 := by
  apply (S.quotient_mk_isUnit_primeCompl N s).mul_left_inj.mp
  rw [zero_mul, mul_comm (S.quotientFractionEvalPrimeCompl N x s),
    S.quotientFractionEvalPrimeCompl_den_mul N x s]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

theorem quotientFractionEvalPrimeCompl_eq_of_sub_mem
    (N : ℕ) {x y : 𝓞 R'} (s : S.Q.primeCompl)
    (hxy : x - y ∈ S.Q ^ (N + 1)) :
    S.quotientFractionEvalPrimeCompl N x s =
      S.quotientFractionEvalPrimeCompl N y s := by
  apply (S.quotient_mk_isUnit_primeCompl N s).mul_left_inj.mp
  rw [mul_comm (S.quotientFractionEvalPrimeCompl N x s),
    S.quotientFractionEvalPrimeCompl_den_mul N x s,
    mul_comm (S.quotientFractionEvalPrimeCompl N y s),
    S.quotientFractionEvalPrimeCompl_den_mul N y s]
  exact Ideal.Quotient.eq.mpr hxy

end ConductorFlexibleConcreteStickelbergerSetup

namespace ConductorFlexibleTraceFormStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')

/-- The selected prime `Q` is nonzero. -/
theorem Q_ne_bot : S.Q ≠ ⊥ :=
  S.concrete.Q_ne_bot

/-- A natural number not divisible by `ℓ` is a `Q`-unit. -/
theorem natCast_not_mem_Q_of_not_dvd {n : ℕ} (hn : ¬ ℓ ∣ n) :
    (n : 𝓞 R') ∉ S.Q := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  intro hmem
  have hres : S.residueMap (n : 𝓞 R') = 0 :=
    (S.concrete.mem_Q_iff_residueMap_eq_zero (n : 𝓞 R')).1
      (by simpa [ConductorFlexibleTraceFormStickelbergerSetup.concrete] using hmem)
  rw [map_natCast] at hres
  exact hn ((CharP.cast_eq_zero_iff k ℓ n).1 hres)

/-- The uniformizer `π = ζ_ℓ - 1` is nonzero. -/
theorem pi_ne_zero : S.π ≠ 0 := by
  rw [S.hπ]
  intro hc
  have h1 : S.zeta_ell_int = 1 := by linear_combination hc
  have h_prim := S.concrete.zeta_ell_int_isPrimitiveRoot
  have hℓ_two_le : 2 ≤ ℓ := (Fact.out : Nat.Prime ℓ).two_le
  have h_ord_one : S.zeta_ell_int ^ 1 = 1 := by rw [pow_one]; exact h1
  have h_ord_dvd : ℓ ∣ 1 := h_prim.dvd_of_pow_eq_one 1 h_ord_one
  have : ℓ ≤ 1 := Nat.le_of_dvd (by omega) h_ord_dvd
  omega

/-- The rational prime `ℓ` has at least `ℓ - 1` units of `Q`-adic order. -/
theorem natCast_ell_mem_Q_pow_pred :
    (ℓ : 𝓞 R') ∈ S.Q ^ (ℓ - 1) := by
  have hassoc :
      Associated (ℓ : 𝓞 R') ((S.zeta_ell_int - 1) ^ (ℓ - 1)) :=
    associated_ell_zeta_sub_one_pow S.concrete.zeta_ell_int_isPrimitiveRoot
  have hzeta_mem : (S.zeta_ell_int - 1) ^ (ℓ - 1) ∈ S.Q ^ (ℓ - 1) := by
    have hζ_sub_mem : S.zeta_ell_int - 1 ∈ S.Q := by
      rw [← S.hπ]
      exact S.concrete.π_mem_Q
    exact Ideal.pow_mem_pow hζ_sub_mem (ℓ - 1)
  exact (associated_mem_ideal_iff hassoc).2 hzeta_mem

/-- Power form of `natCast_ell_mem_Q_pow_pred`. -/
theorem natCast_ell_pow_mem_Q_pow_mul_pred (m : ℕ) :
    (ℓ : 𝓞 R') ^ m ∈ S.Q ^ (m * (ℓ - 1)) := by
  have hpow : (ℓ : 𝓞 R') ^ m ∈ (S.Q ^ (ℓ - 1)) ^ m :=
    Ideal.pow_mem_pow S.natCast_ell_mem_Q_pow_pred m
  rw [← pow_mul] at hpow
  simpa [Nat.mul_comm] using hpow

/-- If a natural coefficient is divisible by `ℓ^m`, then its image has
`Q`-adic order at least `m * (ℓ - 1)`. -/
theorem natCast_mem_Q_pow_mul_pred_of_ell_pow_dvd {c m : ℕ}
    (hc : ℓ ^ m ∣ c) :
    (c : 𝓞 R') ∈ S.Q ^ (m * (ℓ - 1)) := by
  rcases hc with ⟨t, rfl⟩
  have hpow := S.natCast_ell_pow_mem_Q_pow_mul_pred m
  have hmul : (ℓ : 𝓞 R') ^ m * (t : 𝓞 R') ∈ S.Q ^ (m * (ℓ - 1)) :=
    Ideal.mul_mem_right (t : 𝓞 R') (S.Q ^ (m * (ℓ - 1))) hpow
  simpa [Nat.cast_mul, Nat.cast_pow] using hmul

/-- Structural Dedekind-domain fact: if `π ∈ Q`, `π ∉ Q^2`, and `π ≠ 0`,
then `π^s ∉ Q^(s+1)` for any `s`. -/
theorem pi_pow_not_mem_Q_pow_succ_of_not_mem_sq
    (h_pi_ne_zero : S.π ≠ 0) (h_pi_nondeg : S.π ∉ S.Q ^ 2) (s : ℕ) :
    S.π ^ s ∉ S.Q ^ (s + 1) := by
  classical
  intro h_in
  set I : Ideal (𝓞 R') := Ideal.span ({S.π} : Set (𝓞 R')) with hI_def
  have h_span_pi_pow : Ideal.span ({S.π ^ s} : Set (𝓞 R')) = I ^ s := by
    rw [hI_def, Ideal.span_singleton_pow]
  have h_pow_le : I ^ s ≤ S.Q ^ (s + 1) := by
    rw [← h_span_pi_pow]
    exact (Ideal.span_singleton_le_iff_mem _).mpr h_in
  have hI_ne_bot : I ≠ ⊥ := by
    rw [hI_def, Ne, Ideal.span_singleton_eq_bot]
    exact h_pi_ne_zero
  have hI_pow_ne_bot : I ^ s ≠ ⊥ := pow_ne_zero s hI_ne_bot
  have hI_le_Q : I ≤ S.Q :=
    (Ideal.span_singleton_le_iff_mem _).mpr S.concrete.π_mem_Q
  have hI_not_le_Qsq : ¬ I ≤ S.Q ^ 2 := fun h =>
    h_pi_nondeg <| h <| Ideal.mem_span_singleton_self S.π
  have h_count_I : Multiset.count S.Q
      (UniqueFactorizationMonoid.normalizedFactors I) = 1 := by
    have h_le_one : I ≤ S.Q ^ 1 := by simpa using hI_le_Q
    exact Ideal.count_normalizedFactors_eq h_le_one hI_not_le_Qsq
  have h_count_Is : Multiset.count S.Q
      (UniqueFactorizationMonoid.normalizedFactors (I ^ s)) = s := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.count_nsmul, h_count_I, mul_one]
  have hQ_irr : Irreducible S.Q := by
    have hQp : Prime S.Q := Ideal.prime_of_isPrime S.Q_ne_bot S.Q_isPrime
    exact hQp.irreducible
  have h_count_Qpow : s + 1 ≤ Multiset.count S.Q
      (UniqueFactorizationMonoid.normalizedFactors (S.Q ^ (s + 1))) := by
    rw [UniqueFactorizationMonoid.normalizedFactors_pow,
      Multiset.count_nsmul]
    have h1 : 1 ≤ Multiset.count S.Q
        (UniqueFactorizationMonoid.normalizedFactors S.Q) := by
      rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hQ_irr,
        normalize_eq, Multiset.count_singleton_self]
    nlinarith
  have hcount := Ideal.count_le_of_ideal_ge h_pow_le hI_pow_ne_bot S.Q
  omega

end ConductorFlexibleTraceFormStickelbergerSetup

namespace ConductorFlexibleFullTeichStickelbergerSetup

variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']

variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')

/-- The selected prime `Q` is maximal. -/
theorem Q_isMaximal : F.Q.IsMaximal := by
  have h := F.concrete.Q_isMaximal
  simpa [ConductorFlexibleFullTeichStickelbergerSetup.concrete,
    ConductorFlexibleTraceFormStickelbergerSetup.concrete] using h

/-- Elements outside `Q` become units modulo every positive power of `Q`. -/
theorem quotient_mk_isUnit_of_not_mem_Q (N : ℕ) {s : 𝓞 R'} (hs : s ∉ F.Q) :
    IsUnit (Ideal.Quotient.mk (F.Q ^ (N + 1)) s) := by
  haveI : F.Q.IsMaximal := F.Q_isMaximal
  exact (Ideal.Quotient.isUnit_mk_pow_iff_notMem (I := F.Q)
    (n := N + 1) (Nat.succ_ne_zero N)).2 hs

/-- The canonical unit in `𝓞 R' / Q^(N+1)` attached to an element outside
`Q`. -/
noncomputable def quotientUnitOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ F.Q) : (𝓞 R' ⧸ F.Q ^ (N + 1))ˣ :=
  (F.quotient_mk_isUnit_of_not_mem_Q N hs).unit

@[simp]
theorem quotientUnitOfNotMemQ_coe (N : ℕ) (s : 𝓞 R') (hs : s ∉ F.Q) :
    (F.quotientUnitOfNotMemQ N s hs : 𝓞 R' ⧸ F.Q ^ (N + 1)) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) s :=
  (F.quotient_mk_isUnit_of_not_mem_Q N hs).unit_spec

/-- The chosen inverse of an element outside `Q` in the quotient by
`Q^(N+1)`. -/
noncomputable def quotientInvOfNotMemQ (N : ℕ) (s : 𝓞 R') (hs : s ∉ F.Q) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  ((F.quotientUnitOfNotMemQ N s hs)⁻¹ : (𝓞 R' ⧸ F.Q ^ (N + 1))ˣ)

theorem quotient_mk_mul_quotientInvOfNotMemQ
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) s *
        F.quotientInvOfNotMemQ N s hs = 1 := by
  simp [quotientInvOfNotMemQ]

theorem quotientInvOfNotMemQ_mul_quotient_mk
    (N : ℕ) (s : 𝓞 R') (hs : s ∉ F.Q) :
    F.quotientInvOfNotMemQ N s hs *
        Ideal.Quotient.mk (F.Q ^ (N + 1)) s = 1 := by
  simp [quotientInvOfNotMemQ]

/-- The quotient map sends every local denominator away from `Q` to a unit. -/
theorem quotient_mk_isUnit_primeCompl
    (N : ℕ) (s : F.Q.primeCompl) :
    IsUnit (Ideal.Quotient.mk (F.Q ^ (N + 1)) (s : 𝓞 R')) :=
  F.quotient_mk_isUnit_of_not_mem_Q N s.property

/-- The canonical map from the localization of `𝓞 R'` away from `Q` to the
finite quotient `𝓞 R' / Q^(N+1)`. -/
noncomputable def quotientLocalizationAwayQMap (N : ℕ) :
    Localization F.Q.primeCompl →+* (𝓞 R' ⧸ F.Q ^ (N + 1)) :=
  IsLocalization.lift
    (M := F.Q.primeCompl)
    (S := Localization F.Q.primeCompl)
    (P := 𝓞 R' ⧸ F.Q ^ (N + 1))
    (g := Ideal.Quotient.mk (F.Q ^ (N + 1)))
    (fun s => F.quotient_mk_isUnit_primeCompl N s)

@[simp]
theorem quotientLocalizationAwayQMap_algebraMap
    (N : ℕ) (x : 𝓞 R') :
    F.quotientLocalizationAwayQMap N
        (algebraMap (𝓞 R') (Localization F.Q.primeCompl) x) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x := by
  simp [quotientLocalizationAwayQMap,
    (IsLocalization.lift_eq
      (M := F.Q.primeCompl)
      (S := Localization F.Q.primeCompl)
      (P := 𝓞 R' ⧸ F.Q ^ (N + 1))
      (g := Ideal.Quotient.mk (F.Q ^ (N + 1)))
      (fun s => F.quotient_mk_isUnit_primeCompl N s)
      x)]

/-- Evaluate a local fraction with denominator away from `Q` in the finite
quotient. -/
noncomputable def quotientFractionEvalPrimeCompl
    (N : ℕ) (x : 𝓞 R') (s : F.Q.primeCompl) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  F.quotientLocalizationAwayQMap N
    (IsLocalization.mk' (Localization F.Q.primeCompl) x s)

/-- Evaluate a local fraction with an explicit proof that the denominator is
outside `Q`. -/
noncomputable def quotientFractionEval
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ F.Q) :
    𝓞 R' ⧸ F.Q ^ (N + 1) :=
  F.quotientFractionEvalPrimeCompl N x ⟨s, hs⟩

@[simp]
theorem quotientFractionEvalPrimeCompl_one
    (N : ℕ) (x : 𝓞 R') :
    F.quotientFractionEvalPrimeCompl N x 1 =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x := by
  simpa [quotientFractionEvalPrimeCompl] using
    congrArg (F.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_one
        (S := Localization F.Q.primeCompl)
        x)

theorem quotientFractionEvalPrimeCompl_den_mul
    (N : ℕ) (x : 𝓞 R') (s : F.Q.primeCompl) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (s : 𝓞 R') *
        F.quotientFractionEvalPrimeCompl N x s =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x := by
  have h :
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x =
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (s : 𝓞 R') *
          F.quotientFractionEvalPrimeCompl N x s :=
    (IsLocalization.lift_mk'_spec
        (M := F.Q.primeCompl)
        (S := Localization F.Q.primeCompl)
        (P := 𝓞 R' ⧸ F.Q ^ (N + 1))
        (g := Ideal.Quotient.mk (F.Q ^ (N + 1)))
        (hg := fun t => F.quotient_mk_isUnit_primeCompl N t)
        x
        (F.quotientFractionEvalPrimeCompl N x s)
        s).1 (by
          simp [quotientFractionEvalPrimeCompl, quotientLocalizationAwayQMap])
  exact h.symm

theorem quotientFractionEval_den_mul
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ F.Q) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) s *
        F.quotientFractionEval N x s hs =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x := by
  simpa [quotientFractionEval] using
    F.quotientFractionEvalPrimeCompl_den_mul N x ⟨s, hs⟩

theorem quotientFractionEval_eq_mk_mul_inv
    (N : ℕ) (x s : 𝓞 R') (hs : s ∉ F.Q) :
    F.quotientFractionEval N x s hs =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x *
        F.quotientInvOfNotMemQ N s hs := by
  apply (F.quotient_mk_isUnit_of_not_mem_Q N hs).mul_left_inj.mp
  rw [mul_comm (F.quotientFractionEval N x s hs),
    F.quotientFractionEval_den_mul N x s hs]
  rw [mul_assoc, F.quotientInvOfNotMemQ_mul_quotient_mk N s hs, mul_one]

theorem quotientFractionEvalPrimeCompl_add
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : F.Q.primeCompl) :
    F.quotientFractionEvalPrimeCompl N
        (x₁ * (s₂ : 𝓞 R') + x₂ * (s₁ : 𝓞 R')) (s₁ * s₂) =
      F.quotientFractionEvalPrimeCompl N x₁ s₁ +
        F.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_add] using
    congrArg (F.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_add
        (S := Localization F.Q.primeCompl)
        x₁ x₂ s₁ s₂)

theorem quotientFractionEvalPrimeCompl_mul
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : F.Q.primeCompl) :
    F.quotientFractionEvalPrimeCompl N (x₁ * x₂) (s₁ * s₂) =
      F.quotientFractionEvalPrimeCompl N x₁ s₁ *
        F.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_mul] using
    congrArg (F.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_mul
        (S := Localization F.Q.primeCompl)
        x₁ x₂ s₁ s₂)

theorem quotientFractionEvalPrimeCompl_neg
    (N : ℕ) (x : 𝓞 R') (s : F.Q.primeCompl) :
    F.quotientFractionEvalPrimeCompl N (-x) s =
      -F.quotientFractionEvalPrimeCompl N x s := by
  simpa [quotientFractionEvalPrimeCompl, map_neg] using
    congrArg (F.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_neg
        (S := Localization F.Q.primeCompl)
        x s)

theorem quotientFractionEvalPrimeCompl_sub
    (N : ℕ) (x₁ x₂ : 𝓞 R') (s₁ s₂ : F.Q.primeCompl) :
    F.quotientFractionEvalPrimeCompl N
        (x₁ * (s₂ : 𝓞 R') - x₂ * (s₁ : 𝓞 R')) (s₁ * s₂) =
      F.quotientFractionEvalPrimeCompl N x₁ s₁ -
        F.quotientFractionEvalPrimeCompl N x₂ s₂ := by
  simpa [quotientFractionEvalPrimeCompl, map_sub] using
    congrArg (F.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_sub
        (S := Localization F.Q.primeCompl)
        x₁ x₂ s₁ s₂)

theorem quotientFractionEvalPrimeCompl_pow
    (N : ℕ) (x : 𝓞 R') (s : F.Q.primeCompl) (m : ℕ) :
    F.quotientFractionEvalPrimeCompl N (x ^ m) (s ^ m) =
      F.quotientFractionEvalPrimeCompl N x s ^ m := by
  simpa [quotientFractionEvalPrimeCompl, map_pow] using
    congrArg (F.quotientLocalizationAwayQMap N)
      (IsLocalization.mk'_pow
        (S := Localization F.Q.primeCompl)
        x s m)

theorem quotientFractionEvalPrimeCompl_eq_zero_of_mem
    (N : ℕ) {x : 𝓞 R'} (s : F.Q.primeCompl)
    (hx : x ∈ F.Q ^ (N + 1)) :
    F.quotientFractionEvalPrimeCompl N x s = 0 := by
  apply (F.quotient_mk_isUnit_primeCompl N s).mul_left_inj.mp
  rw [zero_mul, mul_comm (F.quotientFractionEvalPrimeCompl N x s),
    F.quotientFractionEvalPrimeCompl_den_mul N x s]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hx

theorem quotientFractionEvalPrimeCompl_eq_of_sub_mem
    (N : ℕ) {x y : 𝓞 R'} (s : F.Q.primeCompl)
    (hxy : x - y ∈ F.Q ^ (N + 1)) :
    F.quotientFractionEvalPrimeCompl N x s =
      F.quotientFractionEvalPrimeCompl N y s := by
  apply (F.quotient_mk_isUnit_primeCompl N s).mul_left_inj.mp
  rw [mul_comm (F.quotientFractionEvalPrimeCompl N x s),
    F.quotientFractionEvalPrimeCompl_den_mul N x s,
    mul_comm (F.quotientFractionEvalPrimeCompl N y s),
    F.quotientFractionEvalPrimeCompl_den_mul N y s]
  exact Ideal.Quotient.eq.mpr hxy

/-- A natural number coprime to `ℓ` is a `Q`-unit in the full flexible setup. -/
theorem natCast_not_mem_Q_of_coprime_ell {m : ℕ} (hm : m.Coprime ℓ) :
    (m : 𝓞 R') ∉ F.Q :=
  F.concrete.natCast_not_mem_Q_of_coprime_ell hm

/-- Denominators of `ℓ`-integral rationals are units modulo every power of
`Q` in the full flexible quotient. -/
theorem rIntegralRat_den_isUnit_mod_Q_pow
    (N : ℕ) (q : DieudonneDwork.rIntegralRatSubring ℓ) :
    IsUnit
      (Ideal.Quotient.mk (F.Q ^ (N + 1))
        ((((q : ℚ).den : ℕ) : 𝓞 R'))) :=
  F.quotient_mk_isUnit_of_not_mem_Q N
    (F.natCast_not_mem_Q_of_coprime_ell
      (show (((q : ℚ).den : ℕ).Coprime ℓ) from q.property))

/-- Full-setup quotient map for `ℓ`-integral rationals. -/
noncomputable def rIntegralRatToQuotient (N : ℕ) :
    DieudonneDwork.rIntegralRatSubring ℓ →+*
      (𝓞 R' ⧸ F.Q ^ (N + 1)) :=
  F.concrete.rIntegralRatToQuotient N

theorem rIntegralRatToQuotient_den_mul
    (N : ℕ) (q : DieudonneDwork.rIntegralRatSubring ℓ) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((((q : ℚ).den : ℕ) : 𝓞 R')) *
        F.rIntegralRatToQuotient N q =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (((q : ℚ).num : ℤ) : 𝓞 R') := by
  rw [rIntegralRatToQuotient]
  exact F.concrete.rIntegralRatToQuotient_den_mul N q

/-- Precision-reduction compatibility for the full-setup quotient coefficient
maps. -/
theorem rIntegralRatToQuotient_factor_comp
    {M N : ℕ} (hMN : M ≤ N) :
    (Ideal.Quotient.factor
        (Ideal.pow_le_pow_right (Nat.succ_le_succ hMN))).comp
      (F.rIntegralRatToQuotient N) =
    F.rIntegralRatToQuotient M := by
  rw [rIntegralRatToQuotient, rIntegralRatToQuotient]
  exact F.concrete.rIntegralRatToQuotient_factor_comp hMN

/-- Powers of the rational residue characteristic have exactly the expected
`Q`-adic order coming from `ℓ ~ (ζ_ℓ - 1)^(ℓ-1)`. -/
theorem natCast_ell_pow_not_mem_Q_pow_mul_pred_succ (m : ℕ) :
    ((ℓ : 𝓞 R') ^ m) ∉ F.Q ^ (m * (ℓ - 1) + 1) := by
  have hassoc :
      Associated ((ℓ : 𝓞 R') ^ m) (F.π ^ (m * (ℓ - 1))) := by
    have h :=
      (associated_ell_zeta_sub_one_pow
        F.concrete.zeta_ell_int_isPrimitiveRoot).pow_pow (n := m)
    have hπpow :
        Associated (((F.zeta_ell_int - 1) ^ (ℓ - 1)) ^ m)
          (F.π ^ (m * (ℓ - 1))) := by
      rw [F.hπ, ← pow_mul]
      rw [Nat.mul_comm (ℓ - 1) m]
    exact h.trans hπpow
  intro hmem
  have hpi_mem : F.π ^ (m * (ℓ - 1)) ∈ F.Q ^ (m * (ℓ - 1) + 1) :=
    (associated_mem_ideal_iff hassoc).1 hmem
  exact
    F.toConductorFlexibleTraceFormStickelbergerSetup.pi_pow_not_mem_Q_pow_succ_of_not_mem_sq
      F.toConductorFlexibleTraceFormStickelbergerSetup.pi_ne_zero
      F.toConductorFlexibleTraceFormStickelbergerSetup.pi_not_mem_Q_sq
      (m * (ℓ - 1)) hpi_mem

/-- Exact `Q`-adic cancellation for powers of the rational residue
characteristic. -/
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
      F.toConductorFlexibleTraceFormStickelbergerSetup.natCast_ell_pow_mem_Q_pow_mul_pred m
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
      Ideal.prime_of_isPrime F.toConductorFlexibleTraceFormStickelbergerSetup.Q_ne_bot
        F.toConductorFlexibleTraceFormStickelbergerSetup.Q_isPrime
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
    pow_ne_zero n F.toConductorFlexibleTraceFormStickelbergerSetup.Q_ne_bot
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

/-- A fraction with numerator already divisible by its away-from-`Q`
denominator evaluates to the expected quotient class. -/
theorem quotientFractionEvalPrimeCompl_den_mul_eq_mk
    (N : ℕ) (x : 𝓞 R') (d : F.Q.primeCompl) :
    F.quotientFractionEvalPrimeCompl N
        ((d : 𝓞 R') * x) d =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x := by
  rw [show
      F.quotientFractionEvalPrimeCompl N
          ((d : 𝓞 R') * x) d =
        F.quotientFractionEval N
          ((d : 𝓞 R') * x) (d : 𝓞 R') d.property from rfl]
  rw [F.quotientFractionEval_eq_mk_mul_inv]
  rw [map_mul, mul_assoc,
    mul_comm (Ideal.Quotient.mk (F.Q ^ (N + 1)) x),
    ← mul_assoc,
    F.quotient_mk_mul_quotientInvOfNotMemQ,
    one_mul]

/-- Multiplying the evaluated local fraction `y / d` by `ℓ^m` gives the
evaluation of `(ℓ^m * y) / d`. -/
theorem quotient_natCast_ell_pow_mul_fractionEvalPrimeCompl
    (N m : ℕ) (y : 𝓞 R') (d : F.Q.primeCompl) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((ℓ : 𝓞 R') ^ m) *
        F.quotientFractionEvalPrimeCompl N y d =
      F.quotientFractionEvalPrimeCompl N
        (((ℓ : 𝓞 R') ^ m) * y) d := by
  simpa [one_mul] using
    (F.quotientFractionEvalPrimeCompl_mul
      N ((ℓ : 𝓞 R') ^ m) y 1 d).symm

/-- If `ℓ^m * y = d * x` with `d ∉ Q`, then `y / d` is the quotient-level
local value of `x / ℓ^m`. -/
theorem quotient_natCast_ell_pow_mul_fractionEvalPrimeCompl_eq_mk_of_eq
    (N m : ℕ) {x y : 𝓞 R'} {d : F.Q.primeCompl}
    (hxy : ((ℓ : 𝓞 R') ^ m) * y = (d : 𝓞 R') * x) :
    Ideal.Quotient.mk (F.Q ^ (N + 1)) ((ℓ : 𝓞 R') ^ m) *
        F.quotientFractionEvalPrimeCompl N y d =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) x := by
  rw [F.quotient_natCast_ell_pow_mul_fractionEvalPrimeCompl N m y d, hxy]
  exact F.quotientFractionEvalPrimeCompl_den_mul_eq_mk N x d

/-- Local existence of the quotient by `ℓ^m`: if `x` has at least
`m * (ℓ - 1)` extra `Q`-adic order, then `x / ℓ^m` is represented in the
localization at `Q` by a fraction `y / d` with `d ∉ Q`. -/
theorem exists_primeCompl_natCast_ell_pow_denom_of_mem_Q_pow
    (m s : ℕ) {x : 𝓞 R'}
    (hx : x ∈ F.Q ^ (m * (ℓ - 1) + s)) :
    ∃ y : 𝓞 R', ∃ d : F.Q.primeCompl,
      ((ℓ : 𝓞 R') ^ m) * y = (d : 𝓞 R') * x ∧ y ∈ F.Q ^ s := by
  classical
  by_cases hx0 : x = 0
  · subst x
    refine ⟨0, 1, ?_, by simp⟩
    simp
  let v : HeightOneSpectrum (𝓞 R') :=
    { asIdeal := F.Q
      isPrime := F.toConductorFlexibleTraceFormStickelbergerSetup.Q_isPrime
      ne_bot := F.toConductorFlexibleTraceFormStickelbergerSetup.Q_ne_bot }
  let r : ℕ := m * (ℓ - 1)
  let e : 𝓞 R' := (ℓ : 𝓞 R') ^ m
  have he_ne : e ≠ 0 :=
    pow_ne_zero m (Nat.cast_ne_zero.mpr (Fact.out : Nat.Prime ℓ).ne_zero)
  have hval_x :
      v.intValuation x ≤ exp (-(r : ℤ)) := by
    have hx' : x ∈ v.asIdeal ^ (r + s) := by
      simpa [v, r, Nat.add_comm] using hx
    have hmain := (v.intValuation_le_pow_iff_mem x (r + s)).2 hx'
    refine hmain.trans ?_
    rw [exp_le_exp]
    omega
  have he_mem : e ∈ F.Q ^ r := by
    simpa [e, r] using
      F.toConductorFlexibleTraceFormStickelbergerSetup.natCast_ell_pow_mem_Q_pow_mul_pred m
  have he_not_mem : e ∉ F.Q ^ (r + 1) := by
    simpa [e, r, Nat.add_comm] using
      F.natCast_ell_pow_not_mem_Q_pow_mul_pred_succ m
  let Ie : Ideal (𝓞 R') := Ideal.span ({e} : Set (𝓞 R'))
  have hIe_le : Ie ≤ F.Q ^ r := by
    rw [Ideal.span_singleton_le_iff_mem]
    exact he_mem
  have hIe_not_le : ¬ Ie ≤ F.Q ^ (r + 1) := fun hle =>
    he_not_mem (hle (Ideal.mem_span_singleton_self e))
  have hIe_count :
      Multiset.count F.Q (UniqueFactorizationMonoid.normalizedFactors Ie) = r :=
    Ideal.count_normalizedFactors_eq hIe_le hIe_not_le
  have hIe_ne : Ie ≠ ⊥ := by
    change Ideal.span ({e} : Set (𝓞 R')) ≠ ⊥
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hval_e :
      v.intValuation e = exp (-(r : ℤ)) := by
    rw [v.intValuation_if_neg he_ne]
    have hcount_assoc :
        (Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span ({e} : Set (𝓞 R')) : Ideal (𝓞 R'))).factors = r := by
      rw [Ideal.count_associates_factors_eq]
      · simpa [v, Ie] using hIe_count
      · simpa [Ie] using hIe_ne
      · exact F.toConductorFlexibleTraceFormStickelbergerSetup.Q_isPrime
      · exact F.toConductorFlexibleTraceFormStickelbergerSetup.Q_ne_bot
    rw [hcount_assoc]
  have hquot_val :
      v.valuation R' (algebraMap (𝓞 R') R' x / algebraMap (𝓞 R') R' e) ≤ 1 := by
    simpa [div_eq_mul_inv, v.valuation_of_algebraMap (K := R'), hval_e] using
      div_le_one_of_le₀ hval_x zero_le
  obtain ⟨y, d, hfrac⟩ :=
    v.exists_primeCompl_mul_eq_of_integer (K := R')
      (algebraMap (𝓞 R') R' x / algebraMap (𝓞 R') R' e) hquot_val
  have hfield :
      algebraMap (𝓞 R') R' (e * y) =
        algebraMap (𝓞 R') R' ((d : 𝓞 R') * x) := by
    have he_field_ne : algebraMap (𝓞 R') R' e ≠ 0 :=
      NumberField.RingOfIntegers.coe_ne_zero_iff.mpr he_ne
    calc
      algebraMap (𝓞 R') R' (e * y)
          = algebraMap (𝓞 R') R' y * algebraMap (𝓞 R') R' e := by
            rw [map_mul]
            ring
      _ = ((algebraMap (𝓞 R') R' x / algebraMap (𝓞 R') R' e) *
              algebraMap (𝓞 R') R' (d : 𝓞 R')) *
            algebraMap (𝓞 R') R' e := by
            rw [hfrac]
      _ = algebraMap (𝓞 R') R' ((d : 𝓞 R') * x) := by
            rw [map_mul]
            field_simp [he_field_ne]
  have hxy : e * y = (d : 𝓞 R') * x :=
    NumberField.RingOfIntegers.coe_injective hfield
  refine ⟨y, d, hxy, ?_⟩
  refine F.mem_Q_pow_of_natCast_ell_pow_mul_mem_Q_pow_add_mul_pred
    (m := m) (n := s) ?_
  rw [show ((ℓ : 𝓞 R') ^ m) = e from rfl, hxy]
  exact Ideal.mul_mem_left (F.Q ^ (m * (ℓ - 1) + s)) (d : 𝓞 R') hx

/-- Exact `Q`-adic order of `(ℓ)^m`: after cancelling the local denominator
`ℓ^m`, a represented local fraction has the predicted `Q`-adic order in the
finite quotient. -/
theorem quotientFractionEvalPrimeCompl_mem_map_Q_pow_of_natCast_ell_pow_mul_mem
    (N m s : ℕ) {y : 𝓞 R'} (d : F.Q.primeCompl)
    (hy : ((ℓ : 𝓞 R') ^ m) * y ∈ F.Q ^ (m * (ℓ - 1) + s)) :
    F.quotientFractionEvalPrimeCompl N y d ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ s) := by
  have hy_mem :
      y ∈ F.Q ^ s :=
    F.mem_Q_pow_of_natCast_ell_pow_mul_mem_Q_pow_add_mul_pred
      (m := m) (n := s) hy
  rw [show
      F.quotientFractionEvalPrimeCompl N y d =
        F.quotientFractionEval N y (d : 𝓞 R') d.property
      from rfl]
  rw [F.quotientFractionEval_eq_mk_mul_inv]
  exact
    (Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ s)).mul_mem_right
      (F.quotientInvOfNotMemQ N (d : 𝓞 R') d.property)
      (Ideal.mem_map_of_mem (Ideal.Quotient.mk (F.Q ^ (N + 1))) hy_mem)

/-- Usable local-denominator form: if a high-order numerator `x` is represented
locally as `ℓ^m * y = d * x` with `d ∉ Q`, then the quotient image of
`y / d = x / ℓ^m` lies in `Q^s / Q^(N+1)`. -/
theorem quotientFractionEvalPrimeCompl_mem_map_Q_pow_of_natCast_ell_pow_eq
    (N m s : ℕ) {x y : 𝓞 R'} {d : F.Q.primeCompl}
    (hxy : ((ℓ : 𝓞 R') ^ m) * y = (d : 𝓞 R') * x)
    (hx : x ∈ F.Q ^ (m * (ℓ - 1) + s)) :
    F.quotientFractionEvalPrimeCompl N y d ∈
      Ideal.map (Ideal.Quotient.mk (F.Q ^ (N + 1))) (F.Q ^ s) := by
  refine F.quotientFractionEvalPrimeCompl_mem_map_Q_pow_of_natCast_ell_pow_mul_mem
    N m s d ?_
  rw [hxy]
  exact Ideal.mul_mem_left (F.Q ^ (m * (ℓ - 1) + s)) (d : 𝓞 R') hx

end ConductorFlexibleFullTeichStickelbergerSetup

end Furtwaengler

end BernoulliRegular
