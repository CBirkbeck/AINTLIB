module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part13

@[expose] public section

noncomputable section

open scoped NumberField Topology

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

open Furtwaengler.KummerArtinHasse

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

theorem dworkParameterPowerLinearMap_coeff_mem_primeIdeal_of_eq_zero
    {a : Fin (p - 1) → RationalPadicIntegerRing p}
    (ha : dworkParameterPowerLinearMap p K a = 0)
    (i : Fin (p - 1)) :
    a i ∈ rationalPadicPrimeIdeal p := by
  classical
  let R₀ : Type := RationalPadicIntegerRing p
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal S := dworkParameterIdeal p K
  let varpi : S := dworkParameter p K
  let term : Fin (p - 1) → S :=
    fun j => algebraMap R₀ S (a j) * varpi ^ (j : ℕ)
  have hsum_zero : ∑ j : Fin (p - 1), term j = 0 := by
    simpa [term, R₀, S, varpi, dworkParameterPowerLinearMap_apply] using ha
  have hmem_varpi : varpi ∈ I := by
    dsimp [I, varpi, dworkParameterIdeal]
    exact Ideal.mem_span_singleton_self (dworkParameter p K)
  have hmain :
      ∀ n : ℕ, ∀ i : Fin (p - 1), (i : ℕ) = n →
        a i ∈ rationalPadicPrimeIdeal p := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro i hi
        let Jpow : Ideal S := I ^ ((i : ℕ) + 1)
        have htotal : (∑ j : Fin (p - 1), term j) ∈ Jpow := by
          rw [hsum_zero]
          exact Ideal.zero_mem Jpow
        have hother :
            (∑ j ∈ (Finset.univ.erase i), term j) ∈ Jpow := by
          refine Ideal.sum_mem _ ?_
          intro j hj
          have hji : j ≠ i := (Finset.mem_erase.mp hj).1
          have hne_nat : (j : ℕ) ≠ (i : ℕ) := fun hnat =>
            hji (Fin.ext hnat)
          have hlt_or_gt : (j : ℕ) < (i : ℕ) ∨ (i : ℕ) < (j : ℕ) := by
            omega
          cases hlt_or_gt with
          | inl hlt =>
              have haj : a j ∈ rationalPadicPrimeIdeal p :=
                ih (j : ℕ) (by omega) j rfl
              have hcoeff :
                  algebraMap R₀ S (a j) ∈ I ^ (p - 1) := by
                simpa [R₀, S, I, one_mul] using
                  algebraMap_mem_dworkParameterIdeal_pow_mul_pred_of_mem_rationalPadicPrimeIdeal_pow
                    (p := p) (K := K) (q := 1)
                    (by simpa [pow_one] using haj)
              have hpow : varpi ^ (j : ℕ) ∈ I ^ (j : ℕ) :=
                Ideal.pow_mem_pow hmem_varpi (j : ℕ)
              have hmul : term j ∈ I ^ (p - 1) * I ^ (j : ℕ) :=
                Ideal.mul_mem_mul hcoeff hpow
              have hmul' : term j ∈ I ^ ((p - 1) + (j : ℕ)) := by
                rw [← pow_add] at hmul
                exact hmul
              have hle : (i : ℕ) + 1 ≤ (p - 1) + (j : ℕ) := by
                have hi_lt : (i : ℕ) < p - 1 := i.2
                omega
              exact Ideal.pow_le_pow_right hle hmul'
          | inr hgt =>
              have hpow : varpi ^ (j : ℕ) ∈ I ^ (j : ℕ) :=
                Ideal.pow_mem_pow hmem_varpi (j : ℕ)
              have hterm : term j ∈ I ^ (j : ℕ) :=
                (I ^ (j : ℕ)).mul_mem_left (algebraMap R₀ S (a j)) hpow
              have hle : (i : ℕ) + 1 ≤ (j : ℕ) := by
                omega
              exact Ideal.pow_le_pow_right hle hterm
        have hterm_i : term i ∈ Jpow := by
          have hdecomp :
              term i + (∑ j ∈ (Finset.univ.erase i), term j) =
                ∑ j : Fin (p - 1), term j :=
            Finset.add_sum_erase Finset.univ term (Finset.mem_univ i)
          have hcalc :
              term i =
                (∑ j : Fin (p - 1), term j) -
                  (∑ j ∈ (Finset.univ.erase i), term j) := by
            rw [← hdecomp]
            abel
          rw [hcalc]
          exact Ideal.sub_mem Jpow htotal hother
        have hspan :
            term i ∈ Ideal.span ({varpi ^ ((i : ℕ) + 1)} : Set S) := by
          simpa [Jpow, I, varpi, dworkParameterIdeal, Ideal.span_singleton_pow] using hterm_i
        rcases Ideal.mem_span_singleton'.mp hspan with ⟨y, hy⟩
        have hzero :
            varpi ^ (i : ℕ) *
              (algebraMap R₀ S (a i) - y * varpi) = 0 := by
          have hy' :
              algebraMap R₀ S (a i) * varpi ^ (i : ℕ) =
                y * varpi ^ ((i : ℕ) + 1) := by
            simpa [term, varpi] using hy.symm
          have hcalc :
              varpi ^ (i : ℕ) *
                  (algebraMap R₀ S (a i) - y * varpi) =
                algebraMap R₀ S (a i) * varpi ^ (i : ℕ) -
                  y * varpi ^ ((i : ℕ) + 1) := by
            ring
          rw [hcalc, hy', sub_self]
        have hcancel :
            algebraMap R₀ S (a i) - y * varpi = 0 :=
          dworkParameter_pow_regular (p := p) (K := K) (i : ℕ) hzero
        have hcoeff_mem : algebraMap R₀ S (a i) ∈ I := by
          have heq : algebraMap R₀ S (a i) = y * varpi :=
            sub_eq_zero.mp hcancel
          rw [heq]
          exact I.mul_mem_left y hmem_varpi
        exact rationalPadicInteger_mem_primeIdeal_of_algebraMap_mem_dworkParameterIdeal
          (p := p) (K := K) (c := a i) (by simpa [I, R₀, S] using hcoeff_mem)
  exact hmain (i : ℕ) i rfl

theorem dworkParameterPowerLinearMap_mem_primeIdeal_smul_top_of_eq_zero
    {a : Fin (p - 1) → RationalPadicIntegerRing p}
    (ha : dworkParameterPowerLinearMap p K a = 0) :
    a ∈ rationalPadicPrimeIdeal p •
      (⊤ : Submodule (RationalPadicIntegerRing p)
        (Fin (p - 1) → RationalPadicIntegerRing p)) :=
  pi_mem_ideal_smul_top_of_forall_mem (rationalPadicPrimeIdeal p)
    (fun i => dworkParameterPowerLinearMap_coeff_mem_primeIdeal_of_eq_zero
      (p := p) (K := K) ha i)

theorem exists_natCast_prime_smul_eq_of_mem_primeIdeal_smul_top
    {a : Fin (p - 1) → RationalPadicIntegerRing p}
    (ha : a ∈ rationalPadicPrimeIdeal p •
      (⊤ : Submodule (RationalPadicIntegerRing p)
        (Fin (p - 1) → RationalPadicIntegerRing p))) :
    ∃ b : Fin (p - 1) → RationalPadicIntegerRing p,
      (p : RationalPadicIntegerRing p) • b = a := by
  classical
  have hcoord : ∀ i, a i ∈ rationalPadicPrimeIdeal p :=
    fun i => pi_apply_mem_of_mem_ideal_smul_top (rationalPadicPrimeIdeal p) ha i
  have hdiv : ∀ i, ∃ b : RationalPadicIntegerRing p,
      (p : RationalPadicIntegerRing p) * b = a i := by
    intro i
    have hi : a i ∈ Ideal.span ({(p : RationalPadicIntegerRing p)} :
        Set (RationalPadicIntegerRing p)) := by
      simpa [rationalPadicPrimeIdeal] using hcoord i
    rcases Ideal.mem_span_singleton'.mp hi with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    simpa [mul_comm] using hb
  choose b hb using hdiv
  refine ⟨b, ?_⟩
  ext i
  simpa [Pi.smul_apply, smul_eq_mul] using congrArg Subtype.val (hb i)

theorem dworkParameterPowerLinearMap_eq_zero_of_natCast_prime_smul_eq
    {a b : Fin (p - 1) → RationalPadicIntegerRing p}
    (hab : (p : RationalPadicIntegerRing p) • b = a)
    (ha : dworkParameterPowerLinearMap p K a = 0) :
    dworkParameterPowerLinearMap p K b = 0 := by
  have hpT :
      (p : RationalPadicIntegerRing p) •
          dworkParameterPowerLinearMap p K b = 0 := by
    rw [← map_smul, hab]
    exact ha
  apply dworkComplete_natCast_p_nsmul_eq_zero (p := p) (K := K)
  simpa [Nat.cast_smul_eq_nsmul, Algebra.smul_def] using hpT

theorem dworkParameterPowerLinearMap_kernel_mem_primeIdeal_pow_smul_top
    {a : Fin (p - 1) → RationalPadicIntegerRing p}
    (ha : dworkParameterPowerLinearMap p K a = 0) :
    ∀ n : ℕ,
      a ∈ (rationalPadicPrimeIdeal p) ^ n •
        (⊤ : Submodule (RationalPadicIntegerRing p)
          (Fin (p - 1) → RationalPadicIntegerRing p)) := by
  classical
  intro n
  let R₀ : Type := RationalPadicIntegerRing p
  let J : Ideal R₀ := rationalPadicPrimeIdeal p
  have hdata : ∀ n : ℕ,
      ∃ b : Fin (p - 1) → R₀,
        a = ((p : R₀) ^ n) • b ∧
          dworkParameterPowerLinearMap p K b = 0 := by
    intro n
    induction n with
    | zero =>
        exact ⟨a, by simp, ha⟩
    | succ n ih =>
        rcases ih with ⟨b, hb_eq, hb_zero⟩
        have hb_mem :=
          dworkParameterPowerLinearMap_mem_primeIdeal_smul_top_of_eq_zero
            (p := p) (K := K) hb_zero
        rcases exists_natCast_prime_smul_eq_of_mem_primeIdeal_smul_top
            (p := p) hb_mem with ⟨c, hc⟩
        refine ⟨c, ?_, ?_⟩
        · rw [hb_eq, ← hc]
          ext i
          simp [Pi.smul_apply, pow_succ, mul_assoc]
        · exact dworkParameterPowerLinearMap_eq_zero_of_natCast_prime_smul_eq
            (p := p) (K := K) hc hb_zero
  rcases hdata n with ⟨b, hb_eq, _hb_zero⟩
  have hp_mem : ((p : R₀) ^ n) ∈ J ^ n := by
    simp [J, rationalPadicPrimeIdeal, Ideal.span_singleton_pow]
  have hmem :
      ((p : R₀) ^ n) • b ∈
        J ^ n • (⊤ : Submodule R₀ (Fin (p - 1) → R₀)) :=
    Submodule.smul_mem_smul hp_mem trivial
  simpa [J, R₀, hb_eq] using hmem

instance instIsHausdorffRationalPadicIntegerRing :
    IsHausdorff (rationalPadicPrimeIdeal p) (RationalPadicIntegerRing p) :=
  (rationalPadicPrimeIdeal_isAdic (p := p)).isHausdorff_iff.mpr inferInstance

instance instIsHausdorffPiFinite
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (J : Ideal R) [IsHausdorff J R] :
    IsHausdorff J (ι → R) where
  haus' f hf := by
    ext i
    exact IsHausdorff.haus (I := J) (M := R)
      (show IsHausdorff J R from inferInstance) (f i) (by
        intro n
        rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
        have hmem' :
            f - 0 ∈ J ^ n • (⊤ : Submodule R (ι → R)) :=
          SModEq.sub_mem.mp (hf n)
        have hmem :
            f ∈ J ^ n • (⊤ : Submodule R (ι → R)) := by
          simpa using hmem'
        exact pi_apply_mem_of_mem_ideal_smul_top (J ^ n) hmem i)

instance instIsHausdorffRationalPadicPowerCoefficients :
    IsHausdorff (rationalPadicPrimeIdeal p)
      (Fin (p - 1) → RationalPadicIntegerRing p) :=
  inferInstance

theorem dworkParameterPowerLinearMap_injective :
    Function.Injective (dworkParameterPowerLinearMap p K) := by
  intro a b hab
  suffices a - b = 0 by
    exact sub_eq_zero.mp this
  have hker : dworkParameterPowerLinearMap p K (a - b) = 0 := by
    simp [map_sub, hab]
  exact IsHausdorff.haus
    (I := rationalPadicPrimeIdeal p)
    (M := Fin (p - 1) → RationalPadicIntegerRing p)
    (show IsHausdorff (rationalPadicPrimeIdeal p)
      (Fin (p - 1) → RationalPadicIntegerRing p) from inferInstance)
    (a - b) (by
      intro n
      rw [SModEq.zero]
      simpa using
        dworkParameterPowerLinearMap_kernel_mem_primeIdeal_pow_smul_top
          (p := p) (K := K) hker n)

theorem dworkParameterPowerLinearMap_bijective :
    Function.Bijective (dworkParameterPowerLinearMap p K) :=
  ⟨dworkParameterPowerLinearMap_injective (p := p) (K := K),
    dworkParameterPowerLinearMap_surjective (p := p) (K := K)⟩

noncomputable def dworkParameterPowerBasis :
    Module.Basis (Fin (p - 1)) (RationalPadicIntegerRing p)
      (DworkCompleteIntegerRing p K) :=
  dworkParameterPowerBasisOfBijective p K
    (dworkParameterPowerLinearMap_bijective (p := p) (K := K))

theorem dworkParameterPowerBasis_apply (i : Fin (p - 1)) :
    dworkParameterPowerBasis p K i = dworkParameter p K ^ (i : ℕ) :=
  dworkParameterPowerBasisOfBijective_apply
    (p := p) (K := K)
    (dworkParameterPowerLinearMap_bijective (p := p) (K := K)) i

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
