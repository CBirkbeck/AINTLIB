module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part12

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

def dworkParameterPowerBlock (N : ℕ) : ℕ :=
  N / (p - 1)

def dworkParameterPowerIndex (N : ℕ) : Fin (p - 1) :=
  ⟨N % (p - 1),
    Nat.mod_lt N (Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt)⟩

@[simp]
theorem dworkParameterPowerIndex_val (N : ℕ) :
    (dworkParameterPowerIndex p N : ℕ) = N % (p - 1) :=
  rfl

theorem le_dworkParameterPowerBlock_of_mul_pred_le
    {q N : ℕ} (hN : q * (p - 1) ≤ N) :
    q ≤ dworkParameterPowerBlock p N := by
  have hp_pred_pos : 0 < p - 1 :=
    Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  exact (Nat.le_div_iff_mul_le hp_pred_pos).mpr hN

theorem dworkComplete_residue_lift_rationalPadicInteger
    (x : DworkCompleteIntegerRing p K) :
    ∃ a : RationalPadicIntegerRing p,
      x - algebraMap (RationalPadicIntegerRing p)
          (DworkCompleteIntegerRing p K) a ∈ dworkParameterIdeal p K :=
  dworkComplete_residue_lift_of_valuedInteger_residue_lift
    (p := p) (K := K)
    (valuedInteger_residue_lift_rationalPadicInteger (p := p) (K := K)) x

/-- The coefficient-side `p`-adic ideal used for coherent Dwork power
approximations. -/
abbrev rationalPadicPrimeIdeal : Ideal (RationalPadicIntegerRing p) :=
  Ideal.span ({(p : RationalPadicIntegerRing p)} : Set (RationalPadicIntegerRing p))

instance instCompleteSpaceRationalPadicIntegerRing :
    CompleteSpace (RationalPadicIntegerRing p) := by
  let A : Set ((lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) :=
    {x | Valued.v x ≤ 1}
  have hA' : IsClopen
      {x : (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ |
        Valued.v.restrict x ≤ 1} :=
    Valued.isClopen_closedBall
      (R := (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)
      (r := 1) (by exact one_ne_zero)
  have hA : IsClosed A := by
    convert hA'.1 using 1
    ext x
    simp [A, Valuation.restrict_le_one_iff]
  change CompleteSpace A
  infer_instance

theorem rationalPadicPrimeIdeal_pow_eq_valuation_closedBall (n : ℕ) :
    (((rationalPadicPrimeIdeal p) ^ n :
        Ideal (RationalPadicIntegerRing p)) : Set (RationalPadicIntegerRing p)) =
      {x | Valued.v ((x : RationalPadicIntegerRing p) :
          (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ) ≤
        Valued.v (((p : RationalPadicIntegerRing p) ^ n :
          RationalPadicIntegerRing p) :
          (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)} := by
  rw [rationalPadicPrimeIdeal, Ideal.span_singleton_pow]
  simpa using
    (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
      (K := ℚ) (v := lambdaRationalHeightOneSpectrum p)).coe_span_singleton_eq_setOf_le_v_algebraMap
      ((p : RationalPadicIntegerRing p) ^ n)

theorem rationalPadicPrimeIdeal_pow_isOpen (n : ℕ) :
    IsOpen ((((rationalPadicPrimeIdeal p) ^ n :
      Ideal (RationalPadicIntegerRing p)) : Set (RationalPadicIntegerRing p))) := by
  let F : Type := (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ
  let R₀ : Type := RationalPadicIntegerRing p
  let r : MonoidWithZeroHom.ValueGroup₀
      (MonoidWithZeroHom.ofClass (Valued.v : Valuation F (WithZero (Multiplicative ℤ)))) :=
    Valued.v.restrict (((p : R₀) ^ n : R₀) : F)
  have hr : r ≠ 0 := by
    dsimp [r, F, R₀]
    change Valued.v.restrict (((p : R₀) ^ n : R₀) : F) ≠ 0
    intro h
    rw [Valuation.restrict_eq_zero_iff, Valuation.zero_iff] at h
    have hpF : ((p : R₀) : F) ≠ 0 := by
      have hpQ : (p : ℚ) ≠ 0 := by
        exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
      have hpF' : algebraMap ℚ F (p : ℚ) ≠ 0 :=
        (map_ne_zero (algebraMap ℚ F)).mpr hpQ
      simpa [R₀] using hpF'
    have hpR : (p : R₀) ≠ 0 := fun hp ↦ hpF (congrArg Subtype.val hp)
    exact pow_ne_zero n hpR (Subtype.ext h)
  have hopenF : IsOpen {x : F | Valued.v.restrict x ≤ r} :=
    Valued.isOpen_closedBall (R := F) (r := r) hr
  have hpre :
      ((fun x : R₀ ↦ (x : F)) ⁻¹' {x : F | Valued.v.restrict x ≤ r}) =
        (((rationalPadicPrimeIdeal p) ^ n : Ideal R₀) : Set R₀) := by
    ext x
    rw [Set.mem_preimage, Set.mem_setOf_eq]
    dsimp [r, R₀, F]
    rw [rationalPadicPrimeIdeal_pow_eq_valuation_closedBall (p := p) n]
    dsimp [r]
    rw [Valuation.restrict_le_iff]
  rw [← hpre]
  exact hopenF.preimage continuous_subtype_val

theorem rationalPadicInteger_natCast_prime_valuation_eq_exp_neg_one :
    Valued.v (((p : RationalPadicIntegerRing p) :
      (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)) = WithZero.exp (-1 : ℤ) := by
  let F : Type := (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  have has :
      (lambdaRationalHeightOneSpectrum p).asIdeal =
        Ideal.span ({(p : ℤ)} : Set ℤ) := by
    simp [lambdaRationalHeightOneSpectrum_asIdeal, lambdaRationalPrimeIdeal]
  have hval :
      (lambdaRationalHeightOneSpectrum p).intValuation (p : ℤ) =
        WithZero.exp (-1 : ℤ) :=
    IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
      (v := lambdaRationalHeightOneSpectrum p) hp0 has
  have hvalF : Valued.v (algebraMap ℤ F (p : ℤ)) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation]
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact hval
  simpa [F] using hvalF

theorem rationalPadicInteger_natCast_prime_valuation_lt_one :
    Valued.v (((p : RationalPadicIntegerRing p) :
      (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ)) < 1 := by
  rw [rationalPadicInteger_natCast_prime_valuation_eq_exp_neg_one (p := p)]
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  norm_num

theorem rationalPadicPrimeIdeal_eq_maximalIdeal :
    rationalPadicPrimeIdeal p =
      IsLocalRing.maximalIdeal (RationalPadicIntegerRing p) := by
  apply Ideal.ext
  intro c
  let F : Type := (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ
  let R₀ : Type := RationalPadicIntegerRing p
  have hunit : IsUnit c ↔ Valued.v ((c : R₀) : F) = 1 := by
    simpa [F, R₀] using
      (IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.integers
        (K := ℚ) (v := lambdaRationalHeightOneSpectrum p)).isUnit_iff_valuation_eq_one
        (x := c)
  have hJ : c ∈ rationalPadicPrimeIdeal p ↔
      Valued.v ((c : R₀) : F) ≤ WithZero.exp (-1 : ℤ) := by
    have h := (Set.ext_iff.mp
      (rationalPadicPrimeIdeal_pow_eq_valuation_closedBall (p := p) 1) c)
    have h' : c ∈ rationalPadicPrimeIdeal p ↔
        Valued.v ((c : R₀) : F) ≤ Valued.v (((p : R₀) : F)) := by
      simpa [pow_one, F, R₀] using h
    have hpval : Valued.v (((p : R₀) : F)) = WithZero.exp (-1 : ℤ) := by
      simpa [F, R₀] using
        rationalPadicInteger_natCast_prime_valuation_eq_exp_neg_one (p := p)
    rw [hpval] at h'
    exact h'
  constructor
  · intro hc
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit c
    intro hcunit
    have hcval : Valued.v ((c : R₀) : F) = 1 := hunit.mp hcunit
    have hcle : Valued.v ((c : R₀) : F) ≤ WithZero.exp (-1 : ℤ) := hJ.mp hc
    have hexp_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      norm_num
    have : Valued.v ((c : R₀) : F) < 1 := lt_of_le_of_lt hcle hexp_lt_one
    rw [hcval] at this
    exact (lt_self_iff_false (1 : WithZero (Multiplicative ℤ))).mp this
  · intro hcmax
    rw [IsLocalRing.mem_maximalIdeal] at hcmax
    change ¬ IsUnit c at hcmax
    rw [hJ]
    by_cases hc0 : c = 0
    · simp [hc0]
    have hvne0 : Valued.v ((c : R₀) : F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact fun h ↦ hc0 (Subtype.ext h)
    have hvle1 : Valued.v ((c : R₀) : F) ≤ 1 := c.property
    have hvne1 : Valued.v ((c : R₀) : F) ≠ 1 := fun hv1 ↦
      hcmax (hunit.mpr hv1)
    have hvlt1 : Valued.v ((c : R₀) : F) < 1 := lt_of_le_of_ne hvle1 hvne1
    have hloglt : WithZero.log (Valued.v ((c : R₀) : F)) < (0 : ℤ) := by
      rw [WithZero.log_lt_iff_lt_exp hvne0]
      simpa using hvlt1
    have hlogle : WithZero.log (Valued.v ((c : R₀) : F)) ≤ (-1 : ℤ) := by
      omega
    exact (WithZero.log_le_iff_le_exp hvne0).mp hlogle

theorem rationalPadicInteger_mem_primeIdeal_of_algebraMap_mem_dworkParameterIdeal
    {c : RationalPadicIntegerRing p}
    (hc : algebraMap (RationalPadicIntegerRing p)
        (DworkCompleteIntegerRing p K) c ∈ dworkParameterIdeal p K) :
    c ∈ rationalPadicPrimeIdeal p := by
  let R : Type _ := ValuedIntegerRing p K
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  have hxsmul :
      algebraMap (RationalPadicIntegerRing p) S c ∈
        I ^ 1 • (⊤ : Submodule R S) := by
    simpa [S, I, dworkCompleteLambdaIdeal,
      dworkParameterIdeal_eq_dworkCompleteLambdaIdeal (p := p) (K := K),
      Ideal.map_pow, pow_one] using hc
  have hxker :
      algebraMap (RationalPadicIntegerRing p) S c ∈
        LinearMap.ker (AdicCompletion.eval I R 1) := by
    rw [← AdicCompletion.pow_smul_top_eq_ker_eval
      (I := I) (M := R) (lambdaIdeal_fg (p := p) (K := K)) (n := 1)]
    exact hxsmul
  have heval :
      AdicCompletion.eval I R 1
        (algebraMap (RationalPadicIntegerRing p) S c) = 0 :=
    LinearMap.mem_ker.mp hxker
  have hle : I ^ 1 • (⊤ : Ideal R) ≤ I ^ 1 := by
    intro x hx
    simpa [smul_eq_mul, Ideal.mul_top] using hx
  have hevalA :
      AdicCompletion.evalₐ I 1
        (algebraMap (RationalPadicIntegerRing p) S c) = 0 := by
    rw [← AdicCompletion.factor_eval_eq_evalₐ
      (I := I) (R := R)
      (x := algebraMap (RationalPadicIntegerRing p) S c) hle]
    rw [heval, map_zero]
  have hvalmem : rationalPadicIntegerToValuedInteger (p := p) (K := K) c ∈ I := by
    rw [algebraMap_rationalPadicInteger_dworkComplete_apply,
      AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of] at hevalA
    have hmem1 :
        rationalPadicIntegerToValuedInteger (p := p) (K := K) c ∈ I ^ 1 :=
      Ideal.Quotient.eq_zero_iff_mem.mp hevalA
    simpa [I, pow_one] using hmem1
  by_contra hcnot
  have hcunit : IsUnit c := by
    have hcmaxnot :
        c ∉ IsLocalRing.maximalIdeal (RationalPadicIntegerRing p) := by
      rwa [← rationalPadicPrimeIdeal_eq_maximalIdeal (p := p)]
    rwa [IsLocalRing.notMem_maximalIdeal] at hcmaxnot
  have hmapunit : IsUnit (rationalPadicIntegerToValuedInteger (p := p) (K := K) c) :=
    hcunit.map (rationalPadicIntegerToValuedInteger (p := p) (K := K))
  rcases hmapunit with ⟨u, hu⟩
  have hone : (1 : ValuedIntegerRing p K) ∈ I := by
    have hmul := I.mul_mem_right (↑u⁻¹) hvalmem
    simpa [I, ← hu, mul_assoc] using hmul
  have hvalone :=
    (mem_lambdaIdeal_iff_valuation_le_exp_neg_one (p := p) (K := K)
      (1 : ValuedIntegerRing p K)).mp (by simpa [I] using hone)
  have hexp_lt_one : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have : (1 : WithZero (Multiplicative ℤ)) < 1 := by
    simpa using lt_of_le_of_lt hvalone hexp_lt_one
  exact (lt_self_iff_false (1 : WithZero (Multiplicative ℤ))).mp this

theorem rationalPadicPrimeIdeal_pow_nhds_zero
    (s : Set (RationalPadicIntegerRing p))
    (hs : s ∈ 𝓝 (0 : RationalPadicIntegerRing p)) :
    ∃ n : ℕ,
      (((rationalPadicPrimeIdeal p) ^ n :
        Ideal (RationalPadicIntegerRing p)) : Set (RationalPadicIntegerRing p)) ⊆ s := by
  let F : Type := (lambdaRationalHeightOneSpectrum p).adicCompletion ℚ
  let R₀ : Type := RationalPadicIntegerRing p
  let A : Set F := {x | Valued.v x ≤ 1}
  let zA : A := ⟨(0 : F), by simp [A]⟩
  change s ∈ 𝓝 zA at hs
  rcases (mem_nhds_subtype A zA s).mp hs with ⟨u, hu, hus⟩
  rcases Valued.mem_nhds_zero.mp hu with ⟨γ, hγu⟩
  have hp_lt :
      Valued.v.restrict (((p : R₀) : F)) <
        (1 : MonoidWithZeroHom.ValueGroup₀
          (MonoidWithZeroHom.ofClass
            (Valued.v : Valuation F (WithZero (Multiplicative ℤ))))) :=
    (Valuation.restrict_lt_one_iff
      (v := (Valued.v : Valuation F (WithZero (Multiplicative ℤ))))).mpr
      (rationalPadicInteger_natCast_prime_valuation_lt_one (p := p))
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hp_lt γ
  refine ⟨n, ?_⟩
  intro x hx
  apply hus
  apply hγu
  rw [Set.mem_setOf_eq]
  have hxv :
      Valued.v ((x : R₀) : F) ≤
        Valued.v (((p : R₀) ^ n : R₀) : F) := by
    simpa [R₀] using
      (Set.ext_iff.mp
        (rationalPadicPrimeIdeal_pow_eq_valuation_closedBall (p := p) n) x).mp hx
  have hxvr :
      Valued.v.restrict ((x : R₀) : F) ≤
        Valued.v.restrict (((p : R₀) ^ n : R₀) : F) := by
    rw [Valuation.restrict_le_iff]
    exact hxv
  have hpown :
      Valued.v.restrict (((p : R₀) ^ n : R₀) : F) =
        Valued.v.restrict (((p : R₀) : F)) ^ n := by
    change Valued.v.restrict ((((p : R₀) : F) ^ n)) =
      Valued.v.restrict (((p : R₀) : F)) ^ n
    exact map_pow (Valued.v.restrict : Valuation F
      (MonoidWithZeroHom.ValueGroup₀
        (MonoidWithZeroHom.ofClass
          (Valued.v : Valuation F (WithZero (Multiplicative ℤ))))))
      (((p : R₀) : F)) n
  rw [hpown] at hxvr
  exact lt_of_le_of_lt hxvr hn

theorem rationalPadicPrimeIdeal_isAdic :
    IsAdic (rationalPadicPrimeIdeal p) := by
  rw [isAdic_iff]
  exact ⟨rationalPadicPrimeIdeal_pow_isOpen (p := p),
    rationalPadicPrimeIdeal_pow_nhds_zero (p := p)⟩

theorem pi_mem_ideal_smul_top_of_forall_mem
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (J : Ideal R) {f : ι → R} (hf : ∀ i, f i ∈ J) :
    f ∈ (J • (⊤ : Submodule R (ι → R))) := by
  classical
  letI := Fintype.ofFinite ι
  rw [← Finset.univ_sum_single f]
  refine Submodule.sum_mem _ ?_
  intro i _hi
  have hterm :
      (f i) • Pi.single i (1 : R) ∈
        (J • (⊤ : Submodule R (ι → R))) :=
    Submodule.smul_mem_smul (hf i) trivial
  have hsingle : Pi.single i (f i) = (f i) • Pi.single i (1 : R) := by
    ext j
    by_cases hji : j = i
    · subst j
      simp
    · simp [hji]
  rw [hsingle]
  exact hterm

theorem pi_apply_mem_of_mem_ideal_smul_top
    {R : Type*} [CommRing R] {ι : Type*} (J : Ideal R)
    {f : ι → R} (hf : f ∈ (J • (⊤ : Submodule R (ι → R)))) (i : ι) :
    f i ∈ J := by
  refine Submodule.smul_induction_on hf ?_ ?_
  · intro r hr g _hg
    simpa [Pi.smul_apply, mul_comm] using J.mul_mem_left (g i) hr
  · intro x y hx hy
    exact J.add_mem hx hy

instance instIsPrecompleteRationalPadicIntegerRing :
    IsPrecomplete (rationalPadicPrimeIdeal p) (RationalPadicIntegerRing p) :=
  (rationalPadicPrimeIdeal_isAdic (p := p)).isPrecomplete_iff.mpr inferInstance

instance instIsPrecompletePiFinite
    {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    (J : Ideal R) [IsPrecomplete J R] :
    IsPrecomplete J (ι → R) where
  prec' f hf := by
    classical
    have hcoord : ∀ i : ι, ∃ L : R, ∀ n : ℕ,
        f n i ≡ L [SMOD (J ^ n • (⊤ : Submodule R R))] := fun i ↦
      (inferInstance : IsPrecomplete J R).prec
        (f := fun n ↦ f n i)
        (fun {m n} hmn ↦ by
          rw [SModEq.sub_mem]
          have hmem :
              f m - f n ∈
                (J ^ m • (⊤ : Submodule R (ι → R))) :=
            SModEq.sub_mem.mp (hf hmn)
          simpa [Pi.sub_apply, smul_eq_mul, Ideal.mul_top] using
            pi_apply_mem_of_mem_ideal_smul_top (J ^ m) hmem i)
    choose L hL using hcoord
    refine ⟨L, fun n ↦ ?_⟩
    rw [SModEq.sub_mem]
    exact pi_mem_ideal_smul_top_of_forall_mem (J ^ n) (fun i ↦ by
      simpa [smul_eq_mul, Ideal.mul_top] using SModEq.sub_mem.mp (hL i n))

instance instIsPrecompleteRationalPadicPowerCoefficients :
    IsPrecomplete (rationalPadicPrimeIdeal p)
      (Fin (p - 1) → RationalPadicIntegerRing p) :=
  inferInstance


theorem dworkParameterPowerLinearMap_single_primePow_coeff
    (m : ℕ) (i : Fin (p - 1)) (b : RationalPadicIntegerRing p) :
    dworkParameterPowerLinearMap p K
        (Pi.single i ((p : RationalPadicIntegerRing p) ^ m * b)) =
      (p : DworkCompleteIntegerRing p K) ^ m *
        algebraMap (RationalPadicIntegerRing p)
          (DworkCompleteIntegerRing p K) b *
          dworkParameter p K ^ (i : ℕ) := by
  classical
  rw [dworkParameterPowerLinearMap_single_coeff]
  simp [mul_assoc]

theorem dworkParameter_residue_error_mul_pow_mem
    {y : DworkCompleteIntegerRing p K} {b : RationalPadicIntegerRing p}
    (s : ℕ)
    (hb : y - algebraMap (RationalPadicIntegerRing p)
        (DworkCompleteIntegerRing p K) b ∈ dworkParameterIdeal p K) :
    (y - algebraMap (RationalPadicIntegerRing p)
        (DworkCompleteIntegerRing p K) b) * dworkParameter p K ^ s ∈
      (dworkParameterIdeal p K) ^ (s + 1) := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal S := dworkParameterIdeal p K
  let varpi : S := dworkParameter p K
  have hvarpi_pow : varpi ^ s ∈ I ^ s :=
    Ideal.pow_mem_pow
      (by
        dsimp [I, varpi, dworkParameterIdeal]
        exact Ideal.mem_span_singleton_self (dworkParameter p K)) s
  have hmul :
      (y - algebraMap (RationalPadicIntegerRing p) S b) * varpi ^ s ∈ I * I ^ s :=
    Ideal.mul_mem_mul (show _ ∈ dworkParameterIdeal p K from hb) hvarpi_pow
  have hmul1 :
      (y - algebraMap (RationalPadicIntegerRing p) S b) * varpi ^ s ∈ I ^ 1 * I ^ s := by
    simpa using hmul
  rw [← pow_add] at hmul1
  simpa [S, I, varpi, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmul1

theorem dworkParameter_power_residue_error_mem
    {z y : DworkCompleteIntegerRing p K} {b : RationalPadicIntegerRing p}
    (s : ℕ)
    (hyz : z = y * dworkParameter p K ^ s)
    (hb : y - algebraMap (RationalPadicIntegerRing p)
        (DworkCompleteIntegerRing p K) b ∈ dworkParameterIdeal p K) :
    z - algebraMap (RationalPadicIntegerRing p)
        (DworkCompleteIntegerRing p K) b * dworkParameter p K ^ s ∈
      (dworkParameterIdeal p K) ^ (s + 1) := by
  let S : Type _ := DworkCompleteIntegerRing p K
  have hcalc :
      z - algebraMap (RationalPadicIntegerRing p) S b * dworkParameter p K ^ s =
        (y - algebraMap (RationalPadicIntegerRing p) S b) *
          dworkParameter p K ^ s := by
    rw [hyz]
    ring
  rw [hcalc]
  exact dworkParameter_residue_error_mul_pow_mem (p := p) (K := K) s hb

theorem natCast_prime_pow_mul_mem_parameterIdeal_pow_mul_pred_add_succ
    {w : DworkCompleteIntegerRing p K} (m s : ℕ)
    (hw : w ∈ (dworkParameterIdeal p K) ^ (s + 1)) :
    (p : DworkCompleteIntegerRing p K) ^ m * w ∈
      (dworkParameterIdeal p K) ^ (m * (p - 1) + (s + 1)) := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let I : Ideal S := dworkParameterIdeal p K
  have hmul : (p : S) ^ m * w ∈
      Ideal.span ({((p : S) ^ m)} : Set S) * I ^ (s + 1) :=
    Ideal.mul_mem_mul
      (Ideal.mem_span_singleton_self ((p : S) ^ m)) (by simpa [I] using hw)
  rw [← dworkParameterIdeal_pow_mul_pred_add_eq_span_natCast_prime_pow_mul
    (p := p) (K := K) m (s + 1)] at hmul
  simpa [S, I] using hmul

theorem algebraMap_mem_dworkParameterIdeal_pow_mul_pred_of_mem_rationalPadicPrimeIdeal_pow
    {c : RationalPadicIntegerRing p} {q : ℕ}
    (hc : c ∈ (rationalPadicPrimeIdeal p) ^ q) :
    algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) c ∈
      (dworkParameterIdeal p K) ^ (q * (p - 1)) := by
  let S : Type _ := DworkCompleteIntegerRing p K
  let R₀ : Type := RationalPadicIntegerRing p
  have hmap :
      algebraMap R₀ S c ∈
        ((rationalPadicPrimeIdeal p) ^ q).map (algebraMap R₀ S) :=
    Ideal.mem_map_of_mem (algebraMap R₀ S) hc
  have hle :
      ((rationalPadicPrimeIdeal p) ^ q).map (algebraMap R₀ S) ≤
        (dworkParameterIdeal p K) ^ (q * (p - 1)) := by
    rw [rationalPadicPrimeIdeal, Ideal.span_singleton_pow, Ideal.map_span]
    rw [Ideal.span_le]
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_singleton_iff] at hx
    subst x
    simpa [S, R₀, map_pow] using
      natCast_prime_pow_mem_dworkParameterIdeal_pow_mul_pred
        (p := p) (K := K) q
  exact hle hmap

theorem dworkParameterPowerLinearMap_mem_parameterIdeal_pow_mul_pred_of_forall_mem_primeIdeal_pow
    {a : Fin (p - 1) → RationalPadicIntegerRing p} {q : ℕ}
    (ha : ∀ i, a i ∈ (rationalPadicPrimeIdeal p) ^ q) :
    dworkParameterPowerLinearMap p K a ∈
      (dworkParameterIdeal p K) ^ (q * (p - 1)) := by
  classical
  rw [dworkParameterPowerLinearMap_apply]
  refine Ideal.sum_mem _ ?_
  intro i _hi
  have hcoeff :
      algebraMap (RationalPadicIntegerRing p) (DworkCompleteIntegerRing p K) (a i) ∈
        (dworkParameterIdeal p K) ^ (q * (p - 1)) :=
    algebraMap_mem_dworkParameterIdeal_pow_mul_pred_of_mem_rationalPadicPrimeIdeal_pow
      (p := p) (K := K) (ha i)
  exact Ideal.mul_mem_right _ _ hcoeff

theorem dworkParameterPowerLinearMap_mem_parameterIdeal_pow_mul_pred_of_mem_primeIdeal_pow_smul_top
    {a : Fin (p - 1) → RationalPadicIntegerRing p} {q : ℕ}
    (ha : a ∈
      ((rationalPadicPrimeIdeal p) ^ q •
        (⊤ : Submodule (RationalPadicIntegerRing p)
          (Fin (p - 1) → RationalPadicIntegerRing p)))) :
    dworkParameterPowerLinearMap p K a ∈
      (dworkParameterIdeal p K) ^ (q * (p - 1)) :=
  dworkParameterPowerLinearMap_mem_parameterIdeal_pow_mul_pred_of_forall_mem_primeIdeal_pow
    (p := p) (K := K)
    (fun i ↦ pi_apply_mem_of_mem_ideal_smul_top
      ((rationalPadicPrimeIdeal p) ^ q) ha i)

set_option maxHeartbeats 1200000 in
-- This packages the correction step extracted from the quotient-spanning
-- induction; the kernel otherwise spends most of the default budget reducing
-- the completed Dwork algebra maps in the returned correction data.
theorem dworkParameterPowerLinearMap_oneStepCorrection_of_residue_lift
    (hres :
      ∀ y : DworkCompleteIntegerRing p K,
        ∃ b : RationalPadicIntegerRing p,
          y - algebraMap (RationalPadicIntegerRing p)
              (DworkCompleteIntegerRing p K) b ∈ dworkParameterIdeal p K)
    (m s : ℕ) (hs : s < p - 1)
    (x : DworkCompleteIntegerRing p K)
    (a : Fin (p - 1) → RationalPadicIntegerRing p)
    (ha : x - dworkParameterPowerLinearMap p K a ∈
      (dworkParameterIdeal p K) ^ (m * (p - 1) + s)) :
    ∃ (b : RationalPadicIntegerRing p)
      (corr : Fin (p - 1) → RationalPadicIntegerRing p),
      corr = Pi.single ⟨s, hs⟩
        ((p : RationalPadicIntegerRing p) ^ m * b) ∧
      x - dworkParameterPowerLinearMap p K (a + corr) ∈
        (dworkParameterIdeal p K) ^ (m * (p - 1) + s + 1) := by
  classical
  let S : Type _ := DworkCompleteIntegerRing p K
  let R₀ : Type := RationalPadicIntegerRing p
  let I : Ideal S := dworkParameterIdeal p K
  let varpi : S := dworkParameter p K
  rcases exists_natCast_prime_pow_mul_eq_of_mem_dworkParameterIdeal_pow_mul_pred_add
      (p := p) (K := K) m s (by simpa [I] using ha) with
    ⟨z, hz, hz_eq⟩
  have hz_span : z ∈ Ideal.span ({varpi ^ s} : Set S) := by
    simpa [I, varpi, dworkParameterIdeal, Ideal.span_singleton_pow] using hz
  rcases Ideal.mem_span_singleton'.mp hz_span with ⟨y, hyz⟩
  rcases hres y with ⟨b, hb⟩
  have hz_sub :
      z - algebraMap R₀ S b * varpi ^ s ∈ I ^ (s + 1) :=
    dworkParameter_power_residue_error_mem (p := p) (K := K)
      (z := z) (y := y) (b := b) s hyz.symm hb
  have hmul_mem :
      (p : S) ^ m * (z - algebraMap R₀ S b * varpi ^ s) ∈
        I ^ (m * (p - 1) + (s + 1)) := by
    simpa [S, I, varpi] using
      natCast_prime_pow_mul_mem_parameterIdeal_pow_mul_pred_add_succ
        (p := p) (K := K) (m := m) (s := s) hz_sub
  let corr : Fin (p - 1) → R₀ :=
    Pi.single ⟨s, hs⟩ ((p : R₀) ^ m * b)
  refine ⟨b, corr, rfl, ?_⟩
  have hcorr :
      dworkParameterPowerLinearMap p K corr =
        (p : S) ^ m * algebraMap R₀ S b * varpi ^ s := by
    simp [corr, S, R₀, varpi,
      dworkParameterPowerLinearMap_single_primePow_coeff
        (p := p) (K := K) m ⟨s, hs⟩ b]
  have hresid :
      x - dworkParameterPowerLinearMap p K (a + corr) =
        (p : S) ^ m * (z - algebraMap R₀ S b * varpi ^ s) := by
    have hz_eq' : (p : S) ^ m * z =
        x - dworkParameterPowerLinearMap p K a :=
      hz_eq
    calc
      x - dworkParameterPowerLinearMap p K (a + corr) =
          (x - dworkParameterPowerLinearMap p K a) -
            dworkParameterPowerLinearMap p K corr := by
        rw [map_add]
        abel
      _ = (p : S) ^ m * z - (p : S) ^ m * algebraMap R₀ S b * varpi ^ s := by
        rw [hz_eq', hcorr]
      _ = (p : S) ^ m * (z - algebraMap R₀ S b * varpi ^ s) := by
        ring
  rw [hresid]
  simpa [Nat.add_assoc] using hmul_mem

theorem dworkParameterPowerLinearMap_oneStepCorrection
    {N : ℕ} (x : DworkCompleteIntegerRing p K)
    (a : Fin (p - 1) → RationalPadicIntegerRing p)
    (ha : x - dworkParameterPowerLinearMap p K a ∈
      (dworkParameterIdeal p K) ^ N) :
    ∃ (b : RationalPadicIntegerRing p)
      (corr : Fin (p - 1) → RationalPadicIntegerRing p),
      corr = Pi.single (dworkParameterPowerIndex p N)
        ((p : RationalPadicIntegerRing p) ^
          dworkParameterPowerBlock p N * b) ∧
      x - dworkParameterPowerLinearMap p K (a + corr) ∈
        (dworkParameterIdeal p K) ^ (N + 1) := by
  classical
  let m : ℕ := dworkParameterPowerBlock p N
  let s : ℕ := N % (p - 1)
  have hp_pred_pos : 0 < p - 1 :=
    Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
  have hs : s < p - 1 := Nat.mod_lt N hp_pred_pos
  have hN : N = m * (p - 1) + s := by
    dsimp [m, s, dworkParameterPowerBlock]
    calc
      N = (p - 1) * (N / (p - 1)) + N % (p - 1) :=
        (Nat.div_add_mod N (p - 1)).symm
      _ = N / (p - 1) * (p - 1) + N % (p - 1) := by
        rw [Nat.mul_comm]
  rcases dworkParameterPowerLinearMap_oneStepCorrection_of_residue_lift
      (p := p) (K := K)
      (dworkComplete_residue_lift_rationalPadicInteger (p := p) (K := K))
      m s hs x a (by simpa [hN] using ha) with
    ⟨b, corr, hcorr, hmem⟩
  refine ⟨b, corr, ?_, ?_⟩
  · simpa [dworkParameterPowerIndex, dworkParameterPowerBlock, m, s] using hcorr
  · have hidx : m * (p - 1) + s + 1 = N + 1 := by
      omega
    simpa [hidx] using hmem

noncomputable def dworkParameterPowerApproxSeq
    (x : DworkCompleteIntegerRing p K) :
    (N : ℕ) →
      {a : Fin (p - 1) → RationalPadicIntegerRing p //
        x - dworkParameterPowerLinearMap p K a ∈
          (dworkParameterIdeal p K) ^ N}
  | 0 => ⟨0, by simp⟩
  | N + 1 =>
      let prev := dworkParameterPowerApproxSeq x N
      let hstep := dworkParameterPowerLinearMap_oneStepCorrection
        (p := p) (K := K) (N := N) x prev.1 prev.2
      let b := Classical.choose hstep
      let hcorrExists := Classical.choose_spec hstep
      let corr := Classical.choose hcorrExists
      let hcorrSpec := Classical.choose_spec hcorrExists
      ⟨prev.1 + corr, hcorrSpec.2⟩

theorem dworkParameterPowerApproxSeq_spec
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    x - dworkParameterPowerLinearMap p K
        (dworkParameterPowerApproxSeq p K x N).1 ∈
      (dworkParameterIdeal p K) ^ N :=
  (dworkParameterPowerApproxSeq p K x N).2

@[simp]
theorem dworkParameterPowerApproxSeq_zero
    (x : DworkCompleteIntegerRing p K) :
    (dworkParameterPowerApproxSeq p K x 0).1 = 0 :=
  rfl

theorem dworkParameterPowerApproxSeq_succ
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    (dworkParameterPowerApproxSeq p K x (N + 1)).1 =
      (dworkParameterPowerApproxSeq p K x N).1 +
        Classical.choose
          (Classical.choose_spec
            (dworkParameterPowerLinearMap_oneStepCorrection
              (p := p) (K := K) (N := N) x
              (dworkParameterPowerApproxSeq p K x N).1
              (dworkParameterPowerApproxSeq p K x N).2)) :=
  rfl

noncomputable def dworkParameterPowerApproxStepCoeff
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    RationalPadicIntegerRing p :=
  Classical.choose
    (dworkParameterPowerLinearMap_oneStepCorrection
      (p := p) (K := K) (N := N) x
      (dworkParameterPowerApproxSeq p K x N).1
      (dworkParameterPowerApproxSeq p K x N).2)

noncomputable def dworkParameterPowerApproxStepCorrection
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    Fin (p - 1) → RationalPadicIntegerRing p :=
  Classical.choose
    (Classical.choose_spec
      (dworkParameterPowerLinearMap_oneStepCorrection
        (p := p) (K := K) (N := N) x
        (dworkParameterPowerApproxSeq p K x N).1
        (dworkParameterPowerApproxSeq p K x N).2))

theorem dworkParameterPowerApproxStepCorrection_eq_single
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    dworkParameterPowerApproxStepCorrection p K x N =
      Pi.single (dworkParameterPowerIndex p N)
        ((p : RationalPadicIntegerRing p) ^ dworkParameterPowerBlock p N *
          dworkParameterPowerApproxStepCoeff p K x N) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (dworkParameterPowerLinearMap_oneStepCorrection
        (p := p) (K := K) (N := N) x
        (dworkParameterPowerApproxSeq p K x N).1
        (dworkParameterPowerApproxSeq p K x N).2))).1

theorem dworkParameterPowerApproxSeq_succ_eq_stepCorrection
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    (dworkParameterPowerApproxSeq p K x (N + 1)).1 =
      (dworkParameterPowerApproxSeq p K x N).1 +
        dworkParameterPowerApproxStepCorrection p K x N :=
  rfl

theorem dworkParameterPowerApproxStepCorrection_apply_mem_primeIdeal_pow
    (x : DworkCompleteIntegerRing p K) (N : ℕ)
    (i : Fin (p - 1)) :
    dworkParameterPowerApproxStepCorrection p K x N i ∈
      (rationalPadicPrimeIdeal p) ^ dworkParameterPowerBlock p N := by
  classical
  rw [dworkParameterPowerApproxStepCorrection_eq_single]
  by_cases hi : i = dworkParameterPowerIndex p N
  · subst i
    simp only [Pi.single_eq_same]
    have hp_mem :
        (p : RationalPadicIntegerRing p) ∈ rationalPadicPrimeIdeal p :=
      Ideal.mem_span_singleton_self (p : RationalPadicIntegerRing p)
    have hp_pow :
        (p : RationalPadicIntegerRing p) ^ dworkParameterPowerBlock p N ∈
          (rationalPadicPrimeIdeal p) ^ dworkParameterPowerBlock p N :=
      Ideal.pow_mem_pow hp_mem (dworkParameterPowerBlock p N)
    exact Ideal.mul_mem_right
      (dworkParameterPowerApproxStepCoeff p K x N)
      ((rationalPadicPrimeIdeal p) ^ dworkParameterPowerBlock p N) hp_pow
  · simp [Pi.single_eq_of_ne hi]

theorem dworkParameterPowerApproxStepCorrection_mem_primeIdeal_pow_smul_top
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    dworkParameterPowerApproxStepCorrection p K x N ∈
      ((rationalPadicPrimeIdeal p) ^ dworkParameterPowerBlock p N •
        (⊤ : Submodule (RationalPadicIntegerRing p)
          (Fin (p - 1) → RationalPadicIntegerRing p))) :=
  pi_mem_ideal_smul_top_of_forall_mem
    ((rationalPadicPrimeIdeal p) ^ dworkParameterPowerBlock p N)
    (dworkParameterPowerApproxStepCorrection_apply_mem_primeIdeal_pow
      (p := p) (K := K) x N)

theorem dworkParameterPowerApproxStepCorrection_mem_primeIdeal_pow_smul_top_of_le
    (x : DworkCompleteIntegerRing p K) (N q : ℕ)
    (hq : q ≤ dworkParameterPowerBlock p N) :
    dworkParameterPowerApproxStepCorrection p K x N ∈
      ((rationalPadicPrimeIdeal p) ^ q •
        (⊤ : Submodule (RationalPadicIntegerRing p)
          (Fin (p - 1) → RationalPadicIntegerRing p))) :=
  (Submodule.smul_mono_left (Ideal.pow_le_pow_right hq))
    (dworkParameterPowerApproxStepCorrection_mem_primeIdeal_pow_smul_top
      (p := p) (K := K) x N)

theorem dworkParameterPowerApproxSeq_succ_sub_mem_primeIdeal_pow_smul_top_of_le
    (x : DworkCompleteIntegerRing p K) (N q : ℕ)
    (hq : q ≤ dworkParameterPowerBlock p N) :
    (dworkParameterPowerApproxSeq p K x (N + 1)).1 -
        (dworkParameterPowerApproxSeq p K x N).1 ∈
      ((rationalPadicPrimeIdeal p) ^ q •
        (⊤ : Submodule (RationalPadicIntegerRing p)
          (Fin (p - 1) → RationalPadicIntegerRing p))) := by
  rw [dworkParameterPowerApproxSeq_succ_eq_stepCorrection]
  simpa using
    dworkParameterPowerApproxStepCorrection_mem_primeIdeal_pow_smul_top_of_le
      (p := p) (K := K) x N q hq

theorem dworkParameterPowerApproxSeq_sub_mem_primeIdeal_pow_smul_top_of_mul_pred_le
    (x : DworkCompleteIntegerRing p K) {q M N : ℕ}
    (hMN : M ≤ N) (hM : q * (p - 1) ≤ M) :
    (dworkParameterPowerApproxSeq p K x N).1 -
        (dworkParameterPowerApproxSeq p K x M).1 ∈
      ((rationalPadicPrimeIdeal p) ^ q •
        (⊤ : Submodule (RationalPadicIntegerRing p)
          (Fin (p - 1) → RationalPadicIntegerRing p))) := by
  induction N, hMN using Nat.le_induction with
  | base =>
      simp
  | succ N hMN ih =>
      have hqblock : q ≤ dworkParameterPowerBlock p N :=
        le_dworkParameterPowerBlock_of_mul_pred_le (p := p)
          (hM.trans hMN)
      have hstep :
          (dworkParameterPowerApproxSeq p K x (N + 1)).1 -
              (dworkParameterPowerApproxSeq p K x N).1 ∈
            ((rationalPadicPrimeIdeal p) ^ q •
              (⊤ : Submodule (RationalPadicIntegerRing p)
                (Fin (p - 1) → RationalPadicIntegerRing p))) :=
        dworkParameterPowerApproxSeq_succ_sub_mem_primeIdeal_pow_smul_top_of_le
          (p := p) (K := K) x N q hqblock
      have hcalc :
          (dworkParameterPowerApproxSeq p K x (N + 1)).1 -
              (dworkParameterPowerApproxSeq p K x M).1 =
            ((dworkParameterPowerApproxSeq p K x N).1 -
                (dworkParameterPowerApproxSeq p K x M).1) +
              ((dworkParameterPowerApproxSeq p K x (N + 1)).1 -
                (dworkParameterPowerApproxSeq p K x N).1) := by
        abel
      rw [hcalc]
      exact Submodule.add_mem _ ih hstep

noncomputable def dworkParameterPowerApproxBlockSeq
    (x : DworkCompleteIntegerRing p K) (q : ℕ) :
    Fin (p - 1) → RationalPadicIntegerRing p :=
  (dworkParameterPowerApproxSeq p K x (q * (p - 1))).1

theorem dworkParameterPowerApproxBlockSeq_sub_mem_primeIdeal_pow_smul_top
    (x : DworkCompleteIntegerRing p K) {m n : ℕ} (hmn : m ≤ n) :
    dworkParameterPowerApproxBlockSeq p K x n -
        dworkParameterPowerApproxBlockSeq p K x m ∈
      ((rationalPadicPrimeIdeal p) ^ m •
        (⊤ : Submodule (RationalPadicIntegerRing p)
          (Fin (p - 1) → RationalPadicIntegerRing p))) :=
  dworkParameterPowerApproxSeq_sub_mem_primeIdeal_pow_smul_top_of_mul_pred_le
    (p := p) (K := K) x
    (hMN := Nat.mul_le_mul_right (p - 1) hmn)
    (hM := le_rfl)

set_option maxHeartbeats 1200000 in
-- This is the formal limit step for CU-09e2.  It is conditional only on the
-- coefficient module's `p`-adic precompleteness; the coherent approximation
-- and Dwork-continuity estimates are proved above.
theorem dworkParameterPowerLinearMap_surjective_of_precomplete
    [IsPrecomplete (rationalPadicPrimeIdeal p)
      (Fin (p - 1) → RationalPadicIntegerRing p)] :
    Function.Surjective (dworkParameterPowerLinearMap p K) := by
  classical
  intro x
  let R₀ : Type := RationalPadicIntegerRing p
  let M : Type := Fin (p - 1) → R₀
  let S : Type _ := DworkCompleteIntegerRing p K
  let J : Ideal R₀ := rationalPadicPrimeIdeal p
  let I : Ideal S := dworkParameterIdeal p K
  let f : ℕ → M := dworkParameterPowerApproxBlockSeq p K x
  have hf : ∀ {m n : ℕ}, m ≤ n →
      f m ≡ f n [SMOD (J ^ m • (⊤ : Submodule R₀ M))] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have hmem :
        f n - f m ∈
          ((rationalPadicPrimeIdeal p) ^ m •
            (⊤ : Submodule R₀ M)) :=
      dworkParameterPowerApproxBlockSeq_sub_mem_primeIdeal_pow_smul_top
        (p := p) (K := K) x hmn
    have hneg :
        -(f n - f m) ∈
          ((rationalPadicPrimeIdeal p) ^ m •
            (⊤ : Submodule R₀ M)) :=
      neg_mem hmem
    have hcalc : f m - f n = -(f n - f m) := by
      abel
    rw [hcalc]
    simpa [f, J, M] using hneg
  obtain ⟨a, ha⟩ :=
    (inferInstance : IsPrecomplete J M).prec (f := f) hf
  refine ⟨a, ?_⟩
  have hhaus : IsHausdorff I S := by
    dsimp [I, S]
    rw [dworkParameterIdeal_eq_dworkCompleteLambdaIdeal (p := p) (K := K)]
    exact (dworkComplete_isAdicComplete (p := p) (K := K)).toIsHausdorff
  have hzero : x - dworkParameterPowerLinearMap p K a = 0 := by
    apply hhaus.haus
    intro N
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    have hp_pred_pos : 0 < p - 1 :=
      Nat.sub_pos_of_lt (Fact.out : Nat.Prime p).one_lt
    have hN_le : N ≤ N * (p - 1) :=
      Nat.le_mul_of_pos_right N hp_pred_pos
    have happrox :
        x - dworkParameterPowerLinearMap p K (f N) ∈
          I ^ (N * (p - 1)) := by
      simpa [f, I, dworkParameterPowerApproxBlockSeq] using
        dworkParameterPowerApproxSeq_spec
          (p := p) (K := K) x (N * (p - 1))
    have hsource : f N - a ∈ J ^ N • (⊤ : Submodule R₀ M) :=
      SModEq.sub_mem.mp (ha N)
    have himage :
        dworkParameterPowerLinearMap p K (f N) -
            dworkParameterPowerLinearMap p K a ∈
          I ^ (N * (p - 1)) := by
      have hlin :
          dworkParameterPowerLinearMap p K (f N - a) ∈
            I ^ (N * (p - 1)) :=
        dworkParameterPowerLinearMap_mem_parameterIdeal_pow_mul_pred_of_mem_primeIdeal_pow_smul_top
          (p := p) (K := K) (q := N) (by simpa [J, M] using hsource)
      simpa [map_sub, I, f] using hlin
    have hsum :
        x - dworkParameterPowerLinearMap p K a ∈
          I ^ (N * (p - 1)) := by
      have hcalc :
          x - dworkParameterPowerLinearMap p K a =
            (x - dworkParameterPowerLinearMap p K (f N)) +
              (dworkParameterPowerLinearMap p K (f N) -
                dworkParameterPowerLinearMap p K a) := by
        abel
      rw [hcalc]
      exact Ideal.add_mem _ happrox himage
    exact Ideal.pow_le_pow_right hN_le hsum
  exact (sub_eq_zero.mp hzero).symm

theorem dworkParameterPowerLinearMap_surjective :
    Function.Surjective (dworkParameterPowerLinearMap p K) :=
  dworkParameterPowerLinearMap_surjective_of_precomplete (p := p) (K := K)

theorem dworkParameterAdjoin_eq_top :
    dworkParameterAdjoin p K = ⊤ :=
  dworkParameterAdjoin_eq_top_of_powerLinearMap_surjective
    (p := p) (K := K)
    (dworkParameterPowerLinearMap_surjective (p := p) (K := K))

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular

end
