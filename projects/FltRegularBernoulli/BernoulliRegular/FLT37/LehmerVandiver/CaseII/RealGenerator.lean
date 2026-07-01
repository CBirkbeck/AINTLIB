import BernoulliRegular.FLT37.LehmerVandiver.CaseII.ConjAction
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.AntiRadicalNotPthPower
import BernoulliRegular.TotallyRealSubfield.FixedAssociate
import BernoulliRegular.HMinus.KplusPrimeArithmetic
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.GaloisDescent
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.CaseIIRealDescent

/-!
# [II1-REAL-GEN] Real generator for the σ-stable Case-II object

Following the 2026-05-27-3 expert review, the Case-II II1 target is **not** the raw anchored
quotient `𝔞(η)/𝔞₀` (which is not `σ`-stable, so has no real generator) but the `σ`-stable object
`𝔞(η)·𝔞(η⁻¹)` and its anchored ratio. `caseII_anchored_mul_conj_mk0_eq` already shows the ratio is
principal. This file builds the real generator: a `σ`-stable principal object `(g)` has `σ g = u·g`
with `u` a `σ`-anti unit, hence `u = (-1)^k·ζ^n` (`caseII_sigma_anti_unit_classification`), feeding
`FixedAssociate.exists_conj_fixed_associate_of_classification`.

## References
* Washington GTM 83 §9.1, Thm 9.4.
* Expert review 2026-05-27-3 (the σ-stable object is the correct II1 target).
-/

@[expose] public section

open NumberField IsCyclotomicExtension Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-- **A `σ`-anti unit is `(-1)^k · ζ^n`.** If `σ μ = μ⁻¹` then `μ = (-1)^k · ζ^n` for some `n, k`.
Proof: `sigma_anti_unit_decomposition` gives `μ = ζ^m · algebraMap s` with `s² = 1`; since `𝓞 K⁺`
is a domain, `s = ±1`, so `algebraMap s = ±1`. This is the classification hypothesis for
`FixedAssociate.exists_conj_fixed_associate_of_classification`. -/
theorem caseII_sigma_anti_unit_classification {μ : (𝓞 K)ˣ}
    (hμ_anti : NumberField.IsCMField.unitsComplexConj K μ = μ⁻¹) :
    ∃ (n k : ℕ), μ = (-1 : (𝓞 K)ˣ) ^ k *
      ((zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.isUnit
        (by decide : (37 : ℕ) ≠ 0)).unit ^ n := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  obtain ⟨m, s, hs, hs2⟩ :=
    CaseI.sigma_anti_unit_decomposition (K := K) (p := 37) (by norm_num) hμ_anti
  have hscoe : (s : 𝓞 (NumberField.maximalRealSubfield K)) *
      (s : 𝓞 (NumberField.maximalRealSubfield K)) = 1 := by
    have h := congrArg Units.val hs2
    rwa [Units.val_pow_eq_pow_val, Units.val_one, sq] at h
  rcases mul_self_eq_one_iff.mp hscoe with h | h
  · refine ⟨m, 0, ?_⟩
    have hs1 : s = 1 := Units.ext h
    rw [hs, hs1, map_one, pow_zero, one_mul, mul_one]
  · refine ⟨m, 1, ?_⟩
    have hsm1 : s = -1 := Units.ext h
    have hmap : Units.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)).toMonoidHom
        (-1 : (𝓞 (NumberField.maximalRealSubfield K))ˣ) = (-1 : (𝓞 K)ˣ) := by
      apply Units.ext
      simp
    rw [hs, hsm1, hmap, pow_one, mul_comm]

/-- **Real generator of a `σ`-stable principal ideal with a real-ideal model.** If a real ideal
`I : Ideal (𝓞 K⁺)` extends to a principal ideal `(a)` of `𝓞 K`, and `σ a = u·a` with `u` a `σ`-anti
unit (`σ u = u⁻¹`, automatic when `(a)` is `σ`-stable), then `(a)` has a conjugation-fixed (real)
generator `b`. Composes `caseII_sigma_anti_unit_classification` with
`FixedAssociate.exists_conj_fixed_associate_of_classification`. -/
theorem caseII_real_generator_of_sigma_stable_model
    (I : Ideal (𝓞 (NumberField.maximalRealSubfield K)))
    (a : 𝓞 K) (u : (𝓞 K)ˣ)
    (hIa : I.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) = Ideal.span {a})
    (hu : NumberField.IsCMField.ringOfIntegersComplexConj K a = u * a)
    (hu_anti : NumberField.IsCMField.unitsComplexConj K u = u⁻¹) :
    ∃ b : 𝓞 K, NumberField.IsCMField.ringOfIntegersComplexConj K b = b ∧
      Ideal.span {b} = Ideal.span {a} := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact BernoulliRegular.exists_conj_fixed_associate_of_classification (K := K) 37 (by decide)
    I a u hIa hu (caseII_sigma_anti_unit_classification hu_anti)

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **`galRestrict (complexConj) = ringOfIntegersComplexConj`.** The restriction to `𝓞 K` of the
abstract `Gal(K/K⁺)` complex conjugation is the concrete `ringOfIntegersComplexConj`. Both send `x`
to the element whose image in `K` is `complexConj (algebraMap x)` (`algebraMap_galRestrict_apply`,
`coe_ringOfIntegersComplexConj`), so they agree by injectivity of `𝓞 K → K`. This is the link that
lets the `σ`-stability of the Washington product feed the `Gal`-fixed `comap` descent condition. -/
theorem caseII_galRestrict_complexConj_eq :
    galRestrict (𝓞 (NumberField.maximalRealSubfield K)) (NumberField.maximalRealSubfield K) K (𝓞 K)
        (NumberField.IsCMField.complexConj K) =
      NumberField.IsCMField.ringOfIntegersComplexConj K := by
  apply AlgEquiv.ext
  intro x
  apply FaithfulSMul.algebraMap_injective (𝓞 K) K
  rw [algebraMap_galRestrict_apply]
  exact (NumberField.IsCMField.coe_ringOfIntegersComplexConj (K := K) x).symm

/-- **The σ-stable Washington product is `Gal(K/K⁺)`-fixed under `comap`** (the descent condition
for `comap_map_eq_of_unramifiedAt_support`). For `σ = 1` trivial; for `σ = complexConj` it is the
`σ`-stability `map_rootIdeal_mul_conj` transported through `caseII_galRestrict_complexConj_eq`. -/
theorem caseII_rootIdeal_mul_conj_comap_fixed {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    (σ : K ≃ₐ[NumberField.maximalRealSubfield K] K) :
    (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
       rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)).comap
      (galRestrict (𝓞 (NumberField.maximalRealSubfield K)) (NumberField.maximalRealSubfield K) K
        (𝓞 K) σ) =
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) := by
  rcases BernoulliRegular.algEquiv_eq_one_or_complexConj (K := K) σ with h1 | hc
  · rw [h1, map_one]; exact Ideal.comap_id _
  · rw [hc, caseII_galRestrict_complexConj_eq]
    nth_rewrite 1 [← D.map_rootIdeal_mul_conj hp η]
    exact Ideal.comap_map_of_bijective _
      (EquivLike.bijective (NumberField.IsCMField.ringOfIntegersComplexConj K))

/-- **`𝔭 ∤ 𝔞(η)·𝔞(η⁻¹)` for `η, η⁻¹ ≠ η₀`.** Since `𝔭 = (ζ-1)` is prime and `𝔭 ∣ 𝔞(ζ) ↔ ζ = η₀`
(`p_dvd_a_iff`), neither factor is divisible by `𝔭`, hence neither is the product. This is the
coprimality input to the unramified-support of the descent. -/
theorem caseII_zetaSubOne_not_dvd_rootIdeal_mul {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero)
    (hηinv : caseII_etaInv η ≠ D.etaZero) :
    ¬ (Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} ∣
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) := by
  have h1 := (p_dvd_a_iff hp D.hζ D.equation D.hy η).not.mpr hη
  have h2 := (p_dvd_a_iff hp D.hζ D.equation D.hy (caseII_etaInv η)).not.mpr hηinv
  intro hdvd
  rcases (Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime').dvd_or_dvd hdvd with h | h
  · exact h1 h
  · exact h2 h

/-- **`𝔞(η)·𝔞(η⁻¹)` is coprime to `𝔭 = (ζ-1)`** (for `η, η⁻¹ ≠ η₀`). Since `𝔭` is a nonzero prime
of the Dedekind domain `𝓞 K` it is maximal, and `𝔭 ∤ 𝔞(η)·𝔞(η⁻¹)`
(`caseII_zetaSubOne_not_dvd_rootIdeal_mul`) gives `I ⊔ 𝔭 = ⊤`. The coprimality fact underlying the
descent's unramified support. -/
theorem caseII_isCoprime_rootIdeal_mul_zetaSubOne {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero)
    (hηinv : caseII_etaInv η ≠ D.etaZero) :
    IsCoprime (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))
      (Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)}) := by
  have hprime : Prime (Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)}) :=
    Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime'
  have hmax : (Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)}).IsMaximal :=
    (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  exact caseII_zetaSubOne_not_dvd_rootIdeal_mul D hp η hη hηinv
    (Ideal.dvd_iff_le.mpr (le_sup_left.trans (hmax.eq_of_le hne le_sup_right).ge))

/-- **`𝔞(η)·𝔞(η⁻¹)` is coprime to `(37)`** (for `η, η⁻¹ ≠ η₀`). Since `(37) = 𝔭³⁶` in `𝓞 K`
(`associated_zeta_sub_one_pow_prime`: `(ζ-1)³⁶ ~ 37`), coprimality to the prime `𝔭`
(`caseII_isCoprime_rootIdeal_mul_zetaSubOne`) gives coprimality to its power `(37)`. This is what
descends to `𝓞 K⁺` (via the conjugation trace) for the unramified support. -/
theorem caseII_isCoprime_rootIdeal_mul_int37 {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero)
    (hηinv : caseII_etaInv η ≠ D.etaZero) :
    IsCoprime (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))
      (Ideal.span {(37 : 𝓞 K)}) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hsp : Ideal.span {(37 : 𝓞 K)} = Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} ^ (37 - 1) := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
    exact_mod_cast (associated_zeta_sub_one_pow_prime D.hζ).symm
  rw [hsp]
  exact (caseII_isCoprime_rootIdeal_mul_zetaSubOne D hp η hη hηinv).pow_right

/-- **`I.comap` is coprime to `(37)` in `𝓞 K⁺`** (the unramified-support input), via the conjugation
trace. From `IsCoprime I (37)` (in `𝓞 K`) write `1 = a + c` (`a ∈ I`, `c ∈ (37)`); then
`2 = (a + σa) + (c + σc)` with `a + σa ∈ I` (σ-stable) and `σ`-fixed, so `a + σa = ι a⁺` with
`a⁺ ∈ I.comap`, and `c + σc = ι(37·e⁺)`; injectivity gives `2 = a⁺ + 37·e⁺ ∈ I.comap + (37)`, and
Bézout (`1 = 2·(-18) + 37`) upgrades `2` to `1`. -/
theorem caseII_isCoprime_comap_int37 {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero)
    (hηinv : caseII_etaInv η ≠ D.etaZero) :
    IsCoprime ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)).comap
        (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)))
      (Ideal.span {(37 : 𝓞 (NumberField.maximalRealSubfield K))}) := by
  set σ := (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom with hσ
  set I := rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
    rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) with hI
  have hI_stable : I.map σ = I := D.map_rootIdeal_mul_conj hp η
  have hinv : ∀ x : 𝓞 K, σ (σ x) = x := fun x => by
    apply RingOfIntegers.ext
    simp only [hσ, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
      NumberField.IsCMField.coe_ringOfIntegersComplexConj,
      NumberField.IsCMField.complexConj_apply_apply]
  -- `1 = a + c`, `a ∈ I`, `c ∈ (37)`.
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp
    ((Ideal.isCoprime_iff_sup_eq.mp (caseII_isCoprime_rootIdeal_mul_int37 D hp η hη hηinv)) ▸
      (Submodule.mem_top : (1 : 𝓞 K) ∈ (⊤ : Ideal (𝓞 K))))
  -- `a + σa ∈ I`, `σ`-fixed, so it descends.
  have haσ_I : a + σ a ∈ I := I.add_mem ha (hI_stable ▸ Ideal.mem_map_of_mem σ ha)
  have haσ_fix : NumberField.IsCMField.ringOfIntegersComplexConj K (a + σ a) = a + σ a := by
    show σ (a + σ a) = a + σ a; rw [map_add, hinv]; ring
  obtain ⟨aP, haP⟩ := Set.mem_range.mp
    ((NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) (a + σ a)).mp haσ_fix)
  -- `c = 37 * d`, so `c + σc = 37 * (d + σd)`, also descending.
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
  have hdσ_fix : NumberField.IsCMField.ringOfIntegersComplexConj K (d + σ d) = d + σ d := by
    show σ (d + σ d) = d + σ d; rw [map_add, hinv]; ring
  obtain ⟨eP, heP⟩ := Set.mem_range.mp
    ((NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) (d + σ d)).mp hdσ_fix)
  have hσ37 : σ (37 : 𝓞 K) = 37 := map_ofNat σ 37
  have hσ1 : σ a + 37 * σ d = 1 := by
    have h := congrArg σ hac
    rwa [map_add, map_mul, hσ37, map_one] at h
  -- `2 = aP + 37 * eP` in `𝓞 K⁺` (injectivity + the trace `(a+σa)+37(d+σd)=2`).
  have h2 : (2 : 𝓞 (NumberField.maximalRealSubfield K)) = aP + 37 * eP := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
    rw [map_add, map_mul, haP, heP]
    simp only [map_ofNat]
    linear_combination -hac - hσ1
  -- Bézout `1 = (-18)·2 + 37·…` ⟹ `1 ∈ I.comap + (37)`.
  have haP_mem : aP ∈ (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)).comap
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) := by
    rw [Ideal.mem_comap, haP]; exact haσ_I
  have hbez : (1 : 𝓞 (NumberField.maximalRealSubfield K)) =
      (-18) * aP + (-18 * eP + 1) * 37 := by linear_combination (-18) * h2
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, hbez]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ haP_mem))
    (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

/-- **The σ-stable Washington product `𝔞(η)·𝔞(η⁻¹)` descends from `𝓞 K⁺`.** For `η, η⁻¹ ≠ η₀`, the
`Gal(K/K⁺)`-fixed ideal `𝔞(η)·𝔞(η⁻¹)` is the extension of `J = (𝔞(η)·𝔞(η⁻¹)).comap`. Combines the
`Gal`-fixed comap condition (`caseII_rootIdeal_mul_conj_comap_fixed`) with
`comap_map_eq_of_unramifiedAt_support`, whose unramified support holds because every prime factor of
`(𝔞(η)·𝔞(η⁻¹)).comap` avoids the prime over `37` (else, with `IsCoprime (I.comap) (37)`, it would be
`⊤`), so `isUnramifiedAt_of_not_over_37` applies. -/
theorem caseII_sigma_stable_ideal_descends {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero)
    (hηinv : caseII_etaInv η ≠ D.etaZero) :
    ∃ J : Ideal (𝓞 (NumberField.maximalRealSubfield K)),
      J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) := by
  refine ⟨(rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)).comap
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)), ?_⟩
  apply comap_map_eq_of_unramifiedAt_support (R := 𝓞 (NumberField.maximalRealSubfield K))
    (K := NumberField.maximalRealSubfield K) (L := K) (S := 𝓞 K)
  · exact caseII_rootIdeal_mul_conj_comap_fixed D hp η
  · intro p hp_mem
    rw [Multiset.mem_toFinset] at hp_mem
    have hp_prime : Prime p := UniqueFactorizationMonoid.prime_of_factor p hp_mem
    haveI hp_isPrime : p.IsPrime := Ideal.isPrime_of_prime hp_prime
    apply isUnramifiedAt_of_not_over_37 p hp_prime.ne_zero
    intro h37
    have hcop := caseII_isCoprime_comap_int37 D hp η hη hηinv
    rw [Ideal.isCoprime_iff_sup_eq] at hcop
    have htop : (⊤ : Ideal (𝓞 (NumberField.maximalRealSubfield K))) ≤ p := by
      rw [← hcop]
      refine sup_le (Ideal.dvd_iff_le.mp (UniqueFactorizationMonoid.dvd_of_mem_factors hp_mem)) ?_
      rw [Ideal.span_singleton_le_iff_mem]
      have : (37 : 𝓞 (NumberField.maximalRealSubfield K)) =
          algebraMap ℤ (𝓞 (NumberField.maximalRealSubfield K)) 37 :=
        (map_ofNat (algebraMap ℤ (𝓞 (NumberField.maximalRealSubfield K))) 37).symm
      rw [this]; exact h37
    exact hp_isPrime.ne_top (top_le_iff.mp htop)

/-- **The descended anchored `σ`-stable ideals lie in the same `Cl(𝓞 K⁺)` class.** If
`J.map = 𝔞(η)·𝔞(η⁻¹)` and `J₀.map = 𝔞(η₀)·𝔞(η₀⁻¹)` (the descents from
`caseII_sigma_stable_ideal_descends`), then `[J] = [J₀]` in `Cl(𝓞 K⁺)`. Proof: `classGroupMap`
sends these to `[J.map] = [J₀.map]`, equal by step 3b (`caseII_anchored_mul_conj_mk0_eq`), and
`classGroupMap` is injective (`hPlus_dvd_h`/Diekmann Prop 55). Hence the anchored ratio `J/J₀` is
principal in `𝓞 K⁺`, i.e. has a real generator — the substance of the restated II1 target. -/
theorem caseII_descended_anchored_class_eq {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {J J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ_ne : J ≠ ⊥) (hJ0_ne : J₀ ≠ ⊥)
    (hJ : J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))
    (hJ0 : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)) :
    ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_iff_ne_zero.mpr hJ_ne⟩ =
      ClassGroup.mk0 ⟨J₀, mem_nonZeroDivisors_iff_ne_zero.mpr hJ0_ne⟩ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h3b := caseII_anchored_mul_conj_mk0_eq D hp h_VC η
  rw [← map_mul, ← map_mul] at h3b
  apply classGroupMap_injective (K := K) (p := 37) (hp_odd := by decide)
  rw [ClassGroup.extensionMap_mk0, ClassGroup.extensionMap_mk0]
  convert h3b using 2
  · exact Subtype.ext hJ
  · exact Subtype.ext hJ0

/-- **Conjugate-paired real generators for the anchored σ-stable descent.** For `η, η⁻¹ ≠ η₀` and
the descents `J.map = 𝔞(η)·𝔞(η⁻¹)`, `J₀.map = 𝔞(η₀)·𝔞(η₀⁻¹)`, there are nonzero **real** elements
`x, y ∈ 𝓞 K⁺` with `(x)·J = (y)·J₀`. This is the restated, satisfiable Washington II1 datum: the
descent variable is built from the real `x, y` (not from a real generator of the non-σ-stable raw
quotient). Immediate from `caseII_descended_anchored_class_eq` + `ClassGroup.mk0_eq_mk0_iff`. -/
theorem caseII_descended_anchored_real_generators {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (η : nthRootsFinset 37 (1 : 𝓞 K))
    {J J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    (hJ_ne : J ≠ ⊥) (hJ0_ne : J₀ ≠ ⊥)
    (hJ : J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))
    (hJ0 : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)) :
    ∃ (x y : 𝓞 (NumberField.maximalRealSubfield K)) (_ : x ≠ 0) (_ : y ≠ 0),
      Ideal.span {x} * J = Ideal.span {y} * J₀ := by
  have hclass := caseII_descended_anchored_class_eq D hp h_VC η hJ_ne hJ0_ne hJ hJ0
  obtain ⟨x, y, hx, hy, h⟩ := ClassGroup.mk0_eq_mk0_iff.mp hclass
  exact ⟨x, y, hx, hy, h⟩

/-- **The σ-stable anchored real-generator identity (integral form).** Extending the conjugate
real generators `(x)·J = (y)·J₀` (`caseII_descended_anchored_real_generators`) through the descents
`J.map = 𝔞(η)·𝔞(η⁻¹)`, `J₀.map = 𝔞(η₀)·𝔞(η₀⁻¹)` gives, in `𝓞 K`,
`(algebraMap x)·(𝔞(η)·𝔞(η⁻¹)) = (algebraMap y)·(𝔞(η₀)·𝔞(η₀⁻¹))` with `algebraMap x, algebraMap y`
real (images of `𝓞 K⁺` elements). This is the satisfiable σ-stable Washington II1 target,
replacing the unsatisfiable raw-quotient span identity. -/
theorem caseII_sigma_stable_anchored_real_identity {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    {J J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    {x y : 𝓞 (NumberField.maximalRealSubfield K)}
    (hJ : J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))
    (hJ0 : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    (hxy : Ideal.span {x} * J = Ideal.span {y} * J₀) :
    Ideal.span {algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) x} *
        (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η)) =
      Ideal.span {algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y} *
        (rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
          rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero)) := by
  have h := congrArg (Ideal.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K))) hxy
  rwa [Ideal.map_mul, Ideal.map_mul, Ideal.map_span, Set.image_singleton, hJ,
    Ideal.map_span, Set.image_singleton, hJ0] at h

/-- **The σ-stable anchored real-generator identity (fractional form).** The fractional-ideal
restatement of `caseII_sigma_stable_anchored_real_identity`: in `FractionalIdeal (𝓞 K)⁰ K`,
`spanSingleton (algebraMap x) · (𝔞(η)·𝔞(η⁻¹)) = spanSingleton (algebraMap y) · (𝔞(η₀)·𝔞(η₀⁻¹))`.
Dividing, the σ-stable anchored quotient `(𝔞(η)·𝔞(η⁻¹))/(𝔞(η₀)·𝔞(η₀⁻¹))` is generated by the real
ratio `(algebraMap y)/(algebraMap x)` — the producer-ready σ-stable analog of the (unsatisfiable)
raw-quotient span identity `spanSingleton (a/b) = 𝔞(η)/𝔞₀`. -/
theorem caseII_sigma_stable_anchored_real_frac_mul {m : ℕ} (D : RealCaseIIData37 K m)
    (hp : (37 : ℕ) ≠ 2) (η : nthRootsFinset 37 (1 : 𝓞 K))
    {J J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K))}
    {x y : 𝓞 (NumberField.maximalRealSubfield K)}
    (hJ : J.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η))
    (hJ0 : J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
      rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
        rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero))
    (hxy : Ideal.span {x} * J = Ideal.span {y} * J₀) :
    FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) x)) *
        ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy η *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv η) :
          Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰
          (algebraMap (𝓞 K) K (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K) y)) *
        ((rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy D.etaZero *
            rootDivZetaSubOneDvdGcd hp D.hζ D.equation D.hy (caseII_etaInv D.etaZero) :
          Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) := by
  have hint := caseII_sigma_stable_anchored_real_identity D hp η hJ hJ0 hxy
  have h := congrArg (fun I : Ideal (𝓞 K) => (↑I : FractionalIdeal (𝓞 K)⁰ K)) hint
  simpa only [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton] using h

end BernoulliRegular.FLT37.LehmerVandiver.CaseII

end
