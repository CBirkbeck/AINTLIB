import BernoulliRegular.FLT37.Eichler.CaseIISection91ExtractionProducer
import BernoulliRegular.FLT37.Eichler.CaseIIConjNormDescendedDatum
import BernoulliRegular.FLT37.Eichler.CaseIIFreeContentDescentStep
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.RealGenerator
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.CaseIIRealDescent
import BernoulliRegular.UnitQuotient.Washington83UnitForward

/-!
# [FLT37-CASEII-R2-L1] Washington's real anchor `ρ₀` (GTM 83 §9.1 p.169)

This file PROVES the genuine-new leaf **L1** `caseII_anchor_real_rho0` of Washington's second-case
descent (*Introduction to Cyclotomic Fields*, GTM 83, §9.1 p. 169, "Assumption I implies `B₀` is
principal … `B₀ = (ρ₀)`, `ρ₀` real").

## The mathematics

Let `B₀ = aEtaZeroDvdPPow` be the `𝔭`-free anchor root ideal of a **real** Case-II datum `D`
with coprime Fermat variables.

1. **`B₀` is `σ`-fixed** (`caseII_map_a_eta_zero`, since `η₀ = 1`) and **coprime to `𝔭`**
   (`not_p_div_a_zero`).
2. **`[B₀]³⁷ = 1`** (`caseII_anchorClass_pow37_eq_one_of_anchorCube` applied to
   `caseII_span_x_add_y_eq_anchorCube` under coprimality: `span(x+y) = 𝔭^{37m+1}·B₀³⁷`).
3. **`[B₀] = 1`, i.e. `B₀` is PRINCIPAL.**  This is the crux, and it is where the *correct* group
   matters: although `37 ∣ h⁻` (so `[B₀]` could be a nontrivial `37`-torsion class of `Cl(K)`),
   the proven `caseII_classGroup_mul_conj_eq_one` (Vandiver, `37 ∤ h⁺` =
   `Sinnott.flt37_not_dvd_hPlus`) gives `[B₀]·σ[B₀] = 1` for ANY `37`-torsion class; with
   `σ[B₀] = [B₀]` (`B₀` `σ`-fixed) this is `[B₀]² = 1`, and `gcd(2, 37) = 1` forces `[B₀] = 1`.
   (The class effectively lives in the `+`-part; the prior `Cl(K)`-degeneracy used the wrong group.)
4. **`B₀ = (ρ₀)` with `ρ₀` REAL.**  `B₀` `σ`-fixed and coprime to the ramified `𝔭` descends to a
   real-ideal model `J₀` of `𝒪_{K⁺}` (`comap_map_eq_of_unramifiedAt_support`, mirroring
   `caseII_sigma_stable_ideal_descends`); a generator `ρ` of `B₀` then has `σρ = u·ρ` with `u` a
   `σ`-anti unit, and `caseII_real_generator_of_sigma_stable_model` (the
   `(-1)^k·ζ^n`-classification + real-ideal model) produces a conjugation-fixed generator `ρ₀`.
5. **The anchor equation.**  `span(x+y) = 𝔭^{37m+1}·B₀³⁷`, `m` odd (`realCaseIIData37_odd_m`) so
   `37m+1 = 2e` even, `𝔭² = (Λ)` (`caseII_span_lambda_eq_p_sq`, `Λ = (1−ζ)(1−ζ³⁶)`); hence
   `span(x+y) = span(Λ^e·ρ₀³⁷)`, so `x+y = u₀·Λ^e·ρ₀³⁷` (associate), with `u₀` real because all of
   `x+y, Λ, ρ₀` are real (`σ` cancellation).  Set `η₀ = algebraMap u₀ : Kˣ`.

It imports only; it does **not** modify any existing file.  No `axiom`, no `sorry` in the final
`caseII_anchor_real_rho0`.

## References
* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.1, p. 169.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension UniqueFactorizationMonoid Polynomial
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

/-! ## Step 3: `B₀` is principal (the `Cl(K⁺)`-Vandiver `[B₀]² = 1 ∧ [B₀]³⁷ = 1` argument) -/

/-- **[L1-STEP-3] The anchor `B₀` is principal**, from `[B₀]² = 1` (Vandiver, `σ`-fixed) and
`[B₀]³⁷ = 1` (anchor cube), with `gcd(2, 37) = 1`.

For a real Case-II datum `D` with coprime Fermat variables, the `𝔭`-free anchor
`B₀ = aEtaZeroDvdPPow` is principal.

Mechanism (Washington p.169): `[B₀]³⁷ = 1` (`caseII_anchorClass_pow37_eq_one_of_anchorCube` on the
proven anchor-cube factorization `span(x+y) = 𝔭^{37m+1}·B₀³⁷`); and `[B₀]·σ[B₀] = 1`
(`caseII_classGroup_mul_conj_eq_one`, the proven Vandiver `37 ∤ h⁺` consequence for any
`37`-torsion class), with `σ[B₀] = [B₀]` because `B₀` is `σ`-fixed (`caseII_map_a_eta_zero` +
naturality `caseII_classGroup_conj_mk0`), so `[B₀]² = 1`.  `gcd(2, 37) = 1` forces `[B₀] = 1`. -/
theorem caseII_anchor_B0_isPrincipal {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K)))) :
    (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).IsPrincipal := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set 𝔞₀ := aEtaZeroDvdPPow hp D.hζ D.equation D.hy with h𝔞₀_def
  -- `𝔞₀ ≠ ⊥` (it divides `span z ≠ 0`).
  have h𝔞₀_ne0 : 𝔞₀ ≠ 0 := by
    have hz_ne : Ideal.span ({D.z} : Set (𝓞 K)) ≠ 0 :=
      caseIIData37_span_z_ne_bot D.toCaseIIData37
    have h𝔞₀_dvd_z : 𝔞₀ ∣ Ideal.span ({D.z} : Set (𝓞 K)) :=
      caseII_a_eta_zero_dvd_z D.toCaseIIData37 hp
    exact fun h0 => hz_ne (by rw [h0] at h𝔞₀_dvd_z; exact zero_dvd_iff.mp h𝔞₀_dvd_z)
  have h𝔞₀_ne : 𝔞₀ ≠ ⊥ := by rwa [Ideal.zero_eq_bot] at h𝔞₀_ne0
  -- `x + y ≠ 0` (else `x = -y` ⟹ `x³⁷+y³⁷ = 0` ⟹ `z = 0`, contradicting `hz`).
  have hxy_ne : D.x + D.y ≠ 0 := by
    intro h0
    have hx_eq : D.x = -D.y := by linear_combination h0
    have hpow0 : (D.ε : 𝓞 K) * ((D.hζ.toInteger - 1) ^ (m + 1) * D.z) ^ 37 = 0 := by
      rw [← D.equation, hx_eq, Odd.neg_pow (by decide)]; ring
    rcases mul_eq_zero.mp hpow0 with hε | hz37
    · exact D.ε.ne_zero hε
    · rcases mul_eq_zero.mp (pow_eq_zero_iff (by decide : 37 ≠ 0) |>.mp hz37) with hpow | hzz
      · exact D.hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 37)
          (pow_eq_zero_iff (by omega : m + 1 ≠ 0) |>.mp hpow)
      · exact D.hz (hzz ▸ dvd_zero _)
  have h𝔞₀_mem : 𝔞₀ ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞₀_ne
  set c := ClassGroup.mk0 (⟨𝔞₀, h𝔞₀_mem⟩ : (Ideal (𝓞 K))⁰) with hc_def
  -- `[B₀]³⁷ = 1` from the anchor cube.
  have hc37 : c ^ 37 = 1 := by
    have hcube := caseII_span_x_add_y_eq_anchorCube D hp hcop
    refine caseII_anchorClass_pow37_eq_one_of_anchorCube (m := m) (xpy := D.x + D.y)
      (s := (D.hζ.toInteger - 1 : 𝓞 K)) (𝔞₀ := 𝔞₀) ?_ ?_ hxy_ne h𝔞₀_ne0
    · rw [hcube]
    · exact D.hζ.toInteger_isPrimitiveRoot.sub_one_ne_zero (by decide : 1 < 37)
  -- `[B₀]·σ[B₀] = 1` (Vandiver), and `σ[B₀] = [B₀]` (`B₀` `σ`-fixed), so `[B₀]² = 1`.
  have hmul := caseII_classGroup_mul_conj_eq_one h_VC c hc37
  have hσc : ClassGroup.mulEquiv (ringOfIntegersComplexConj K).toRingEquiv c = c := by
    rw [hc_def, caseII_classGroup_conj_mk0 h𝔞₀_ne]
    congr 1
    exact Subtype.ext (caseII_map_a_eta_zero D hp)
  rw [hσc] at hmul
  have hc2 : c ^ 2 = 1 := by rw [sq]; exact hmul
  -- `gcd(2, 37) = 1` ⟹ `[B₀] = 1`.
  have hdvd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc2) (orderOf_dvd_of_pow_eq_one hc37)
  rw [show Nat.gcd 2 37 = 1 from by decide] at hdvd
  have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  exact (ClassGroup.mk0_eq_one_iff h𝔞₀_mem).mp hc1

/-! ## Step 4a: a `σ`-stable ideal coprime to `(37)` has `comap` coprime to `(37)` (generic) -/

omit [IsCyclotomicExtension {37} ℚ K] in
/-- **Generic: `σ`-stable `I` coprime to `(37)` ⟹ `I.comap` coprime to `(37)` in `𝒪_{K⁺}`** (the
unramified-support input), via the conjugation trace.

This is the ideal-generic form of `caseII_isCoprime_comap_int37` (which is stated for the specific
Washington product ideal): from `IsCoprime I (37)` (in `𝒪 K`) write `1 = a + c` (`a ∈ I`,
`c ∈ (37)`); then `2 = (a + σa) + (c + σc)` with `a + σa ∈ I` (`σ`-stable, `hI_stable`) and
`σ`-fixed, hence `= ι a⁺` (`a⁺ ∈ I.comap`), and `c + σc = ι(37·e⁺)`; injectivity gives
`2 = a⁺ + 37·e⁺ ∈ I.comap + (37)`, and Bézout (`1 = (-18)·2 + 37`) upgrades `2` to `1`. -/
theorem caseII_isCoprime_comap_int37_of_stable
    (I : Ideal (𝓞 K))
    (hI_stable : I.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom = I)
    (hcop : IsCoprime I (Ideal.span {(37 : 𝓞 K)})) :
    IsCoprime (I.comap (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)))
      (Ideal.span {(37 : 𝓞 (NumberField.maximalRealSubfield K))}) := by
  set σ := (NumberField.IsCMField.ringOfIntegersComplexConj K).toRingEquiv.toRingHom with hσ
  have hinv : ∀ x : 𝓞 K, σ (σ x) = x := fun x => by
    apply RingOfIntegers.ext
    simp only [hσ, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
      NumberField.IsCMField.coe_ringOfIntegersComplexConj,
      NumberField.IsCMField.complexConj_apply_apply]
  -- `1 = a + c`, `a ∈ I`, `c ∈ (37)`.
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp
    ((Ideal.isCoprime_iff_sup_eq.mp hcop) ▸
      (Submodule.mem_top : (1 : 𝓞 K) ∈ (⊤ : Ideal (𝓞 K))))
  -- `a + σa ∈ I`, `σ`-fixed, so it descends.
  have haσ_I : a + σ a ∈ I := I.add_mem ha (hI_stable ▸ Ideal.mem_map_of_mem σ ha)
  have haσ_fix : NumberField.IsCMField.ringOfIntegersComplexConj K (a + σ a) = a + σ a := by
    change σ (a + σ a) = a + σ a; rw [map_add, hinv]; ring
  obtain ⟨aP, haP⟩ := Set.mem_range.mp
    ((NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) (a + σ a)).mp haσ_fix)
  -- `c = 37 * d`, so `c + σc = 37 * (d + σd)`, also descending.
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
  have hdσ_fix : NumberField.IsCMField.ringOfIntegersComplexConj K (d + σ d) = d + σ d := by
    change σ (d + σ d) = d + σ d; rw [map_add, hinv]; ring
  obtain ⟨eP, heP⟩ := Set.mem_range.mp
    ((NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K) (d + σ d)).mp hdσ_fix)
  have hσ37 : σ (37 : 𝓞 K) = 37 := map_ofNat σ 37
  have hσ1 : σ a + 37 * σ d = 1 := by
    have h := congrArg σ hac
    rwa [map_add, map_mul, hσ37, map_one] at h
  -- `2 = aP + 37 * eP` in `𝒪 K⁺` (injectivity + the trace `(a+σa)+37(d+σd)=2`).
  have h2 : (2 : 𝓞 (NumberField.maximalRealSubfield K)) = aP + 37 * eP := by
    apply FaithfulSMul.algebraMap_injective (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)
    rw [map_add, map_mul, haP, heP]
    simp only [map_ofNat]
    linear_combination -hac - hσ1
  -- Bézout `1 = (-18)·2 + 37·…` ⟹ `1 ∈ I.comap + (37)`.
  have haP_mem : aP ∈ I.comap (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) := by
    rw [Ideal.mem_comap, haP]; exact haσ_I
  have hbez : (1 : 𝓞 (NumberField.maximalRealSubfield K)) =
      (-18) * aP + (-18 * eP + 1) * 37 := by linear_combination (-18) * h2
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, hbez]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ haP_mem))
    (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

/-! ## Step 4b: `B₀` is coprime to `(37)`, and descends from a real-ideal model -/

/-- **`B₀` is coprime to `𝔭 = (ζ−1)`.** `not_p_div_a_zero` gives `𝔭 ∤ B₀`; with `𝔭` maximal,
`B₀ ⊔ 𝔭 = ⊤`. -/
theorem caseII_isCoprime_B0_zetaSubOne {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    IsCoprime (aEtaZeroDvdPPow hp D.hζ D.equation D.hy)
      (Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)}) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hprime : Prime (Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)}) :=
    Ideal.prime_span_singleton_iff.mpr D.hζ.zeta_sub_one_prime'
  have hmax : (Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)}).IsMaximal :=
    (Ideal.isPrime_of_prime hprime).isMaximal hprime.ne_zero
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hne
  exact not_p_div_a_zero hp D.hζ D.equation D.hy D.hz
    (Ideal.dvd_iff_le.mpr (le_sup_left.trans (hmax.eq_of_le hne le_sup_right).ge))

/-- **`B₀` is coprime to `(37)`.** Since `(37) = 𝔭³⁶` (`associated_zeta_sub_one_pow_prime`),
coprimality to `𝔭` (`caseII_isCoprime_B0_zetaSubOne`) gives coprimality to its power `(37)`. -/
theorem caseII_isCoprime_B0_int37 {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    IsCoprime (aEtaZeroDvdPPow hp D.hζ D.equation D.hy) (Ideal.span {(37 : 𝓞 K)}) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hsp : Ideal.span {(37 : 𝓞 K)} = Ideal.span {(D.hζ.toInteger - 1 : 𝓞 K)} ^ (37 - 1) := by
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
    exact_mod_cast (associated_zeta_sub_one_pow_prime D.hζ).symm
  rw [hsp]
  exact (caseII_isCoprime_B0_zetaSubOne D hp).pow_right

/-- **`B₀` is `Gal(K/K⁺)`-fixed under `comap`.** For `σ = 1` trivial; for `σ = complexConj` it is
the `σ`-fixedness `caseII_map_a_eta_zero` (`σ B₀ = B₀`) transported through
`caseII_galRestrict_complexConj_eq`. -/
theorem caseII_B0_comap_fixed {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (σ : K ≃ₐ[NumberField.maximalRealSubfield K] K) :
    (aEtaZeroDvdPPow hp D.hζ D.equation D.hy).comap
      (galRestrict (𝓞 (NumberField.maximalRealSubfield K)) (NumberField.maximalRealSubfield K) K
        (𝓞 K) σ) =
    aEtaZeroDvdPPow hp D.hζ D.equation D.hy := by
  rcases BernoulliRegular.algEquiv_eq_one_or_complexConj (K := K) σ with h1 | hc
  · rw [h1, map_one]; exact Ideal.comap_id _
  · rw [hc, caseII_galRestrict_complexConj_eq]
    nth_rewrite 1 [← caseII_map_a_eta_zero D hp]
    exact Ideal.comap_map_of_bijective _
      (EquivLike.bijective (NumberField.IsCMField.ringOfIntegersComplexConj K))

/-- **`B₀` descends from `𝒪_{K⁺}`.** The `Gal(K/K⁺)`-fixed anchor `B₀` is the extension of
`J₀ = B₀.comap`.  Combines the `Gal`-fixed comap condition (`caseII_B0_comap_fixed`) with
`comap_map_eq_of_unramifiedAt_support`, whose unramified support holds because every prime factor of
`B₀.comap` avoids the prime over `37` (else, with `IsCoprime (B₀.comap) (37)`
— `caseII_isCoprime_comap_int37_of_stable` on the `σ`-stable, `(37)`-coprime `B₀` — it would be
`⊤`), so `isUnramifiedAt_of_not_over_37` applies. -/
theorem caseII_B0_ideal_descends {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2) :
    ∃ J₀ : Ideal (𝓞 (NumberField.maximalRealSubfield K)),
      J₀.map (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) =
        aEtaZeroDvdPPow hp D.hζ D.equation D.hy := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  refine ⟨(aEtaZeroDvdPPow hp D.hζ D.equation D.hy).comap
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)), ?_⟩
  apply comap_map_eq_of_unramifiedAt_support (R := 𝓞 (NumberField.maximalRealSubfield K))
    (K := NumberField.maximalRealSubfield K) (L := K) (S := 𝓞 K)
  · exact caseII_B0_comap_fixed D hp
  · intro q hq_mem
    rw [Multiset.mem_toFinset] at hq_mem
    have hq_prime : Prime q := UniqueFactorizationMonoid.prime_of_factor q hq_mem
    haveI hq_isPrime : q.IsPrime := Ideal.isPrime_of_prime hq_prime
    apply isUnramifiedAt_of_not_over_37 q hq_prime.ne_zero
    intro h37
    have hcop := caseII_isCoprime_comap_int37_of_stable
      (aEtaZeroDvdPPow hp D.hζ D.equation D.hy) (caseII_map_a_eta_zero D hp)
      (caseII_isCoprime_B0_int37 D hp)
    rw [Ideal.isCoprime_iff_sup_eq] at hcop
    have htop : (⊤ : Ideal (𝓞 (NumberField.maximalRealSubfield K))) ≤ q := by
      rw [← hcop]
      refine sup_le (Ideal.dvd_iff_le.mp (UniqueFactorizationMonoid.dvd_of_mem_factors hq_mem)) ?_
      rw [Ideal.span_singleton_le_iff_mem]
      have : (37 : 𝓞 (NumberField.maximalRealSubfield K)) =
          algebraMap ℤ (𝓞 (NumberField.maximalRealSubfield K)) 37 :=
        (map_ofNat (algebraMap ℤ (𝓞 (NumberField.maximalRealSubfield K))) 37).symm
      rw [this]; exact h37
    exact hq_isPrime.ne_top (top_le_iff.mp htop)

/-! ## Step 4c: `B₀` has a REAL generator `ρ₀` -/

/-- **[L1-STEP-4] The anchor `B₀` has a REAL generator `ρ₀`.**

For a real Case-II datum `D` with coprime Fermat variables, the `𝔭`-free anchor
`B₀ = aEtaZeroDvdPPow` has a conjugation-fixed generator: `∃ ρ₀, σ ρ₀ = ρ₀ ∧ span {ρ₀} = B₀`.

Proof: `B₀` is principal (`caseII_anchor_B0_isPrincipal`); pick a generator `ρ` of `B₀`.  `B₀` is
`σ`-fixed (`caseII_map_a_eta_zero`), so `span {σρ} = (span {ρ}).map σ = B₀.map σ = B₀ = span {ρ}`,
giving `Associated ρ (σρ)`, i.e. `σρ = u·ρ` with `u : (𝓞 K)ˣ`.  Applying `σ` and cancelling the
nonzero `ρ` shows `u` is `σ`-anti (`σu = u⁻¹`).  `B₀` descends from a real-ideal model `J₀`
(`caseII_B0_ideal_descends`), so `caseII_real_generator_of_sigma_stable_model` (the `(-1)^k·ζ^n`
classification + real-ideal model, which rules out the `-1`) gives a conjugation-fixed generator. -/
theorem caseII_anchor_B0_real_generator {m : ℕ} (D : RealCaseIIData37 K m) (hp : (37 : ℕ) ≠ 2)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K)))) :
    ∃ ρ0 : 𝓞 K,
      NumberField.IsCMField.ringOfIntegersComplexConj K ρ0 = ρ0 ∧
      Ideal.span ({ρ0} : Set (𝓞 K)) = aEtaZeroDvdPPow hp D.hζ D.equation D.hy := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set 𝔞₀ := aEtaZeroDvdPPow hp D.hζ D.equation D.hy with h𝔞₀_def
  -- `B₀` principal with generator `ρ`.
  obtain ⟨ρ, hρ⟩ := (caseII_anchor_B0_isPrincipal D hp h_VC hcop).principal
  have hρspan : Ideal.span ({ρ} : Set (𝓞 K)) = 𝔞₀ := hρ.symm
  -- `B₀ ≠ ⊥`, so `ρ ≠ 0`.
  have h𝔞₀_ne : 𝔞₀ ≠ ⊥ := by
    have hz_ne : Ideal.span ({D.z} : Set (𝓞 K)) ≠ 0 :=
      caseIIData37_span_z_ne_bot D.toCaseIIData37
    have h𝔞₀_dvd_z : 𝔞₀ ∣ Ideal.span ({D.z} : Set (𝓞 K)) :=
      caseII_a_eta_zero_dvd_z D.toCaseIIData37 hp
    rw [Ideal.zero_eq_bot] at hz_ne
    exact fun h0 => hz_ne (by rw [h0] at h𝔞₀_dvd_z; exact zero_dvd_iff.mp h𝔞₀_dvd_z)
  have hρ_ne : ρ ≠ 0 := by
    intro h0
    apply h𝔞₀_ne
    rw [← hρspan, h0, Set.singleton_zero, Ideal.span_zero]
  -- `span {σρ} = span {ρ}`: `B₀` is `σ`-fixed.
  have hσspan : Ideal.span ({NumberField.IsCMField.ringOfIntegersComplexConj K ρ} : Set (𝓞 K)) =
      Ideal.span ({ρ} : Set (𝓞 K)) := by
    rw [← caseII_map_span_singleton_complexConj ρ, hρspan, caseII_map_a_eta_zero D hp]
  -- `Associated ρ (σρ)`: `σρ = u·ρ` for a unit `u`.
  obtain ⟨u, hu_eq⟩ := Ideal.span_singleton_eq_span_singleton.mp hσspan.symm
  -- `hu_eq : ρ * u = σ ρ`; rewrite to `σ ρ = u * ρ`.
  have hu : NumberField.IsCMField.ringOfIntegersComplexConj K ρ = u * ρ := by
    rw [← hu_eq, mul_comm]
  -- `u` is `σ`-anti: apply `σ` to `σρ = u·ρ`, cancel nonzero `ρ`.
  have hu_anti : NumberField.IsCMField.unitsComplexConj K u = u⁻¹ := by
    -- `ρ = σ(σρ) = σ(u·ρ) = σu·σρ = σu·u·ρ`, so `σu·u = 1`.
    have hcalc : ρ = (NumberField.IsCMField.unitsComplexConj K u : 𝓞 K) * (u * ρ) := by
      calc ρ = NumberField.IsCMField.ringOfIntegersComplexConj K
                (NumberField.IsCMField.ringOfIntegersComplexConj K ρ) :=
              (ringOfIntegersComplexConj_apply_apply ρ).symm
        _ = NumberField.IsCMField.ringOfIntegersComplexConj K (u * ρ) := by rw [hu]
        _ = NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) *
              NumberField.IsCMField.ringOfIntegersComplexConj K ρ := by rw [map_mul]
        _ = NumberField.IsCMField.ringOfIntegersComplexConj K (u : 𝓞 K) * (u * ρ) := by rw [hu]
        _ = (NumberField.IsCMField.unitsComplexConj K u : 𝓞 K) * (u * ρ) := by
              rw [← unitsComplexConj_val_eq_ringOfIntegersComplexConj]
    -- `(σu·u)·ρ = ρ` and `ρ ≠ 0` ⟹ `σu·u = 1` as units.
    have hunit : (NumberField.IsCMField.unitsComplexConj K u * u : (𝓞 K)ˣ) = 1 := by
      apply Units.ext
      have : ((NumberField.IsCMField.unitsComplexConj K u : 𝓞 K) * (u : 𝓞 K)) * ρ = 1 * ρ := by
        rw [one_mul, mul_assoc]; exact hcalc.symm
      simpa using mul_right_cancel₀ hρ_ne this
    rw [eq_inv_iff_mul_eq_one]; exact hunit
  -- The real-ideal model `J₀`.
  obtain ⟨J₀, hJ₀⟩ := caseII_B0_ideal_descends D hp
  -- Feed everything to `caseII_real_generator_of_sigma_stable_model`.
  obtain ⟨b, hb_real, hb_span⟩ := caseII_real_generator_of_sigma_stable_model
    J₀ ρ u (by rw [hJ₀, hρspan]) hu hu_anti
  exact ⟨b, hb_real, by rw [hb_span, hρspan]⟩

/-! ## Step 5: the anchor equation `x+y = η₀·Λ^e·ρ₀³⁷`, `η₀` real (generic `K`, given `h_VC`) -/

/-- **`Λ_int = (1−ζ_spec)(1−ζ_spec³⁶)` is real** (`σ`-fixed), since `ζ_spec³⁷ = 1`. Re-export of
`washington_L_real` at `η = ζ_spec`. -/
theorem caseII_lambda_int_real :
    NumberField.IsCMField.ringOfIntegersComplexConj K
        ((1 - (zeta_spec 37 ℚ K).toInteger) * (1 - (zeta_spec 37 ℚ K).toInteger ^ 36)) =
      (1 - (zeta_spec 37 ℚ K).toInteger) * (1 - (zeta_spec 37 ℚ K).toInteger ^ 36) :=
  washington_L_real (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.pow_eq_one

/-- **[L1 — generic `K`] Washington's real anchor `ρ₀` and anchor equation**, given the real-class
hypothesis `h_VC` (`37 ∤ h⁺`).

For a real Case-II datum `D` with coprime Fermat variables, there are `e ≥ 1`, a real unit
`η₀ : Kˣ`, and a **real** generator `ρ₀` of the `𝔭`-free anchor `B₀ = aEtaZeroDvdPPow`, with
the anchor equation `algebraMap(x+y) = η₀ · Λ^e · algebraMap(ρ₀)³⁷`, `Λ = (1−ζ_spec)(1−ζ_spec³⁶)`.

Proof (Washington §9.1 p.169): `ρ₀` is the real generator of `caseII_anchor_B0_real_generator`
(B₀ principal via `Cl(K⁺)`-Vandiver, real via the real-ideal-model descent).  `m` is odd
(`realCaseIIData37_odd_m`) so `37m+1 = 2e`; with `span(x+y) = 𝔭^{37m+1}·B₀³⁷`
(`caseII_span_x_add_y_eq_anchorCube`), `𝔭² = (Λ)` (`caseII_span_lambda_eq_p_sq`), and
`span(ρ₀) = B₀`, we get `span(x+y) = span(Λ^e·ρ₀³⁷)`, so `x+y = u₀·Λ^e·ρ₀³⁷` (associate); `u₀` is
real because `x+y, Λ, ρ₀` are real (`σ`-cancellation), and `η₀ = algebraMap u₀`. -/
theorem caseII_anchor_real_rho0_of_VC
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 K m)
    (h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield K)))))
    (hodd : Odd m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 K))) (Ideal.span ({D.y} : Set (𝓞 K)))) :
    ∃ (e : ℕ) (η0 : Kˣ) (ρ0 : 𝓞 K),
      1 ≤ e ∧
      NumberField.IsCMField.ringOfIntegersComplexConj K ρ0 = ρ0 ∧
      Ideal.span ({ρ0} : Set (𝓞 K)) =
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ∧
      NumberField.IsCMField.complexConj K (η0 : K) = (η0 : K) ∧
      algebraMap (𝓞 K) K (D.x + D.y) =
        (η0 : K) *
          (algebraMap (𝓞 K) K
            ((1 - (zeta_spec 37 ℚ K).toInteger) *
              (1 - (zeta_spec 37 ℚ K).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 K) K ρ0 ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hp : (37 : ℕ) ≠ 2 := by decide
  set 𝔭 : Ideal (𝓞 K) := Ideal.span ({(D.hζ.toInteger - 1 : 𝓞 K)} : Set (𝓞 K)) with h𝔭_def
  set 𝔞₀ := aEtaZeroDvdPPow hp D.hζ D.equation D.hy with h𝔞₀_def
  set Λi : 𝓞 K := (1 - (zeta_spec 37 ℚ K).toInteger) * (1 - (zeta_spec 37 ℚ K).toInteger ^ 36)
    with hΛi_def
  -- The real anchor generator `ρ₀`.
  obtain ⟨ρ0, hρ0_real, hρ0_span⟩ := caseII_anchor_B0_real_generator D hp h_VC hcop
  -- `m` odd ⟹ `37m+1 = 2e`, with `e = 37k+19 ≥ 1`.
  obtain ⟨k, hk⟩ := hodd
  set e : ℕ := 37 * k + 19 with he_def
  have h2e : 37 * m + 1 = 2 * e := by rw [hk, he_def]; ring
  -- Anchor-cube ideal factorization: `span(x+y) = 𝔭^{37m+1}·B₀³⁷`.
  have hcube : Ideal.span ({D.x + D.y} : Set (𝓞 K)) = 𝔭 ^ (37 * m + 1) * 𝔞₀ ^ 37 :=
    caseII_span_x_add_y_eq_anchorCube D hp hcop
  -- `span(Λi) = 𝔭²`, so `𝔭^{37m+1} = 𝔭^{2e} = span(Λi)^e = span(Λi^e)`.
  have hΛspan : Ideal.span ({Λi} : Set (𝓞 K)) = 𝔭 ^ 2 :=
    caseII_span_lambda_eq_p_sq D.hζ (zeta_spec 37 ℚ K)
  have hp_pow : 𝔭 ^ (37 * m + 1) = Ideal.span ({Λi ^ e} : Set (𝓞 K)) := by
    rw [← Ideal.span_singleton_pow, hΛspan, ← pow_mul, h2e]
  -- `span(ρ0)^37 = 𝔞₀^37 = span(ρ0^37)`.
  have hρ0_pow : 𝔞₀ ^ 37 = Ideal.span ({ρ0 ^ 37} : Set (𝓞 K)) := by
    rw [h𝔞₀_def, ← hρ0_span, Ideal.span_singleton_pow]
  -- `span(x+y) = span(Λi^e · ρ0^37)`.
  have hspan_eq : Ideal.span ({D.x + D.y} : Set (𝓞 K)) =
      Ideal.span ({Λi ^ e * ρ0 ^ 37} : Set (𝓞 K)) := by
    rw [hcube, hp_pow, hρ0_pow, Ideal.span_singleton_mul_span_singleton]
  -- `Associated (x+y) (Λi^e · ρ0^37)`: `(x+y)·u = Λi^e·ρ0^37` for a unit `u`.
  obtain ⟨u, hu_eq⟩ := Ideal.span_singleton_eq_span_singleton.mp hspan_eq
  -- so `x+y = u⁻¹·(Λi^e·ρ0^37)`.
  have hxy_int : D.x + D.y = (u⁻¹ : (𝓞 K)ˣ) * (Λi ^ e * ρ0 ^ 37) := by
    have h1 : (D.x + D.y) * (u : 𝓞 K) = Λi ^ e * ρ0 ^ 37 := hu_eq
    have h2 : D.x + D.y = (Λi ^ e * ρ0 ^ 37) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
      rw [← h1, mul_assoc, Units.mul_inv, mul_one]
    rw [h2, mul_comm]
  -- `Λi^e·ρ0^37 ≠ 0`.
  have hΛi_ne : Λi ≠ 0 := by
    rw [hΛi_def]
    refine mul_ne_zero ?_ ?_
    · have : (zeta_spec 37 ℚ K).toInteger ≠ 1 :=
        (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37)
      exact fun h => this (by linear_combination -h)
    · have hne : (zeta_spec 37 ℚ K).toInteger ^ 36 ≠ 1 := by
        intro h
        have h37 : (zeta_spec 37 ℚ K).toInteger ^ 37 = 1 :=
          (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.pow_eq_one
        have : (zeta_spec 37 ℚ K).toInteger = 1 := by
          have hps : (zeta_spec 37 ℚ K).toInteger ^ 37 =
              (zeta_spec 37 ℚ K).toInteger ^ 36 * (zeta_spec 37 ℚ K).toInteger := pow_succ _ _
          rw [h37, h, one_mul] at hps; exact hps.symm
        exact (zeta_spec 37 ℚ K).toInteger_isPrimitiveRoot.ne_one (by decide : 1 < 37) this
      exact fun h => hne (by linear_combination -h)
  have hρ0_ne : ρ0 ≠ 0 := by
    intro h0
    have hbot : aEtaZeroDvdPPow hp D.hζ D.equation D.hy = ⊥ := by
      rw [← hρ0_span, h0, Set.singleton_zero, Ideal.span_zero]
    have hz_ne : Ideal.span ({D.z} : Set (𝓞 K)) ≠ 0 := caseIIData37_span_z_ne_bot D.toCaseIIData37
    have h𝔞₀_dvd_z : aEtaZeroDvdPPow hp D.hζ D.equation D.hy ∣
        Ideal.span ({D.z} : Set (𝓞 K)) :=
      caseII_a_eta_zero_dvd_z D.toCaseIIData37 hp
    rw [Ideal.zero_eq_bot] at hz_ne
    rw [hbot] at h𝔞₀_dvd_z
    exact hz_ne (zero_dvd_iff.mp h𝔞₀_dvd_z)
  have hΛρ_ne : Λi ^ e * ρ0 ^ 37 ≠ 0 := mul_ne_zero (pow_ne_zero _ hΛi_ne) (pow_ne_zero _ hρ0_ne)
  -- `u⁻¹` (hence `η0 := algebraMap u⁻¹`) is REAL: apply `σ` to `x+y = u⁻¹·(Λi^e·ρ0^37)`.
  set σ := NumberField.IsCMField.ringOfIntegersComplexConj K with hσ_def
  have hΛi_real : σ Λi = Λi := caseII_lambda_int_real
  have hxy_real : σ (D.x + D.y) = D.x + D.y := by rw [hσ_def, map_add, D.x_real, D.y_real]
  have hΛρ_real : σ (Λi ^ e * ρ0 ^ 37) = Λi ^ e * ρ0 ^ 37 := by
    rw [hσ_def] at hΛi_real hρ0_real ⊢
    rw [map_mul, map_pow, map_pow, hΛi_real, hρ0_real]
  -- `σ(u⁻¹) = u⁻¹` as elements.
  have huinv_real : σ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
    have hσxy : (D.x + D.y) = σ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (Λi ^ e * ρ0 ^ 37) := by
      calc D.x + D.y = σ (D.x + D.y) := hxy_real.symm
        _ = σ (((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (Λi ^ e * ρ0 ^ 37)) := by rw [hxy_int]
        _ = σ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * σ (Λi ^ e * ρ0 ^ 37) := by rw [hσ_def, map_mul]
        _ = σ ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (Λi ^ e * ρ0 ^ 37) := by rw [hΛρ_real]
    -- cancel `Λi^e·ρ0^37` from `hxy_int` vs `hσxy`.
    have := hxy_int.symm.trans hσxy
    exact (mul_right_cancel₀ hΛρ_ne this).symm
  -- The field unit `η0 := algebraMap u⁻¹`, real, satisfying the anchor equation.
  refine ⟨e, Units.map (algebraMap (𝓞 K) K).toMonoidHom u⁻¹, ρ0, by omega, hρ0_real, hρ0_span,
    ?_, ?_⟩
  · -- reality of `η0` in `K`.
    have : (Units.map (algebraMap (𝓞 K) K).toMonoidHom u⁻¹ : K) =
        algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by
      simp [Units.coe_map]
    rw [this, ← coe_ringOfIntegersComplexConj, ← hσ_def, huinv_real]
  · -- the anchor equation in `K`.
    have hmapxy := congrArg (algebraMap (𝓞 K) K) hxy_int
    rw [map_mul, map_mul, map_pow, map_pow] at hmapxy
    rw [hmapxy]
    have hu0coe : (Units.map (algebraMap (𝓞 K) K).toMonoidHom u⁻¹ : K) =
        algebraMap (𝓞 K) K ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by simp [Units.coe_map]
    rw [hu0coe, hΛi_def]
    ring

/-! ## The L1 leaf `caseII_anchor_real_rho0`, specialised to `CyclotomicField 37 ℚ` -/

variable [NumberField.IsCMField (CyclotomicField 37 ℚ)]

/-- **[L1 — REAL ANCHOR] Washington's real anchor generator `ρ₀`** (Washington GTM 83 §9.1 p.169),
the genuine-new leaf of the R2 second-case descent.

For a real Case-II datum `D` over `CyclotomicField 37 ℚ` with coprime Fermat variables, the `𝔭`-free
anchor root ideal `B₀ = aEtaZeroDvdPPow` is principal with a **real** generator `ρ₀`
(`ringOfIntegersComplexConj K ρ₀ = ρ₀`), giving the anchor equation
`algebraMap(x+y) = η₀ · Λ^e · ρ₀³⁷` with `η₀ : Kˣ` a **real** unit, `Λ = (1−ζ_spec)(1−ζ_spec³⁶)`,
`e ≥ 1`.

This discharges the `sorry` of `CaseIIWashingtonDescentSkeleton.caseII_anchor_real_rho0` (which is
defined to be exactly this): it is the specialisation of `caseII_anchor_real_rho0_of_VC` to
`K = CyclotomicField 37 ℚ`, with the real-class hypothesis `h_VC` discharged by the proven
`Sinnott.flt37_not_dvd_hPlus` (`37 ∤ h⁺`) and `m` odd by `realCaseIIData37_odd_m`. -/
theorem caseII_anchor_real_rho0_impl
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    {m : ℕ} (D : RealCaseIIData37 (CyclotomicField 37 ℚ) m)
    (hcop : IsCoprime (Ideal.span ({D.x} : Set (𝓞 (CyclotomicField 37 ℚ))))
      (Ideal.span ({D.y} : Set (𝓞 (CyclotomicField 37 ℚ))))) :
    ∃ (e : ℕ) (η0 : (CyclotomicField 37 ℚ)ˣ) (ρ0 : 𝓞 (CyclotomicField 37 ℚ)),
      1 ≤ e ∧
      ringOfIntegersComplexConj (CyclotomicField 37 ℚ) ρ0 = ρ0 ∧
      Ideal.span ({ρ0} : Set (𝓞 (CyclotomicField 37 ℚ))) =
        aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy ∧
      complexConj (CyclotomicField 37 ℚ) (η0 : CyclotomicField 37 ℚ) =
          (η0 : CyclotomicField 37 ℚ) ∧
      algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) (D.x + D.y) =
        (η0 : CyclotomicField 37 ℚ) *
          (algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ)
            ((1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger) *
              (1 - (zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger ^ 36))) ^ e *
          algebraMap (𝓞 (CyclotomicField 37 ℚ)) (CyclotomicField 37 ℚ) ρ0 ^ 37 := by
  have h_VC : (37 : ℕ).Coprime
      (Fintype.card (ClassGroup (𝓞 (NumberField.maximalRealSubfield (CyclotomicField 37 ℚ))))) :=
    (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 37)).mpr Sinnott.flt37_not_dvd_hPlus
  exact caseII_anchor_real_rho0_of_VC D h_VC (realCaseIIData37_odd_m D) hcop

end BernoulliRegular.FLT37.Eichler

end

end
