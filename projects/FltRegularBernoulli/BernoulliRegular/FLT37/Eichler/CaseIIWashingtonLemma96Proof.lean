import BernoulliRegular.FLT37.Eichler.CaseIIRootClassConjFixedClosed
import BernoulliRegular.FLT37.Eichler.CaseIIRootClassConjFixedProof
import BernoulliRegular.FLT37.Eichler.CaseIISection91ProductHalfProof
import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PrimeIdentification
import BernoulliRegular.FLT37.Eichler.CaseIIWashingtonCoprimeThreaded

/-!
# [F4] Washington Lemma 9.6 for `p = 37`, `ℓ = 149` — PROVEN

This file **proves** the rational **Washington Lemma 9.6** (GTM 83, p. 176–177): for a Case-II
Fermat triple `a³⁷ + b³⁷ = c³⁷` (coprime, `37 ∣ abc`), the auxiliary prime `ℓ = 149` divides
**none** of the two `37`-coprime slots.  This is exactly the `h_lemma96` hypothesis of the
coprime-threaded FLT37 endpoint `fermatLastTheoremFor_thirtyseven_of_lemma96`
(`CaseIIWashingtonCoprimeThreaded.lean`), discharged here unconditionally — so Fermat's Last
Theorem for `37` now rests on the carried **Kellner** input alone
(`fermatLastTheoremFor_thirtyseven_of_kellner`).

## Washington's proof, and how each step is realised

Slot the triple so that `Y` is the `149`-divisible slot, `Z` the `37`-divisible slot and
`X` the third (sign juggling: `37` is odd).  Then `∏_{η³⁷=1} (Y − ηZ) = Y³⁷ − Z³⁷ = (−X)³⁷`.

1. **Coprime ideal factorisation** (`lemma96_exists_ideal`): the factors `Y − ηZ` are pairwise
   coprime — a common maximal `𝔮` of two factors contains `(η₂ − η₁)Z`; the root difference is
   associated to `ζ − 1` (`ntRootsFinset_pairwise_associated_sub_one_sub_of_prime`), and
   `(ζ−1)³⁶ ~ 37 ∣ Z`, so in either case `Z ∈ 𝔮`, hence `Y ∈ 𝔮`, hence `1 ∈ 𝔮` by Bézout
   (`IsCoprime Y Z`).  `Finset.exists_eq_pow_of_mul_eq_pow_of_coprime` then gives
   `(Y − ζ^{±1}Z) = A_{±1}³⁷`.
2. **The anti-fixed radical is a `37`-th power** (`lemma96_radical_isPthPower`):
   `α = (Y−ζZ)/(Y−ζ³⁶Z)` is anti-fixed (`Y, Z ∈ ℤ`), is **primary**
   (`α − 1 = (ζ³⁶−ζ)Z/(Y−ζ³⁶Z)` with `(ζ³⁶−ζ) ~ (ζ−1)` and `(ζ−1)³⁶ ~ 37 ∣ Z` giving the full
   `(ζ−1)³⁷`), and `(α) = (A₁/A₂)³⁷` as fractional ideals.  The **proven** ideal-theoretic
   Washington Lemma 9.1 (`caseIIIdealKummerUnramified37_proven`) makes `K(α^{1/37})/K`
   unramified, and the **proven** Lemma 9.2 Hilbert-94 core
   (`flt37_antiFixed_radical_isPthPower`, under the proven `Sinnott.flt37_not_dvd_hPlus`)
   gives `α = β³⁷`.
3. **Product half** (`lemma96_product_real_generator`): `C = A₁A₂` is σ-stable (conjugation swaps
   `A₁ ↔ A₂` by uniqueness of ideal `37`-th roots), coprime to `(37)`, with `C³⁷ = (F₁F₂)`
   principal.  It descends to `𝓞 K⁺` (the localized Galois descent
   `comap_map_eq_of_unramifiedAt_support` away from the ramified prime), where `¬37 ∣ h⁺` forces
   it principal (`caseII_productHalf_J_isPrincipal`), so `C = (γ₀)` with `γ₀` **real**.
4. **Factor equations** (`lemma96_factor_equations`): `F₁² = α·(F₁F₂) = β³⁷·u·γ₀³⁷` with the
   unit `u = F₁F₂/γ₀³⁷` real; Washington's `(p+1)/2`-power trick
   (`washington_factor_of_squared_pair`) yields `F₁ = u^{19}·ρ³⁷`, `F₂ = u^{19}·(σρ)³⁷` with the
   **integral** unit `u^{19}` and (by integral closedness) integral `ρ`.
5. **Finite-field contradiction** (`lemma96_core`): reduce along the explicit residue map
   `φ : 𝓞 K →+* ZMod 149` (`cyclotomicReduction`, `ζ ↦ 2⁴ = 16`).  `149 ∣ Y` kills `Y`;
   `149 ∤ Z` (coprimality), so dividing the two reduced factor equations gives
   `16·s³⁷ = 16³⁶·r³⁷` with `r, s ≠ 0` in `𝔽₁₄₉`.  Raising to the `4`-th power and using
   `w¹⁴⁸ = 1` gives `16¹⁶ = 16⁵⁷⁶` — false by `decide` (the order of `16` is `37 ∤ 4`).
6. **Slotting** (`caseII_washington_lemma96`): the gcd-1 condition plus the equation make
   `a, b, c` pairwise coprime; `37` divides at least one slot, and for the `149`-divisible slot
   `x` (with `37 ∤ x`) each arrangement feeds `lemma96_core` after odd-power sign juggling.

It imports only; it does **not** modify any existing file.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., GTM 83, §9.2, Lemma 9.6 (p. 176–177).
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension NumberField.IsCMField Polynomial Ideal
open scoped nonZeroDivisors

namespace BernoulliRegular.FLT37.Eichler

open FLT37.LehmerVandiver.CaseII

local notation3 "K37" => CyclotomicField 37 ℚ
local notation3 "KP37" => NumberField.maximalRealSubfield (CyclotomicField 37 ℚ)
local notation3 "ζ₀" =>
  ((IsCyclotomicExtension.zeta_spec 37 ℚ (CyclotomicField 37 ℚ)).toInteger :
    𝓞 (CyclotomicField 37 ℚ))
local notation3 "σ₀" => NumberField.IsCMField.ringOfIntegersComplexConj (CyclotomicField 37 ℚ)
local notation3 "σRH" => (NumberField.IsCMField.ringOfIntegersComplexConj
  (CyclotomicField 37 ℚ)).toRingEquiv.toRingHom

/-! ## 1. Integer arithmetic: pairwise coprimality from the Fermat equation -/

/-- **Pairwise coprimality of a Fermat triple.**  If `a³⁷ + b³⁷ = c³⁷` and
`gcd {a, b, c} = 1`, then `a, b, c` are pairwise coprime: a common prime of two of them divides
the third's `37`-th power (via the equation), hence the third, hence the full gcd `= 1`. -/
theorem lemma96_pairwise_coprime {a b c : ℤ} (H : a ^ 37 + b ^ 37 = c ^ 37)
    (hgcd : ({a, b, c} : Finset ℤ).gcd id = 1) :
    IsCoprime a b ∧ IsCoprime b c ∧ IsCoprime a c := by
  -- A common prime of any two slots divides all three.
  have key : ∀ q : ℤ, Prime q → q ∣ a → q ∣ b → q ∣ c → False := by
    intro q hq hqa hqb hqc
    have hdvd : q ∣ ({a, b, c} : Finset ℤ).gcd id := by
      refine Finset.dvd_gcd fun x hx => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simpa using ‹q ∣ x›
    rw [hgcd] at hdvd
    exact hq.not_dvd_one hdvd
  have hthird_ab : ∀ q : ℤ, Prime q → q ∣ a → q ∣ b → q ∣ c := by
    intro q hq hqa hqb
    refine hq.dvd_of_dvd_pow (n := 37) ?_
    rw [← H]
    exact dvd_add (hqa.pow (by norm_num)) (hqb.pow (by norm_num))
  have hthird_bc : ∀ q : ℤ, Prime q → q ∣ b → q ∣ c → q ∣ a := by
    intro q hq hqb hqc
    refine hq.dvd_of_dvd_pow (n := 37) ?_
    have : a ^ 37 = c ^ 37 - b ^ 37 := by linarith
    rw [this]
    exact dvd_sub (hqc.pow (by norm_num)) (hqb.pow (by norm_num))
  have hthird_ac : ∀ q : ℤ, Prime q → q ∣ a → q ∣ c → q ∣ b := by
    intro q hq hqa hqc
    refine hq.dvd_of_dvd_pow (n := 37) ?_
    have : b ^ 37 = c ^ 37 - a ^ 37 := by linarith
    rw [this]
    exact dvd_sub (hqc.pow (by norm_num)) (hqa.pow (by norm_num))
  -- Reduce `IsCoprime` to the absence of a common prime.
  have main : ∀ x y : ℤ, (∀ q : ℤ, Prime q → q ∣ x → q ∣ y → False) → IsCoprime x y := by
    intro x y hxy
    rw [Int.isCoprime_iff_gcd_eq_one]
    by_contra h
    obtain ⟨q, hqpri, hq⟩ := Nat.exists_prime_and_dvd h
    have hqpri' : Prime (q : ℤ) := Int.prime_iff_natAbs_prime.2 (by simpa using hqpri)
    have hqx : (q : ℤ) ∣ x :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hq) (Int.gcd_dvd_left _ _)
    have hqy : (q : ℤ) ∣ y :=
      dvd_trans (Int.natCast_dvd_natCast.mpr hq) (Int.gcd_dvd_right _ _)
    exact hxy _ hqpri' hqx hqy
  refine ⟨main a b fun q hq hqa hqb => key q hq hqa hqb (hthird_ab q hq hqa hqb),
    main b c fun q hq hqb hqc => key q hq (hthird_bc q hq hqb hqc) hqb hqc,
    main a c fun q hq hqa hqc => key q hq hqa (hthird_ac q hq hqa hqc) hqc⟩

/-! ## 2. `𝔭 = (ζ−1)`-divisibility of integer casts and of the factors -/

/-- `(ζ₀ − 1) ∣ (n : 𝓞 K)` for `37 ∣ n` (transfer of `zeta_sub_one_dvd_Int_iff`). -/
theorem lemma96_zetaSubOne_dvd_intCast {n : ℤ} (h : (37 : ℤ) ∣ n) :
    (ζ₀ - 1) ∣ ((n : ℤ) : 𝓞 K37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact (zeta_sub_one_dvd_Int_iff (IsCyclotomicExtension.zeta_spec 37 ℚ K37)).mpr
    (by exact_mod_cast h)

/-- `¬ (ζ₀ − 1) ∣ (n : 𝓞 K)` for `37 ∤ n`. -/
theorem lemma96_zetaSubOne_not_dvd_intCast {n : ℤ} (h : ¬ (37 : ℤ) ∣ n) :
    ¬ (ζ₀ - 1) ∣ ((n : ℤ) : 𝓞 K37) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro hd
  exact h (by exact_mod_cast
    (zeta_sub_one_dvd_Int_iff (IsCyclotomicExtension.zeta_spec 37 ℚ K37)).mp hd)

/-- **The factors are `𝔭`-coprime**: `(ζ₀−1) ∤ Y − ηZ` for any `η : 𝓞 K`, since `𝔭 ∣ Z`
(`37 ∣ Z`) forces `Y − ηZ ≡ Y mod 𝔭` and `37 ∤ Y`. -/
theorem lemma96_not_dvd_factor {Y Z : ℤ} (h37Z : (37 : ℤ) ∣ Z) (h37Y : ¬ (37 : ℤ) ∣ Y)
    (η : 𝓞 K37) :
    ¬ (ζ₀ - 1) ∣ ((Y : ℤ) : 𝓞 K37) - η * ((Z : ℤ) : 𝓞 K37) := by
  intro hd
  have hZ : (ζ₀ - 1) ∣ ((Z : ℤ) : 𝓞 K37) := lemma96_zetaSubOne_dvd_intCast h37Z
  have hY : (ζ₀ - 1) ∣ ((Y : ℤ) : 𝓞 K37) := by
    have : ((Y : ℤ) : 𝓞 K37) =
        (((Y : ℤ) : 𝓞 K37) - η * ((Z : ℤ) : 𝓞 K37)) + η * ((Z : ℤ) : 𝓞 K37) := by ring
    rw [this]
    exact dvd_add hd (Dvd.dvd.mul_left hZ η)
  exact lemma96_zetaSubOne_not_dvd_intCast h37Y hY

/-- The factors are nonzero (a zero factor would be divisible by `ζ₀ − 1`). -/
theorem lemma96_factor_ne_zero {Y Z : ℤ} (h37Z : (37 : ℤ) ∣ Z) (h37Y : ¬ (37 : ℤ) ∣ Y)
    (η : 𝓞 K37) :
    ((Y : ℤ) : 𝓞 K37) - η * ((Z : ℤ) : 𝓞 K37) ≠ 0 := by
  intro h0
  exact lemma96_not_dvd_factor h37Z h37Y η (h0 ▸ dvd_zero _)

/-! ## 3. Pairwise coprimality of the factor ideals and the `A³⁷` extraction -/

/-- **Pairwise coprimality of the factor ideals** `(Y − η₁Z)`, `(Y − η₂Z)` (`η₁ ≠ η₂` roots of
unity).  A common maximal ideal `𝔮` contains `(η₂ − η₁)Z`; if it contains the root difference,
it contains `ζ₀ − 1` (associated), hence `37 ~ (ζ₀−1)³⁶`, hence `Z` (`37 ∣ Z`); in either case
`Z ∈ 𝔮`, so `Y ∈ 𝔮`, contradicting `IsCoprime Y Z` by Bézout. -/
theorem lemma96_spans_coprime {Y Z : ℤ} (hYZ : IsCoprime Y Z) (h37Z : (37 : ℤ) ∣ Z) :
    ∀ η₁ ∈ nthRootsFinset 37 (1 : 𝓞 K37), ∀ η₂ ∈ nthRootsFinset 37 (1 : 𝓞 K37), η₁ ≠ η₂ →
      IsCoprime (span ({((Y : ℤ) : 𝓞 K37) + η₁ * (-((Z : ℤ) : 𝓞 K37))} : Set (𝓞 K37)))
        (span ({((Y : ℤ) : 𝓞 K37) + η₂ * (-((Z : ℤ) : 𝓞 K37))} : Set (𝓞 K37))) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  intro η₁ hη₁ η₂ hη₂ hne
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra hsup
  obtain ⟨𝔮, h𝔮max, hle⟩ := Ideal.exists_le_maximal _ hsup
  haveI h𝔮prime : 𝔮.IsPrime := h𝔮max.isPrime
  -- both factors in `𝔮`
  have h1 : ((Y : ℤ) : 𝓞 K37) + η₁ * (-((Z : ℤ) : 𝓞 K37)) ∈ 𝔮 :=
    hle (le_sup_left (α := Ideal (𝓞 K37)) (Ideal.subset_span (Set.mem_singleton _)))
  have h2 : ((Y : ℤ) : 𝓞 K37) + η₂ * (-((Z : ℤ) : 𝓞 K37)) ∈ 𝔮 :=
    hle (le_sup_right (α := Ideal (𝓞 K37)) (Ideal.subset_span (Set.mem_singleton _)))
  -- difference: `(η₂ − η₁)·Z ∈ 𝔮`
  have hdiff : (η₂ - η₁) * ((Z : ℤ) : 𝓞 K37) ∈ 𝔮 := by
    have : (η₂ - η₁) * ((Z : ℤ) : 𝓞 K37) =
        (((Y : ℤ) : 𝓞 K37) + η₁ * (-((Z : ℤ) : 𝓞 K37))) -
          (((Y : ℤ) : 𝓞 K37) + η₂ * (-((Z : ℤ) : 𝓞 K37))) := by ring
    rw [this]
    exact Ideal.sub_mem _ h1 h2
  -- in either branch, `Z ∈ 𝔮`
  have hZmem : ((Z : ℤ) : 𝓞 K37) ∈ 𝔮 := by
    rcases h𝔮prime.mem_or_mem hdiff with hroot | hZ
    · -- `η₂ − η₁ ∈ 𝔮 ⟹ ζ₀ − 1 ∈ 𝔮 ⟹ 37 ∈ 𝔮 ⟹ Z ∈ 𝔮`
      have hassoc : Associated (ζ₀ - 1) (η₂ - η₁) :=
        (IsCyclotomicExtension.zeta_spec 37 ℚ
          K37).toInteger_isPrimitiveRoot.ntRootsFinset_pairwise_associated_sub_one_sub_of_prime
          (by norm_num) hη₂ hη₁ (Ne.symm hne)
      have hζmem : (ζ₀ - 1) ∈ 𝔮 := by
        obtain ⟨t, ht⟩ := hassoc.symm.dvd
        rw [ht]
        exact Ideal.mul_mem_right _ _ hroot
      have h37mem : ((37 : ℕ) : 𝓞 K37) ∈ 𝔮 := by
        obtain ⟨t, ht⟩ :=
          (associated_zeta_sub_one_pow_prime
            (IsCyclotomicExtension.zeta_spec 37 ℚ K37)).dvd
        rw [ht]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hζmem _ (by norm_num))
      obtain ⟨z', hz'⟩ := id h37Z
      have : ((Z : ℤ) : 𝓞 K37) = ((37 : ℕ) : 𝓞 K37) * ((z' : ℤ) : 𝓞 K37) := by
        rw [hz']; push_cast; ring
      rw [this]
      exact Ideal.mul_mem_right _ _ h37mem
    · exact hZ
  -- hence `Y ∈ 𝔮`
  have hYmem : ((Y : ℤ) : 𝓞 K37) ∈ 𝔮 := by
    have : ((Y : ℤ) : 𝓞 K37) =
        (((Y : ℤ) : 𝓞 K37) + η₁ * (-((Z : ℤ) : 𝓞 K37))) + η₁ * ((Z : ℤ) : 𝓞 K37) := by ring
    rw [this]
    exact Ideal.add_mem _ h1 (Ideal.mul_mem_left _ _ hZmem)
  -- Bézout: `1 ∈ 𝔮`
  obtain ⟨u, v, huv⟩ := hYZ
  have h1mem : (1 : 𝓞 K37) ∈ 𝔮 := by
    have : (1 : 𝓞 K37) = ((u : ℤ) : 𝓞 K37) * ((Y : ℤ) : 𝓞 K37) +
        ((v : ℤ) : 𝓞 K37) * ((Z : ℤ) : 𝓞 K37) := by
      have := congrArg (fun t : ℤ => ((t : ℤ) : 𝓞 K37)) huv
      push_cast at this
      simpa using this.symm
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hYmem) (Ideal.mul_mem_left _ _ hZmem)
  exact h𝔮max.ne_top ((Ideal.eq_top_iff_one 𝔮).mpr h1mem)

/-- **The Washington `(Y − ηZ) = A³⁷` extraction.**  From
`∏_{η³⁷=1} (Y + η(−Z)) = Y³⁷ − Z³⁷ = (−X)³⁷` and the pairwise coprimality, every factor ideal
is a `37`-th power. -/
theorem lemma96_exists_ideal {X Y Z : ℤ} (heq : X ^ 37 + Y ^ 37 = Z ^ 37)
    (hYZ : IsCoprime Y Z) (h37Z : (37 : ℤ) ∣ Z) :
    ∀ η ∈ nthRootsFinset 37 (1 : 𝓞 K37), ∃ A : Ideal (𝓞 K37),
      span ({((Y : ℤ) : 𝓞 K37) + η * (-((Z : ℤ) : 𝓞 K37))} : Set (𝓞 K37)) = A ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have hodd : Odd 37 := by decide
  -- the product identity
  have hfact := (IsCyclotomicExtension.zeta_spec 37 ℚ
      K37).toInteger_isPrimitiveRoot.pow_add_pow_eq_prod_add_mul
        ((Y : ℤ) : 𝓞 K37) (-((Z : ℤ) : 𝓞 K37)) hodd
  have hsum : ((Y : ℤ) : 𝓞 K37) ^ 37 + (-((Z : ℤ) : 𝓞 K37)) ^ 37 =
      (-((X : ℤ) : 𝓞 K37)) ^ 37 := by
    have hc := congrArg (fun t : ℤ => ((t : ℤ) : 𝓞 K37)) heq
    push_cast at hc
    rw [hodd.neg_pow, hodd.neg_pow]
    linear_combination hc
  have hspan : (∏ η ∈ nthRootsFinset 37 (1 : 𝓞 K37),
      span ({((Y : ℤ) : 𝓞 K37) + η * (-((Z : ℤ) : 𝓞 K37))} : Set (𝓞 K37))) =
      (span ({-((X : ℤ) : 𝓞 K37)} : Set (𝓞 K37))) ^ 37 := by
    rw [Ideal.prod_span_singleton, Ideal.span_singleton_pow, ← hsum, hfact]
  exact Finset.exists_eq_pow_of_mul_eq_pow_of_coprime
    (lemma96_spans_coprime hYZ h37Z) hspan

/-! ## 4. Conjugation arithmetic -/

/-- The `algebraMap` form of `coe_ringOfIntegersComplexConj` (definitional). -/
theorem lemma96_conj_coe (x : 𝓞 K37) :
    algebraMap (𝓞 K37) K37 (σ₀ x) =
      NumberField.IsCMField.complexConj K37 (algebraMap (𝓞 K37) K37 x) := rfl

/-- `σ₀ ζ₀ = ζ₀³⁶` (complex conjugation inverts the root of unity). -/
theorem lemma96_conj_zeta : σ₀ ζ₀ = ζ₀ ^ 36 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  apply (FaithfulSMul.algebraMap_injective (𝓞 K37) K37)
  rw [map_pow, lemma96_conj_coe,
    FLT37.LehmerVandiver.CaseI.complexConj_K_apply_primRoot_eq_inv (K := K37) (p := 37)
      (IsCyclotomicExtension.zeta_spec 37 ℚ K37).toInteger_isPrimitiveRoot]
  have hpow : algebraMap (𝓞 K37) K37 ζ₀ ^ 37 = 1 := by
    rw [← map_pow,
      (IsCyclotomicExtension.zeta_spec 37 ℚ K37).toInteger_isPrimitiveRoot.pow_eq_one, map_one]
  exact inv_eq_of_mul_eq_one_right (by
    rw [show algebraMap (𝓞 K37) K37 ζ₀ * algebraMap (𝓞 K37) K37 ζ₀ ^ 36 =
      algebraMap (𝓞 K37) K37 ζ₀ ^ 37 from by ring, hpow])

/-- `ζ₀³⁶·³⁶ = ζ₀` (since `36·36 = 35·37 + 1`). -/
theorem lemma96_zeta_pow_36_36 : (ζ₀ ^ 36) ^ 36 = ζ₀ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h37 : ζ₀ ^ 37 = 1 :=
    (IsCyclotomicExtension.zeta_spec 37 ℚ K37).toInteger_isPrimitiveRoot.pow_eq_one
  rw [← pow_mul, show (36 * 36 : ℕ) = 37 * 35 + 1 from by norm_num, pow_add, pow_mul, h37,
    one_pow, pow_one, one_mul]

/-- `σ₀ (Y − ζ₀Z) = Y − ζ₀³⁶Z`. -/
theorem lemma96_conj_factor_pos (Y Z : ℤ) :
    σ₀ (((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37)) =
      ((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37) := by
  rw [map_sub, map_mul, map_intCast, map_intCast, lemma96_conj_zeta]

/-- `σ₀ (Y − ζ₀³⁶Z) = Y − ζ₀Z`. -/
theorem lemma96_conj_factor_neg (Y Z : ℤ) :
    σ₀ (((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37)) =
      ((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37) := by
  rw [map_sub, map_mul, map_intCast, map_intCast, map_pow, lemma96_conj_zeta,
    lemma96_zeta_pow_36_36]

/-! ## 5. The σ-swap of the root ideals and the σ-stable product `C = A₁A₂` -/

set_option backward.isDefEq.respectTransparency false in
/-- **Conjugation swaps the root ideals**: if `(F) = A³⁷`, `(G) = B³⁷` and `σ₀F = G`, then
`σ₀(A) = B` (uniqueness of `37`-th roots of ideals). -/
theorem lemma96_map_conj_rootIdeal {F G : 𝓞 K37} {A B : Ideal (𝓞 K37)}
    (hσ : σ₀ F = G)
    (hA : span ({F} : Set (𝓞 K37)) = A ^ 37)
    (hB : span ({G} : Set (𝓞 K37)) = B ^ 37) :
    A.map σRH = B := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  have h1 : (A.map σRH) ^ 37 = B ^ 37 := by
    rw [← Ideal.map_pow, ← hA, Ideal.map_span, Set.image_singleton]
    have hFG : σRH F = G := hσ
    rw [hFG, hB]
  have hAB := (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp h1.dvd
  have hBA :=
    (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd (n := 37) (by norm_num)).mp h1.symm.dvd
  exact le_antisymm (Ideal.dvd_iff_le.mp hBA) (Ideal.dvd_iff_le.mp hAB)

/-! ## 6. The localized Galois descent for a σ-stable ideal coprime to `(37)` -/

set_option backward.isDefEq.respectTransparency false in
/-- **Comap-fixedness of a σ-stable ideal**: the `Gal(K/K⁺)`-fixed comap condition for the
localized descent, from `σ₀`-stability (generic version of
`caseII_rootIdeal_mul_conj_comap_fixed`). -/
theorem lemma96_comap_fixed (C : Ideal (𝓞 K37))
    (hC : C.map σRH = C)
    (σ : K37 ≃ₐ[KP37] K37) :
    C.comap (galRestrict (𝓞 KP37) KP37 K37 (𝓞 K37) σ) = C := by
  rcases BernoulliRegular.algEquiv_eq_one_or_complexConj (K := K37) σ with h1 | hc
  · rw [h1, map_one]; exact Ideal.comap_id _
  · rw [hc, caseII_galRestrict_complexConj_eq]
    nth_rewrite 1 [← hC]
    exact Ideal.comap_map_of_bijective _
      (EquivLike.bijective (NumberField.IsCMField.ringOfIntegersComplexConj K37))

set_option backward.isDefEq.respectTransparency false in
/-- **`C.comap` is coprime to `(37)` in `𝓞 K⁺`** for a σ-stable `C` coprime to `(37)` in `𝓞 K`
(the conjugation-trace argument; generic version of `caseII_isCoprime_comap_int37`). -/
theorem lemma96_isCoprime_comap_int37 (C : Ideal (𝓞 K37))
    (hC : C.map σRH = C)
    (hcop : IsCoprime C (Ideal.span {(37 : 𝓞 K37)})) :
    IsCoprime (C.comap (algebraMap (𝓞 KP37) (𝓞 K37)))
      (Ideal.span {(37 : 𝓞 KP37)}) := by
  set σ := (NumberField.IsCMField.ringOfIntegersComplexConj K37).toRingEquiv.toRingHom with hσ
  have hinv : ∀ x : 𝓞 K37, σ (σ x) = x := fun x => by
    apply RingOfIntegers.ext
    simp only [hσ, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv,
      NumberField.IsCMField.coe_ringOfIntegersComplexConj,
      NumberField.IsCMField.complexConj_apply_apply]
  -- `1 = a + c`, `a ∈ C`, `c ∈ (37)`.
  obtain ⟨a, ha, c, hc, hac⟩ := Submodule.mem_sup.mp
    ((Ideal.isCoprime_iff_sup_eq.mp hcop) ▸ (Submodule.mem_top : (1 : 𝓞 K37) ∈ ⊤))
  -- `a + σa ∈ C`, σ-fixed, so it descends.
  have haσ_C : a + σ a ∈ C := C.add_mem ha (hC ▸ Ideal.mem_map_of_mem σ ha)
  have haσ_fix : NumberField.IsCMField.ringOfIntegersComplexConj K37 (a + σ a) = a + σ a := by
    have h : σ (a + σ a) = a + σ a := by rw [map_add, hinv]; ring
    exact h
  obtain ⟨aP, haP⟩ := Set.mem_range.mp
    ((NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K37) (a + σ a)).mp
      haσ_fix)
  -- `c = 37 * d`, so `c + σc = 37 * (d + σd)`, also descending.
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hc
  have hdσ_fix : NumberField.IsCMField.ringOfIntegersComplexConj K37 (d + σ d) = d + σ d := by
    have h : σ (d + σ d) = d + σ d := by rw [map_add, hinv]; ring
    exact h
  obtain ⟨eP, heP⟩ := Set.mem_range.mp
    ((NumberField.IsCMField.ringOfIntegersComplexConj_eq_self_iff (K := K37) (d + σ d)).mp
      hdσ_fix)
  have hσ37 : σ (37 : 𝓞 K37) = 37 := map_ofNat σ 37
  have hσ1 : σ a + 37 * σ d = 1 := by
    have h := congrArg σ hac
    rwa [map_add, map_mul, hσ37, map_one] at h
  -- `2 = aP + 37 * eP` in `𝓞 K⁺`.
  have h2 : (2 : 𝓞 KP37) = aP + 37 * eP := by
    apply FaithfulSMul.algebraMap_injective (𝓞 KP37) (𝓞 K37)
    rw [map_add, map_mul, haP, heP]
    simp only [map_ofNat]
    linear_combination -hac - hσ1
  -- Bézout `1 = (-18)·2 + 37·…` ⟹ `1 ∈ C.comap + (37)`.
  have haP_mem : aP ∈ C.comap (algebraMap (𝓞 KP37) (𝓞 K37)) := by
    rw [Ideal.mem_comap, haP]; exact haσ_C
  have hbez : (1 : 𝓞 KP37) = (-18) * aP + (-18 * eP + 1) * 37 := by
    linear_combination (-18 : 𝓞 KP37) * h2
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, hbez]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (Ideal.mul_mem_left _ _ haP_mem))
    (Submodule.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))

set_option backward.isDefEq.respectTransparency false in
/-- **A σ-stable ideal of `𝓞 K` coprime to `(37)` descends from `𝓞 K⁺`** (generic version of
`caseII_sigma_stable_ideal_descends`, via the localized Galois descent away from the ramified
prime). -/
theorem lemma96_sigma_stable_descends (C : Ideal (𝓞 K37))
    (hC : C.map σRH = C)
    (hcop : IsCoprime C (Ideal.span {(37 : 𝓞 K37)})) :
    ∃ J : Ideal (𝓞 KP37), J.map (algebraMap (𝓞 KP37) (𝓞 K37)) = C := by
  refine ⟨C.comap (algebraMap (𝓞 KP37) (𝓞 K37)), ?_⟩
  apply comap_map_eq_of_unramifiedAt_support (R := 𝓞 KP37)
    (K := KP37) (L := K37) (S := 𝓞 K37)
  · exact lemma96_comap_fixed C hC
  · intro p hp_mem
    rw [Multiset.mem_toFinset] at hp_mem
    have hp_prime : Prime p := UniqueFactorizationMonoid.prime_of_factor p hp_mem
    haveI hp_isPrime : p.IsPrime := Ideal.isPrime_of_prime hp_prime
    apply isUnramifiedAt_of_not_over_37 p hp_prime.ne_zero
    intro h37
    have hcop' := lemma96_isCoprime_comap_int37 C hC hcop
    rw [Ideal.isCoprime_iff_sup_eq] at hcop'
    have htop : (⊤ : Ideal (𝓞 KP37)) ≤ p := by
      rw [← hcop']
      refine sup_le (Ideal.dvd_iff_le.mp
        (UniqueFactorizationMonoid.dvd_of_mem_factors hp_mem)) ?_
      rw [Ideal.span_singleton_le_iff_mem]
      have : (37 : 𝓞 KP37) = algebraMap ℤ (𝓞 KP37) 37 :=
        (map_ofNat (algebraMap ℤ (𝓞 KP37)) 37).symm
      rw [this]; exact h37
    exact hp_isPrime.ne_top (top_le_iff.mp htop)

/-! ## 7. The product half: real generator for `C = A₁A₂` -/

set_option backward.isDefEq.respectTransparency false in
/-- **The real generator of the σ-stable product `C = A₁A₂`** (Washington's B₀ argument).
`C` is σ-stable (`σ₀` swaps `A₁ ↔ A₂`), coprime to `(37)` (the factors are `𝔭`-coprime), and
`C³⁷ = (F₁F₂)` is principal; descent + `¬37 ∣ h⁺` give `C = (γ₀)` with `γ₀` real. -/
theorem lemma96_product_real_generator {Y Z : ℤ}
    (h37Z : (37 : ℤ) ∣ Z) (h37Y : ¬ (37 : ℤ) ∣ Y)
    {A₁ A₂ : Ideal (𝓞 K37)}
    (hA₁ : span ({((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37)} : Set (𝓞 K37)) = A₁ ^ 37)
    (hA₂ : span ({((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37)} : Set (𝓞 K37)) = A₂ ^ 37) :
    ∃ γ₀ : 𝓞 K37, σ₀ γ₀ = γ₀ ∧ span ({γ₀} : Set (𝓞 K37)) = A₁ * A₂ := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set F₁ : 𝓞 K37 := ((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37) with hF₁_def
  set F₂ : 𝓞 K37 := ((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37) with hF₂_def
  set C : Ideal (𝓞 K37) := A₁ * A₂ with hC_def
  -- `C ≠ ⊥`
  have hA₁_ne : A₁ ≠ ⊥ := by
    intro h0
    have : span ({F₁} : Set (𝓞 K37)) = ⊥ := by
      rw [hA₁, h0, ← Ideal.zero_eq_bot, zero_pow (by norm_num : (37 : ℕ) ≠ 0)]
    exact lemma96_factor_ne_zero h37Z h37Y ζ₀ (Ideal.span_singleton_eq_bot.mp this)
  have hA₂_ne : A₂ ≠ ⊥ := by
    intro h0
    have : span ({F₂} : Set (𝓞 K37)) = ⊥ := by
      rw [hA₂, h0, ← Ideal.zero_eq_bot, zero_pow (by norm_num : (37 : ℕ) ≠ 0)]
    exact lemma96_factor_ne_zero h37Z h37Y (ζ₀ ^ 36) (Ideal.span_singleton_eq_bot.mp this)
  have hC_ne : C ≠ ⊥ := by
    rw [hC_def, Ne, Ideal.mul_eq_bot]
    rintro (h | h)
    · exact hA₁_ne h
    · exact hA₂_ne h
  -- σ-stability: conjugation swaps `A₁ ↔ A₂`
  have hswap₁ : A₁.map σRH = A₂ :=
    lemma96_map_conj_rootIdeal (lemma96_conj_factor_pos Y Z) hA₁ hA₂
  have hswap₂ : A₂.map σRH = A₁ :=
    lemma96_map_conj_rootIdeal (lemma96_conj_factor_neg Y Z) hA₂ hA₁
  have hC_stable : C.map σRH = C := by
    rw [hC_def, Ideal.map_mul, hswap₁, hswap₂, mul_comm]
  -- `C³⁷ = (F₁F₂)` is principal
  have hCpow : C ^ 37 = span ({F₁ * F₂} : Set (𝓞 K37)) := by
    rw [hC_def, mul_pow, ← hA₁, ← hA₂, Ideal.span_singleton_mul_span_singleton]
  -- `𝔭 ∤ C`, hence `IsCoprime C (37)`
  have hp_not_dvd : ¬ Ideal.span ({(ζ₀ - 1 : 𝓞 K37)} : Set (𝓞 K37)) ∣ C := by
    intro hdvd
    have hdvd37 : Ideal.span ({(ζ₀ - 1 : 𝓞 K37)} : Set (𝓞 K37)) ∣ C ^ 37 :=
      hdvd.trans (dvd_pow_self C (by norm_num))
    rw [hCpow, Ideal.dvd_span_singleton, Ideal.mem_span_singleton] at hdvd37
    rcases ((IsCyclotomicExtension.zeta_spec 37 ℚ K37).zeta_sub_one_prime').dvd_or_dvd hdvd37
      with h | h
    · exact lemma96_not_dvd_factor h37Z h37Y ζ₀ h
    · exact lemma96_not_dvd_factor h37Z h37Y (ζ₀ ^ 36) h
  have hcop_p : IsCoprime C (Ideal.span ({(ζ₀ - 1 : 𝓞 K37)} : Set (𝓞 K37))) := by
    have hmax : (Ideal.span ({(ζ₀ - 1 : 𝓞 K37)} : Set (𝓞 K37))).IsMaximal :=
      (Ideal.isPrime_of_prime
        (Ideal.prime_span_singleton_iff.mpr
          (IsCyclotomicExtension.zeta_spec 37 ℚ K37).zeta_sub_one_prime')).isMaximal
        (Ideal.prime_span_singleton_iff.mpr
          (IsCyclotomicExtension.zeta_spec 37 ℚ K37).zeta_sub_one_prime').ne_zero
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra hne
    exact hp_not_dvd
      (Ideal.dvd_iff_le.mpr (le_sup_left.trans (hmax.eq_of_le hne le_sup_right).ge))
  have hcop37 : IsCoprime C (Ideal.span {(37 : 𝓞 K37)}) := by
    have hsp : Ideal.span {(37 : 𝓞 K37)} =
        Ideal.span ({(ζ₀ - 1 : 𝓞 K37)} : Set (𝓞 K37)) ^ (37 - 1) := by
      rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
      exact_mod_cast
        (associated_zeta_sub_one_pow_prime (IsCyclotomicExtension.zeta_spec 37 ℚ K37)).symm
    rw [hsp]
    exact hcop_p.pow_right
  -- descend and principalize
  obtain ⟨J, hJ⟩ := lemma96_sigma_stable_descends C hC_stable hcop37
  have hJ_ne : J ≠ ⊥ := by
    intro h0
    rw [h0, Ideal.map_bot] at hJ
    exact hC_ne hJ.symm
  have hJpow_principal : ((J.map (algebraMap (𝓞 KP37) (𝓞 K37))) ^ 37).IsPrincipal := by
    rw [hJ, hCpow]
    exact ⟨F₁ * F₂, rfl⟩
  have hJ_principal : J.IsPrincipal := caseII_productHalf_J_isPrincipal hJ_ne hJpow_principal
  obtain ⟨a, ha⟩ := hJ_principal
  have ha' : J = Ideal.span ({a} : Set _) := ha
  refine ⟨algebraMap (𝓞 KP37) (𝓞 K37) a, ?_, ?_⟩
  · exact ringOfIntegersComplexConj_algebraMap_eq (K := K37) a
  · rw [← hJ, ha', Ideal.map_span, Set.image_singleton]

/-! ## 8. The anti-fixed radical `α = F₁/F₂` is a `37`-th power (Lemmas 9.1 + 9.2) -/

set_option backward.isDefEq.respectTransparency false in
/-- **The Lemma 9.6 radical is a `37`-th power.**  `α = (Y−ζZ)/(Y−ζ³⁶Z)` is anti-fixed and
nonsquare-trivial; it is primary (thanks to `37 ∣ Z`) and its fractional ideal is `(A₁/A₂)³⁷`;
the proven ideal-theoretic Lemma 9.1 + the Hilbert-94 Lemma 9.2 core (under the proven
`¬37 ∣ h⁺`) give `α = β³⁷`. -/
theorem lemma96_radical_isPthPower {Y Z : ℤ}
    (h37Z : (37 : ℤ) ∣ Z) (h37Y : ¬ (37 : ℤ) ∣ Y) (hZ0 : Z ≠ 0)
    {A₁ A₂ : Ideal (𝓞 K37)}
    (hA₁ : span ({((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37)} : Set (𝓞 K37)) = A₁ ^ 37)
    (hA₂ : span ({((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37)} : Set (𝓞 K37)) = A₂ ^ 37) :
    ∃ β : K37, β ^ 37 =
      algebraMap (𝓞 K37) K37 (((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37)) /
        algebraMap (𝓞 K37) K37 (((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37)) := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set F₁ : 𝓞 K37 := ((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37) with hF₁_def
  set F₂ : 𝓞 K37 := ((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37) with hF₂_def
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K37) K37
  have hF₁_ne : F₁ ≠ 0 := lemma96_factor_ne_zero h37Z h37Y ζ₀
  have hF₂_ne : F₂ ≠ 0 := lemma96_factor_ne_zero h37Z h37Y (ζ₀ ^ 36)
  have hf₁_ne : algebraMap (𝓞 K37) K37 F₁ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hF₁_ne
  have hf₂_ne : algebraMap (𝓞 K37) K37 F₂ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hF₂_ne
  set α : K37 := algebraMap (𝓞 K37) K37 F₁ / algebraMap (𝓞 K37) K37 F₂ with hα_def
  have hα_ne : α ≠ 0 := div_ne_zero hf₁_ne hf₂_ne
  -- conjugation swaps the two factors at the field level
  have hconj₁ : NumberField.IsCMField.complexConj K37 (algebraMap (𝓞 K37) K37 F₁) =
      algebraMap (𝓞 K37) K37 F₂ := by
    rw [← lemma96_conj_coe]
    exact congrArg (algebraMap (𝓞 K37) K37)
      (show σ₀ F₁ = F₂ from lemma96_conj_factor_pos Y Z)
  have hconj₂ : NumberField.IsCMField.complexConj K37 (algebraMap (𝓞 K37) K37 F₂) =
      algebraMap (𝓞 K37) K37 F₁ := by
    rw [← lemma96_conj_coe]
    exact congrArg (algebraMap (𝓞 K37) K37)
      (show σ₀ F₂ = F₁ from lemma96_conj_factor_neg Y Z)
  -- anti-fixedness
  have h_anti : NumberField.IsCMField.complexConj K37 α = α⁻¹ := by
    rw [hα_def, map_div₀, hconj₁, hconj₂, inv_div]
  -- `α² ≠ 1`
  have h_sq_ne : α ^ 2 ≠ 1 := by
    intro hsq
    have hZK_ne : ((Z : ℤ) : 𝓞 K37) ≠ 0 := by
      simpa using (Int.cast_injective (α := 𝓞 K37)).ne hZ0
    have hf : algebraMap (𝓞 K37) K37 F₁ ^ 2 = algebraMap (𝓞 K37) K37 F₂ ^ 2 := by
      have h1 : (algebraMap (𝓞 K37) K37 F₁ / algebraMap (𝓞 K37) K37 F₂) ^ 2 = 1 := hsq
      field_simp at h1
      exact h1
    have hF : (F₁ - F₂) * (F₁ + F₂) = 0 := by
      apply hinj
      rw [map_mul, map_sub, map_add, map_zero]
      ring_nf
      ring_nf at hf
      linear_combination hf
    rcases mul_eq_zero.mp hF with h | h
    · -- `F₁ = F₂ ⟹ (ζ³⁶ − ζ)Z = 0 ⟹ ζ³⁵ = 1`
      have hzz : (ζ₀ ^ 36 - ζ₀) * ((Z : ℤ) : 𝓞 K37) = 0 := by
        rw [hF₁_def, hF₂_def] at h
        linear_combination h
      rcases mul_eq_zero.mp hzz with h' | h'
      · have hζ_ne : (ζ₀ : 𝓞 K37) ≠ 0 :=
          (IsCyclotomicExtension.zeta_spec 37 ℚ K37).toInteger_isPrimitiveRoot.ne_zero (by norm_num)
        have h35 : ζ₀ ^ 35 = 1 := by
          have hfac : ζ₀ * (ζ₀ ^ 35 - 1) = 0 := by linear_combination h'
          rcases mul_eq_zero.mp hfac with h'' | h''
          · exact absurd h'' hζ_ne
          · exact sub_eq_zero.mp h''
        exact (IsCyclotomicExtension.zeta_spec 37 ℚ
          K37).toInteger_isPrimitiveRoot.pow_ne_one_of_pos_of_lt (by norm_num) (by norm_num) h35
      · exact hZK_ne h'
    · -- `F₁ = −F₂ ⟹ 2Y = (ζ+ζ³⁶)Z ⟹ 𝔭 ∣ 2Y ⟹ 37 ∣ 2Y`
      have h2Y : ((2 * Y : ℤ) : 𝓞 K37) = (ζ₀ + ζ₀ ^ 36) * ((Z : ℤ) : 𝓞 K37) := by
        rw [hF₁_def, hF₂_def] at h
        push_cast
        linear_combination h
      have hdvd : (ζ₀ - 1) ∣ ((2 * Y : ℤ) : 𝓞 K37) := by
        rw [h2Y]
        exact Dvd.dvd.mul_left (lemma96_zetaSubOne_dvd_intCast h37Z) _
      have h37_2Y : (37 : ℤ) ∣ 2 * Y := by
        have := lemma96_zetaSubOne_not_dvd_intCast (n := 2 * Y)
        by_contra hno
        exact this hno hdvd
      have h37_prime : Prime (37 : ℤ) := Int.prime_iff_natAbs_prime.2 (by norm_num)
      rcases h37_prime.dvd_mul.mp h37_2Y with h' | h'
      · norm_num at h'
      · exact h37Y h'
  -- the primarity witness: `(α−1)·F₂ = (ζ₀−1)³⁷·N`
  obtain ⟨v, hv⟩ := (associated_zeta_sub_one_zeta_pow_sub_one 37 K37 35
    (by norm_num) (by norm_num)).dvd
  obtain ⟨w, hw⟩ :=
    (associated_zeta_sub_one_pow_prime (IsCyclotomicExtension.zeta_spec 37 ℚ K37)).dvd
  obtain ⟨z', hz'⟩ := id h37Z
  have hwitness : (α - 1) * algebraMap (𝓞 K37) K37 F₂ =
      algebraMap (𝓞 K37) K37 ((ζ₀ - 1) ^ 37 * (ζ₀ * v * w * ((z' : ℤ) : 𝓞 K37))) := by
    have hαm1 : (α - 1) * algebraMap (𝓞 K37) K37 F₂ =
        algebraMap (𝓞 K37) K37 (F₁ - F₂) := by
      rw [hα_def, sub_mul, div_mul_cancel₀ _ hf₂_ne, one_mul, ← map_sub]
    rw [hαm1]
    congr 1
    -- `F₁ − F₂ = (ζ³⁶ − ζ)·Z = (ζ−1)³⁷·(ζvw·z')`
    have hZcast : ((Z : ℤ) : 𝓞 K37) = ((37 : ℕ) : 𝓞 K37) * ((z' : ℤ) : 𝓞 K37) := by
      rw [hz']; push_cast; ring
    have h36 : ζ₀ ^ 36 - ζ₀ = ζ₀ * ((ζ₀ - 1) * v) := by
      rw [← hv]; ring
    have h37c : ((37 : ℕ) : 𝓞 K37) = (ζ₀ - 1) ^ (37 - 1) * w := hw
    rw [hF₁_def, hF₂_def]
    calc ((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37) -
          (((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37)) =
        (ζ₀ ^ 36 - ζ₀) * ((Z : ℤ) : 𝓞 K37) := by ring
      _ = (ζ₀ * ((ζ₀ - 1) * v)) * ((ζ₀ - 1) ^ (37 - 1) * w * ((z' : ℤ) : 𝓞 K37)) := by
        rw [← h36, ← h37c, ← hZcast]
      _ = (ζ₀ - 1) ^ 37 * (ζ₀ * v * w * ((z' : ℤ) : 𝓞 K37)) := by
        norm_num
        ring
  -- the fractional ideal of `α` is `(A₁/A₂)³⁷`
  have hfrac : FractionalIdeal.spanSingleton (𝓞 K37)⁰ α =
      ((A₁ : FractionalIdeal (𝓞 K37)⁰ K37) / (A₂ : FractionalIdeal (𝓞 K37)⁰ K37)) ^ 37 := by
    rw [hα_def, ← FractionalIdeal.spanSingleton_div_spanSingleton,
      ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton,
      hA₁, hA₂, div_pow, FractionalIdeal.coeIdeal_pow, FractionalIdeal.coeIdeal_pow]
  -- Lemma 9.1 (proven): the Kummer extension is unramified
  have h_unram := caseIIIdealKummerUnramified37_proven α hα_ne
    ⟨IsCyclotomicExtension.zeta 37 ℚ K37, IsCyclotomicExtension.zeta_spec 37 ℚ K37,
      ζ₀ * v * w * ((z' : ℤ) : 𝓞 K37), F₂, lemma96_not_dvd_factor h37Z h37Y (ζ₀ ^ 36),
      hwitness⟩
    ⟨_, hfrac⟩
  -- Lemma 9.2 (proven core): the anti-fixed radical is a `37`-th power
  exact flt37_antiFixed_radical_isPthPower (K := K37) Sinnott.flt37_not_dvd_hPlus
    hα_ne h_anti h_sq_ne h_unram

/-! ## 9. The integral factor equations `F₁ = u·r³⁷`, `F₂ = u·(σ₀r)³⁷`, `u` real -/

set_option backward.isDefEq.respectTransparency false in
/-- **The Washington Lemma 9.6 factor equations.**  For the slotted triple, there are an
**integral real** unit `u` and an integer `r` with
`Y − ζ₀Z = u·r³⁷` and `Y − ζ₀³⁶Z = u·(σ₀ r)³⁷`. -/
theorem lemma96_factor_equations {X Y Z : ℤ} (heq : X ^ 37 + Y ^ 37 = Z ^ 37)
    (hYZ : IsCoprime Y Z) (h37Z : (37 : ℤ) ∣ Z) (h37Y : ¬ (37 : ℤ) ∣ Y) (hZ0 : Z ≠ 0) :
    ∃ (u : (𝓞 K37)ˣ) (r : 𝓞 K37),
      σ₀ ((u : (𝓞 K37)ˣ) : 𝓞 K37) = ((u : (𝓞 K37)ˣ) : 𝓞 K37) ∧
      ((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37) = (u : 𝓞 K37) * r ^ 37 ∧
      ((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37) = (u : 𝓞 K37) * (σ₀ r) ^ 37 := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  set F₁ : 𝓞 K37 := ((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37) with hF₁_def
  set F₂ : 𝓞 K37 := ((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37) with hF₂_def
  have hinj := FaithfulSMul.algebraMap_injective (𝓞 K37) K37
  have hF₁_ne : F₁ ≠ 0 := lemma96_factor_ne_zero h37Z h37Y ζ₀
  have hF₂_ne : F₂ ≠ 0 := lemma96_factor_ne_zero h37Z h37Y (ζ₀ ^ 36)
  have hf₁_ne : algebraMap (𝓞 K37) K37 F₁ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hF₁_ne
  have hf₂_ne : algebraMap (𝓞 K37) K37 F₂ ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]; exact hF₂_ne
  -- the two root ideals
  have hmem₁ : ζ₀ ∈ nthRootsFinset 37 (1 : 𝓞 K37) :=
    (IsCyclotomicExtension.zeta_spec 37 ℚ K37).toInteger_isPrimitiveRoot.mem_nthRootsFinset
      (by norm_num)
  have hmem₂ : ζ₀ ^ 36 ∈ nthRootsFinset 37 (1 : 𝓞 K37) := by
    refine (Polynomial.mem_nthRootsFinset (by norm_num) _).mpr ?_
    rw [← pow_mul, mul_comm, pow_mul,
      (IsCyclotomicExtension.zeta_spec 37 ℚ K37).toInteger_isPrimitiveRoot.pow_eq_one, one_pow]
  obtain ⟨A₁, hA₁'⟩ := lemma96_exists_ideal heq hYZ h37Z ζ₀ hmem₁
  obtain ⟨A₂, hA₂'⟩ := lemma96_exists_ideal heq hYZ h37Z (ζ₀ ^ 36) hmem₂
  have hA₁ : span ({F₁} : Set (𝓞 K37)) = A₁ ^ 37 := by
    rw [hF₁_def, show ((Y : ℤ) : 𝓞 K37) - ζ₀ * ((Z : ℤ) : 𝓞 K37) =
      ((Y : ℤ) : 𝓞 K37) + ζ₀ * (-((Z : ℤ) : 𝓞 K37)) from by ring]
    exact hA₁'
  have hA₂ : span ({F₂} : Set (𝓞 K37)) = A₂ ^ 37 := by
    rw [hF₂_def, show ((Y : ℤ) : 𝓞 K37) - ζ₀ ^ 36 * ((Z : ℤ) : 𝓞 K37) =
      ((Y : ℤ) : 𝓞 K37) + ζ₀ ^ 36 * (-((Z : ℤ) : 𝓞 K37)) from by ring]
    exact hA₂'
  -- the real generator of `C = A₁A₂` and the product unit
  obtain ⟨γ₀, hγ₀_real, hγ₀_span⟩ := lemma96_product_real_generator h37Z h37Y hA₁ hA₂
  have hprod_span : span ({F₁ * F₂} : Set (𝓞 K37)) = span ({γ₀ ^ 37} : Set (𝓞 K37)) := by
    rw [← Ideal.span_singleton_mul_span_singleton, hA₁, hA₂, ← mul_pow, ← hγ₀_span,
      Ideal.span_singleton_pow]
  have hassoc : Associated (γ₀ ^ 37) (F₁ * F₂) :=
    Ideal.span_singleton_eq_span_singleton.mp hprod_span.symm
  obtain ⟨u₀, hu₀⟩ := hassoc
  -- `γ₀ ≠ 0`
  have hγ₀_ne : γ₀ ≠ 0 := by
    intro h0
    have : F₁ * F₂ = 0 := by rw [← hu₀, h0]; ring
    exact (mul_ne_zero hF₁_ne hF₂_ne) this
  -- the product unit is real
  have hu₀_real : σ₀ ((u₀ : (𝓞 K37)ˣ) : 𝓞 K37) = ((u₀ : (𝓞 K37)ˣ) : 𝓞 K37) := by
    have hconjprod : σ₀ (F₁ * F₂) = F₁ * F₂ := by
      have e1 : σ₀ F₁ = F₂ := lemma96_conj_factor_pos Y Z
      have e2 : σ₀ F₂ = F₁ := lemma96_conj_factor_neg Y Z
      rw [map_mul, e1, e2, mul_comm]
    have h1 : γ₀ ^ 37 * σ₀ ((u₀ : (𝓞 K37)ˣ) : 𝓞 K37) = γ₀ ^ 37 * ((u₀ : (𝓞 K37)ˣ) : 𝓞 K37) := by
      have := congrArg σ₀ hu₀
      rw [map_mul, map_pow, hγ₀_real, hconjprod] at this
      rw [this, hu₀]
    exact mul_left_cancel₀ (pow_ne_zero 37 hγ₀_ne) h1
  -- the radical β
  obtain ⟨β, hβ⟩ := lemma96_radical_isPthPower h37Z h37Y hZ0 hA₁ hA₂
  -- the squared pair
  set η' : K37ˣ := Units.map (algebraMap (𝓞 K37) K37).toMonoidHom u₀ with hη'_def
  have hη'_val : (η' : K37) = algebraMap (𝓞 K37) K37 ((u₀ : (𝓞 K37)ˣ) : 𝓞 K37) := rfl
  have hη'_real : NumberField.IsCMField.complexConj K37 (η' : K37) = (η' : K37) := by
    rw [hη'_val, ← lemma96_conj_coe, hu₀_real]
  have hconj₁ : NumberField.IsCMField.complexConj K37 (algebraMap (𝓞 K37) K37 F₁) =
      algebraMap (𝓞 K37) K37 F₂ := by
    rw [← lemma96_conj_coe]
    exact congrArg (algebraMap (𝓞 K37) K37)
      (show σ₀ F₁ = F₂ from lemma96_conj_factor_pos Y Z)
  set W : K37 := β * algebraMap (𝓞 K37) K37 γ₀ with hW_def
  have hsqp : algebraMap (𝓞 K37) K37 F₁ ^ 2 = (η' : K37) * W ^ 37 := by
    have hsplit : algebraMap (𝓞 K37) K37 F₁ ^ 2 =
        (algebraMap (𝓞 K37) K37 F₁ / algebraMap (𝓞 K37) K37 F₂) *
          (algebraMap (𝓞 K37) K37 F₁ * algebraMap (𝓞 K37) K37 F₂) := by
      field_simp
    have hprodK : algebraMap (𝓞 K37) K37 F₁ * algebraMap (𝓞 K37) K37 F₂ =
        algebraMap (𝓞 K37) K37 γ₀ ^ 37 * (η' : K37) := by
      rw [hη'_val, ← map_pow, ← map_mul, ← map_mul, hu₀]
    rw [hsplit, ← hβ, hprodK, hW_def]
    ring
  have hsqn : algebraMap (𝓞 K37) K37 F₂ ^ 2 =
      (η' : K37) * (NumberField.IsCMField.complexConj K37 W) ^ 37 := by
    have hc := congrArg (NumberField.IsCMField.complexConj K37) hsqp
    rw [map_pow, hconj₁, map_mul, hη'_real, map_pow] at hc
    exact hc
  obtain ⟨hXeq, hXconjEq⟩ := washington_factor_of_squared_pair (K := K37) (p := 37)
    (by decide : Odd 37) hf₁_ne hf₂_ne hconj₁ hsqp hsqn
  -- integrality of the generator
  set ρ : K37 := W ^ ((37 + 1) / 2) * (algebraMap (𝓞 K37) K37 F₁)⁻¹ with hρ_def
  set u : (𝓞 K37)ˣ := u₀ ^ ((37 + 1) / 2) with hu_def
  have hu_val : ((η' ^ ((37 + 1) / 2) : K37ˣ) : K37) =
      algebraMap (𝓞 K37) K37 ((u : (𝓞 K37)ˣ) : 𝓞 K37) := by
    rw [hu_def, hη'_def]
    simp [Units.coe_map]
  have hρ_pow : ρ ^ 37 =
      algebraMap (𝓞 K37) K37 (F₁ * (((u⁻¹ : (𝓞 K37)ˣ) : 𝓞 K37))) := by
    have hu_ne : ((η' ^ ((37 + 1) / 2) : K37ˣ) : K37) ≠ 0 := Units.ne_zero _
    rw [map_mul]
    have huinv : algebraMap (𝓞 K37) K37 ((u⁻¹ : (𝓞 K37)ˣ) : 𝓞 K37) =
        (algebraMap (𝓞 K37) K37 ((u : (𝓞 K37)ˣ) : 𝓞 K37))⁻¹ := map_units_inv _ u
    rw [huinv, ← hu_val]
    rw [eq_comm, mul_comm]
    rw [inv_mul_eq_iff_eq_mul₀ hu_ne]
    exact hXeq
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow
    (R := 𝓞 K37) (K := K37) (by norm_num : 0 < 37)
    (by rw [hρ_pow]; exact isIntegral_algebraMap)
  -- the integral equations
  refine ⟨u, r, ?_, ?_, ?_⟩
  · -- `u = u₀^{19}` is real
    rw [hu_def, Units.val_pow_eq_pow_val, map_pow, hu₀_real]
  · -- `F₁ = u·r³⁷`
    apply hinj
    rw [map_mul, map_pow, hr, ← hu_val]
    exact hXeq
  · -- `F₂ = u·(σ₀r)³⁷`
    apply hinj
    have hσρ : algebraMap (𝓞 K37) K37 (σ₀ r) =
        NumberField.IsCMField.complexConj K37 ρ := by
      rw [lemma96_conj_coe, hr]
    rw [map_mul, map_pow, hσρ, ← hu_val]
    exact hXconjEq

/-! ## 10. The finite-field contradiction at `ℓ = 149` -/

/-- `2⁴ ≠ 0` in `𝔽₁₄₉` (closed-context `decide`). -/
theorem lemma96_two_pow_four_ne_zero : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 0 := by decide

set_option maxRecDepth 8000 in
/-- `2¹⁴⁸ = 1` in `𝔽₁₄₉` (Fermat; closed-context `decide`). -/
theorem lemma96_two_pow_oneFortyEight : ((2 : ℕ) : ZMod 149) ^ 148 = 1 := by decide

/-- `2³² ≠ 1` in `𝔽₁₄₉` (closed-context `decide`; the order of `2` mod `149` is `148 ∤ 32`). -/
theorem lemma96_two_pow_thirtytwo_ne_one : ((2 : ℕ) : ZMod 149) ^ 32 ≠ 1 := by decide

/-- **The explicit residue map `φ : 𝓞 K → 𝔽₁₄₉`** with `φ(ζ₀) = 2⁴ = 16` (the
`cyclotomicReduction` of the Lehmer–Vandiver prime-identification chain, composed with the
`CyclotomicIntegers` presentation). -/
noncomputable def lemma96ResidueMap : 𝓞 K37 →+* ZMod 149 :=
  (BernoulliRegular.FLT37.cyclotomicReduction 37 149 4
    (by norm_num : (149 : ℕ) = 4 * 37 + 1)
    (by decide : (2 : ℕ).Coprime 149)
    (by decide : ((2 : ℕ) : ZMod 149) ^ 4 ≠ 1)).comp
    (CyclotomicIntegers.equiv 37).symm.toRingHom

/-- `φ(ζ₀) = 2⁴` (the defining property of the cyclotomic reduction). -/
theorem lemma96ResidueMap_zeta : lemma96ResidueMap ζ₀ = ((2 : ℕ) : ZMod 149) ^ 4 := by
  have hζ_toInt : ζ₀ = (IsCyclotomicExtension.zeta_spec 37 ℚ K37).toInteger := rfl
  have hsymm : (CyclotomicIntegers.equiv 37).symm
      ((IsCyclotomicExtension.zeta_spec 37 ℚ K37).toInteger) =
      CyclotomicIntegers.zeta 37 := by
    rw [← CyclotomicIntegers.equiv_zeta]
    exact RingEquiv.symm_apply_apply _ _
  unfold lemma96ResidueMap
  rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hζ_toInt, hsymm]
  exact BernoulliRegular.FLT37.cyclotomicReduction_zeta 37 149 4 _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- **The Lemma 9.6 core**: a slotted Case-II triple with `149` dividing the `𝔭`-coprime slot
`Y` is impossible.  The factor equations reduce mod the explicit residue map
`φ : 𝓞 K →+* ZMod 149` (`ζ ↦ 2⁴`) to `16·s³⁷ = 16³⁶·r³⁷` with `r, s ≠ 0`; raising to the
`4`-th power and `w¹⁴⁸ = 1` give `16¹⁶ = 16⁵⁷⁶` in `𝔽₁₄₉`, false by `decide`. -/
theorem lemma96_core {X Y Z : ℤ} (heq : X ^ 37 + Y ^ 37 = Z ^ 37)
    (hYZ : IsCoprime Y Z) (h37Z : (37 : ℤ) ∣ Z) (h37Y : ¬ (37 : ℤ) ∣ Y)
    (h149Y : (149 : ℤ) ∣ Y) : False := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  haveI : Fact (Nat.Prime 149) := ⟨by decide⟩
  -- `Z ≠ 0` (else `Y` is a unit, contradicting `149 ∣ Y`)
  have hZ0 : Z ≠ 0 := by
    rintro rfl
    have hYunit : IsUnit Y := isCoprime_zero_right.mp hYZ
    rcases Int.isUnit_iff.mp hYunit with rfl | rfl <;> norm_num at h149Y
  obtain ⟨u, r, hu_real, hF₁, hF₂⟩ := lemma96_factor_equations heq hYZ h37Z h37Y hZ0
  -- the residue map `φ : 𝓞 K →+* ZMod 149` with `φ(ζ₀) = 2⁴`
  set φ : 𝓞 K37 →+* ZMod 149 := lemma96ResidueMap
  set t : ZMod 149 := ((2 : ℕ) : ZMod 149)
  have hφζ : φ ζ₀ = t ^ 4 := lemma96ResidueMap_zeta
  -- residues
  have hφY : φ ((Y : ℤ) : 𝓞 K37) = 0 := by
    rw [map_intCast]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd Y 149).mpr (by exact_mod_cast h149Y)
  have hφZ_ne : φ ((Z : ℤ) : 𝓞 K37) ≠ 0 := by
    rw [map_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h149Z
    obtain ⟨a, b, hab⟩ := hYZ
    have : (149 : ℤ) ∣ 1 := by
      rw [← hab]
      exact dvd_add (Dvd.dvd.mul_left h149Y a)
        (Dvd.dvd.mul_left (by exact_mod_cast h149Z) b)
    norm_num at this
  have ht4_ne : t ^ 4 ≠ 0 := lemma96_two_pow_four_ne_zero
  -- the two reduced factor equations
  have hE₁ : -(t ^ 4) * φ ((Z : ℤ) : 𝓞 K37) =
      φ ((u : (𝓞 K37)ˣ) : 𝓞 K37) * (φ r) ^ 37 := by
    have := congrArg φ hF₁
    rw [map_sub, map_mul, map_mul, map_pow, hφY, hφζ] at this
    linear_combination this
  have hE₂ : -((t ^ 4) ^ 36) * φ ((Z : ℤ) : 𝓞 K37) =
      φ ((u : (𝓞 K37)ˣ) : 𝓞 K37) * (φ (σ₀ r)) ^ 37 := by
    have := congrArg φ hF₂
    rw [map_sub, map_mul, map_mul, map_pow, map_pow, hφY, hφζ] at this
    linear_combination this
  -- nonvanishing of the reduced generators
  have hr_ne : φ r ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (37 : ℕ) ≠ 0), mul_zero] at hE₁
    rcases mul_eq_zero.mp hE₁ with h | h
    · exact ht4_ne (neg_eq_zero.mp h)
    · exact hφZ_ne h
  have hs_ne : φ (σ₀ r) ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num : (37 : ℕ) ≠ 0), mul_zero] at hE₂
    rcases mul_eq_zero.mp hE₂ with h | h
    · exact pow_ne_zero 36 ht4_ne (neg_eq_zero.mp h)
    · exact hφZ_ne h
  -- cross-multiply and cancel `−z`
  have hkey : t ^ 4 * (φ (σ₀ r)) ^ 37 = (t ^ 4) ^ 36 * (φ r) ^ 37 := by
    have hcross : φ ((Z : ℤ) : 𝓞 K37) * (t ^ 4 * (φ (σ₀ r)) ^ 37) =
        φ ((Z : ℤ) : 𝓞 K37) * ((t ^ 4) ^ 36 * (φ r) ^ 37) := by
      have h1 : (-(t ^ 4) * φ ((Z : ℤ) : 𝓞 K37)) * (φ (σ₀ r)) ^ 37 =
          (φ ((u : (𝓞 K37)ˣ) : 𝓞 K37) * (φ r) ^ 37) * (φ (σ₀ r)) ^ 37 := by rw [hE₁]
      have h2 : (-((t ^ 4) ^ 36) * φ ((Z : ℤ) : 𝓞 K37)) * (φ r) ^ 37 =
          (φ ((u : (𝓞 K37)ˣ) : 𝓞 K37) * (φ (σ₀ r)) ^ 37) * (φ r) ^ 37 := by rw [hE₂]
      linear_combination -h1 + h2
    exact mul_left_cancel₀ hφZ_ne hcross
  -- raise to the 4th power; `w¹⁴⁸ = 1`
  have hr148 : (φ r) ^ 148 = 1 := by
    rw [show (148 : ℕ) = 149 - 1 from by norm_num]
    exact ZMod.pow_card_sub_one_eq_one hr_ne
  have hs148 : (φ (σ₀ r)) ^ 148 = 1 := by
    rw [show (148 : ℕ) = 149 - 1 from by norm_num]
    exact ZMod.pow_card_sub_one_eq_one hs_ne
  -- absorb the `t`-power: `t⁸·s³⁷ = r³⁷` (using `(t⁴)³⁷ = t¹⁴⁸ = 1`)
  have ht148 : t ^ 148 = 1 := lemma96_two_pow_oneFortyEight
  have ht4_37 : (t ^ 4) ^ 37 = 1 := by
    rw [← pow_mul, show (4 * 37 : ℕ) = 148 from by norm_num]
    exact ht148
  have hkey2 : t ^ 8 * (φ (σ₀ r)) ^ 37 = (φ r) ^ 37 := by
    calc t ^ 8 * (φ (σ₀ r)) ^ 37
        = t ^ 4 * (φ (σ₀ r)) ^ 37 * t ^ 4 := by ring
      _ = (t ^ 4) ^ 36 * (φ r) ^ 37 * t ^ 4 := by rw [hkey]
      _ = (t ^ 4) ^ 37 * (φ r) ^ 37 := by ring
      _ = (φ r) ^ 37 := by rw [ht4_37, one_mul]
  -- raise to the `4`-th power: `t³² = 1`
  have h32 : t ^ 32 = 1 := by
    have h4' : (t ^ 8 * (φ (σ₀ r)) ^ 37) ^ 4 = ((φ r) ^ 37) ^ 4 := by rw [hkey2]
    calc t ^ 32
        = t ^ 32 * (φ (σ₀ r)) ^ 148 := by rw [hs148, mul_one]
      _ = (t ^ 8 * (φ (σ₀ r)) ^ 37) ^ 4 := by ring
      _ = ((φ r) ^ 37) ^ 4 := h4'
      _ = (φ r) ^ 148 := by rw [← pow_mul]
      _ = 1 := hr148
  -- `2³² = 1` in `𝔽₁₄₉` is false (the order of `2` mod `149` is `148 ∤ 32`)
  exact lemma96_two_pow_thirtytwo_ne_one h32

/-! ## 11. Washington Lemma 9.6 — the slotting -/

/-- **Washington Lemma 9.6 for `p = 37`, `ℓ = 149` (PROVEN).**  For a Fermat triple
`a³⁷ + b³⁷ = c³⁷` with `abc ≠ 0`, `gcd{a,b,c} = 1` and `37 ∣ abc`, no slot coprime to `37` is
divisible by `149`.  This is exactly the `h_lemma96` hypothesis of
`fermatLastTheoremFor_thirtyseven_of_lemma96_coprimality`. -/
theorem caseII_washington_lemma96 :
    ∀ a b c : ℤ, a * b * c ≠ 0 → ({a, b, c} : Finset ℤ).gcd id = 1 →
      (37 : ℤ) ∣ a * b * c → a ^ 37 + b ^ 37 = c ^ 37 →
      ∀ x : ℤ, (¬ (37 : ℤ) ∣ x) → (x = a ∨ x = b ∨ x = c) → ¬ (149 : ℤ) ∣ x := by
  intro a b c _habc hgcd h37abc heq x h37x hxabc h149x
  obtain ⟨hab, hbc, hac⟩ := lemma96_pairwise_coprime heq hgcd
  have h37_prime : Prime (37 : ℤ) := Int.prime_iff_natAbs_prime.2 (by norm_num)
  have hodd : Odd 37 := by decide
  rcases hxabc with rfl | rfl | rfl
  · -- `x = a` (so `37 ∤ a`, `149 ∣ a`): the `37`-slot is `b` or `c`
    rcases h37_prime.dvd_mul.mp h37abc with hab37 | h37c
    · rcases h37_prime.dvd_mul.mp hab37 with h37a | h37b
      · exact h37x h37a
      · -- `(X, Y, Z) = (−c, a, −b)`
        refine lemma96_core (X := -c) (Y := x) (Z := -b) ?_ (hab.neg_right)
          (dvd_neg.mpr h37b) h37x h149x
        rw [hodd.neg_pow, hodd.neg_pow]
        linarith [heq]
    · -- `(X, Y, Z) = (b, a, c)`
      exact lemma96_core (X := b) (Y := x) (Z := c) (by linarith [heq]) hac h37c h37x h149x
  · -- `x = b`
    rcases h37_prime.dvd_mul.mp h37abc with hab37 | h37c
    · rcases h37_prime.dvd_mul.mp hab37 with h37a | h37b
      · -- `(X, Y, Z) = (−c, b, −a)`
        refine lemma96_core (X := -c) (Y := x) (Z := -a) ?_ (hab.symm.neg_right)
          (dvd_neg.mpr h37a) h37x h149x
        rw [hodd.neg_pow, hodd.neg_pow]
        linarith [heq]
      · exact h37x h37b
    · -- `(X, Y, Z) = (a, b, c)`
      exact lemma96_core (X := a) (Y := x) (Z := c) (by linarith [heq]) hbc h37c h37x h149x
  · -- `x = c`
    rcases h37_prime.dvd_mul.mp h37abc with hab37 | h37c
    · rcases h37_prime.dvd_mul.mp hab37 with h37a | h37b
      · -- `(X, Y, Z) = (−b, c, a)`
        refine lemma96_core (X := -b) (Y := x) (Z := a) ?_ (hac.symm) h37a h37x h149x
        rw [hodd.neg_pow]
        linarith [heq]
      · -- `(X, Y, Z) = (−a, c, b)`
        refine lemma96_core (X := -a) (Y := x) (Z := b) ?_ (hbc.symm) h37b h37x h149x
        rw [hodd.neg_pow]
        linarith [heq]
    · exact h37x h37c

/-! ## 12. The FLT37 endpoint with Lemma 9.6 discharged -/

/-- **[F4 — FLT37 FROM KELLNER ALONE]** Fermat's Last Theorem for `37` from the carried
**Kellner** input (`NoSecondOrderIrregularPair 37 32`) as the **only** hypothesis: the rational
Washington Lemma 9.6 hypothesis of the coprime-threaded endpoint
`fermatLastTheoremFor_thirtyseven_of_lemma96` is now the **proven**
`caseII_washington_lemma96`. -/
theorem fermatLastTheoremFor_thirtyseven_of_kellner
    (noSecondOrderIrregular : NoSecondOrderIrregularPair 37 32) :
    FermatLastTheoremFor 37 :=
  fermatLastTheoremFor_thirtyseven_of_lemma96 caseII_washington_lemma96 noSecondOrderIrregular

end BernoulliRegular.FLT37.Eichler

end
