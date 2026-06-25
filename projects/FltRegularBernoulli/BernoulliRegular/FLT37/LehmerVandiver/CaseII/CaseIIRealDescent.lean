import BernoulliRegular.FLT37.LehmerVandiver.CaseII.GaloisDescent
import BernoulliRegular.FLT37.LehmerVandiver.CaseII.SpecificChain

/-!
# Case-II II1: real-ideal descent of the anchored quotients

Specialises the localized Galois descent (`GaloisDescent.lean`) to `K = ℚ(ζ₃₇) / K⁺`:
a `Gal(K/K⁺)`-stable ideal coprime to `𝔭` (the prime above `37`) descends to an ideal of
`𝒪_{K⁺}`, because `K/K⁺` is unramified at every prime not above `37`.

## References
* Reviewer reply 2026-05-27 (Q5).
* flt-regular `comap_map_eq_of_isUnramified` (localized here as
  `comap_map_eq_of_unramifiedAt_support`).
-/

@[expose] public section

open NumberField IsCyclotomicExtension Ideal UniqueFactorizationMonoid Polynomial

namespace BernoulliRegular.FLT37.LehmerVandiver.CaseII

variable {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {37} ℚ K]
  [NumberField.IsCMField K]

local notation3 "K⁺" => NumberField.maximalRealSubfield K

omit [NumberField.IsCMField K] in
/-- **`K/K⁺` is unramified at every prime of `𝒪_{K⁺}` not lying over `37`.** A prime `P` of
`𝒪 K` over `p` (a prime of `𝒪 K⁺` with `37 ∉ p`) lies over a rational prime `ℓ ≠ 37`; since
`K = ℚ(ζ₃₇)` is unramified over `ℚ` away from `37`, the ramification index `e(ℓ,P) = 1`, and tower
multiplicativity `e(ℓ,P) = e(ℓ,p)·e(p,P)` forces `e(p,P) = 1`. -/
theorem isUnramifiedAt_of_not_over_37 (p : Ideal (𝓞 K⁺)) [p.IsPrime] (hp_ne : p ≠ ⊥)
    (h37 : (algebraMap ℤ (𝓞 K⁺)) 37 ∉ p) :
    IsUnramifiedAt (𝓞 K) p := by
  intro P hP
  haveI hP_prime : P.IsPrime := hP.1
  haveI hP_lies : P.LiesOver p := hP.2
  have hP_ne : P ≠ ⊥ := by
    intro h
    exact hp_ne (by rw [hP_lies.over, h, Ideal.under_bot])
  haveI : Algebra.IsUnramifiedAt ℤ P := by
    haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
    have hunder_ne : Ideal.under ℤ P ≠ ⊥ := by
      rw [Ideal.under_def]
      exact mt (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (S := 𝓞 K)) hP_ne
    set ℓ : ℤ := Submodule.IsPrincipal.generator (Ideal.under ℤ P)
    have hℓ_eq : Ideal.under ℤ P = Ideal.span {ℓ} :=
      (Ideal.span_singleton_generator (Ideal.under ℤ P)).symm
    have hℓ_ne0 : ℓ ≠ 0 := by
      intro h; apply hunder_ne; rw [hℓ_eq, h, Ideal.span_singleton_zero]
    have hℓ_prime : Prime ℓ := by
      rw [← Ideal.span_singleton_prime hℓ_ne0, ← hℓ_eq]; infer_instance
    have h_mem : (ℓ : 𝓞 K) ∈ P := by
      have hmemZ : ℓ ∈ Ideal.under ℤ P := by rw [hℓ_eq]; exact Ideal.mem_span_singleton_self ℓ
      simpa [Ideal.under_def, Ideal.mem_comap] using hmemZ
    have hℓ_ne : ¬ ℓ ∣ (37 : ℤ) := by
      intro hdvd
      have h37P : (37 : 𝓞 K) ∈ P := by
        have : (37 : ℤ) ∈ Ideal.under ℤ P := by
          rw [hℓ_eq, Ideal.mem_span_singleton]; exact hdvd
        simpa [Ideal.under_def, Ideal.mem_comap] using this
      apply h37
      have h37P' : (algebraMap (𝓞 K⁺) (𝓞 K)) ((algebraMap ℤ (𝓞 K⁺)) 37) ∈ P := by
        rw [map_ofNat, map_ofNat]; exact h37P
      rwa [hP_lies.over, Ideal.mem_comap]
    have h_ndvd : ¬ ℓ ∣ NumberField.discr K := by
      rw [IsCyclotomicExtension.Rat.discr_prime (p := 37) (K := K)]
      intro hdvd
      have hpow : ℓ ∣ (37 : ℤ) ^ (37 - 2) := by
        rcases (Prime.dvd_mul hℓ_prime).mp hdvd with h | h
        · exact absurd (isUnit_of_dvd_unit h (by simp)) hℓ_prime.not_unit
        · exact h
      exact hℓ_ne (hℓ_prime.dvd_of_dvd_pow hpow)
    exact (NumberField.not_dvd_discr_iff_forall_mem (K := K) (𝒪 := 𝓞 K) hℓ_prime).mp
      h_ndvd P hP_prime h_mem
  haveI : Algebra.IsUnramifiedAt (𝓞 K⁺) P :=
    Algebra.IsUnramifiedAt.of_restrictScalars (R := ℤ) (A := 𝓞 K⁺) P
  have he : Ideal.ramificationIdx (Ideal.under (𝓞 K⁺) P) P = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 K⁺) hP_ne
  rwa [← hP_lies.over] at he

/-- **II1-E (coprimality):** for an adjacent root `η ≠ η₀`, the auxiliary ideal `𝔞(η)` is coprime
to `𝔭 = (ζ-1)`. Direct from flt-regular `p_dvd_a_iff` (`𝔭 ∣ 𝔞(η) ↔ η = η₀`). -/
theorem not_zetaSubOne_dvd_rootIdeal {m : ℕ} (D : CaseIIData37 K m)
    (η : nthRootsFinset 37 (1 : 𝓞 K)) (hη : η ≠ D.etaZero) :
    ¬ Ideal.span ({D.hζ.toInteger - 1} : Set (𝓞 K)) ∣ D.rootIdeal η := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  simp only [CaseIIData37.rootIdeal]
  rwa [p_dvd_a_iff (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy η]

/-- **II1-E (coprimality), denominator:** `𝔞₀` (the `𝔭`-coprime part of `𝔞(η₀)`) is coprime to
`𝔭`. Direct from flt-regular `not_p_div_a_zero`. -/
theorem not_zetaSubOne_dvd_aEtaZero {m : ℕ} (D : CaseIIData37 K m) :
    ¬ Ideal.span ({D.hζ.toInteger - 1} : Set (𝓞 K)) ∣
      aEtaZeroDvdPPow (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy := by
  haveI : Fact (Nat.Prime 37) := ⟨by decide⟩
  exact not_p_div_a_zero (by decide : (37 : ℕ) ≠ 2) D.hζ D.equation D.hy D.hz

end BernoulliRegular.FLT37.LehmerVandiver.CaseII

end
