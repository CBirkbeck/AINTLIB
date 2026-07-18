import BernoulliRegular.FLT37.LehmerVandiver.CaseI.PrimaryNormalization
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.ClassEqFromKummerRatioK
import BernoulliRegular.FLT37.LehmerVandiver.CaseI.ClassEqDischarge
import FltRegular.FltRegular

/-!
# LV010 Stage 2 interface: Kummer's ratio adapted

Stage 2 of Vandiver's class-equality discharge: under `¬ p ∣ h⁺(K)`,
the case-I factor `α = ζ^k · (a + ζ b)` (after Stage 1's weak-primary
normalization) admits the Kummer ratio identity

  `α / σ(α) = β^p`  in `K^×`.

This file packages Stage 2 as a `Prop` predicate
`Stage2KummerRatioK p K` and shows it composes with Stage 1 (already
shipped via `caseI_exists_zeta_pow_weakPrimary`) plus the integral
descent (LV010-class-eq-1d/1e, already shipped) to discharge
`CaseIClassEqDischarge`.

Closing Stage 2 unconditionally requires Kummer's lemma adapted to
`¬ p ∣ h⁺` (via Hilbert 90 / Hilbert 92 / Hilbert 94 descent on
unramified Kummer extensions). This is the substantive Vandiver work
left to a follow-up.

## References

* Washington, *Introduction to Cyclotomic Fields*, §9.3.
* flt-regular's `eq_pow_prime_of_unit_of_congruent`
  (`KummersLemma.lean:49`), regularity-based.
* `caseI_exists_zeta_pow_weakPrimary` (Stage 1, this project).
* `exists_integral_kummer_ratio_of_K` (LV010-class-eq-1e).
* `caseI_class_eq_complexConj_of_conj_kummer_eq` (LV010-class-eq-1d).
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

variable (p : ℕ) [Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [IsCMField K]

/-- **Stage 2 Kummer ratio (K-level)**: predicate capturing the
content "for the case-I weak-primary factor, α/σα is a p-th power in
K^×, under `¬ p ∣ h⁺`".

The hypotheses input:
- FLT case-I scenario `(a, b, c, p)` with `a^p + b^p = c^p`,
  `gcd(a,b,c) = 1`, `p ∤ abc`.
- A primitive p-th root `ζ : 𝓞 K`.
- The case-I factor identity `(a + ζ b) = I^p` for some non-zero ideal
  `I` (LV008-CTOR-a).
- `¬ p ∣ h⁺(K)` (Vandiver's conjecture for p; not literally a
  hypothesis here as the predicate is parametric on K with the VC
  baked into K's choice).

The conclusion: there exists `k : Fin p` such that the weak-primary
form `α' = ζ^k · (a + ζ b)` satisfies `α' / σα' = β^p` for some
`β ∈ K^×`. -/
def Stage2KummerRatioK : Prop :=
  ∀ {a b c : ℤ}, ({a, b, c} : Finset ℤ).gcd id = 1 →
    ¬ (p : ℤ) ∣ a * b * c →
    a ^ p + b ^ p = c ^ p →
    ∀ {ζ : 𝓞 K}, IsPrimitiveRoot ζ p →
    ∀ {I : Ideal (𝓞 K)}, I ≠ ⊥ →
    Ideal.span ({(a : 𝓞 K) + ζ * (b : 𝓞 K)} : Set (𝓞 K)) = I ^ p →
    ∃ k : ℕ, k < p ∧ ∃ β : K, β ≠ 0 ∧
      (algebraMap (𝓞 K) K
        (ζ ^ k * ((a : 𝓞 K) + ζ * (b : 𝓞 K)))) /
      (algebraMap (𝓞 K) K
        (ringOfIntegersComplexConj K
          (ζ ^ k * ((a : 𝓞 K) + ζ * (b : 𝓞 K))))) = β ^ p

variable {p K}

/-- **Stage 2 → CaseIClassEqDischarge.** Composes Stage 2 (the
K-level Kummer ratio) with the integral descent
(`exists_integral_kummer_ratio_of_K`, LV010-class-eq-1e) and the
class-equality conversion
(`caseI_class_eq_complexConj_of_conj_kummer_eq`, LV010-class-eq-1d) to
produce the `CaseIClassEqDischarge` predicate.

Once Stage 2 is closed unconditionally (via Kummer's lemma adapted to
`¬ p ∣ h⁺`), this composition gives the unconditional case-I bridge. -/
theorem caseIClassEqDischarge_of_stage2 (h_stage2 : Stage2KummerRatioK p K) :
    CaseIClassEqDischarge p K := by
  intro a b c hgcd hcaseI heq ζ hζ I hI_nz hI
  obtain ⟨k, _hk_lt, β, hβ_nz, h_kummer_K⟩ :=
    h_stage2 hgcd hcaseI heq hζ hI_nz hI
  set α : 𝓞 K := ζ ^ k * ((a : 𝓞 K) + ζ * (b : 𝓞 K)) with hα_def
  have hζk_unit : IsUnit (ζ ^ k) := (hζ.isUnit (Fact.out : p.Prime).ne_zero).pow k
  -- `α` and `a + ζ b` are associates (differ by the unit `ζ ^ k`), so `(α) = (a + ζ b) = I ^ p`.
  have hα_ideal : Ideal.span ({α} : Set (𝓞 K)) = I ^ p := by
    rw [hα_def, Ideal.span_singleton_mul_left_unit hζk_unit]
    exact hI
  -- `α ≠ 0`, else `(α) = (0) = ⊥`, forcing `I ^ p = ⊥` and hence `I = ⊥`.
  have hα_ne : α ≠ 0 := fun h => hI_nz <| by
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl] at hα_ideal
    exact (pow_eq_zero_iff (Fact.out : p.Prime).pos.ne').mp hα_ideal.symm
  have hσα_ne : ringOfIntegersComplexConj K α ≠ 0 :=
    (map_ne_zero_iff _ (ringOfIntegersComplexConj K).injective).mpr hα_ne
  obtain ⟨γ, δ, hγ_ne, hδ_ne, h_int_kummer⟩ :=
    exists_integral_kummer_ratio_of_K hα_ne hσα_ne hβ_nz h_kummer_K
  -- `(σα) = σ(α) = σ(I ^ p) = (σI) ^ p`.
  have hσα_ideal :
      Ideal.span ({ringOfIntegersComplexConj K α} : Set (𝓞 K)) =
        (I.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom) ^ p := by
    rw [← Ideal.map_pow, ← hα_ideal, Ideal.map_span]
    simp
  exact caseI_class_eq_complexConj_of_conj_kummer_eq
    (Fact.out : p.Prime).pos hα_ne hI_nz hα_ideal hσα_ideal hγ_ne hδ_ne h_int_kummer

/-- **Stage 2 vacuous discharge under regularity.** Under regularity
(`IsRegularPrime p`), `flt_regular` gives `FermatLastTheoremFor p`.
The Stage 2 predicate then holds vacuously: its antecedent
`a^p + b^p = c^p` with the case-I conditions has no solutions.

For irregular primes (FLT37), this does NOT apply; the substantive
Stage 2 work via Kummer's lemma adapted to `¬p ∣ h⁺` is required. -/
theorem stage2KummerRatioK_of_regular (hp_odd : p ≠ 2)
    (K' : Type) [Field K'] [NumberField K'] [IsCyclotomicExtension {p} ℚ K']
    [IsCMField K']
    (hreg : IsRegularPrime p) :
    Stage2KummerRatioK p K' := by
  intro a b c _ hcaseI heq _ _ _ _ _
  -- Regularity gives `FermatLastTheoremFor p`; with `p ∤ abc` forcing `a, b, c ≠ 0`,
  -- the integer form of FLT contradicts `a ^ p + b ^ p = c ^ p`.
  have hflt_int := fermatLastTheoremFor_iff_int.mp (flt_regular hreg hp_odd)
  have habc : a * b * c ≠ 0 := fun h0 => hcaseI (h0 ▸ dvd_zero _)
  have ha : a ≠ 0 := fun h => habc (by rw [h]; ring)
  have hb : b ≠ 0 := fun h => habc (by rw [h]; ring)
  have hc : c ≠ 0 := fun h => habc (by rw [h]; ring)
  exact absurd heq (hflt_int a b c ha hb hc)

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
