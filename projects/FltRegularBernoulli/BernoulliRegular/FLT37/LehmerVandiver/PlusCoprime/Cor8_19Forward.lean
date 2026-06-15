import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.KummerLift.Bridge
import BernoulliRegular.TotallyRealSubfield.ClassGroup

/-!
# Cor 8.19 forward formulation + contrapositive constructor

The `Cor8_19Bridge` structure stores the contrapositive form
`(¬ IsPthPower(pollaczekUnitPlus)) → ¬ p ∣ h⁺`. Mathematically, the
classical statement (Washington Cor 8.19) is the forward form
`p ∣ h⁺ → IsPthPower(pollaczekUnitPlus)`.

This file provides:
* The forward Prop `Cor8_19Forward`.
* A bridge constructor `cor8_19Bridge_of_forward` showing the forward
  form yields the contrapositive bundle field. Useful for callers
  who'd rather prove the forward form directly.

The mathematical content (Sinnott's index formula
`[(𝓞 K⁺)ˣ : C⁺] = h⁺(K)`) is unchanged either way; this is just a
re-packaging convenience.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed., §8.3,
  Cor 8.19.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **Cor 8.19 forward statement**: classical direction.
`p ∣ h⁺(K) → pollaczekUnitPlus is a p-th power in (𝓞 K)ˣ`.

This is the natural statement of Washington Corollary 8.19 (real
form, applied to `pollaczekUnitPlus`). The bundle field
`Cor8_19Bridge.not_dvd_hPlus_of_not_isPthPower` is the contrapositive
of this. -/
def Cor8_19Forward (i : ℕ) : Prop :=
  (p : ℕ) ∣ hPlus K →
    ∃ α : (𝓞 K)ˣ,
      ((FLT37.pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) =
        ((α : (𝓞 K)ˣ) : 𝓞 K) ^ p

/-- **Bridge constructor from forward statement.** Convert the forward
form `p ∣ h⁺ → IsPthPower(pollaczekUnitPlus)` into the contrapositive
`Cor8_19Bridge` bundle field via classical contraposition.

Useful for callers who prove Cor 8.19 in the forward direction
(matching the standard textbook formulation). -/
def cor8_19Bridge_of_forward {i : ℕ} (h : Cor8_19Forward p K i) :
    Cor8_19Bridge p K i where
  not_dvd_hPlus_of_not_isPthPower h_no_pth h_dvd := by
    obtain ⟨α, hα⟩ := h h_dvd
    exact h_no_pth α hα

/-- **Forward statement from bridge.** Conversely, the bridge gives
the forward form. Trivial direction. -/
theorem cor8_19Forward_of_bridge {i : ℕ} (B : Cor8_19Bridge p K i) :
    Cor8_19Forward p K i := by
  intro h_dvd
  by_contra h_no
  push Not at h_no
  exact B.not_dvd_hPlus_of_not_isPthPower h_no h_dvd

/-- **`Cor8_19Bridge_of_not_dvd_hPlus`** — direct constructor from
`¬ p ∣ hPlus K`. If `p ∤ h⁺` is already known (e.g., for regular primes
or via direct computation), the bridge is trivially constructible: the
conclusion `¬ p ∣ h⁺` is already given. -/
def cor8_19Bridge_of_not_dvd_hPlus {i : ℕ}
    (h : ¬ (p : ℕ) ∣ hPlus K) : Cor8_19Bridge p K i where
  not_dvd_hPlus_of_not_isPthPower _ := h

/-- **`Cor8_19Forward_of_not_dvd_hPlus`** — direct constructor of the
forward statement from `¬ p ∣ hPlus K`. Vacuous: the antecedent
`p ∣ h⁺` is false, so the implication holds trivially. -/
theorem cor8_19Forward_of_not_dvd_hPlus {i : ℕ}
    (h : ¬ (p : ℕ) ∣ hPlus K) : Cor8_19Forward p K i := fun h_dvd =>
  absurd h_dvd h

/-- **`Cor8_19Bridge_of_regular`** — under regularity (`p.Coprime |Cl(𝓞 K)|`)
and `p` odd, the bridge holds vacuously. Since `h⁺ ∣ h` (`hPlus_dvd_h`),
regularity (`¬ p ∣ h`) implies `¬ p ∣ h⁺`, which feeds the trivial
constructor.

This is the analogue of `realKummerLemma_of_regular` for the Cor 8.19
side: under regularity the chain composes without any deep CFT input. -/
def cor8_19Bridge_of_regular {i : ℕ} (hp_odd : p ≠ 2)
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K)) :
    Cor8_19Bridge p K i := by
  apply cor8_19Bridge_of_not_dvd_hPlus
  -- regularity = ¬ p ∣ h, and h⁺ ∣ h, so ¬ p ∣ h⁺.
  have hp_prime : p.Prime := Fact.out
  have h_not_dvd_h : ¬ (p : ℕ) ∣ Fintype.card (ClassGroup (𝓞 K)) :=
    hp_prime.coprime_iff_not_dvd.mp hreg
  -- hPlus K ∣ h K, and h K is definitionally Fintype.card (ClassGroup (𝓞 K))
  have hdvd : hPlus K ∣ Fintype.card (ClassGroup (𝓞 K)) := by
    have hh := hPlus_dvd_h p hp_odd K
    unfold BernoulliRegular.h at hh
    convert hh
  exact fun h => h_not_dvd_h (h.trans hdvd)

/-- **`Cor8_19Forward_of_regular`** — same for the forward form. -/
theorem cor8_19Forward_of_regular {i : ℕ} (hp_odd : p ≠ 2)
    [Fintype (ClassGroup (𝓞 K))]
    (hreg : p.Coprime <| Fintype.card <| ClassGroup (𝓞 K)) :
    Cor8_19Forward p K i :=
  cor8_19Forward_of_bridge p K (cor8_19Bridge_of_regular p K hp_odd hreg)

end BernoulliRegular

end
