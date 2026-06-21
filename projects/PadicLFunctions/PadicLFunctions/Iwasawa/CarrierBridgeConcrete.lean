import PadicLFunctions.Iwasawa.GPlusDecomp
import PadicLFunctions.Iwasawa.CarrierBridge

/-!
# The concrete carrier bridge `Λ(𝒢⁺) ≅ IwasawaAlgebraGroup ℤ_p Δ`  (S13-G, CARRIER-BRIDGE, assembled)

The carrier-bridge ring isomorphism `Φ` of the Iwasawa Main Conjecture, **fully assembled** (no longer
a bundled hypothesis) from:

* the group decomposition `𝒢⁺ ≅ Δ × Γ` (`gplusMulEquiv`, `Δ = μ_{p−1}/⟨-1⟩`, `Γ` the 1-units), promoted
  to a homeomorphism `gplusHomeo` (continuous bijection from the compact `𝒢⁺` to the T2 `Δ × Γ`); and
* the logarithm isomorphism `Γ ≅ (ℤ_p,+)` (`logCM`/`expCM` + their homomorphism/inverse laws),

fed through the measure-functoriality `carrierBridge` (`Iwasawa/CarrierBridge.lean`).

## Main declarations

* `PadicMeasure.gplusHomeo`: the homeomorphism `𝒢⁺ ≃ₜ Δ × Γ`.
* `PadicMeasure.carrierBridgeFull`: the ring isomorphism
  `Λ(𝒢⁺) = PadicMeasure p (𝒢⁺) ≃+* IwasawaAlgebraGroup ℤ_p Δ`.
-/

noncomputable section

namespace PadicMeasure

open PadicLFunctions

variable (p : ℕ) [hp : Fact p.Prime]

/-- The group decomposition `𝒢⁺ ≃* Δ × Γ` promoted to a **homeomorphism**: a continuous bijection from
the compact `𝒢⁺` (quotient of the compact `ℤ_[p]ˣ`) to the T2 space `Δ × Γ` is a homeomorphism
(`Continuous.homeoOfEquivCompactToT2`, using `continuous_gplusMulEquiv`). -/
def gplusHomeo (hp2 : p ≠ 2) : GPlus p ≃ₜ (Delta p hp2 × Gamma p) :=
  Continuous.homeoOfEquivCompactToT2 (continuous_gplusMulEquiv p hp2)

/-- **The carrier bridge `Φ`, fully assembled**: `Λ(𝒢⁺) = PadicMeasure p (𝒢⁺) ≃+* IwasawaAlgebraGroup
ℤ_p Δ`.  Composes the group homeomorphism `𝒢⁺ ≃ₜ Δ × Γ` (`gplusMulEquiv`/`gplusHomeo`) and the
logarithm isomorphism `Γ ≅ ℤ_p` (`logCM`/`expCM`) through the measure-functoriality `carrierBridge`.
This discharges the previously-bundled carrier-bridge input of the Main-Conjecture capstone. -/
def carrierBridgeFull (hp2 : p ≠ 2) :
    PadicMeasure p (GPlus p) ≃+* Iwasawa.IwasawaAlgebraGroup ℤ_[p] (Delta p hp2) := by
  letI : Fintype (Delta p hp2) := Fintype.ofFinite _
  letI : DecidableEq (Delta p hp2) := Classical.decEq _
  exact carrierBridge p
    (⟨gplusMulEquiv p hp2, continuous_gplusMulEquiv p hp2⟩ : C(GPlus p, _))
    (⟨(gplusHomeo p hp2).symm, (gplusHomeo p hp2).symm.continuous⟩ : C(_, GPlus p))
    (fun x y => map_mul (gplusMulEquiv p hp2) x y)
    (map_one (gplusMulEquiv p hp2))
    (fun x => (gplusMulEquiv p hp2).symm_apply_apply x)
    (fun y => (gplusMulEquiv p hp2).apply_symm_apply y)
    (logCM p hp2) (expCM p hp2)
    (logCM_mul p hp2) (logCM_one p hp2) (expCM_logCM p hp2) (logCM_expCM p hp2)

end PadicMeasure
