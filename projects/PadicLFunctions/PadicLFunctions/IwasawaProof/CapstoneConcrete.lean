import PadicLFunctions.IwasawaProof.Capstone
import PadicLFunctions.Iwasawa.CarrierBridgeConcrete
import PadicLFunctions.Iwasawa.StructureTheory.Completeness

/-!
# The Vandiver Main Conjecture with the concrete carrier bridge  (S13-G)

`iwasawa_main_conjecture_full` (both halves of `thm:vandiver`) instantiated with the **concrete**
carrier bridge `carrierBridgeFull` (`Iwasawa/CarrierBridgeConcrete.lean`) in place of the previously-
bundled ring-isomorphism hypothesis `Φ`, AND with the isotypic completeness `∑ e_ω = 1` discharged by
the proven `isotypicIdempotent_sum_eq_one` (`HasEnoughRootsOfUnity ℤ_[p] (exponent Δ)` from the
Teichmüller roots).  This strictly reduces the capstone's bundled inputs to just the classical CFT
data (`CFTUnitsData`) and the §12 analytic identification (`h12`) — both `Φ` and the completeness are
now internalized.

## Main declarations

* `Iwasawa.Galois.iwasawa_main_conjecture_full_concrete`: both halves of `thm:vandiver` with
  `Φ = carrierBridgeFull`.
-/

noncomputable section

namespace Iwasawa.Galois

open Iwasawa PadicMeasure PadicLFunctions

variable (p : ℕ) [Fact p.Prime]
variable {XPlus YPlus MmodL UPlus : Type*}
  [AddCommGroup XPlus] [Module (LambdaGPlus p) XPlus]
  [AddCommGroup YPlus] [Module (LambdaGPlus p) YPlus]
  [AddCommGroup MmodL] [Module (LambdaGPlus p) MmodL]
  [AddCommGroup UPlus] [Module (LambdaGPlus p) UPlus]

/-- **The Vandiver Main Conjecture, both halves, fully reduced.**  `iwasawa_main_conjecture_full`
with the carrier bridge `Φ` discharged by `carrierBridgeFull` (`Δ = Delta p hp2 = μ_{p−1}/⟨-1⟩`), the
isotypic completeness `∑_ω e_ω = 1` discharged by `isotypicIdempotent_sum_eq_one`, and the `Δ`
typeclass instances (`Fintype (Δ →* ℤ_[p]ˣ)`, `Invertible (|Δ| : ℤ_[p])`) all derived.  The **only**
remaining hypotheses are the genuinely-classical inputs the project bundles by design: the Galois data
`D`, the class-field-theory data `cd : CFTUnitsData`, the Vandiver vanishing `hY` + `hEC`, and the §12
analytic identification `h12`. -/
theorem iwasawa_main_conjecture_full_concrete (hp2 : p ≠ 2)
    {D : IwasawaGaloisData p XPlus YPlus MmodL} (cd : CFTUnitsData (UPlus := UPlus) p D)
    (hY : Subsingleton YPlus) (hEC : cd.EPlus = cd.CPlus)
    {g : LambdaGPlus p}
    (h12 : Nonempty ((UPlus ⧸ cd.CPlus) ≃ₗ[LambdaGPlus p] (LambdaGPlus p ⧸ Ideal.span {g}))) :
    Nonempty (XPlus ≃ₗ[LambdaGPlus p] (LambdaGPlus p ⧸ Ideal.span {g})) ∧
    (letI : Module (IwasawaAlgebraGroup ℤ_[p] (Delta p hp2)) XPlus :=
        Module.compHom XPlus
          ((carrierBridgeFull p hp2).symm : IwasawaAlgebraGroup ℤ_[p] (Delta p hp2) →+* LambdaGPlus p)
      ∀ [Module.Finite (IwasawaAlgebraGroup ℤ_[p] (Delta p hp2)) XPlus]
        [Module.Finite (IwasawaAlgebraGroup ℤ_[p] (Delta p hp2))
          (IwasawaAlgebraGroup ℤ_[p] (Delta p hp2) ⧸ Ideal.span {carrierBridgeFull p hp2 g})]
        (hX : Module.IsTorsion (IwasawaAlgebraGroup ℤ_[p] (Delta p hp2)) XPlus),
        charIdealGroup ℤ_[p] (Delta p hp2) XPlus hX = Ideal.span {carrierBridgeFull p hp2 g}) :=
  iwasawa_main_conjecture_full p (isotypicIdempotent_sum_eq_one ℤ_[p] (Delta p hp2))
    cd hY hEC h12 (carrierBridgeFull p hp2)

end Iwasawa.Galois
