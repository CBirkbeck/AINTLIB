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

/-- **The Vandiver Main Conjecture, both halves, with the concrete carrier bridge.**  Identical to
`iwasawa_main_conjecture_full` but with `Φ` discharged by the assembled `carrierBridgeFull p hp2`
(`Δ = Delta p hp2 = μ_{p−1}/⟨-1⟩`).  Inputs reduced to the Galois/CFT/Vandiver data and `h12`; the
completeness is discharged internally by `isotypicIdempotent_sum_eq_one`. -/
theorem iwasawa_main_conjecture_full_concrete (hp2 : p ≠ 2)
    [Invertible (Fintype.card (Delta p hp2) : ℤ_[p])] [Fintype (Delta p hp2 →* ℤ_[p]ˣ)]
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
