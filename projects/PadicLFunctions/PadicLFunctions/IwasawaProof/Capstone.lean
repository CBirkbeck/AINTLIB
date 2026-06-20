import PadicLFunctions.IwasawaProof.MainConjecture
import PadicLFunctions.IwasawaProof.CharIdealConjunct

/-!
# The Iwasawa Main Conjecture for Vandiver primes — unified capstone  (S13-G)

Both halves of RJW `thm:vandiver` in a single statement, over the measure carrier
`Λ(𝒢⁺) = PadicMeasure p (𝒢⁺)`:

1. **isomorphism** `𝒳⁺_∞ ≅ Λ(𝒢⁺)/(g)` (`iwasawa_main_conjecture_vandiver`), and
2. **characteristic ideal** `Ch_{Λ(𝒢⁺)}(𝒳⁺_∞) = (g)` — read off, via the carrier bridge
   `Φ : Λ(𝒢⁺) ≃+* IwasawaAlgebraGroup ℤ_p Δ` (`charIdealGroup_eq_of_carrierBridge`), as the bridged
   generator `Φ g` of the equivariant characteristic ideal.

Every genuinely Iwasawa-theoretic step is proven (the Galois decomposition, the Nakayama Vandiver
vanishing, the four-term collapse, the entire `Λ`-module structure theory behind the characteristic
ideal, and the measure-algebra carrier bridge machinery).  The remaining hypotheses are precisely the
classical/analytic inputs the project bundles by design — the class field theory `CFTUnitsData`, the
§12 analytic identification `h12`, and the carrier-bridge ring isomorphism `Φ` (assembled from the
p-adic group decomposition `𝒢⁺ ≅ Δ × Γ` and the logarithm iso `Γ ≅ ℤ_p`, `Iwasawa/CarrierBridge.lean`).

## Main declarations

* `Iwasawa.Galois.iwasawa_main_conjecture_full`: both halves of `thm:vandiver` from the bundled inputs.
-/

noncomputable section

namespace Iwasawa.Galois

open Iwasawa

variable (p : ℕ) [Fact p.Prime]
variable {XPlus YPlus MmodL UPlus : Type*}
  [AddCommGroup XPlus] [Module (LambdaGPlus p) XPlus]
  [AddCommGroup YPlus] [Module (LambdaGPlus p) YPlus]
  [AddCommGroup MmodL] [Module (LambdaGPlus p) MmodL]
  [AddCommGroup UPlus] [Module (LambdaGPlus p) UPlus]

/-- **The Iwasawa Main Conjecture for Vandiver primes — both halves.**  From the Galois data `D`, the
CFT units data `cd`, the Vandiver vanishing `hY : 𝒴⁺_∞ = 0`, `hEC : 𝓔⁺ = 𝓒⁺`, the §12 identification
`h12 : 𝒰⁺/𝓒⁺ ≅ Λ(𝒢⁺)/(g)`, and the carrier bridge `Φ : Λ(𝒢⁺) ≃+* IwasawaAlgebraGroup ℤ_p Δ`:

* (isomorphism) `𝒳⁺_∞ ≅ Λ(𝒢⁺)/(g)`;
* (characteristic ideal) viewing `𝒳⁺_∞` as an `IwasawaAlgebraGroup ℤ_p Δ`-module along `Φ⁻¹`,
  `Ch_{Λ(𝒢⁺)}(𝒳⁺_∞) = (Φ g)`. -/
theorem iwasawa_main_conjecture_full
    {Δ : Type*} [CommGroup Δ] [Fintype Δ] [Invertible (Fintype.card Δ : ℤ_[p])]
    [Fintype (Δ →* ℤ_[p]ˣ)]
    (hcomplete : ∑ ω : Δ →* ℤ_[p]ˣ, isotypicIdempotent ℤ_[p] Δ ω = 1)
    {D : IwasawaGaloisData p XPlus YPlus MmodL} (cd : CFTUnitsData (UPlus := UPlus) p D)
    (hY : Subsingleton YPlus) (hEC : cd.EPlus = cd.CPlus)
    {g : LambdaGPlus p}
    (h12 : Nonempty ((UPlus ⧸ cd.CPlus) ≃ₗ[LambdaGPlus p] (LambdaGPlus p ⧸ Ideal.span {g})))
    (Φ : LambdaGPlus p ≃+* IwasawaAlgebraGroup ℤ_[p] Δ) :
    Nonempty (XPlus ≃ₗ[LambdaGPlus p] (LambdaGPlus p ⧸ Ideal.span {g})) ∧
    (letI : Module (IwasawaAlgebraGroup ℤ_[p] Δ) XPlus := Module.compHom XPlus (Φ.symm : _ →+* LambdaGPlus p)
      ∀ [Module.Finite (IwasawaAlgebraGroup ℤ_[p] Δ) XPlus]
        [Module.Finite (IwasawaAlgebraGroup ℤ_[p] Δ)
          (IwasawaAlgebraGroup ℤ_[p] Δ ⧸ Ideal.span {Φ g})]
        (hX : Module.IsTorsion (IwasawaAlgebraGroup ℤ_[p] Δ) XPlus),
        charIdealGroup ℤ_[p] Δ XPlus hX = Ideal.span {Φ g}) := by
  obtain ⟨e⟩ := iwasawa_main_conjecture_vandiver p cd hY hEC h12
  refine ⟨⟨e⟩, ?_⟩
  letI : Module (IwasawaAlgebraGroup ℤ_[p] Δ) XPlus := Module.compHom XPlus (Φ.symm : _ →+* LambdaGPlus p)
  intro hF1 hF2 hX
  haveI := hF1
  haveI := hF2
  exact charIdealGroup_eq_of_carrierBridge hcomplete Φ e hX

end Iwasawa.Galois
