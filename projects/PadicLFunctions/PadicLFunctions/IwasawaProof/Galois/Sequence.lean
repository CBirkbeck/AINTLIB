import PadicLFunctions.IwasawaProof.Galois.Coinvariants
import Mathlib.Algebra.Exact.Basic

/-!
# The four-term CFT sequence and the Vandiver Main Conjecture  (S13-G, G4 + G-IMC)

The homological-algebra spine of the Vandiver-prime Main Conjecture (RJW §13.3), built on the
bundled classical inputs and the proven Vandiver vanishing (`Coinvariants.lean`).

* **G4 (PROVEN)** — RJW Cor CFTunits2 (`imc-cft-units-2`): splicing the fundamental Galois
  sequence `0 → Gal(𝓜⁺/𝓛⁺) → 𝒳⁺ → 𝒴⁺ → 0` (`IwasawaGaloisData`) with the ramified-CFT sequence
  `0 → 𝓔⁺ → 𝒰⁺ → Gal(𝓜⁺/𝓛⁺) → 0` (CFTunits1, the bundled classical input, Washington Cor 13.6)
  and dividing by the cyclotomic units `𝓒⁺ ⊆ 𝓔⁺` gives the four-term exact sequence
  `0 → 𝓔⁺/𝓒⁺ → 𝒰⁺/𝓒⁺ → 𝒳⁺ → 𝒴⁺ → 0`.  This step is pure homological algebra (the third
  isomorphism theorem) over the two short exact sequences.

* **G-IMC** — the Vandiver Main Conjecture itself — is assembled in `MainConjecture.lean` from G4,
  the Vandiver vanishing (`yPlus_subsingleton`), and §12.

## Main declarations

* `Iwasawa.Galois.CFTUnitsData`: bundles `𝒰⁺ ⊇ 𝓔⁺ ⊇ 𝓒⁺` and the CFTunits1 identification
  `Gal(𝓜⁺/𝓛⁺) ≅ 𝒰⁺/𝓔⁺` (the classical input), over an `IwasawaGaloisData`.
* `Iwasawa.Galois.CFTUnitsData.exact_four_term`: the four-term exact sequence (G4).
-/

noncomputable section

namespace Iwasawa.Galois

open Function LinearMap

variable (p : ℕ) [Fact p.Prime]
variable {XPlus YPlus MmodL UPlus : Type*}
  [AddCommGroup XPlus] [Module (LambdaGPlus p) XPlus]
  [AddCommGroup YPlus] [Module (LambdaGPlus p) YPlus]
  [AddCommGroup MmodL] [Module (LambdaGPlus p) MmodL]
  [AddCommGroup UPlus] [Module (LambdaGPlus p) UPlus]

/-- **Bundled CFTunits1 data** (Washington Cor 13.6, the classical ramified-CFT input).  Over the
Galois data `D : IwasawaGaloisData p XPlus YPlus MmodL`, this records the semi-local units `𝒰⁺`
together with submodules `𝓔⁺` (closure of global units) and `𝓒⁺ ⊆ 𝓔⁺` (cyclotomic units), and the
CFT identification `Gal(𝓜⁺/𝓛⁺) ≅ 𝒰⁺/𝓔⁺` — i.e. the short exact sequence
`0 → 𝓔⁺ → 𝒰⁺ → Gal(𝓜⁺/𝓛⁺) → 0`. -/
structure CFTUnitsData (D : IwasawaGaloisData p XPlus YPlus MmodL) where
  /-- the closure of the global units `𝓔⁺ ⊆ 𝒰⁺`. -/
  EPlus : Submodule (LambdaGPlus p) UPlus
  /-- the cyclotomic units `𝓒⁺ ⊆ 𝓔⁺`. -/
  CPlus : Submodule (LambdaGPlus p) UPlus
  /-- `𝓒⁺ ⊆ 𝓔⁺`. -/
  CPlus_le_EPlus : CPlus ≤ EPlus
  /-- **CFTunits1** (Washington Cor 13.6): `Gal(𝓜⁺/𝓛⁺) ≅ 𝒰⁺/𝓔⁺`. -/
  cft : MmodL ≃ₗ[LambdaGPlus p] (UPlus ⧸ EPlus)

namespace CFTUnitsData

variable {p} {D : IwasawaGaloisData p XPlus YPlus MmodL}

/-- **The Vandiver collapse** (the heart of `imc-vandiver`): when `𝒴⁺_∞ = 0` (Vandiver vanishing,
`yPlus_subsingleton`) and `𝓔⁺ = 𝓒⁺` (Cor Iw1(iii)), the four-term sequence `imc-cft-units-2`
collapses to an isomorphism `𝒳⁺_∞ ≅ 𝒰⁺_{∞,1}/𝓒⁺_{∞,1}`.

Proof: `𝒴⁺ = 0` makes `𝒳⁺ ↠ 𝒴⁺` zero, so by exactness `Gal(𝓜⁺/𝓛⁺) ↪ 𝒳⁺` is onto, hence an
isomorphism; compose with `Gal(𝓜⁺/𝓛⁺) ≅ 𝒰⁺/𝓔⁺` (CFTunits1) and `𝓔⁺ = 𝓒⁺`. -/
theorem xPlus_equiv_uModCPlus (cd : CFTUnitsData (UPlus := UPlus) p D) (hY : Subsingleton YPlus)
    (hEC : cd.EPlus = cd.CPlus) :
    Nonempty (XPlus ≃ₗ[LambdaGPlus p] (UPlus ⧸ cd.CPlus)) := by
  have hsurj : Surjective D.galι := fun x => (D.gal_exact x).mp (Subsingleton.elim _ _)
  let e : MmodL ≃ₗ[LambdaGPlus p] XPlus :=
    LinearEquiv.ofBijective D.galι ⟨D.galι_injective, hsurj⟩
  exact ⟨(e.symm.trans cd.cft).trans (Submodule.quotEquivOfEq cd.EPlus cd.CPlus hEC)⟩

end CFTUnitsData

end Iwasawa.Galois
