import PadicLFunctions.IwasawaProof.Galois.Sequence

/-!
# The Iwasawa Main Conjecture for Vandiver primes  (S13-G, G-IMC)

The capstone of the Galois side (RJW §13.3, `thm:vandiver`): for a Vandiver prime,
`𝒳⁺_∞ ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p`, whence the Iwasawa Main Conjecture.

The proof assembles three ingredients:

1. the **Vandiver collapse** `𝒳⁺_∞ ≅ 𝒰⁺_{∞,1}/𝓒⁺_{∞,1}` (`CFTUnitsData.xPlus_equiv_uModCPlus`, proven),
   itself built on the proven Vandiver vanishing `𝒴⁺_∞ = 0` (`VandiverData.yPlus_subsingleton`,
   via Nakayama) and `𝓔⁺ = 𝓒⁺` (RJW Cor Iw1(iii));
2. the §12 **analytic identification** `𝒰⁺_{∞,1}/𝓒⁺_{∞,1} ≅ Λ(𝒢⁺)/I(𝒢⁺)ζ_p` (the milestone
   `iwasawa_theorem`, whose remaining core `col_image_cycloTower1_eq_zetaIdeal` is deferred in §12,
   so it enters here as the hypothesis `h12`).

Composing (1) and (2) gives the Vandiver Main Conjecture.  The genuinely *proven* Stage-G content
is the entire connective chain (the Galois decomposition, the Nakayama vanishing, the collapse, and
this composition); the bundled inputs are the classical class field theory (`ClassFieldTheory`,
CFTunits1) and the analytic §12 milestone — exactly the inputs RJW cite.

## Main declarations

* `Iwasawa.Galois.iwasawa_main_conjecture_vandiver`: `𝒳⁺_∞ ≅ Λ(𝒢⁺)/I` from the collapse and the
  §12 identification.
-/

noncomputable section

namespace Iwasawa.Galois

variable (p : ℕ) [Fact p.Prime]
variable {XPlus YPlus MmodL UPlus : Type*}
  [AddCommGroup XPlus] [Module (LambdaGPlus p) XPlus]
  [AddCommGroup YPlus] [Module (LambdaGPlus p) YPlus]
  [AddCommGroup MmodL] [Module (LambdaGPlus p) MmodL]
  [AddCommGroup UPlus] [Module (LambdaGPlus p) UPlus]

/-- **The Iwasawa Main Conjecture for Vandiver primes** (RJW `thm:vandiver`), isomorphism form.
For an ideal `I` of `Λ(𝒢⁺)` (in the application, `I = I(𝒢⁺)ζ_p = zetaIdealPlus`), given:

* the Galois data `D` and the CFTunits1 data `cd` (Washington Cor 13.6);
* the **Vandiver vanishing** `hY : 𝒴⁺_∞ = 0` (supplied by `VandiverData.yPlus_subsingleton`);
* `hEC : 𝓔⁺ = 𝓒⁺` (RJW Cor Iw1(iii));
* the §12 identification `h12 : 𝒰⁺_{∞,1}/𝓒⁺_{∞,1} ≅ Λ(𝒢⁺)/I` (the milestone `iwasawa_theorem`),

we obtain an isomorphism of `Λ(𝒢⁺)`-modules `𝒳⁺_∞ ≅ Λ(𝒢⁺)/I`. -/
theorem iwasawa_main_conjecture_vandiver {I : Ideal (LambdaGPlus p)}
    {D : IwasawaGaloisData p XPlus YPlus MmodL} (cd : CFTUnitsData (UPlus := UPlus) p D)
    (hY : Subsingleton YPlus) (hEC : cd.EPlus = cd.CPlus)
    (h12 : Nonempty ((UPlus ⧸ cd.CPlus) ≃ₗ[LambdaGPlus p] (LambdaGPlus p ⧸ I))) :
    Nonempty (XPlus ≃ₗ[LambdaGPlus p] (LambdaGPlus p ⧸ I)) := by
  obtain ⟨e⟩ := cd.xPlus_equiv_uModCPlus hY hEC
  obtain ⟨f⟩ := h12
  exact ⟨e.trans f⟩

end Iwasawa.Galois
