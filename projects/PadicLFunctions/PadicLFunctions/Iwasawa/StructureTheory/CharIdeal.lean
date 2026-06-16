import PadicLFunctions.Iwasawa.StructureTheory.StructureTheorem

/-!
# The characteristic ideal and its multiplicativity  (S13-S4)

For a finitely generated torsion `Λ`-module `M`, the structure theorem (S13-S3)
gives `M ~ ⨁ Λ/(gᵢ^eᵢ)`; its **characteristic ideal** is the product
`Ch_Λ(M) = ∏ᵢ (gᵢ^eᵢ) = (ϖ^n)·∏ⱼ(fⱼ^mⱼ)` (RJW TeX 3652–3657).  It is a
pseudo-isomorphism invariant — finite modules have characteristic ideal `(1) = ⊤` —
and it is **multiplicative in short exact sequences** (CS06, Appendix A.1, Prop 1;
RJW TeX 3679–3681).

## Main declarations

* `Iwasawa.charIdeal M hM`: the characteristic ideal `Ch_Λ(M) ⊆ Λ` of a finitely
  generated torsion module, read off from `fg_pseudoIso_canonical` (S13-S3).
* `Iwasawa.charIdeal_eq_of_pseudoIso`: well-definedness — `Ch_Λ` is constant on
  pseudo-isomorphism classes.
* `Iwasawa.charIdeal_mul_of_exact`: **multiplicativity** — for a short exact
  sequence `0 → M' → M → M'' → 0` of finitely generated torsion modules,
  `Ch_Λ(M) = Ch_Λ(M') · Ch_Λ(M'')` (CS06 A.1 Prop 1).
-/

noncomputable section

namespace Iwasawa

variable (𝒪 : Type*) [CommRing 𝒪]

local notation "Λ" => IwasawaAlgebra 𝒪

/-- The **characteristic ideal** `Ch_Λ(M) = ∏ᵢ (gᵢ^eᵢ) ⊆ Λ` of a finitely generated
torsion `Λ`-module `M`, defined from the prime-power data of the structure theorem
`fg_pseudoIso_canonical` (S13-S3).  (RJW TeX 3652–3657.) -/
def charIdeal (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
    [Module.Finite (IwasawaAlgebra 𝒪) M] (_hM : Module.IsTorsion (IwasawaAlgebra 𝒪) M) :
    Ideal (IwasawaAlgebra 𝒪) :=
  sorry

variable {𝒪}
variable {M M' M'' : Type*}
  [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M] [Module.Finite (IwasawaAlgebra 𝒪) M]
  [AddCommGroup M'] [Module (IwasawaAlgebra 𝒪) M'] [Module.Finite (IwasawaAlgebra 𝒪) M']
  [AddCommGroup M''] [Module (IwasawaAlgebra 𝒪) M''] [Module.Finite (IwasawaAlgebra 𝒪) M'']

/-- **Well-definedness of the characteristic ideal**: it depends only on the
pseudo-isomorphism class of `M`.  In particular a finite (pseudo-null) module has
characteristic ideal `⊤ = (1)`.  (The `gᵢ^eᵢ` data is the pseudo-iso invariant of
the structure theorem.) -/
theorem charIdeal_eq_of_pseudoIso (hM : Module.IsTorsion (IwasawaAlgebra 𝒪) M)
    (hM' : Module.IsTorsion (IwasawaAlgebra 𝒪) M') (h : IsPseudoIso 𝒪 M M') :
    charIdeal 𝒪 M hM = charIdeal 𝒪 M' hM' := by
  sorry

/-- **Multiplicativity of the characteristic ideal in short exact sequences**
(CS06, App. A.1, Prop 1; RJW TeX 3679–3681): given `0 → M' → M → M'' → 0` with
`M', M, M''` finitely generated torsion `Λ`-modules,
`Ch_Λ(M) = Ch_Λ(M') · Ch_Λ(M'')`. -/
theorem charIdeal_mul_of_exact
    (hM : Module.IsTorsion (IwasawaAlgebra 𝒪) M)
    (hM' : Module.IsTorsion (IwasawaAlgebra 𝒪) M')
    (hM'' : Module.IsTorsion (IwasawaAlgebra 𝒪) M'')
    (f : M' →ₗ[IwasawaAlgebra 𝒪] M) (g : M →ₗ[IwasawaAlgebra 𝒪] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : LinearMap.range f = LinearMap.ker g) :
    charIdeal 𝒪 M hM = charIdeal 𝒪 M' hM' * charIdeal 𝒪 M'' hM'' := by
  sorry

end Iwasawa
