import PadicLFunctions.Iwasawa.StructureTheory.StructureTheorem
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.Module
import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.RingTheory.Ideal.Height

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

/-- The **local multiplicity** of a `Λ`-module `M` at a prime `P`: the length of the
localisation `M_P` as a module over `Λ_P = Localization.AtPrime P`.  For a height-one
prime of the UFD `Λ`, `Λ_P` is a DVR (`iwasawaAlgebra_localization_atPrime_isDVR`, S3b)
and this is finite for finitely generated torsion `M`.  This is the per-prime "order of
vanishing" whose product over height-one primes is the characteristic ideal — the
length-theoretic route that avoids the full structure theorem. -/
noncomputable def localMult (P : Ideal (IwasawaAlgebra 𝒪)) [P.IsPrime]
    (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M] : ℕ∞ :=
  Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M)

/-- **Additivity of the local multiplicity in short exact sequences** — the heart of the
characteristic ideal's multiplicativity.  For `0 → M' → M → M'' → 0`, localisation at `P`
is exact (`LocalizedModule.map_exact`) and module length is additive in short exact
sequences (`Module.length_eq_add_of_exact`), so the local multiplicities add.  No structure
theorem is used. -/
theorem localMult_add_of_exact (P : Ideal (IwasawaAlgebra 𝒪)) [P.IsPrime]
    {M' M M'' : Type*} [AddCommGroup M'] [Module (IwasawaAlgebra 𝒪) M']
    [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
    [AddCommGroup M''] [Module (IwasawaAlgebra 𝒪) M'']
    (f : M' →ₗ[IwasawaAlgebra 𝒪] M) (g : M →ₗ[IwasawaAlgebra 𝒪] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    localMult 𝒪 P M = localMult 𝒪 P M' + localMult 𝒪 P M'' :=
  Module.length_eq_add_of_exact
    (LocalizedModule.map P.primeCompl f) (LocalizedModule.map P.primeCompl g)
    (LocalizedModule.map_injective _ f hf) (LocalizedModule.map_surjective _ g hg)
    (LocalizedModule.map_exact _ f g hfg)

/-- The **characteristic ideal** `Ch_Λ(M) ⊆ Λ` of a finitely generated torsion `Λ`-module,
defined the length-theoretic way: the product over height-one primes `P` of
`P ^ localMult P M` (RJW TeX 3652–3657).  Only finitely many factors are non-trivial (the
support is finite, `iwasawaAlgebra_associatedPrimes_finite`), so the `finprod` is genuine.
This definition needs no structure theorem; its multiplicativity is `localMult_add_of_exact`
through `finprod`. -/
noncomputable def charIdeal (M : Type*) [AddCommGroup M] [Module (IwasawaAlgebra 𝒪) M]
    [Module.Finite (IwasawaAlgebra 𝒪) M] (_hM : Module.IsTorsion (IwasawaAlgebra 𝒪) M) :
    Ideal (IwasawaAlgebra 𝒪) :=
  ∏ᶠ (P : {P : Ideal (IwasawaAlgebra 𝒪) // P.IsPrime ∧ P.height = 1}),
    letI : P.1.IsPrime := P.2.1
    P.1 ^ (localMult 𝒪 P.1 M).toNat

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
