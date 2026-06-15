module

public import BernoulliRegular.Reflection.Kummer.Basic
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.PthSymbolCanonical

/-!
# Residue-symbol vanishing and local Kummer splitting

This file contains the local bridge used in the nontriviality step of weak
reflection: in the good case, canonical residue-symbol vanishing implies that
`X^p - η` splits over the residue field.
-/

@[expose] public section

noncomputable section

open scoped NumberField
open Polynomial

namespace BernoulliRegular
namespace Reflection
namespace Kummer

variable {p : ℕ} [Fact p.Prime]
variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- A `p`-th-power residue unit makes `X^p - η` split over the residue field. -/
theorem residue_X_pow_sub_C_splits_of_residue_isPow
    {η : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hη : η ∉ q) (hp_in : (p : 𝓞 K) ∉ q)
    (hpow : ∃ y : (𝓞 K ⧸ q)ˣ,
      ResidueSymbol.PowerResidue.quotientUnitOfNotMem q η hη = y ^ p) :
    (X ^ p - C (Ideal.Quotient.mk q η) : (𝓞 K ⧸ q)[X]).Splits := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : NeZero q := ⟨hbot⟩
  haveI hmax' : q.IsMaximal := hmax
  haveI : q.IsPrime := hmax.isPrime
  letI : Field (𝓞 K ⧸ q) := Ideal.Quotient.field q
  obtain ⟨y, hy⟩ := hpow
  have hζ_unit : IsPrimitiveRoot
      (Furtwaengler.canonicalResidueZetaP (p := p) (K := K) q) p :=
    Furtwaengler.canonicalResidueZetaP_isPrimitiveRoot hbot hp_in
  have hζ : IsPrimitiveRoot
      ((Furtwaengler.canonicalResidueZetaP (p := p) (K := K) q : (𝓞 K ⧸ q)ˣ) :
        𝓞 K ⧸ q) p :=
    IsPrimitiveRoot.coe_units_iff.mpr hζ_unit
  have hy_val : (y : 𝓞 K ⧸ q) ^ p = Ideal.Quotient.mk q η := by
    have h := congrArg Units.val hy
    simpa [ResidueSymbol.PowerResidue.quotientUnitOfNotMem] using h.symm
  exact X_pow_sub_C_splits_of_isPrimitiveRoot hζ hy_val

/-- Canonical prime-symbol vanishing makes `X^p - η` split over the residue
field in the good case. -/
theorem residue_X_pow_sub_C_splits_of_pthSymbolAtPrime_canonical_eq_zero
    {η : 𝓞 K} {q : Ideal (𝓞 K)} (hbot : q ≠ ⊥) (hmax : q.IsMaximal)
    (hη : η ∉ q) (hdiv : p ∣ Fintype.card (𝓞 K ⧸ q) - 1)
    (hp_in : (p : 𝓞 K) ∉ q)
    (hsym : Furtwaengler.pthSymbolAtPrime_canonical (p := p) (K := K) η q = 0) :
    (X ^ p - C (Ideal.Quotient.mk q η) : (𝓞 K ⧸ q)[X]).Splits :=
  residue_X_pow_sub_C_splits_of_residue_isPow hbot hmax hη hp_in <|
    Furtwaengler.residue_isPow_of_pthSymbolAtPrime_canonical_eq_zero
      hbot hmax hη hdiv hp_in hsym

end Kummer
end Reflection
end BernoulliRegular

end
