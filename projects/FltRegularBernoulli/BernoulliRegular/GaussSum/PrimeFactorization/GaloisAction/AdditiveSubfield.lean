module

public import BernoulliRegular.GaussSum.PrimeFactorization.GaloisAction.CharacterSubfield

/-!
# Additive subfield primes in the Stickelberger field
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped Pointwise

namespace BernoulliRegular

section GaloisAction

variable (p : ℕ) [hp : Fact p.Prime]
  (L : Type*) [Field L] [NumberField L] [IsCyclotomicExtension {p * (p - 1)} ℚ L]

local notation "𝔭" => (Ideal.span ({(p : ℤ)} : Set ℤ))
local instance : NeZero (p - 1) := ⟨Nat.sub_ne_zero_of_lt hp.out.one_lt⟩

/-- The `p`-cyclotomic subfield inside the Stickelberger field. -/
noncomputable abbrev additiveSubfield : IntermediateField ℚ L :=
  IntermediateField.adjoin ℚ {(((gaussSumLiftAdditiveRoot (p := p) L : 𝓞 L) : L))}

instance additiveSubfield_isCyclotomic :
    IsCyclotomicExtension {p} ℚ (additiveSubfield (L := L) (p := p)) := by
  let ζ : L := ((gaussSumLiftAdditiveRoot (p := p) L : 𝓞 L) : L)
  have hζ : IsPrimitiveRoot ζ p := by
    simpa [ζ] using
      (gaussSumLiftAdditiveRoot_isPrimitiveRoot (p := p) (L := L)).map_of_injective
        NumberField.RingOfIntegers.coe_injective
  exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
    (K := ℚ) (L := L) (n := p) (F := additiveSubfield (L := L) (p := p)) hζ).2 rfl

/-- The canonical `1 - ζ_p` prime in the `p`-cyclotomic subfield. -/
noncomputable abbrev additiveZetaPrime :
    Ideal (𝓞 (additiveSubfield (L := L) (p := p))) :=
  Ideal.span
    ({(IsCyclotomicExtension.zeta_spec p ℚ
        (additiveSubfield (L := L) (p := p))).toInteger - 1} :
      Set (𝓞 (additiveSubfield (L := L) (p := p))))

/-- Any prime of `𝓞 L` lying over `𝔭` contracts to the canonical `1 - ζ_p` prime in the
`p`-cyclotomic subfield. -/
private lemma under_additiveSubfield_eq_additiveZetaPrime (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver 𝔭] :
    Q.under (𝓞 (additiveSubfield (L := L) (p := p))) = additiveZetaPrime (L := L) (p := p) := by
  simpa [additiveZetaPrime] using
    (IsCyclotomicExtension.Rat.eq_span_zeta_sub_one_of_liesOver'
      (p := p)
      (K := additiveSubfield (L := L) (p := p))
      (hζ := IsCyclotomicExtension.zeta_spec p ℚ (additiveSubfield (L := L) (p := p)))
      (P := Q.under (𝓞 (additiveSubfield (L := L) (p := p)))))

lemma distinguishedPrimeAboveP_under_additiveSubfield_eq_additiveZetaPrime :
    (distinguishedPrimeAboveP p L).under (𝓞 (additiveSubfield (L := L) (p := p))) =
      additiveZetaPrime (L := L) (p := p) :=
  under_additiveSubfield_eq_additiveZetaPrime p L (distinguishedPrimeAboveP p L)

lemma sigmaOfUnit_smul_distinguishedPrimeAboveP_under_eq_additiveZetaPrime (a : (ZMod p)ˣ) :
    ((sigmaOfUnit (p := p) L a) • distinguishedPrimeAboveP p L).under
        (𝓞 (additiveSubfield (L := L) (p := p))) =
      additiveZetaPrime (L := L) (p := p) :=
  under_additiveSubfield_eq_additiveZetaPrime p L
    ((sigmaOfUnit (p := p) L a) • distinguishedPrimeAboveP p L)

end GaloisAction

end BernoulliRegular
