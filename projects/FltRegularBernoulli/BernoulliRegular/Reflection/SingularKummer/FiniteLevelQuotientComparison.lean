module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelTorsionReduction
public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelProjectionBridge

/-!
# Singular Kummer: finite-level projection and the elementary quotient

This file proves the quotient half of the exact finite-level bridge.  If the
coefficients of the exact finite-level idempotent reduce modulo `p` to the
usual `i`-th character-projection coefficients, then the image of the exact
finite-level projection subgroup contains the mod-`p` component `V_i`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelQuotientComparison

open ElementaryQuotientComponent

variable {p m : ℕ} [NeZero p] [NeZero m]
variable {A : Type*} [AddCommGroup A] [Module (ZMod m) A]

/-- Natural-number scalar multiplication on `A / pA` agrees with scalar
multiplication by its class in `ZMod p`. -/
theorem nsmul_elementaryQuotient_eq_zmod_smul
    (n : ℕ) (x : ElementaryQuotient A p) :
    n • x = (n : ZMod p) • x := by
  rw [zmod_smul_eq_val_nsmul, ZMod.val_natCast]
  have hpx : p • x = 0 := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x]
    simp
  exact nsmul_eq_mod_nsmul n hpx

/-- Scalar multiplication before quotienting by `pA` depends only on the
coefficient modulo `p`. -/
theorem quotientMap_zmod_smul_eq_of_castHom_eq
    (hm : p ∣ m) (c : ZMod m) (a : ZMod p) (x : A)
    (hc : ZMod.castHom hm (ZMod p) c = a) :
    quotientMap A p (c • x) = a • quotientMap A p x := by
  have hcval : (c.val : ZMod p) = a := by
    have hcast :
        ZMod.castHom hm (ZMod p) (c.val : ZMod m) =
          ZMod.castHom hm (ZMod p) c := by
      rw [ZMod.natCast_zmod_val c]
    simpa [ZMod.castHom_apply] using hcast.trans hc
  calc
    quotientMap A p (c • x) = quotientMap A p (c.val • x) := by
      have hcx : c • x = c.val • x := by
        calc
          c • x = (c.val : ZMod m) • x := by
            rw [ZMod.natCast_zmod_val c]
          _ = c.val • x := Nat.cast_smul_eq_nsmul (ZMod m) c.val x
      rw [hcx]
    _ = c.val • quotientMap A p x := by
      simp [map_nsmul]
    _ = (c.val : ZMod p) • quotientMap A p x :=
      nsmul_elementaryQuotient_eq_zmod_smul
        (p := p) c.val (quotientMap A p x)
    _ = a • quotientMap A p x := by
      rw [hcval]

/-- The exact finite-level projection descends to the usual mod-`p`
projection on `A / pA`, provided its coefficients reduce to the usual
character-projection coefficients. -/
theorem quotientMap_finiteLevelProjection
    (hm : p ∣ m) (i : ℕ)
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (chi : CharacterProjection.Delta p →* (ZMod m)ˣ)
    (hcoeff : ∀ d : CharacterProjection.Delta p,
      ZMod.castHom hm (ZMod p)
          (FiniteLevelIdempotent.coefficient (m := m) chi d) =
        CharacterProjection.characterProjectionCoefficient (p := p) i d)
    (x : A) :
    quotientMap A p
        (FiniteLevelAdditiveProjection.projection (m := m) rho chi x) =
      elementaryProjection (p := p) i rho (quotientMap A p x) := by
  calc
    quotientMap A p
        (FiniteLevelAdditiveProjection.projection (m := m) rho chi x)
        = ∑ d : CharacterProjection.Delta p,
            quotientMap A p
              (FiniteLevelIdempotent.coefficient (m := m) chi d • rho d x) := by
          simp [FiniteLevelAdditiveProjection.projection,
            FiniteLevelIdempotent.projection]
    _ = ∑ d : CharacterProjection.Delta p,
          CharacterProjection.characterProjectionCoefficient (p := p) i d •
            quotientMap A p (rho d x) := by
          apply Finset.sum_congr rfl
          intro d _hd
          exact quotientMap_zmod_smul_eq_of_castHom_eq
            (p := p) (m := m) hm
            (FiniteLevelIdempotent.coefficient (m := m) chi d)
            (CharacterProjection.characterProjectionCoefficient (p := p) i d)
            (rho d x) (hcoeff d)
    _ = elementaryProjection (p := p) i rho (quotientMap A p x) := by
          simp [elementaryProjection, CharacterProjection.characterProjection,
            CharacterProjection.projection]

/-- The exact finite-level projection subgroup maps onto the mod-`p`
component `V_i`. -/
theorem elementaryComponent_le_finiteLevelComponent_image
    (hm : p ∣ m) (i : ℕ)
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (chi : CharacterProjection.Delta p →* (ZMod m)ˣ)
    (hcoeff : ∀ d : CharacterProjection.Delta p,
      ZMod.castHom hm (ZMod p)
          (FiniteLevelIdempotent.coefficient (m := m) chi d) =
        CharacterProjection.characterProjectionCoefficient (p := p) i d) :
    elementaryComponent (p := p) i rho ≤
      LinearMap.range
        (FiniteLevelProjectionBridge.subgroupElementaryQuotientLinearMap
          (p := p)
          (FiniteLevelAdditiveProjection.componentSubgroup (m := m) rho chi)) := by
  rintro y ⟨v, rfl⟩
  obtain ⟨x, rfl⟩ := quotientMap_surjective (A := A) p v
  refine ⟨QuotientAddGroup.mk
      (⟨FiniteLevelAdditiveProjection.projection (m := m) rho chi x,
        ⟨x, rfl⟩⟩ :
        FiniteLevelAdditiveProjection.componentSubgroup (m := m) rho chi), ?_⟩
  change quotientMap A p
      (FiniteLevelAdditiveProjection.projection (m := m) rho chi x) =
    elementaryProjection (p := p) i rho x
  exact quotientMap_finiteLevelProjection (p := p) (m := m)
    hm i rho chi hcoeff x

end FiniteLevelQuotientComparison

end SingularKummer
end Reflection
end BernoulliRegular

end

end
