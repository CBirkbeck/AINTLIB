module

public import BernoulliRegular.Reflection.SingularKummer.FiniteGroupComparison
public import BernoulliRegular.Reflection.SingularKummer.SingularClassChoice

/-!
# Singular Kummer: finite comparison on projected components

The finite-group comparison between `A / nA` and `A[n]` applies to any finite
additive subgroup, in particular to the range of an additive endomorphism or a
linear projection.  This is the component-level form needed before connecting
the nontriviality of `V_i` with the projected target component of `A[p]`.
-/

@[expose] public section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace ProjectedFiniteComparison

variable {A : Type*} [AddCommGroup A] [Finite A]

/-- The finite comparison applied to the range of an additive endomorphism. -/
theorem endomorphismRange_elementaryQuotient_nontrivial_iff_torsion_nontrivial
    (e : A →+ A) (n : ℕ) :
    Nontrivial (elementaryQuotient e.range n) ↔
      Nontrivial (torsionBySubgroup e.range n) :=
  elementaryQuotient_nontrivial_iff_torsionBySubgroup_nontrivial
    (A := e.range) n

/-- Direction used in the singular-Kummer argument: a nontrivial elementary quotient of a projected
finite component gives nontrivial torsion in that same projected component. -/
theorem torsion_nontrivial_of_endomorphismRange_elementaryQuotient_nontrivial
    (e : A →+ A) {n : ℕ} :
    Nontrivial (elementaryQuotient e.range n) →
      Nontrivial (torsionBySubgroup e.range n) :=
  (endomorphismRange_elementaryQuotient_nontrivial_iff_torsion_nontrivial
    (A := A) e n).1

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [Finite M]

/-- The same comparison for the range of a linear endomorphism. -/
theorem linearRange_elementaryQuotient_nontrivial_iff_torsion_nontrivial
    (e : M →ₗ[R] M) (n : ℕ) :
    Nontrivial (elementaryQuotient (LinearMap.range e) n) ↔
      Nontrivial (torsionBySubgroup (LinearMap.range e) n) :=
  elementaryQuotient_nontrivial_iff_torsionBySubgroup_nontrivial
    (A := LinearMap.range e) n

/-- Direction used in the singular-Kummer argument for a linear projected component. -/
theorem torsion_nontrivial_of_linearRange_elementaryQuotient_nontrivial
    (e : M →ₗ[R] M) {n : ℕ} :
    Nontrivial (elementaryQuotient (LinearMap.range e) n) →
      Nontrivial (torsionBySubgroup (LinearMap.range e) n) :=
  (linearRange_elementaryQuotient_nontrivial_iff_torsion_nontrivial
    (M := M) e n).1

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

/-- In a `ZMod p`-module, every element is killed by `p`. -/
theorem torsionBySubgroup_eq_top_of_zmodModule :
    torsionBySubgroup V p = ⊤ := by
  ext x
  simp [torsionBySubgroup, ZModModule.char_nsmul_eq_zero]

variable {W : Type*} [AddCommGroup W] [Module (ZMod p) W]

/-- The `p`-torsion subgroup of a projected `ZMod p`-linear range is the whole
range. -/
theorem linearRange_torsionBySubgroup_eq_top_zmod
    (e : W →ₗ[ZMod p] W) :
    torsionBySubgroup (LinearMap.range e) p = ⊤ :=
  torsionBySubgroup_eq_top_of_zmodModule
    (p := p) (V := LinearMap.range e)

/-- If the `p`-torsion of a projected `ZMod p`-linear range is nontrivial, then
the projected range itself is nontrivial. -/
theorem linearRange_nontrivial_of_torsion_nontrivial_zmod
    (e : W →ₗ[ZMod p] W) :
    Nontrivial (torsionBySubgroup (LinearMap.range e) p) →
      Nontrivial (LinearMap.range e) := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : torsionBySubgroup (LinearMap.range e) p)
  exact ⟨⟨x.1, 0, fun hzero => hx (Subtype.ext hzero)⟩⟩

/-- Conversely, a nontrivial projected range in a `ZMod p`-module has
nontrivial `p`-torsion. -/
theorem torsion_nontrivial_of_linearRange_nontrivial_zmod
    (e : W →ₗ[ZMod p] W) :
    Nontrivial (LinearMap.range e) →
      Nontrivial (torsionBySubgroup (LinearMap.range e) p) := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : LinearMap.range e)
  let xt : torsionBySubgroup (LinearMap.range e) p :=
    ⟨x, by
      change p • x = 0
      exact ZModModule.char_nsmul_eq_zero (n := p) x⟩
  exact ⟨⟨xt, 0, fun hzero => hx (congrArg Subtype.val hzero)⟩⟩

variable [Finite W]

/-- The bridge used for the singular-Kummer argument: a nontrivial elementary
quotient of a projected `ZMod p` component forces the projected component
itself to be nontrivial. -/
theorem linearRange_ne_bot_of_elementaryQuotient_nontrivial_zmod
    (e : W →ₗ[ZMod p] W)
    (hV : Nontrivial (elementaryQuotient (LinearMap.range e) p)) :
    LinearMap.range e ≠ ⊥ := by
  have htorsion :
      Nontrivial (torsionBySubgroup (LinearMap.range e) p) :=
    torsion_nontrivial_of_linearRange_elementaryQuotient_nontrivial
      (R := ZMod p) e hV
  exact (Submodule.nontrivial_iff_ne_bot).1
    (linearRange_nontrivial_of_torsion_nontrivial_zmod e htorsion)

variable [NeZero p]

/-- Character-projection form of the finite comparison: if the elementary
quotient of a projected component is nontrivial, then the projected component
itself is nontrivial. -/
theorem characterProjection_range_ne_bot_of_elementaryQuotient_nontrivial_zmod
    (i : ℕ) (ρ : CharacterProjection.Delta p →* W ≃ₗ[ZMod p] W)
    (hV :
      Nontrivial
        (elementaryQuotient
          (LinearMap.range
            (CharacterProjection.characterProjection (p := p) i ρ)) p)) :
    LinearMap.range
        (CharacterProjection.characterProjection (p := p) i ρ) ≠ ⊥ :=
  linearRange_ne_bot_of_elementaryQuotient_nontrivial_zmod
    (p := p) (CharacterProjection.characterProjection (p := p) i ρ) hV

/-- The same statement as a `Nontrivial` instance for the projected component. -/
theorem characterProjection_range_nontrivial_of_elementaryQuotient_nontrivial_zmod
    (i : ℕ) (ρ : CharacterProjection.Delta p →* W ≃ₗ[ZMod p] W)
    (hV :
      Nontrivial
        (elementaryQuotient
          (LinearMap.range
            (CharacterProjection.characterProjection (p := p) i ρ)) p)) :
    Nontrivial
      (LinearMap.range
        (CharacterProjection.characterProjection (p := p) i ρ)) :=
  (Submodule.nontrivial_iff_ne_bot).2
    (characterProjection_range_ne_bot_of_elementaryQuotient_nontrivial_zmod
      (p := p) i ρ hV)

end ProjectedFiniteComparison

end SingularKummer
end Reflection
end BernoulliRegular

end
