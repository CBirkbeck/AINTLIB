module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelQuotientComparison

/-!
# Singular Kummer: final finite-level bridge

This file assembles the exact finite-level subgroup argument.  The exact
projection subgroup covers the quotient component `V_i`, and its `p`-torsion
lies in the matching `A[p]_i` component.  Therefore nontriviality of `V_i`
implies nontriviality of `A[p]_i`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelFinalBridge

open ElementaryQuotientComponent
open TorsionComponent

variable {p m : ℕ} [NeZero p] [NeZero m]
variable {A : Type*} [AddCommGroup A] [Module (ZMod m) A] [Finite A]

/-- The final finite-level comparison: an exact lifted character idempotent
whose coefficients and character reduce to the expected mod-`p` data converts
nontriviality of `V_i` into nontriviality of the corresponding `A[p]_i`
component. -/
theorem torsionComponentNontrivial_of_finiteLevelCharacter
    (hcard : IsUnit (Fintype.card (CharacterProjection.Delta p) : ZMod p))
    (hm : p ∣ m) (i : ℕ)
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (chi : CharacterProjection.Delta p →* (ZMod m)ˣ)
    (hcoeff : ∀ d : CharacterProjection.Delta p,
      ZMod.castHom hm (ZMod p)
          (FiniteLevelIdempotent.coefficient (m := m) chi d) =
        CharacterProjection.characterProjectionCoefficient (p := p) i d)
    (hchi : ∀ d : CharacterProjection.Delta p,
      ZMod.castHom hm (ZMod p) (chi d : ZMod m) = ((d : ZMod p) ^ i))
    (hV : ElementaryComponentNontrivial (p := p) i rho) :
    TorsionComponentNontrivial (p := p) i rho := by
  let B : AddSubgroup A :=
    FiniteLevelAdditiveProjection.componentSubgroup (m := m) rho chi
  exact FiniteLevelProjectionBridge.torsionComponentNontrivial_of_finiteLevelSubgroup
    (p := p) i rho B hV
    (FiniteLevelQuotientComparison.elementaryComponent_le_finiteLevelComponent_image
      (p := p) (m := m) hm i rho chi hcoeff)
    (fun x => by
      exact FiniteLevelTorsionReduction.mem_torsionComponent_of_mem_finiteLevelComponent
        (p := p) (m := m) hcard hm i rho chi hchi
        (x := ProjectedSubgroupComparison.subgroupTorsionToTorsion B p x)
        (by
          change (((x : torsionBySubgroup B p).1 : B) : A) ∈ B
          exact ((x : torsionBySubgroup B p).1 : B).2))

end FiniteLevelFinalBridge

end SingularKummer
end Reflection
end BernoulliRegular

end

end
