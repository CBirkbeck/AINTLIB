module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelAdditiveProjection
public import BernoulliRegular.Reflection.SingularKummer.TorsionComponent

/-!
# Singular Kummer: reducing finite-level components to `p`-torsion components

This file records the passage from an exact finite-level character relation to
the mod-`p` character component on `A[p]`.  The point is elementary: on an
element killed by `p`, scalar multiplication by an element of `ZMod m` only
depends on its image in `ZMod p`.
-/

@[expose] public section

noncomputable section

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace FiniteLevelTorsionReduction

variable {p m : ℕ} [NeZero p] [NeZero m]
variable {A : Type*} [AddCommGroup A] [Module (ZMod m) A]

/-- Natural-number scalar multiplication on a `p`-torsion element agrees with
scalar multiplication by its class in `ZMod p`. -/
theorem nsmul_ptorsion_eq_zmod_smul
    (n : ℕ) (x : TorsionComponent.PTorsion A p) :
    n • (x : A) = (((n : ZMod p) • x : TorsionComponent.PTorsion A p) : A) := by
  rw [TorsionComponent.coe_zmod_smul, ZMod.val_natCast]
  exact nsmul_eq_mod_nsmul n x.2

/-- Scalar multiplication by an element of `ZMod m` on a `p`-torsion element
depends only on its image in `ZMod p`. -/
theorem zmod_smul_ptorsion_eq_of_castHom_eq
    (hm : p ∣ m) (c : ZMod m) (a : ZMod p)
    (x : TorsionComponent.PTorsion A p)
    (hc : ZMod.castHom hm (ZMod p) c = a) :
    c • (x : A) = ((a • x : TorsionComponent.PTorsion A p) : A) := by
  have hcval : (c.val : ZMod p) = a := by
    have hcast :
        ZMod.castHom hm (ZMod p) (c.val : ZMod m) =
          ZMod.castHom hm (ZMod p) c := by
      rw [ZMod.natCast_zmod_val c]
    simpa [ZMod.castHom_apply] using hcast.trans hc
  calc
    c • (x : A) = c.val • (x : A) := by
      calc
        c • (x : A) = (c.val : ZMod m) • (x : A) := by
          rw [ZMod.natCast_zmod_val c]
        _ = c.val • (x : A) :=
          Nat.cast_smul_eq_nsmul (ZMod m) c.val (x : A)
    _ = (((c.val : ZMod p) • x : TorsionComponent.PTorsion A p) : A) :=
      nsmul_ptorsion_eq_zmod_smul (p := p) c.val x
    _ = ((a • x : TorsionComponent.PTorsion A p) : A) := by
      rw [hcval]

/-- If the finite-level character reduces to the mod-`p` character
`a ↦ a^i`, then every `p`-torsion element in the exact finite-level component
lies in the existing `A[p]_i` component. -/
theorem mem_torsionComponent_of_mem_finiteLevelComponent
    (hcard : IsUnit (Fintype.card (CharacterProjection.Delta p) : ZMod p))
    (hm : p ∣ m) (i : ℕ)
    (rho : CharacterProjection.Delta p →* Multiplicative (A ≃+ A))
    (chi : CharacterProjection.Delta p →* (ZMod m)ˣ)
    (hchi : ∀ d : CharacterProjection.Delta p,
      ZMod.castHom hm (ZMod p) (chi d : ZMod m) = ((d : ZMod p) ^ i))
    {x : TorsionComponent.PTorsion A p}
    (hx : (x : A) ∈
      FiniteLevelAdditiveProjection.componentSubgroup (m := m) rho chi) :
    x ∈ TorsionComponent.torsionComponent (p := p) i rho := by
  refine CharacterProjection.mem_characterProjection_range_of_forall_apply_eq_smul
    (p := p) hcard i (TorsionComponent.torsionAction (p := p) rho) ?_
  intro d
  apply Subtype.ext
  calc
    ((TorsionComponent.torsionAction (p := p) rho d x :
        TorsionComponent.PTorsion A p) : A)
        = Multiplicative.toAdd (rho d) (x : A) := by
          simp
    _ = (chi d : ZMod m) • (x : A) :=
          FiniteLevelAdditiveProjection.apply_eq_character_smul_of_mem_component
            (m := m) rho chi d hx
    _ = ((((d : ZMod p) ^ i) • x :
        TorsionComponent.PTorsion A p) : A) :=
          zmod_smul_ptorsion_eq_of_castHom_eq
            (p := p) (m := m) hm (chi d : ZMod m) ((d : ZMod p) ^ i) x
            (hchi d)

end FiniteLevelTorsionReduction

end SingularKummer
end Reflection
end BernoulliRegular

end

end
