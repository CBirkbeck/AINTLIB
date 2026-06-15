import BernoulliRegular.UnitQuotient.PadicTensor
import BernoulliRegular.Thaine.PollaczekUnitPlusGaloisAction

/-!
# T-Q1-EIGEN: Pollaczek's image as Padic eigenspace generator (FLT37)

For the FLT37 rank-one Pollaczek specialisation, this file ships the
Padic-side analog of the K-side mod-p eigenspace generation results.

* PU's image in `CyclotomicUnitFreePartPadic K` (via the natural
  inclusion) is non-zero (transfer from mod-p side).

## References

* `flt37_pollaczekUnit_class_in_modp_freepart_ne_zero` (this project,
  `Thaine/PollaczekUnitPlusGaloisAction.lean`).
* Reviewer guidance, 2026-05-07 (Q1 eigenspace iso direct construction).
-/

@[expose] public section

noncomputable section

open NumberField TensorProduct

namespace BernoulliRegular

namespace FLT37

set_option linter.unusedSectionVars false

/-- **PU's image in `CyclotomicUnitFreePartPadic` is non-zero (FLT37)**.

The reduction map is a homomorphism, so any element with non-zero image
mod-p must itself be non-zero. -/
theorem flt37_pollaczekUnit_class_in_padic_ne_zero
    [Fact (Nat.Prime 37)]
    [IsCyclotomicExtension {37} ℚ (CyclotomicField 37 ℚ)]
    [NumberField.IsCMField (CyclotomicField 37 ℚ)] :
    cyclotomicUnitFreePartToPadic (p := 37) (CyclotomicField 37 ℚ)
        (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
          (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32))) ≠ 0 := by
  intro h_zero
  -- If 1 ⊗ v = 0 in PadicFreePart, then reduce(1 ⊗ v) = 0 in FreePartModP.
  -- But reduce(1 ⊗ v) = [v] = mod-p class, which is non-zero by FLT37 cert.
  apply flt37_pollaczekUnit_class_in_modp_freepart_ne_zero
  show cyclotomicUnitToFreePartModPAdd (p := 37) (CyclotomicField 37 ℚ)
      (Additive.ofMul (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)) = 0
  rw [cyclotomicUnitToFreePartModPAdd_apply]
  -- mod-p class = reduce ∘ inclusion (via cyclotomicUnitFreePartPadicReduceModP_one_tmul).
  rw [← cyclotomicUnitFreePartPadicReduceModP_one_tmul (p := 37) (CyclotomicField 37 ℚ)
    (Additive.ofMul (cyclotomicUnitFreeClass (CyclotomicField 37 ℚ)
      (pollaczekUnit 37 (CyclotomicField 37 ℚ) 32)))]
  -- Now apply h_zero: toPadic v = 0.
  rw [h_zero, map_zero]

end FLT37

end BernoulliRegular

end
