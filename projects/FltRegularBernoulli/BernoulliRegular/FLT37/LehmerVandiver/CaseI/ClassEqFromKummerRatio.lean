import BernoulliRegular.FLT37.LehmerVandiver.CaseI.IdealConjugate

/-!
# LV010-class-eq-1: From `𝔞 · σ𝔞^{-1} = (β)`, derive `[σ𝔞] = [𝔞]`

Stage 4 of the Vandiver class-equality discharge. Given the
**fractional-ideal-level** identity `𝔞 · σ𝔞^{-1} = (β)` (from the
Kummer ratio + p-th-root cancellation), the class-group equality
`[σ𝔞] = [𝔞]` follows trivially: principal fractional ideals have
trivial class.

This decouples the **class-group bookkeeping** (this file, axiom-clean)
from the **fractional-ideal cancellation step** (`(X)^p = (Y)^p ⟹ X = Y`,
LV010-class-eq-1b — uses Dedekind-UFD structure on FractionalIdeal),
which is the substantive piece.

## References

* Vandiver, Bull. AMS 40 (1934), Theorem 1.
* Washington, *Introduction to Cyclotomic Fields*, §9.1, Theorem 9.3.
-/

@[expose] public section

noncomputable section

open NumberField NumberField.IsCMField IsCyclotomicExtension Ideal BernoulliRegular

namespace BernoulliRegular

namespace FLT37

namespace LehmerVandiver

namespace CaseI

/-- A ring iso preserves non-zero-ideal-ness. Inline of
`PrimaryDescent.map_ne_bot_iff_complexConj_local` to avoid the import (which
currently transitively pulls in upstream changes in `Primary.lean`). -/
private theorem map_ne_bot_iff_complexConj_local
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    [IsCMField K] (𝔞 : Ideal (𝓞 K)) :
    𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom ≠ ⊥ ↔ 𝔞 ≠ ⊥ :=
  not_congr <| Ideal.map_eq_bot_iff_of_injective
    (f := (ringOfIntegersComplexConj K).toRingEquiv.toRingHom)
    (ringOfIntegersComplexConj K).injective

set_option backward.isDefEq.respectTransparency false in
/-- **Class equality from principal-fractional-ideal-level identity.**
If the (multiplicative) ratio of ideal classes `[𝔞]/[σ𝔞]` equals `1`
in `Cl(K)`, then `[σ𝔞] = [𝔞]`. Trivial group identity, packaged for
downstream consumption.

The hypothesis is the substantive content (fractional-ideal-level
identity from Kummer's lemma); this file is the structural
class-group conclusion. -/
theorem caseI_class_eq_complexConj_of_class_ratio_eq_one
    {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] [IsCMField K]
    {𝔞 : Ideal (𝓞 K)} (h𝔞_nz : 𝔞 ≠ ⊥)
    (h_ratio :
      ClassGroup.mk0
          (⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩
            : nonZeroDivisors (Ideal (𝓞 K))) /
      ClassGroup.mk0
          (⟨𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
            mem_nonZeroDivisors_iff_ne_zero.mpr
              ((map_ne_bot_iff_complexConj_local (p := p) 𝔞).mpr h𝔞_nz)⟩
            : nonZeroDivisors (Ideal (𝓞 K))) = 1) :
    ClassGroup.mk0
        (⟨𝔞.map (ringOfIntegersComplexConj K).toRingEquiv.toRingHom,
          mem_nonZeroDivisors_iff_ne_zero.mpr
            ((map_ne_bot_iff_complexConj_local (p := p) 𝔞).mpr h𝔞_nz)⟩
          : nonZeroDivisors (Ideal (𝓞 K))) =
      ClassGroup.mk0
        (⟨𝔞, mem_nonZeroDivisors_iff_ne_zero.mpr h𝔞_nz⟩
          : nonZeroDivisors (Ideal (𝓞 K))) := by
  -- In any group, a / b = 1 ↔ a = b. ClassGroup is a (commutative) group.
  exact (div_eq_one.mp h_ratio).symm

end CaseI

end LehmerVandiver

end FLT37

end BernoulliRegular

end
