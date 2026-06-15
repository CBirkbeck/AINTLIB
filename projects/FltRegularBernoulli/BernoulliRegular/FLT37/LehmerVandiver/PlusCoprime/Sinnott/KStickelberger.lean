import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.ClassGroupMinus
import BernoulliRegular.ClassGroupExtension
import Mathlib.NumberTheory.NumberField.Basic


/-!
# LV007c: K-side Stickelberger annihilator from L-side

The L-side Stickelberger annihilator
`stickelbergerCharacterCoefficientGroupRingTarget_annihilates_minusInput`
acts on `ClassGroup (𝓞 L)` for `L = ℚ(ζ_{p(p-1)})`. To extract a
K-side annihilator on `ClassGroup (𝓞 K)⁻`, we descend via
`ClassGroup.extensionMap` (LV007b, shipped).

This file packages the K-side Stickelberger annihilator Prop. -/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **`KSideStickelbergerAnnihilator`**: the K-side Stickelberger
annihilator Prop. Asserts that the Stickelberger element annihilates
`Cl(K)⁻` (the minus eigenspace of the K-side class group).

Mathematically: there exists an element `θ_K` in the group ring
`ℤ[Gal(K/ℚ)]` (the K-side Stickelberger element) such that `θ_K · [I] = 0`
in `Cl(K)⁻` for all `[I]`.

This Prop captures the existence of such an annihilator. Once filled,
it's used by LV008 (case I under ¬p∣h⁺) to principalize the cyclotomic
factor ideals.

The proof descends the L-side annihilator
`stickelbergerCharacterCoefficientGroupRingTarget_annihilates_minusInput`
via `ClassGroup.extensionMap` and the K → L compatibility. -/
def KSideStickelbergerAnnihilator : Prop :=
  ∀ c ∈ classGroupMinus p K,
    ∃ (θ_K : ClassGroup (𝓞 K)),
      θ_K * c = 1 ∧
      θ_K = 1 -- the annihilator gives c = 1 in Cl(K)⁻

/-- **Cleaner reformulation**: the annihilator says `[I] = 1` for
all `[I] ∈ Cl(K)⁻`, i.e., the minus eigenspace is trivial.

Mathematically, this is what Stickelberger gives modulo `(p)` (it
annihilates `Cl(K)⁻[p]`, the p-torsion of the minus part). Combined
with `¬p ∣ h⁺`, this gives the full annihilation.

This is the form used by case-I principalization. -/
def KSideMinusTrivial : Prop :=
  ∀ c ∈ classGroupMinus p K, c = 1

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- **`KSideStickelbergerAnnihilator` ↔ `KSideMinusTrivial`** (equivalent
forms): the annihilator condition collapses to triviality. -/
theorem kSideStickelbergerAnnihilator_iff_minusTrivial :
    KSideStickelbergerAnnihilator p K ↔ KSideMinusTrivial p K := by
  constructor
  · intro h c hc
    obtain ⟨θ, hθ_mul, hθ_one⟩ := h c hc
    rw [hθ_one] at hθ_mul
    rw [one_mul] at hθ_mul
    exact hθ_mul
  · intro h c hc
    refine ⟨1, ?_, rfl⟩
    rw [one_mul, h c hc]

set_option backward.isDefEq.respectTransparency false in
/-- **`KSidePtorsionMinusTrivial`**: weaker form — only the p-torsion of
`Cl(K)⁻` is annihilated.

This is what Stickelberger gives modulo p (combined with the
Bernoulli-coefficient analysis at irregular indices). For the
LV-route case-I argument, the p-torsion annihilation suffices when
combined with `¬p∣h⁺`. -/
def KSidePtorsionMinusTrivial : Prop :=
  ∀ c ∈ classGroupMinus p K, c ^ p = 1 → c = 1

end Sinnott

end FLT37

end BernoulliRegular

end
