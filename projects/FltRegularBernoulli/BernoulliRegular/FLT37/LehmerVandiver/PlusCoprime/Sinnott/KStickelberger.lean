import Mathlib.NumberTheory.NumberField.Basic

import BernoulliRegular.ClassGroupExtension
import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.ClassGroupMinus

/-!
# K-side Stickelberger annihilators

This file packages the `K`-side Stickelberger annihilator conditions used to
trivialize the minus part of the class group in the Lehmer--Vandiver route.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

namespace FLT37

namespace Sinnott

variable (p : ℕ) [hp : Fact p.Prime]
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- The `K`-side Stickelberger annihilator condition on `Cl(K)⁻`. -/
def KSideStickelbergerAnnihilator : Prop :=
  ∀ c ∈ classGroupMinus p K,
    ∃ (θ_K : ClassGroup (𝓞 K)),
      θ_K * c = 1 ∧
      θ_K = 1

/-- The minus eigenspace of the `K`-side class group is trivial. -/
def KSideMinusTrivial : Prop :=
  ∀ c ∈ classGroupMinus p K, c = 1

set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- The Stickelberger annihilator condition is equivalent to minus-part triviality. -/
theorem kSideStickelbergerAnnihilator_iff_minusTrivial :
    KSideStickelbergerAnnihilator p K ↔ KSideMinusTrivial p K := by
  constructor
  · intro h c hc
    obtain ⟨θ, hθ_mul, hθ_one⟩ := h c hc
    simpa [hθ_one] using hθ_mul
  · intro h c hc
    exact ⟨1, by simpa using h c hc, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Only the `p`-torsion of `Cl(K)⁻` is annihilated. -/
def KSidePtorsionMinusTrivial : Prop :=
  ∀ c ∈ classGroupMinus p K, c ^ p = 1 → c = 1

end Sinnott

end FLT37

end BernoulliRegular

end
