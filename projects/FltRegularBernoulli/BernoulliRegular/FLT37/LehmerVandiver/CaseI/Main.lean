import BernoulliRegular.HilbertClassField
import BernoulliRegular.TotallyRealSubfield.Basic
import Mathlib.NumberTheory.NumberField.CMField

/-!
# LV008 case I bridge structure

Vandiver 1934 Theorem 1: if `p ∤ h⁺(K)`, then case I of FLT for `p` holds.

The proof (paraphrased): for FLT case I `a^p + b^p = c^p` with `p ∤ abc`,
the cyclotomic factorisation `(a + ζ^k b)` produces ideals `I_k` with
`p`-torsion classes. Under `p ∤ h⁺`, every `p`-torsion class lies in
`Cl(K)⁻` (the minus part), and Stickelberger annihilates `Cl(K)⁻[p]`.
The remaining standard Kummer chain produces a contradiction.

This file packages the full case I implication as a parametric bridge
`CaseIBridge`. **Stickelberger is hidden inside the proof, not exposed
at the bundle boundary** — at the structural top, only `¬ p ∣ h⁺` is
needed. (The original "case I needs StickelbergerKBridge as separate
input" framing was misleading.)

Once filled by Vandiver 1934 / LV008's content (cyclotomic factorisation
+ Stickelberger principalisation + Kummer descent), LV011 absorbs this
to make the case I hypothesis unconditional.
-/

@[expose] public section

noncomputable section

open NumberField

namespace BernoulliRegular

universe u

variable (p : ℕ) [Fact p.Prime]
variable (K : Type u) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]

/-- **LV008 case I bridge (Vandiver 1934)**: under `¬ p ∣ h⁺(K)`, no
case I FLT solution exists for `p`.

The bridge field captures the case-I content: for any FLT case-I scenario
(coprime integers `a`, `b`, `c` with `p ∤ abc` and `a^p + b^p = c^p`),
no such solution exists.

Stickelberger annihilation of `Cl(K)⁻[p]` is used in the proof but is
NOT a separate top-level input — it's classical and provable from
existing infrastructure.

Once filled by Vandiver 1934's content, LV011 absorbs this. -/
structure CaseIBridge where
  /-- Vandiver 1934 case I: under `¬ p ∣ hPlus K`, no FLT case I
  solution exists (in integer form). -/
  no_caseI_solution :
    ¬ (p : ℕ) ∣ hPlus K →
      ∀ ⦃a b c : ℤ⦄,
        ¬ (p : ℤ) ∣ a * b * c → a ^ p + b ^ p ≠ c ^ p

end BernoulliRegular

end
