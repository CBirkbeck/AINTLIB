/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.BigWindows

/-!
# The interval-trace basis of `Y` (D-ii-1)

The loci `κ(v) ∈ [1/q₁, 1/q₂]` for rational radius-exponent pairs — the
index geometry of the `BIQ`-valued structure presheaf of the curve:

* `FarguesFontaine.intervalTrace` : the trace, in `KGE`/`KLE` form;
* `FarguesFontaine.bigWindow_eq_intervalTrace` : the Big windows are the
  `(1/p^n, 1/p^{n+1})`-traces;
* `FarguesFontaine.intervalTrace_mono` : traces are monotone in the interval.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)

/-- **The trace of a radius-exponent interval on `Y`**: the locus
`κ(v) ∈ [1/q₁, 1/q₂]` for a decreasing exponent pair `q₂ < q₁` (radius
exponents; the `BIQ q₁ q₂`-indexing convention). -/
def intervalTrace (q₁ q₂ : ℚ) : Set (Spv (Ainf p F)) :=
  {v ∈ Y p F ϖ | KGE p F ϖ (1 / q₁) v ∧ KLE p F ϖ (1 / q₂) v}

/-- The Big windows are interval traces. -/
theorem bigWindow_eq_intervalTrace (n : ℤ) :
    bigWindow p F ϖ n
      = intervalTrace p F ϖ (1 / (p : ℚ) ^ n) (1 / (p : ℚ) ^ (n + 1)) := by
  ext v
  show (v ∈ Y p F ϖ ∧ KGE p F ϖ ((p : ℚ) ^ n) v ∧ KLE p F ϖ ((p : ℚ) ^ (n + 1)) v)
    ↔ (v ∈ Y p F ϖ ∧ KGE p F ϖ (1 / (1 / (p : ℚ) ^ n)) v
        ∧ KLE p F ϖ (1 / (1 / (p : ℚ) ^ (n + 1))) v)
  rw [one_div_one_div, one_div_one_div]

/-- Interval traces are monotone: a smaller exponent interval has a smaller
trace. -/
theorem intervalTrace_mono {q₁ q₂ r₁ r₂ : ℚ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h₁ : r₁ ≤ q₁) (h₂ : q₂ ≤ r₂) :
    intervalTrace p F ϖ r₁ r₂ ⊆ intervalTrace p F ϖ q₁ q₂ := by
  rintro v ⟨hY, hge, hle⟩
  refine ⟨hY, ?_, ?_⟩
  · refine KGE_mono p F ϖ hY ?_ ?_ hge
    · positivity
    · exact one_div_le_one_div_of_le hr₁ h₁
  · refine KLE_mono p F ϖ hY ?_ ?_ hle
    · positivity
    · exact one_div_le_one_div_of_le hq₂ h₂

end FarguesFontaine

end
