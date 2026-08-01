/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetScottishBook
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# `ℚ_p` is a finite-jet base — the mixed-characteristic case

The [FJP] construction was originally formalized only over `K = F((t))`, i.e. in equal
characteristic. Having abstracted the base to `IsFJPBase` (`FJP/FJPBase.lean`), the
mixed-characteristic case costs one instance: `ℚ_p` is a complete ultrametric
nonarchimedean field and `p` is a pseudouniformizer.

Consequently **everything in the `IsFJPBase` half of the development runs over `ℚ_p`**: the
finite-jet algebra `𝓐` over `ℚ_p` is a complete uniform nonnoetherian Tate domain, the
chart `𝓐⟨W/ϖ⟩ ≅ 𝓑` and the `Q²`-collapse hold, and hence so do the Scottish Book Problem 24
and Problem 28 witnesses (`FJP/FiniteJetScottishBook.lean`).

What does **not** transfer is sheafiness: that needs `IsFJPNoetherianBase`, i.e. that the
Gauss unit ball `ℤ_p⟨T₁,…,T_k⟩` is noetherian. That is true, but proving it needs Stacks
00MA (the `ϖ`-adic completion of a noetherian ring is noetherian), which is a mathlib gap —
the repo's `AdicCompletion.isNoetherianRing` is `sorry`-backed, so it is deliberately *not*
used here. The equal-characteristic instance in `FJP/FJPBaseLaurent.lean` gets it instead
from an elementary transpose argument that only exists because `F[[t]]` is a power series
ring.
-/

namespace FiniteJet

variable (p : ℕ) [hp : Fact p.Prime]

/-- **`ℚ_p` is a finite-jet base**, with pseudouniformizer `p`. -/
noncomputable instance instIsFJPBasePadic : IsFJPBase ℚ_[p] where
  pseudoUniformizer := (p : ℚ_[p])
  pseudoUniformizer_ne_zero := by
    simpa using (Nat.cast_ne_zero (R := ℚ_[p])).mpr hp.out.ne_zero
  norm_pseudoUniformizer_lt_one := Padic.norm_p_lt_one

@[simp] theorem ϖ_padic : ϖ ℚ_[p] = (p : ℚ_[p]) := rfl

/-- The finite-jet algebra over `ℚ_p` is a uniform, nonnoetherian Tate domain — the
mixed-characteristic analogue of [FJP] Theorem 1.3, minus sheafiness (which needs the
noetherian input `IsFJPNoetherianBase`, unavailable here pending Stacks 00MA). -/
theorem finiteJet_padic_quality :
    IsTateRing (JetA ℚ_[p]) ∧
    TopologicalRing.IsUniform (JetA ℚ_[p]) ∧
    IsDomain (JetA ℚ_[p]) ∧
    ¬ IsNoetherianRing (JetA ℚ_[p]) :=
  ⟨inferInstance, finiteJet_isUniform ℚ_[p], finiteJet_isDomain ℚ_[p],
    finiteJet_not_noetherian ℚ_[p]⟩

end FiniteJet
