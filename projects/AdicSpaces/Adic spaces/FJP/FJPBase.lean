/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.RestrictedLaurent

/-!
# The abstract base field of the finite-jet construction

[FJP] runs its construction over "a complete discretely valued nonarchimedean field `k`
with uniformizer `ϖ`". The formalization originally hardcoded `k = F((t))`
(`LaurentSeries F`). This file isolates what the construction *actually* needs, so the
whole development can run over an arbitrary base — in particular over `ℚ_p` and its finite
extensions, which the Laurent-series model excludes.

Two classes, because the two halves of [FJP] need different amounts:

* `IsFJPBase K` — a **pseudouniformizer**: `ϖ ≠ 0` with `‖ϖ‖ < 1`. Together with
  `[NormedField K] [IsUltrametricDist K] [CompleteSpace K]` this is *everything* needed for
  the ring theory (`𝓐` is a complete uniform Tate domain), the chart `𝓐⟨W/ϖ⟩ ≅ 𝓑`, and the
  `Q²`-collapse. Note there is **no discreteness assumption**: multiplicativity of the
  Laurent Gauss norm (`RestrictedLaurent.norm_mul_eq`) holds over any complete
  nonarchimedean field, so this half applies to `ℂ_p` as well.

* `IsFJPNoetherianBase K` — additionally, the Gauss unit ball `K°⟨T₁,…,T_k⟩` is noetherian
  for every `k`. This is what the strict-localization machinery ([FJP] §4) and hence
  **sheafiness** needs, and it is where discreteness genuinely enters: for a dense value
  group `K°` is not even noetherian. It is stated as a class field rather than derived,
  because the general statement ("the ϖ-adic completion of a noetherian ring is
  noetherian", Stacks 00MA) is a mathlib gap — the repo's `AdicCompletion.isNoetherianRing`
  is `sorry`-backed. For `K = F((t))` it is discharged by the elementary transpose argument
  of `ExampleLaurentSeries.lean` (`Psi`/`exists_psi_eq`), which is sorry-free.

Splitting them this way is exactly what makes the Scottish Book answers (Problems 24, 28)
available over an arbitrary base while sheafiness stays tied to the Laurent model.
-/

namespace FiniteJet

universe u

/-- **The base of the finite-jet construction**: a complete ultrametric nonarchimedean
field together with a pseudouniformizer `ϖ` (`ϖ ≠ 0`, `‖ϖ‖ < 1`). No discreteness is
required. -/
class IsFJPBase (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] where
  /-- The chosen pseudouniformizer. -/
  pseudoUniformizer : K
  /-- The pseudouniformizer is nonzero (hence a unit, `K` being a field). -/
  pseudoUniformizer_ne_zero : pseudoUniformizer ≠ 0
  /-- The pseudouniformizer is topologically nilpotent. -/
  norm_pseudoUniformizer_lt_one : ‖pseudoUniformizer‖ < 1

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Base

variable [IsFJPBase K]

/-- The chosen pseudouniformizer `ϖ` of the base field. -/
noncomputable def ϖ : K := IsFJPBase.pseudoUniformizer

theorem ϖ_ne_zero : ϖ K ≠ 0 := IsFJPBase.pseudoUniformizer_ne_zero

theorem norm_ϖ_lt_one : ‖ϖ K‖ < 1 := IsFJPBase.norm_pseudoUniformizer_lt_one

theorem norm_ϖ_pos : 0 < ‖ϖ K‖ := norm_pos_iff.mpr (ϖ_ne_zero K)

theorem isUnit_ϖ : IsUnit (ϖ K) := (ϖ_ne_zero K).isUnit

end Base

/-! The companion class `IsFJPNoetherianBase` — the extra input needed for sheafiness — is
declared in `FiniteJetNoetherianVertices.lean`, because it mentions `unitBall`, which is
defined downstream in `FiniteJetRings.lean`. -/

end FiniteJet
