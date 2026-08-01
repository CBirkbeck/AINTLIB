/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetMain

/-!
# Comparator solution: [FJP] Theorem 1.3

Forwards each statement of `Challenge.lean` to the library's proof. This is the module
comparator rebuilds inside the sandbox, so it is deliberately tiny: the project itself is
already built, and only this file is treated as the untrusted submission.

The binder block is identical to the challenge's, so the two elaborate to the same type.
-/

open FiniteJet ValuationSpectrum TopologicalRing

universe u

variable (F : Type u) [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
  [IsFJPBase F]

/-- **[FJP] Theorem 1.3 (sheafy)**. -/
theorem fjp_1_3_isSheafy [IsFJPNoetherianBase F] : IsSheafy (JetA F) :=
  finiteJet_isSheafy F

/-- **[FJP] Theorem 1.3 (uniform)**. -/
theorem fjp_1_3_isUniform : IsUniform (JetA F) := finiteJet_isUniform F

/-- **[FJP] Theorem 1.3 (domain)**. -/
theorem fjp_1_3_isDomain : IsDomain (JetA F) := finiteJet_isDomain F

/-- **[FJP] Theorem 1.3 (nonnoetherian)**. -/
theorem fjp_1_3_not_isNoetherianRing : ¬ IsNoetherianRing (JetA F) := finiteJet_not_noetherian F

/-- **[FJP] Theorem 1.3 (not stably uniform)**. -/
theorem fjp_1_3_not_isStablyUniform [IsFJPNoetherianBase F] :
    ¬ IsStablyUniform (JetA F) := finiteJet_not_stablyUniform F
