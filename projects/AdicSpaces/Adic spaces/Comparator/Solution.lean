/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetMain

/-!
# Comparator solution: [FJP] Theorem 1.1

Forwards each statement of `Challenge.lean` to the library's proof. This is the module
comparator rebuilds inside the sandbox, so it is deliberately tiny: the project itself is
already built, and only this file is treated as the untrusted submission.

The binder block is identical to the challenge's, so the two elaborate to the same type.
-/

open FiniteJet ValuationSpectrum TopologicalRing

universe u

variable (F : Type u) [Field F]

/-- **[FJP] Theorem 1.1 (sheafy)**. -/
theorem fjp_1_1_isSheafy : IsSheafy (JetA F) := finiteJet_isSheafy F

/-- **[FJP] Theorem 1.1 (uniform)**. -/
theorem fjp_1_1_isUniform : IsUniform (JetA F) := finiteJet_isUniform F

/-- **[FJP] Theorem 1.1 (domain)**. -/
theorem fjp_1_1_isDomain : IsDomain (JetA F) := finiteJet_isDomain F

/-- **[FJP] Theorem 1.1 (nonnoetherian)**. -/
theorem fjp_1_1_not_isNoetherianRing : ¬ IsNoetherianRing (JetA F) := finiteJet_not_noetherian F

/-- **[FJP] Theorem 1.1 (not stably uniform)**. -/
theorem fjp_1_1_not_isStablyUniform : ¬ IsStablyUniform (JetA F) := finiteJet_not_stablyUniform F
