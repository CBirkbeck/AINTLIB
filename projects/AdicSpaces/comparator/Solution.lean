/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetMain
import «Adic spaces».FJP.FiniteJetChart

/-!
# Comparator solution — the FJP headline theorems

Proofs of the statements in `Challenge.lean`, discharged by the library's own theorems.

The point of running this through [`leanprover/comparator`](https://github.com/leanprover/comparator)
is not to prove anything new. It is to obtain a *kernel-level, statement-pinned* certificate:
comparator re-checks each proof with the Lean kernel (optionally also nanoda), confirms it
proves the statement written in `Challenge.lean` rather than some weaker variant, and confirms
it rests on no axiom outside `propext`, `Quot.sound`, `Classical.choice`.

The binder block is identical to the challenge's, so the two elaborate to the same type.
-/

open FiniteJet ValuationSpectrum TopologicalRing

universe u

variable (F : Type u) [Field F]

/-- **[FJP] Theorem 1.3 (sheafy)**. -/
theorem fjp_1_3_isSheafy : IsSheafy (JetA F) := finiteJet_isSheafy F

/-- **[FJP] Theorem 1.3 (uniform)**. -/
theorem fjp_1_3_isUniform : IsUniform (JetA F) := finiteJet_isUniform F

/-- **[FJP] Theorem 1.3 (domain)**. -/
theorem fjp_1_3_isDomain : IsDomain (JetA F) := finiteJet_isDomain F

/-- **[FJP] Theorem 1.3 (nonnoetherian)**. -/
theorem fjp_1_3_not_isNoetherianRing : ¬ IsNoetherianRing (JetA F) :=
  finiteJet_not_noetherian F

/-- **[FJP] Theorem 1.3 (not stably uniform)**. -/
theorem fjp_1_3_not_isStablyUniform : ¬ IsStablyUniform (JetA F) :=
  finiteJet_not_stablyUniform F
