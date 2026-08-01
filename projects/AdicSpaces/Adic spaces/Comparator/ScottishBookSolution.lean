/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import «Adic spaces».FJP.FiniteJetScottishBook

/-!
# Comparator solution: Nonarchimedean Scottish Book Problems 24 and 28

Forwards each statement of `ScottishBookChallenge.lean` to the library's proof. This is the
module comparator rebuilds inside the sandbox, so it is deliberately tiny.

The binder block is identical to the challenge's, so the two elaborate to the same type.
-/

open FiniteJet ValuationSpectrum

universe u

variable (F : Type u) [NormedField F] [IsUltrametricDist F] [CompleteSpace F]
  [IsFJPBase F]

/-- **Scottish Book Problem 28 (affirmative)**. -/
theorem sb_28_strict_inclusion_dies_on_rational_subset :
    ∃ (f : JetA F) (D : RationalLocData (JetA F)),
      D.IsRational ∧
      (rationalOpen D.T D.s).Nonempty ∧
      Nontrivial (presheafValue D) ∧
      Function.Injective (fun a : JetA F => f * a) ∧
      IsStrictMap (fun a : JetA F => f * a) ∧
      IsClosed (Set.range fun a : JetA F => f * a) ∧
      D.canonicalMap f = 0 := by
  obtain ⟨hrat, hne, hnt, hinj, -, hstrict, hclosed, hzero⟩ := finiteJet_problem28 F
  exact ⟨scottishWitness F, chartDatum F, hrat, hne, hnt, hinj, hstrict, hclosed, hzero⟩

/-- **Scottish Book Problem 24 (negative)**. -/
theorem sb_24_rational_localization_not_flat :
    ∃ D : RationalLocData (JetA F),
      ¬ @Module.Flat (JetA F) (presheafValue D) _ _
        (RingHom.toModule D.canonicalMap) :=
  ⟨chartDatum F, finiteJet_not_flat_canonicalMap F⟩
