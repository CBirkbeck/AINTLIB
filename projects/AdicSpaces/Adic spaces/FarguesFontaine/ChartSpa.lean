/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.BigWindows
import «Adic spaces».FarguesFontaine.ChartComparison
import «Adic spaces».NonTateRationalOpenHomeomorph

/-!
# The chart spectra of the Big windows (D-ii)

`Spa (B_n, B_n⁺) ≃ₜ` the trace of `bigWindow n` on `Spa (A_inf, A_inf)`:

* `FarguesFontaine.isTateRing_presheafChart` / `isTateRing_bigWindowChart` :
  the chart presheaf values are Tate rings (transported from `B^I`);
* `FarguesFontaine.spaChartHomeoBigWindow` / `spaChartHomeoBigWindowNeg` :
  the chart homeomorphisms, via the non-Tate-base Wedhorn 8.2(2)
  (`spaPresheafValueHomeomorphRationalOpen'`) with the nilpotent unit
  supplied by the chart ring's own Tate structure, composed with the
  Big-window rational identifications.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}

noncomputable local instance instDecEqAinfChartSpa : DecidableEq (Ainf p F) :=
  Classical.decEq _

include hρ₁0 hρ₁1 hρ₂0 hρ₂1 in
/-- **The chart presheaf value is a Tate ring** (transported from `B^I`). -/
theorem isTateRing_presheafChart (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : b ≤ a)
    (hexact1 : perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) = ρ₁)
    (hexact2 : ρ₂ ^ a
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ b) :
    IsTateRing (presheafValue (chartData p F ϖ 1 b a b)) :=
  isTateRing_congr
    (presheafChartRingEquivBISub p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab hexact1 hexact2).symm
    (presheafChartRingEquivBISub_symm_continuous p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2)
    (presheafChartRingEquivBISub_continuous p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) a b ha hb hab
      hexact1 hexact2)

/-- The Big-window chart datum is Tate at the concrete `(a, b) = (p, 1)`
interval (any twisted uniformizer). -/
theorem isTateRing_bigWindowChart (ϖ' : PseudoUniformizer F) :
    IsTateRing (presheafValue (chartData p F ϖ' 1 1 p 1)) := by
  have hp : 1 < p := Nat.Prime.one_lt (Fact.out : Nat.Prime p)
  exact isTateRing_presheafChart p F ϖ'
    (hρ₁0 := vpi_pos p F ϖ') (hρ₁1 := perfectoidValuation_toOF_lt_one p F ϖ')
    (hρ₂0 := rhoRight_pos p F ϖ' p 1)
    (hρ₂1 := rhoRight_lt_one p F ϖ' p 1 (by omega) one_pos)
    p 1 (by omega) one_pos (by omega) rfl
    (by
      rw [rhoRight_pow_exact p F ϖ' p 1 (by omega), pow_one])


/-- **The Big-window chart homeomorphism (nonnegative side)**:
`Spa (B_n, B_n⁺) ≃ₜ` the trace of `bigWindow n` — Wedhorn 8.2(2) over the
non-Tate base `A_inf`, with the nilpotent unit supplied by the chart ring's
own Tate structure. -/
noncomputable def spaChartHomeoBigWindow (n : ℕ) (hp : 1 < p) :
    ↥(Spa (presheafValue (chartData p F
        (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))
      (ringPlus (presheafValue (chartData p F
        (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))))
      ≃ₜ ↥(bigWindow p F ϖ (n : ℤ) ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
  haveI : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  haveI : IsTateRing (presheafValue (chartData p F
      (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1)) :=
    isTateRing_bigWindowChart p F (PseudoUniformizer.frobRoot p F ϖ n)
  (spaPresheafValueHomeomorphRationalOpen'
    (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1)
    (IsTateRing.exists_topologicallyNilpotent_unit (A := presheafValue
      (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))).choose
    (IsTateRing.exists_topologicallyNilpotent_unit (A := presheafValue
      (chartData p F (PseudoUniformizer.frobRoot p F ϖ n) 1 1 p 1))).choose_spec).trans
    (Homeomorph.setCongr (by
      rw [bigWindow_eq_rationalOpen_ofNat p F ϖ n hp]
      rfl))

/-- **The Big-window chart homeomorphism (negative side).** -/
noncomputable def spaChartHomeoBigWindowNeg (m : ℕ) (hp : 1 < p) :
    ↥(Spa (presheafValue (chartData p F
        (PseudoUniformizer.pPow F ϖ (p ^ m)
          (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1))
      (ringPlus (presheafValue (chartData p F
        (PseudoUniformizer.pPow F ϖ (p ^ m)
          (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1))))
      ≃ₜ ↥(bigWindow p F ϖ (-(m : ℤ)) ∩ Spa (Ainf p F) (ringPlus (Ainf p F))) :=
  haveI : IsRingOfIntegralElements ((Ainf p F)⁺ : Subring (Ainf p F)) :=
    isAffinoidRing_Ainf p F
  haveI : IsTateRing (presheafValue (chartData p F
      (PseudoUniformizer.pPow F ϖ (p ^ m)
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1)) :=
    isTateRing_bigWindowChart p F _
  (spaPresheafValueHomeomorphRationalOpen'
    (chartData p F (PseudoUniformizer.pPow F ϖ (p ^ m)
      (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1)
    (IsTateRing.exists_topologicallyNilpotent_unit (A := presheafValue
      (chartData p F (PseudoUniformizer.pPow F ϖ (p ^ m)
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1))).choose
    (IsTateRing.exists_topologicallyNilpotent_unit (A := presheafValue
      (chartData p F (PseudoUniformizer.pPow F ϖ (p ^ m)
        (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime p)) m)) 1 1 p 1))).choose_spec).trans
    (Homeomorph.setCongr (by
      rw [bigWindow_eq_rationalOpen_neg p F ϖ m hp]
      rfl))

end FarguesFontaine

end
