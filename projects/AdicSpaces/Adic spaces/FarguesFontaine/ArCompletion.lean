/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.Valued.ValuedField
import «Adic spaces».FarguesFontaine.WittF

/-!
# The completed rings `A^r` (Kedlaya, Definition 2.4)

`A^r_{L,E}` is the completion of `A_{L,E} = A_inf[1/[ϖ]]` for the Gauss norm `λ_r`.
Per the AD-3 refinement of `decomposition-laneB.md`, we realize it inside one ambient
completed *field*: the Gauss valuation `w_ρ` extends to `K := Frac(A_inf)` (its support
is trivial by positivity), mathlib's valued-field completion `hatK ρ := (wK ρ).Completion`
applies, and `A^r` (resp. `B^r`) is the topological closure of the image of `Aloc`
(resp. `Bloc`) in `hatK ρ` — a closed subring of a complete Hausdorff ring, hence
complete.

## Main definitions

* `FarguesFontaine.wK` : the Gauss valuation on `Frac(A_inf)`.
* `FarguesFontaine.hatK` : the completed Gauss-valued field.
* `FarguesFontaine.ArSub`, `FarguesFontaine.BrSub` : the closures of `Aloc`, `Bloc`.

## Sources

* [Kedlaya, *Noetherian properties of Fargues–Fontaine curves*][kedlaya-noetherian-ff],
  Definition 2.4.
-/

open TopologicalRing ValuationSpectrum WittVector

universe u


noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type u) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]

/-- The nonzero divisors of `A_inf` avoid the support of the Gauss valuation
(positivity off zero, from multiplicativity). -/
theorem gaussVal_nonZeroDivisors_le_primeCompl {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    nonZeroDivisors (Ainf p F) ≤ (gaussVal p F hρ0 hρ1).supp.primeCompl := by
  intro x hx
  intro hmem
  have hx0 : x ≠ 0 := nonZeroDivisors.ne_zero hx
  have hval : gaussVal p F hρ0 hρ1 x = 0 := by
    have := hmem
    simpa [Valuation.mem_supp_iff] using this
  exact absurd hval (gaussValue_pos_of_ne_zero p F hρ0 hρ1.le hx0).ne'

/-- The Gauss valuation on the fraction field `K = Frac(A_inf)`. -/
def wK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Valuation (FractionRing (Ainf p F)) NNReal :=
  (gaussVal p F hρ0 hρ1).extendToLocalization
    (gaussVal_nonZeroDivisors_le_primeCompl p F hρ0 hρ1) _

@[simp]
theorem wK_algebraMap {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : Ainf p F) :
    wK p F hρ0 hρ1 (algebraMap (Ainf p F) (FractionRing (Ainf p F)) x)
      = gaussValue p F ρ x :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ _

/-- **The ambient completed Gauss-valued field** `hatK ρ`. -/
abbrev hatK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Type u :=
  (wK p F hρ0 hρ1).Completion

/-- The canonical map `A_inf → hatK`. -/
def toHatK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Ainf p F →+* hatK p F hρ0 hρ1 :=
  (UniformSpace.Completion.coeRingHom.comp
    ((WithVal.equiv (wK p F hρ0 hρ1)).symm.toRingHom)).comp
    (algebraMap (Ainf p F) (FractionRing (Ainf p F)))

/-- Values on `A_inf`-images in the completion are the Gauss values. -/
@[simp]
theorem valued_toHatK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : Ainf p F) :
    Valued.v (toHatK p F hρ0 hρ1 x) = gaussValue p F ρ x := by
  rw [toHatK]
  simp only [RingHom.comp_apply]
  rw [show (UniformSpace.Completion.coeRingHom
      ((WithVal.equiv (wK p F hρ0 hρ1)).symm.toRingHom
        (algebraMap (Ainf p F) (FractionRing (Ainf p F)) x)))
    = (((WithVal.equiv (wK p F hρ0 hρ1)).symm.toRingHom
        (algebraMap (Ainf p F) (FractionRing (Ainf p F)) x) : WithVal (wK p F hρ0 hρ1))
          : (wK p F hρ0 hρ1).Completion) from rfl,
    Valued.valuedCompletion_apply]
  exact wK_algebraMap p F hρ0 hρ1 x

variable (ϖ : PseudoUniformizer F)

/-- **Kedlaya's `A_{L,E}`**: the localization `A_inf[1/[ϖ]]` (decision AD-1). -/
abbrev Aloc := Localization.Away (teichPi p F ϖ)

/-- The image of `Aloc = A_inf[1/[ϖ]]` inside `hatK` (through the fraction field). -/
def AlocToHatK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Aloc p F ϖ →+* hatK p F hρ0 hρ1 :=
  IsLocalization.lift (M := Submonoid.powers (teichPi p F ϖ)) (g := toHatK p F hρ0 hρ1)
    (by
      intro y
      refine isUnit_iff_ne_zero.mpr fun h0 => ?_
      have hv := valued_toHatK p F hρ0 hρ1 (y : Ainf p F)
      rw [h0, map_zero] at hv
      have hne : gaussValue p F ρ (y : Ainf p F) ≠ 0 := by
        obtain ⟨k, hk⟩ := y.2
        have hk' : teichPi p F ϖ ^ k = (y : Ainf p F) := hk
        rw [← hk', show gaussValue p F ρ (teichPi p F ϖ ^ k)
          = (gaussValue p F ρ (teichPi p F ϖ)) ^ k from
            map_pow (gaussVal p F hρ0 hρ1) _ k]
        refine pow_ne_zero _ ?_
        rw [teichPi, gaussValue_teichmuller p F hρ1.le]
        exact fun hz => PseudoUniformizer.toOF_ne_zero F ϖ
          (Subtype.ext ((Valuation.zero_iff (perfectoidValuation p F)).mp hz))
      exact hne hv.symm)

/-- `A^r` as a subring of the ambient completed field: the closure of the `Aloc`-image
(Kedlaya Def 2.4, per the AD-3 refinement). -/
def ArSub {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Subring (hatK p F hρ0 hρ1) :=
  (AlocToHatK p F ϖ hρ0 hρ1).range.topologicalClosure

/-- `B^r`: the closure of the `Bloc`-image. Since `Bloc = Aloc[1/p]` with `p` already
a unit scale away, we define it directly as the closure of the image of `Bloc`. -/
def BlocToHatK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Bloc p F ϖ →+* hatK p F hρ0 hρ1 :=
  IsLocalization.lift (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ))
    (g := toHatK p F hρ0 hρ1)
    (by
      intro y
      refine isUnit_iff_ne_zero.mpr fun h0 => ?_
      have hv := valued_toHatK p F hρ0 hρ1 (y : Ainf p F)
      rw [h0, map_zero] at hv
      have hne : gaussValue p F ρ (y : Ainf p F) ≠ 0 := by
        obtain ⟨k, hk⟩ := y.2
        have hk' : ((p : Ainf p F) * teichPi p F ϖ) ^ k = (y : Ainf p F) := hk
        rw [← hk', show gaussValue p F ρ (((p : Ainf p F) * teichPi p F ϖ) ^ k)
          = (gaussValue p F ρ ((p : Ainf p F) * teichPi p F ϖ)) ^ k from
            map_pow (gaussVal p F hρ0 hρ1) _ k]
        exact pow_ne_zero k (gaussValue_p_teichPi_ne_zero p F ϖ hρ0 hρ1)
      exact hne hv.symm)

/-- `B^r` as a subring of `hatK`. -/
def BrSub {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Subring (hatK p F hρ0 hρ1) :=
  (BlocToHatK p F ϖ hρ0 hρ1).range.topologicalClosure

end FarguesFontaine

end
