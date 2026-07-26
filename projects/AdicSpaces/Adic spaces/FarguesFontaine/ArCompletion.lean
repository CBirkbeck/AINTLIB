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

/-- `[ϖ]` becomes a unit in `W(F)`: its inverse is `[ϖ⁻¹]`. -/
theorem isUnit_map_teichPi :
    IsUnit (WittVector.map ((powerBoundedSubring.toSubring F).subtype) (teichPi p F ϖ)) := by
  have hne : (((ϖ.val : Fˣ) : F)) ≠ 0 := (ϖ.val : Fˣ).ne_zero
  have hmul : WittVector.map ((powerBoundedSubring.toSubring F).subtype) (teichPi p F ϖ)
      * WittVector.teichmuller p ((((ϖ.val : Fˣ) : F))⁻¹) = 1 := by
    rw [teichPi, WittVector.map_teichmuller, ← map_mul]
    have hval : ((PseudoUniformizer.toOF F ϖ : OF F) : F) * ((((ϖ.val : Fˣ) : F))⁻¹)
        = 1 := by
      rw [show ((PseudoUniformizer.toOF F ϖ : OF F) : F) = (((ϖ.val : Fˣ) : F)) from rfl,
        mul_inv_cancel₀ hne]
    rw [show ((powerBoundedSubring.toSubring F).subtype) (PseudoUniformizer.toOF F ϖ)
        * ((((ϖ.val : Fˣ) : F))⁻¹)
      = ((PseudoUniformizer.toOF F ϖ : OF F) : F) * ((((ϖ.val : Fˣ) : F))⁻¹) from rfl, hval,
      map_one]
  exact ⟨Units.mkOfMulEqOne _ _ hmul, rfl⟩

/-- **The concrete embedding** `Aloc → W(F)` (Kedlaya's `A_{L,E} ⊆ W(L)_E`, Def 2.2/2.4):
lift the coefficient-wise inclusion `W(O_F) → W(F)` through the `[ϖ]`-localization. -/
def alocToWittF : Aloc p F ϖ →+* WittVector p F :=
  IsLocalization.lift (M := Submonoid.powers (teichPi p F ϖ))
    (g := WittVector.map ((powerBoundedSubring.toSubring F).subtype))
    (by
      intro y
      obtain ⟨k, hk⟩ := y.2
      have hk' : teichPi p F ϖ ^ k = (y : Ainf p F) := hk
      rw [← hk', map_pow]
      exact (isUnit_map_teichPi p F ϖ).pow k)

@[simp]
theorem alocToWittF_algebraMap (x : Ainf p F) :
    alocToWittF p F ϖ (algebraMap (Ainf p F) (Aloc p F ϖ) x)
      = WittVector.map ((powerBoundedSubring.toSubring F).subtype) x :=
  IsLocalization.lift_eq _ x

/-- The powers of `[ϖ]` avoid the support of the Gauss valuation. -/
theorem gaussVal_powers_teichPi_le_primeCompl {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Submonoid.powers (teichPi p F ϖ)
      ≤ (gaussVal p F hρ0 hρ1).supp.primeCompl := by
  rintro x ⟨k, rfl⟩
  intro hx
  simp only [SetLike.mem_coe, Valuation.mem_supp_iff, map_pow] at hx
  refine absurd hx (pow_ne_zero k ?_)
  rw [show gaussVal p F hρ0 hρ1 (teichPi p F ϖ)
    = gaussValue p F ρ (teichPi p F ϖ) from rfl, teichPi,
    gaussValue_teichmuller p F hρ1.le]
  exact fun hz => PseudoUniformizer.toOF_ne_zero F ϖ
    (Subtype.ext ((Valuation.zero_iff (perfectoidValuation p F)).mp hz))

/-- The extended Gauss valuation on `Aloc` (mirror of `wLoc`). -/
def wAloc {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) : Valuation (Aloc p F ϖ) NNReal :=
  (gaussVal p F hρ0 hρ1).extendToLocalization
    (gaussVal_powers_teichPi_le_primeCompl p F ϖ hρ0 hρ1) _

@[simp]
theorem wAloc_algebraMap {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : Ainf p F) :
    wAloc p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Aloc p F ϖ) x)
      = gaussValue p F ρ x :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ _

/-- **Realization on the dense layer**: term values of `Aloc`-elements in `W(F)` are
bounded by (and their sup equals) the extended Gauss valuation. -/
theorem gaussTermF_alocToWittF_le {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (u : Aloc p F ϖ) (n : ℕ) :
    gaussTermF p F ρ (alocToWittF p F ϖ u) n ≤ wAloc p F ϖ hρ0 hρ1 u := by
  obtain ⟨⟨a, y⟩, hu⟩ := IsLocalization.surj (M := Submonoid.powers (teichPi p F ϖ)) u
  change u * algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F)
    = algebraMap (Ainf p F) (Aloc p F ϖ) a at hu
  obtain ⟨k, hk⟩ := y.2
  have hk' : teichPi p F ϖ ^ k = (y : Ainf p F) := hk
  set ϖF : F := ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hϖF
  set c : NNReal := perfectoidValuation p F ϖF with hc
  have hϖne : ϖF ≠ 0 := fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  have hc0 : 0 < c := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
  -- image side
  have hy : alocToWittF p F ϖ (algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F))
      = WittVector.teichmuller p (ϖF ^ k) := by
    rw [alocToWittF_algebraMap, ← hk', map_pow]
    have hone : WittVector.map ((powerBoundedSubring.toSubring F).subtype)
        (teichPi p F ϖ) = WittVector.teichmuller p ϖF := by
      rw [show teichPi p F ϖ = WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ)
        from rfl, WittVector.map_teichmuller]
      rfl
    rw [hone, ← map_pow]
  have himg : alocToWittF p F ϖ u * WittVector.teichmuller p (ϖF ^ k)
      = WittVector.map ((powerBoundedSubring.toSubring F).subtype) a := by
    have happ := congrArg (alocToWittF p F ϖ) hu
    rw [map_mul, hy, alocToWittF_algebraMap] at happ
    exact happ
  -- value side
  have hteich : gaussValue p F ρ (teichPi p F ϖ) = c := by
    rw [show teichPi p F ϖ = WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ)
      from rfl, gaussValue_teichmuller p F hρ1.le]
  have hval : wAloc p F ϖ hρ0 hρ1 u * c ^ k = gaussValue p F ρ a := by
    have happ := congrArg (wAloc p F ϖ hρ0 hρ1) hu
    rw [map_mul, wAloc_algebraMap, wAloc_algebraMap, ← hk'] at happ
    rw [show gaussValue p F ρ (teichPi p F ϖ ^ k)
      = (gaussValue p F ρ (teichPi p F ϖ)) ^ k from map_pow (gaussVal p F hρ0 hρ1) _ k,
      hteich] at happ
    exact happ
  -- term side
  have hterm : gaussTermF p F ρ (alocToWittF p F ϖ u) n * c ^ k
      = gaussTerm p F ρ a n := by
    have h1 := gaussTermF_teichmuller_mul p F (ρ := ρ) (w := ϖF ^ k)
      (s := alocToWittF p F ϖ u) n
    rw [mul_comm (WittVector.teichmuller p (ϖF ^ k)) _] at h1
    rw [himg, gaussTermF_map, map_pow] at h1
    rw [h1]
    ring
  have hle : gaussTermF p F ρ (alocToWittF p F ϖ u) n * c ^ k
      ≤ wAloc p F ϖ hρ0 hρ1 u * c ^ k := by
    rw [hterm, hval]
    exact gaussTerm_le_gaussValue p F hρ1.le a n
  exact le_of_mul_le_mul_right hle (pow_pos hc0 k)

/-- Aloc-images are boundedly termed. -/
theorem bddAbove_gaussTermF_alocToWittF {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (u : Aloc p F ϖ) :
    BddAbove (Set.range (gaussTermF p F ρ (alocToWittF p F ϖ u))) :=
  ⟨wAloc p F ϖ hρ0 hρ1 u, by
    rintro z ⟨n, rfl⟩
    exact gaussTermF_alocToWittF_le p F ϖ hρ0 hρ1 u n⟩

/-- **Realization equality on the dense layer**: the `W(F)`-Gauss value of an
`Aloc`-image equals the extended Gauss valuation (the sup is attained, being a
`c^{-k}`-scaling of the attained `A_inf`-sup). -/
theorem gaussValueF_alocToWittF {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (u : Aloc p F ϖ) :
    gaussValueF p F ρ (alocToWittF p F ϖ u) = wAloc p F ϖ hρ0 hρ1 u := by
  refine le_antisymm
    (ciSup_le fun n => gaussTermF_alocToWittF_le p F ϖ hρ0 hρ1 u n) ?_
  obtain ⟨⟨a, y⟩, hu⟩ := IsLocalization.surj (M := Submonoid.powers (teichPi p F ϖ)) u
  change u * algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F)
    = algebraMap (Ainf p F) (Aloc p F ϖ) a at hu
  obtain ⟨k, hk⟩ := y.2
  have hk' : teichPi p F ϖ ^ k = (y : Ainf p F) := hk
  set ϖF : F := ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hϖF
  set c : NNReal := perfectoidValuation p F ϖF with hc
  have hϖne : ϖF ≠ 0 := fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  have hc0 : 0 < c := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
  have hteich : gaussValue p F ρ (teichPi p F ϖ) = c := by
    rw [show teichPi p F ϖ = WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ)
      from rfl, gaussValue_teichmuller p F hρ1.le]
  have hval : wAloc p F ϖ hρ0 hρ1 u * c ^ k = gaussValue p F ρ a := by
    have happ := congrArg (wAloc p F ϖ hρ0 hρ1) hu
    rw [map_mul, wAloc_algebraMap, wAloc_algebraMap, ← hk'] at happ
    rw [show gaussValue p F ρ (teichPi p F ϖ ^ k)
      = (gaussValue p F ρ (teichPi p F ϖ)) ^ k from map_pow (gaussVal p F hρ0 hρ1) _ k,
      hteich] at happ
    exact happ
  have hy : alocToWittF p F ϖ (algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F))
      = WittVector.teichmuller p (ϖF ^ k) := by
    rw [alocToWittF_algebraMap, ← hk', map_pow]
    have hone : WittVector.map ((powerBoundedSubring.toSubring F).subtype)
        (teichPi p F ϖ) = WittVector.teichmuller p ϖF := by
      rw [show teichPi p F ϖ = WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ)
        from rfl, WittVector.map_teichmuller]
      rfl
    rw [hone, ← map_pow]
  have himg : alocToWittF p F ϖ u * WittVector.teichmuller p (ϖF ^ k)
      = WittVector.map ((powerBoundedSubring.toSubring F).subtype) a := by
    have happ := congrArg (alocToWittF p F ϖ) hu
    rw [map_mul, hy, alocToWittF_algebraMap] at happ
    exact happ
  -- attain the Ainf-sup at n₀ and transfer
  rcases eq_or_ne (wAloc p F ϖ hρ0 hρ1 u) 0 with h0 | hne0
  · rw [h0]
    exact zero_le
  have hane : a ≠ 0 := by
    intro h0a
    rw [h0a, gaussValue_zero] at hval
    exact hne0 (by
      have := hval
      have hck : (0 : NNReal) < c ^ k := pow_pos hc0 k
      exact (mul_eq_zero.mp this).resolve_right hck.ne')
  obtain ⟨n₀, hn₀⟩ := exists_gaussValue_eq_gaussTerm p F hρ0 hρ1 (x := a) hane
  have hterm : gaussTermF p F ρ (alocToWittF p F ϖ u) n₀ * c ^ k
      = gaussTerm p F ρ a n₀ := by
    have h1 := gaussTermF_teichmuller_mul p F (ρ := ρ) (w := ϖF ^ k)
      (s := alocToWittF p F ϖ u) n₀
    rw [mul_comm (WittVector.teichmuller p (ϖF ^ k)) _] at h1
    rw [himg, gaussTermF_map, map_pow] at h1
    rw [h1]
    ring
  have hgoal : wAloc p F ϖ hρ0 hρ1 u * c ^ k
      = gaussTermF p F ρ (alocToWittF p F ϖ u) n₀ * c ^ k := by
    rw [hterm, hval, hn₀]
  have heq : wAloc p F ϖ hρ0 hρ1 u
      = gaussTermF p F ρ (alocToWittF p F ϖ u) n₀ :=
    mul_right_cancel₀ (pow_pos hc0 k).ne' hgoal
  rw [heq]
  exact le_ciSup (bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 u) n₀

/-- The completed-field valuation restricts to `wAloc` on `Aloc`-images. -/
theorem valued_AlocToHatK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (u : Aloc p F ϖ) :
    Valued.v (AlocToHatK p F ϖ hρ0 hρ1 u) = wAloc p F ϖ hρ0 hρ1 u := by
  obtain ⟨⟨a, y⟩, hu⟩ := IsLocalization.surj (M := Submonoid.powers (teichPi p F ϖ)) u
  change u * algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F)
    = algebraMap (Ainf p F) (Aloc p F ϖ) a at hu
  have hyne : gaussValue p F ρ (y : Ainf p F) ≠ 0 := by
    obtain ⟨k, hk⟩ := y.2
    have hk' : teichPi p F ϖ ^ k = (y : Ainf p F) := hk
    rw [← hk', show gaussValue p F ρ (teichPi p F ϖ ^ k)
      = (gaussValue p F ρ (teichPi p F ϖ)) ^ k from map_pow (gaussVal p F hρ0 hρ1) _ k]
    refine pow_ne_zero _ ?_
    rw [show teichPi p F ϖ = WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ)
      from rfl, gaussValue_teichmuller p F hρ1.le]
    exact fun hz => PseudoUniformizer.toOF_ne_zero F ϖ
      (Subtype.ext ((Valuation.zero_iff (perfectoidValuation p F)).mp hz))
  have hAloc : AlocToHatK p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Aloc p F ϖ)
      (y : Ainf p F)) = toHatK p F hρ0 hρ1 (y : Ainf p F) := IsLocalization.lift_eq _ _
  have hAloc' : AlocToHatK p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Aloc p F ϖ) a)
      = toHatK p F hρ0 hρ1 a := IsLocalization.lift_eq _ _
  have h1 : Valued.v (AlocToHatK p F ϖ hρ0 hρ1 u) * gaussValue p F ρ (y : Ainf p F)
      = gaussValue p F ρ a := by
    have happ := congrArg (fun z => Valued.v (AlocToHatK p F ϖ hρ0 hρ1 z)) hu
    simp only [map_mul, hAloc, hAloc'] at happ
    rw [valued_toHatK, valued_toHatK] at happ
    exact happ
  have h2 : wAloc p F ϖ hρ0 hρ1 u * gaussValue p F ρ (y : Ainf p F)
      = gaussValue p F ρ a := by
    have happ := congrArg (wAloc p F ϖ hρ0 hρ1) hu
    rw [map_mul, wAloc_algebraMap, wAloc_algebraMap] at happ
    exact happ
  exact mul_right_cancel₀ hyne (h1.trans h2.symm)

/-- The coordinate functionals on the ambient completion, as filter limits along
`Aloc`-approximants (junk value off the closure). -/
def teichCoeffAr {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (x : hatK p F hρ0 hρ1)
    (n : ℕ) : F :=
  Filter.limUnder (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x))
    (fun u => teichCoeffF p F (alocToWittF p F ϖ u) n)

/-- Valuation balls are neighborhoods of `0` in `F`: `ϖ^m·O_F ⊆ {v ≤ c^m}` and the
left side is open. -/
theorem ball_mem_nhds_zero (m : ℕ) :
    {z : F | perfectoidValuation p F z ≤ (perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m} ∈ nhds (0 : F) := by
  obtain ⟨P⟩ := IsHuberRing.exists_pairOfDefinition (A := F)
  have hopen : IsOpen ((fun z : F => ((ϖ.val : Fˣ) : F) ^ m * z) ''
      (powerBoundedSubring F : Set F)) := by
    have hunit : IsUnit (((ϖ.val : Fˣ) : F) ^ m) := ((ϖ.val : Fˣ).isUnit).pow m
    exact hunit.isOpenMap_smul _ P.isOpen_powerBoundedSubring
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨0, isPowerBounded_zero, mul_zero _⟩) ?_
  rintro z ⟨u, hu, rfl⟩
  have hu1 : perfectoidValuation p F u ≤ 1 := by
    obtain ⟨û, hû⟩ := (⟨u, hu⟩ : powerBoundedSubring F)
    exact perfectoidValuation_le_one p F ⟨u, hu⟩
  calc perfectoidValuation p F (((ϖ.val : Fˣ) : F) ^ m * u)
      = (perfectoidValuation p F (((ϖ.val : Fˣ) : F))) ^ m * perfectoidValuation p F u := by
        rw [Valuation.map_mul, map_pow]
    _ ≤ (perfectoidValuation p F (((ϖ.val : Fˣ) : F))) ^ m * 1 :=
        mul_le_mul_of_nonneg_left hu1 zero_le
    _ = (perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m := by
        rw [mul_one]
        rfl

/-- Every neighborhood of `0` in `F` contains a valuation ball (the power-bounded
subring is bounded; scale by `ϖ^N`). -/
theorem exists_ball_subset_nhds {V : Set F} (hV : V ∈ nhds (0 : F)) :
    ∃ m : ℕ, {z : F | perfectoidValuation p F z ≤ (perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m} ⊆ V := by
  haveI := IsPerfectoidRing.uniform (p := p) (A := F)
  obtain ⟨G, hGV⟩ := NonarchimedeanAddGroup.is_nonarchimedean V hV
  obtain ⟨W, hW, hFW⟩ := IsUniform.isBounded_powerBounded (A := F) (G : Set F)
    (G.isOpen.mem_nhds G.zero_mem')
  obtain ⟨N, hN⟩ := ϖ.isTopologicallyNilpotent.exists_pow_mem_of_mem_nhds hW
  refine ⟨N, fun z hz => hGV ?_⟩
  -- v(z) ≤ c^N means z/ϖ^N ∈ O_F, so z = ϖ^N·(power-bounded) ∈ W·O_F ⊆ G… we use
  -- z = (z·ϖ^{-N})·ϖ^N with the first factor of valuation ≤ 1.
  set ϖF : F := ((ϖ.val : Fˣ) : F) with hϖF
  have hϖne : ϖF ≠ 0 := (ϖ.val : Fˣ).ne_zero
  have hzu : perfectoidValuation p F (z * (ϖF ^ N)⁻¹) ≤ 1 := by
    rw [Valuation.map_mul, map_inv₀, map_pow]
    rcases eq_or_ne (perfectoidValuation p F ϖF) 0 with hc0 | hc0
    · exact absurd ((Valuation.zero_iff _).mp hc0) hϖne
    calc perfectoidValuation p F z * ((perfectoidValuation p F ϖF) ^ N)⁻¹
        ≤ (perfectoidValuation p F ϖF) ^ N * ((perfectoidValuation p F ϖF) ^ N)⁻¹ := by
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          exact hz
      _ = 1 := mul_inv_cancel₀ (pow_ne_zero N hc0)
  obtain ⟨u, hu⟩ := (perfectoidValuation_integers p F).exists_of_le_one hzu
  have hu' : ((u : OF F) : F) = z * (ϖF ^ N)⁻¹ := hu
  have hzeq : z = ((u : OF F) : F) * ϖF ^ N := by
    rw [hu']
    field_simp
  rw [hzeq]
  exact hFW (Set.mul_mem_mul u.2 hN)

/-- The approximant filter of a point of `A^r` is nontrivial. -/
theorem neBot_comap_of_mem_ArSub {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) :
    (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x)).NeBot := by
  rw [Filter.comap_neBot_iff]
  intro t ht
  have hx' : x ∈ closure (Set.range (AlocToHatK p F ϖ hρ0 hρ1)) := by
    have hcarrier : (ArSub p F ϖ hρ0 hρ1 : Set (hatK p F hρ0 hρ1))
        = closure ((AlocToHatK p F ϖ hρ0 hρ1).range : Set (hatK p F hρ0 hρ1)) := rfl
    have hx2 : x ∈ (ArSub p F ϖ hρ0 hρ1 : Set (hatK p F hρ0 hρ1)) := hx
    rw [hcarrier] at hx2
    rwa [show ((AlocToHatK p F ϖ hρ0 hρ1).range : Set (hatK p F hρ0 hρ1))
      = Set.range (AlocToHatK p F ϖ hρ0 hρ1) from rfl] at hx2
  obtain ⟨y, hyt, hyr⟩ := mem_closure_iff_nhds.mp hx' t ht
  obtain ⟨u, rfl⟩ := hyr
  exact ⟨u, hyt⟩

/-- Pairs of approximants of any `x` are eventually `wAloc`-close (transfer of the
completed-field entourages through `restrict_lt_iff` — comparisons between values of
the same valuation only, no value-group computations). -/
theorem eventually_pair_wAloc_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (x : hatK p F hρ0 hρ1) {ε : NNReal} (hε : 0 < ε) :
    ∀ᶠ q in (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x)) ×ˢ
        (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x)),
      wAloc p F ϖ hρ0 hρ1 (q.2 - q.1) ≤ ε := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hρ1
  set z₀ : hatK p F hρ0 hρ1 := toHatK p F hρ0 hρ1 ((p : Ainf p F) ^ N) with hz₀
  have hvz₀ : Valued.v z₀ = ρ ^ N := by
    rw [hz₀, valued_toHatK]
    have : gaussValue p F ρ ((p : Ainf p F) ^ N)
        = (gaussValue p F ρ (p : Ainf p F)) ^ N := map_pow (gaussVal p F hρ0 hρ1) _ N
    rw [this]
    congr 1
    calc gaussValue p F ρ (p : Ainf p F)
        = gaussValue p F ρ ((p : Ainf p F) * 1) := by rw [mul_one]
      _ = ρ * gaussValue p F ρ 1 := gaussValue_p_mul p F hρ1.le 1
      _ = ρ := by rw [gaussValue_one p F hρ1.le, mul_one]
  have hvz₀ne : Valued.v z₀ ≠ 0 := by
    rw [hvz₀]
    exact (pow_pos hρ0 N).ne'
  have hrne : (Valued.v).restrict z₀ ≠ 0 := by
    refine fun h0 => hvz₀ne ?_
    have := (Valuation.restrict_pos_iff (v := (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)) z₀)
    rcases eq_or_ne (Valued.v z₀) 0 with h | h
    · exact h
    · exact absurd (this.mpr (pos_iff_ne_zero.mpr h)) (by rw [h0]; exact lt_irrefl 0)
  set γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)))ˣ := Units.mk0 _ hrne with hγ
  have hcauchy : (nhds x) ×ˢ (nhds x) ≤ uniformity (hatK p F hρ0 hρ1) := cauchy_nhds.2
  have hball := (Valued.hasBasis_uniformity (hatK p F hρ0 hρ1) NNReal).mem_of_mem
    (i := γ) trivial
  have hev := hcauchy hball
  have hev2 : ∀ᶠ q in (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x)) ×ˢ
      (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x)),
      (Valued.v).restrict ((AlocToHatK p F ϖ hρ0 hρ1 q.2)
        - (AlocToHatK p F ϖ hρ0 hρ1 q.1)) < γ.1 := by
    have hcomap : (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x)) ×ˢ
        (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x))
        = Filter.comap (fun q : Aloc p F ϖ × Aloc p F ϖ =>
            (AlocToHatK p F ϖ hρ0 hρ1 q.1, AlocToHatK p F ϖ hρ0 hρ1 q.2))
          ((nhds x) ×ˢ (nhds x)) := Filter.prod_comap_comap_eq
    rw [hcomap]
    exact Filter.eventually_comap.mpr (Filter.Eventually.mono hev
      (by
        rintro ⟨a, b⟩ hab ⟨u, u'⟩ huu'
        have h1 : AlocToHatK p F ϖ hρ0 hρ1 u = a := congrArg Prod.fst huu'
        have h2 : AlocToHatK p F ϖ hρ0 hρ1 u' = b := congrArg Prod.snd huu'
        rw [h1, h2]
        exact hab))
  refine hev2.mono ?_
  rintro ⟨u, u'⟩ hq
  have hlt : Valued.v ((AlocToHatK p F ϖ hρ0 hρ1 u')
      - (AlocToHatK p F ϖ hρ0 hρ1 u)) < Valued.v z₀ := by
    have := hq
    rw [hγ] at this
    have hcast : (Units.mk0 ((Valued.v).restrict z₀) hrne).1
        = (Valued.v).restrict z₀ := rfl
    rw [hcast] at this
    exact (Valuation.restrict_lt_iff (v := (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal))).mp this
  have hsub : (AlocToHatK p F ϖ hρ0 hρ1 u') - (AlocToHatK p F ϖ hρ0 hρ1 u)
      = AlocToHatK p F ϖ hρ0 hρ1 (u' - u) := (map_sub _ _ _).symm
  rw [hsub, valued_AlocToHatK, hvz₀] at hlt
  exact le_of_lt (lt_of_lt_of_le hlt hN.le)

/-- Approximants of a point of `A^r` have eventually bounded values. -/
theorem exists_eventually_wAloc_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) :
    ∃ B : NNReal, ∀ᶠ u in Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x),
      wAloc p F ϖ hρ0 hρ1 u ≤ B := by
  haveI := neBot_comap_of_mem_ArSub p F ϖ hx
  have hpair := eventually_pair_wAloc_le p F ϖ (hρ0 := hρ0) (hρ1 := hρ1) x
    (ε := 1) one_pos
  rw [Filter.eventually_prod_iff] at hpair
  obtain ⟨Pa, hPa, Pb, hPb, hPab⟩ := hpair
  obtain ⟨u₀, hu₀⟩ := (Filter.eventually_and.mpr ⟨hPa, hPb⟩).exists
  refine ⟨max (wAloc p F ϖ hρ0 hρ1 u₀) 1, ?_⟩
  refine Filter.Eventually.mono hPb fun u hu => ?_
  have hdiff : wAloc p F ϖ hρ0 hρ1 (u - u₀) ≤ 1 := hPab hu₀.1 hu
  calc wAloc p F ϖ hρ0 hρ1 u
      = wAloc p F ϖ hρ0 hρ1 ((u - u₀) + u₀) := by rw [sub_add_cancel]
    _ ≤ max (wAloc p F ϖ hρ0 hρ1 (u - u₀)) (wAloc p F ϖ hρ0 hρ1 u₀) :=
        Valuation.map_add _ _ _
    _ ≤ max (wAloc p F ϖ hρ0 hρ1 u₀) 1 := by
        rcases max_cases (wAloc p F ϖ hρ0 hρ1 (u - u₀)) (wAloc p F ϖ hρ0 hρ1 u₀)
          with ⟨heq, -⟩ | ⟨heq, -⟩
        · rw [heq]
          exact le_max_of_le_right hdiff
        · rw [heq]
          exact le_max_left _ _

end FarguesFontaine

end
