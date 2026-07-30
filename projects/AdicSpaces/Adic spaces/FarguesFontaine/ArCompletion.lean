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

/-- **`v(pᴺ) = ρᴺ` in `hatK`.** The Gauss value is multiplicative and `v(p) = ρ`, so a
power of `p` realises the corresponding power of `ρ` as a value.  Used wherever an element
of prescribed value is needed to cut out a ball. -/
private theorem valued_toHatK_p_pow {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℕ) :
    Valued.v (toHatK p F hρ0 hρ1 ((p : Ainf p F) ^ N)) = ρ ^ N := by
  rw [valued_toHatK]
  rw [show gaussValue p F ρ ((p : Ainf p F) ^ N)
    = (gaussValue p F ρ (p : Ainf p F)) ^ N from map_pow (gaussVal p F hρ0 hρ1) _ N]
  congr 1
  calc gaussValue p F ρ (p : Ainf p F)
      = gaussValue p F ρ ((p : Ainf p F) * 1) := by rw [mul_one]
    _ = ρ * gaussValue p F ρ 1 := gaussValue_p_mul p F hρ1.le 1
    _ = ρ := by rw [gaussValue_one p F hρ1.le, mul_one]

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
    rw [hz₀]
    exact valued_toHatK_p_pow p F hρ0 hρ1 N
  have hvz₀ne : Valued.v z₀ ≠ 0 := by
    rw [hvz₀]
    exact (pow_pos hρ0 N).ne'
  have hrne : (Valued.v).restrict z₀ ≠ 0 := by
    refine fun h0 => hvz₀ne ?_
    have := (Valuation.restrict_pos_iff (v := (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)) z₀)
    rcases eq_or_ne (Valued.v z₀) 0 with h | h
    · exact h
    · exact absurd (this.mpr (pos_iff_ne_zero.mpr h)) (by rw [h0]; exact lt_irrefl 0)
  set γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)))ˣ := Units.mk0 _ hrne with hγ
  have hcauchy : (nhds x) ×ˢ (nhds x) ≤ uniformity (hatK p F hρ0 hρ1) := cauchy_nhds.2
  have hball := (Valued.hasBasis_uniformity (hatK p F hρ0 hρ1) NNReal).mem_of_mem (i := γ) trivial
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
    exact Filter.eventually_comap.mpr (Filter.Eventually.mono hev (by
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
    have hcast : (Units.mk0 ((Valued.v).restrict z₀) hrne).1 = (Valued.v).restrict z₀ := rfl
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

/-- **Coordinates converge along approximants** (the T903 step-4 capstone): for
`x ∈ A^r`, the `n`-th Teichmüller coordinates of `Aloc`-approximants converge in `F`,
to `teichCoeffAr x n`. -/
theorem tendsto_teichCoeffAr {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (n : ℕ) :
    Filter.Tendsto (fun u => teichCoeffF p F (alocToWittF p F ϖ u) n)
      (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x))
      (nhds (teichCoeffAr p F ϖ hρ0 hρ1 x n)) := by
  haveI hne := neBot_comap_of_mem_ArSub p F ϖ hx
  haveI hcompl : CompleteSpace F := IsPerfectoidRing.complete (p := p) (A := F)
  haveI ht0 : T0Space F := IsPerfectoidRing.t0 (p := p) (A := F)
  haveI huag : IsUniformAddGroup F := IsPerfectoidRing.uniformAddGroup (p := p) (A := F)
  set L := Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x) with hL
  set coords : Aloc p F ϖ → F := fun u => teichCoeffF p F (alocToWittF p F ϖ u) n
    with hcoords
  -- value scale
  obtain ⟨B, hB⟩ := exists_eventually_wAloc_le p F ϖ (hρ0 := hρ0) (hρ1 := hρ1) hx
  set c : NNReal := perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
    with hc
  have hϖne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
    fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  have hc0 : 0 < c := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
  have hclt : c < 1 := perfectoidValuation_toOF_lt_one p F ϖ
  obtain ⟨M, hM⟩ : ∃ M : ℕ, B ≤ (c⁻¹) ^ M := by
    rcases eq_or_ne B 0 with rfl | hBne
    · exact ⟨0, zero_le⟩
    · obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (inv_pos.mpr
        (pos_iff_ne_zero.mpr hBne)) hclt
      refine ⟨M, ?_⟩
      rw [inv_pow]
      have h1 : B * c ^ M < 1 := by
        have h2 := mul_lt_mul_of_pos_left hM (pos_iff_ne_zero.mpr hBne)
        rwa [mul_inv_cancel₀ hBne] at h2
      exact le_of_lt ((NNReal.lt_inv_iff_mul_lt (pow_ne_zero M hc0.ne')).mpr h1)
  -- Cauchy of the coordinate filter
  have hcauchy : Cauchy (Filter.map coords L) := by
    refine ⟨hne.map _, ?_⟩
    rw [Filter.prod_map_map_eq]
    intro V hV
    rw [uniformity_eq_comap_nhds_zero F] at hV
    obtain ⟨W, hW, hWV⟩ := Filter.mem_comap.mp hV
    have htop := IsPerfectoidRing.topologyEq (p := p) (A := F)
    rw [htop] at hW
    obtain ⟨m, hmW⟩ := exists_ball_subset_nhds p F ϖ hW
    have hε0 : (0 : NNReal) < c ^ m := pow_pos hc0 m
    have hε1 : c ^ m ≤ 1 := pow_le_one₀ zero_le hclt.le
    obtain ⟨δ, hδ0, hδ⟩ := exists_delta_teichCoeffF_sub p F ϖ n hρ0 hρ1 M
      (ε := c ^ m) hε0 hε1
    have hpairs := eventually_pair_wAloc_le p F ϖ (hρ0 := hρ0) (hρ1 := hρ1) x
      (ε := δ) hδ0
    have hbounds : ∀ᶠ q in L ×ˢ L, wAloc p F ϖ hρ0 hρ1 q.1 ≤ B
        ∧ wAloc p F ϖ hρ0 hρ1 q.2 ≤ B := by
      exact Filter.Eventually.and (hB.prod_inl _) (hB.prod_inr _)
    refine Filter.mem_of_superset ((hpairs.and hbounds).mono ?_) hWV
    rintro ⟨u, u'⟩ ⟨hdiff, hbu, hbu'⟩
    refine hmW ?_
    have hkey := hδ (alocToWittF p F ϖ u') (alocToWittF p F ϖ u)
      (bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 u')
      (bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 u)
      (by
        rw [← map_sub]
        exact bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 (u' - u))
      (by
        rw [gaussValueF_alocToWittF p F ϖ hρ0 hρ1 u']
        exact hbu'.trans hM)
      (by
        rw [gaussValueF_alocToWittF p F ϖ hρ0 hρ1 u]
        exact hbu.trans hM)
      (by
        rw [← map_sub, gaussValueF_alocToWittF p F ϖ hρ0 hρ1 (u' - u)]
        exact hdiff)
    exact hkey
  -- conclude via completeness
  obtain ⟨y, hy⟩ := CompleteSpace.complete hcauchy
  have htop2 := IsPerfectoidRing.topologyEq (p := p) (A := F)
  rw [htop2] at hy
  have hty : Filter.Tendsto coords L (nhds y) := hy
  have heq : teichCoeffAr p F ϖ hρ0 hρ1 x n = y := by
    rw [teichCoeffAr]
    exact hty.limUnder_eq
  rw [heq]
  exact hty

/-- For `Valued.v x ≠ 0`, approximants eventually have value exactly `Valued.v x`
(ultrametric ball constancy, through the same value-group-free γ-mechanics as the
Cauchy core). -/
theorem eventually_wAloc_eq {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : Valued.v x ≠ 0) :
    ∀ᶠ u in Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x),
      wAloc p F ϖ hρ0 hρ1 u = Valued.v x := by
  have hrne : (Valued.v).restrict x ≠ 0 := by
    refine fun h0 => hx ?_
    rcases eq_or_ne (Valued.v x) 0 with h | h
    · exact h
    · have hpos := (Valuation.restrict_pos_iff (v := (Valued.v :
        Valuation (hatK p F hρ0 hρ1) NNReal)) x).mpr (pos_iff_ne_zero.mpr h)
      exact absurd hpos (by rw [h0]; exact lt_irrefl 0)
  set γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)))ˣ := Units.mk0 _ hrne with hγ
  have hball : {z : hatK p F hρ0 hρ1 |
      (Valued.v).restrict (z - x) < γ.1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    exact ⟨γ, fun z hz => hz⟩
  refine Filter.eventually_comap.mpr (Filter.Eventually.mono hball ?_)
  intro z hz u hu
  have hlt : Valued.v (z - x) < Valued.v x := by
    have h1 : (Valued.v).restrict (z - x) < (Valued.v).restrict x := hz
    exact (Valuation.restrict_lt_iff (v := (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal))).mp h1
  have hveq : Valued.v z = Valued.v x := by
    refine le_antisymm ?_ ?_
    · calc Valued.v z = Valued.v ((z - x) + x) := by rw [sub_add_cancel]
        _ ≤ max (Valued.v (z - x)) (Valued.v x) := Valuation.map_add _ _ _
        _ ≤ Valued.v x := max_le hlt.le le_rfl
    · by_contra hcon
      push Not at hcon
      have h2 : Valued.v x = Valued.v ((x - z) + z) := by rw [sub_add_cancel]
      have h3 : Valued.v (x - z) = Valued.v (z - x) := by
        rw [show x - z = -(z - x) from by ring, Valuation.map_neg]
      have h4 : Valued.v x ≤ max (Valued.v (x - z)) (Valued.v z) :=
        h2.le.trans (Valuation.map_add _ _ _)
      rw [h3] at h4
      rcases max_cases (Valued.v (z - x)) (Valued.v z) with ⟨heq, -⟩ | ⟨heq, -⟩
      · rw [heq] at h4
        exact absurd (lt_of_le_of_lt h4 hlt) (lt_irrefl _)
      · rw [heq] at h4
        exact absurd (lt_of_le_of_lt h4 hcon) (lt_irrefl _)
  rw [← valued_AlocToHatK p F ϖ hρ0 hρ1 u, hu]
  exact hveq

include ϖ in
/-- Closed valuation balls are closed in `F` (they are subgroups with nonempty
interior, hence open, hence closed). -/
theorem isClosed_ball {r : NNReal} (hr : 0 < r) :
    IsClosed {y : F | perfectoidValuation p F y ≤ r} := by
  set G : AddSubgroup F :=
    { carrier := {y : F | perfectoidValuation p F y ≤ r}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        have h1 : perfectoidValuation p F (a + b)
            ≤ max (perfectoidValuation p F a) (perfectoidValuation p F b) :=
          Valuation.map_add _ a b
        exact le_trans h1 (max_le ha hb)
      neg_mem' := fun {a} ha => by
        simpa only [Set.mem_setOf_eq, Valuation.map_neg] using ha } with hG
  have hopen : IsOpen (G : Set F) := by
    set c : NNReal := perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
      with hc
    have hϖne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
      fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
    have hc0 : 0 < c := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
    have hclt : c < 1 := perfectoidValuation_toOF_lt_one p F ϖ
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr hclt
    refine AddSubgroup.isOpen_of_mem_nhds G (g := 0) ?_
    refine Filter.mem_of_superset (ball_mem_nhds_zero p F ϖ m) ?_
    intro z hz
    exact le_trans hz (le_of_lt hm)
  exact (AddSubgroup.isClosed_of_isOpen G hopen)

/-- **Term bound on `A^r`** (half of Kedlaya's (2.2.1) on the completion): every
Gauss term of the limit coordinates is at most the completed-field value. -/
theorem gaussTerm_teichCoeffAr_le_of_ne_zero {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : Valued.v x ≠ 0)
    (n : ℕ) :
    ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n) ≤ Valued.v x := by
  haveI hne := neBot_comap_of_mem_ArSub p F ϖ hx
  set r : NNReal := Valued.v x * (ρ ^ n)⁻¹ with hr
  have hρn : (0 : NNReal) < ρ ^ n := pow_pos hρ0 n
  have hr0 : 0 < r := mul_pos (pos_iff_ne_zero.mpr hx0) (inv_pos.mpr hρn)
  have hρnr : ρ ^ n * r = Valued.v x := by
    rw [hr, mul_comm (Valued.v x) _, ← mul_assoc, mul_inv_cancel₀ hρn.ne', one_mul]
  have hev : ∀ᶠ u in Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x),
      perfectoidValuation p F (teichCoeffF p F (alocToWittF p F ϖ u) n)
        ∈ {s : NNReal | s ≤ r} := by
    refine (eventually_wAloc_eq p F ϖ (hρ0 := hρ0) (hρ1 := hρ1) hx0).mono fun u hu => ?_
    have h2 := gaussTermF_alocToWittF_le p F ϖ hρ0 hρ1 u n
    rw [hu] at h2
    rw [gaussTermF] at h2
    have h3 : ρ ^ n * perfectoidValuation p F (teichCoeffF p F (alocToWittF p F ϖ u) n)
        ≤ ρ ^ n * r := by
      rw [hρnr]
      exact h2
    exact le_of_mul_le_mul_left h3 hρn
  have hball : teichCoeffAr p F ϖ hρ0 hρ1 x n
      ∈ {y : F | perfectoidValuation p F y ≤ r} := by
    refine (isClosed_ball p F ϖ hr0).mem_of_tendsto
      (tendsto_teichCoeffAr p F ϖ hx n) ?_
    exact hev
  have h4 : perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n) ≤ r := hball
  calc ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
      ≤ ρ ^ n * r := mul_le_mul_of_nonneg_left h4 zero_le
    _ = Valued.v x := hρnr

/-- Teichmüller lifts of arbitrary `F`-elements inside `Aloc` (choose a Tate
absorption `c·ϖ^k ∈ O_F` and divide the Teichmüller lift back by `[ϖ]^k`). -/
def alocTeich (c : F) : Aloc p F ϖ :=
  IsLocalization.mk' (Aloc p F ϖ)
    (WittVector.teichmuller p
      (⟨c * ((ϖ.val : Fˣ) : F) ^ (exists_mul_pow_isPowerBounded p F ϖ c).choose,
        (exists_mul_pow_isPowerBounded p F ϖ c).choose_spec⟩ : OF F))
    (⟨teichPi p F ϖ ^ (exists_mul_pow_isPowerBounded p F ϖ c).choose,
      (exists_mul_pow_isPowerBounded p F ϖ c).choose, rfl⟩ :
        Submonoid.powers (teichPi p F ϖ))

/-- In `W(F)`, `alocTeich c` really is the Teichmüller lift of `c`. -/
theorem alocToWittF_alocTeich (c : F) :
    alocToWittF p F ϖ (alocTeich p F ϖ c) = WittVector.teichmuller p c := by
  set k := (exists_mul_pow_isPowerBounded p F ϖ c).choose with hk
  set a : OF F := ⟨c * ((ϖ.val : Fˣ) : F) ^ k,
    (exists_mul_pow_isPowerBounded p F ϖ c).choose_spec⟩ with ha
  set y : Submonoid.powers (teichPi p F ϖ) :=
    ⟨teichPi p F ϖ ^ k, k, rfl⟩ with hy
  have hϖne : (((ϖ.val : Fˣ) : F)) ≠ 0 := (ϖ.val : Fˣ).ne_zero
  -- multiply through by the denominator and compare in W(F)
  have hspec : alocTeich p F ϖ c * algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F)
      = algebraMap (Ainf p F) (Aloc p F ϖ) (WittVector.teichmuller p a) := by
    rw [alocTeich]
    exact IsLocalization.mk'_spec (Aloc p F ϖ) _ _
  have happ := congrArg (alocToWittF p F ϖ) hspec
  rw [map_mul, alocToWittF_algebraMap, alocToWittF_algebraMap] at happ
  have hyW : WittVector.map ((powerBoundedSubring.toSubring F).subtype)
      ((y : Ainf p F)) = WittVector.teichmuller p (((ϖ.val : Fˣ) : F) ^ k) := by
    have hy' : (y : Ainf p F) = teichPi p F ϖ ^ k := rfl
    rw [hy', map_pow]
    have hone : WittVector.map ((powerBoundedSubring.toSubring F).subtype)
        (teichPi p F ϖ) = WittVector.teichmuller p (((ϖ.val : Fˣ) : F)) := by
      rw [show teichPi p F ϖ = WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ)
        from rfl, WittVector.map_teichmuller]
      rfl
    rw [hone, ← map_pow]
  have haW : WittVector.map ((powerBoundedSubring.toSubring F).subtype)
      (WittVector.teichmuller p a) = WittVector.teichmuller p
        (c * ((ϖ.val : Fˣ) : F) ^ k) := by
    rw [WittVector.map_teichmuller]
    rfl
  rw [hyW, haW] at happ
  -- cancel the Teichmüller unit [ϖ^k]
  have hunit : IsUnit (WittVector.teichmuller p (((ϖ.val : Fˣ) : F) ^ k)) := by
    have hne2 : ((ϖ.val : Fˣ) : F) ^ k ≠ 0 := pow_ne_zero _ hϖne
    refine ⟨Units.mkOfMulEqOne _ (WittVector.teichmuller p ((((ϖ.val : Fˣ) : F) ^ k)⁻¹))
      ?_, rfl⟩
    rw [← map_mul, mul_inv_cancel₀ hne2, map_one]
  have hgoal : alocToWittF p F ϖ (alocTeich p F ϖ c) *
      WittVector.teichmuller p (((ϖ.val : Fˣ) : F) ^ k)
      = WittVector.teichmuller p c *
        WittVector.teichmuller p (((ϖ.val : Fˣ) : F) ^ k) := by
    rw [happ, ← map_mul]
  exact hunit.mul_right_cancel hgoal

/-- The value of `alocTeich c` is `|c|`. -/
theorem wAloc_alocTeich {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (c : F) :
    wAloc p F ϖ hρ0 hρ1 (alocTeich p F ϖ c) = perfectoidValuation p F c := by
  set k := (exists_mul_pow_isPowerBounded p F ϖ c).choose with hkdef
  set a : OF F := ⟨c * ((ϖ.val : Fˣ) : F) ^ k,
    (exists_mul_pow_isPowerBounded p F ϖ c).choose_spec⟩ with hadef
  set y : Submonoid.powers (teichPi p F ϖ) :=
    ⟨teichPi p F ϖ ^ k, k, rfl⟩ with hydef
  set cϖ : NNReal := perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
    with hcϖ
  have hϖne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
    fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  have hcϖ0 : 0 < cϖ := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
  have hspec : alocTeich p F ϖ c * algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F)
      = algebraMap (Ainf p F) (Aloc p F ϖ) (WittVector.teichmuller p a) := by
    rw [alocTeich]
    exact IsLocalization.mk'_spec (Aloc p F ϖ) _ _
  have happ := congrArg (wAloc p F ϖ hρ0 hρ1) hspec
  rw [map_mul, wAloc_algebraMap, wAloc_algebraMap] at happ
  have hyval : gaussValue p F ρ (y : Ainf p F) = cϖ ^ k := by
    have hy' : (y : Ainf p F) = teichPi p F ϖ ^ k := rfl
    rw [hy', show gaussValue p F ρ (teichPi p F ϖ ^ k)
      = (gaussValue p F ρ (teichPi p F ϖ)) ^ k from map_pow (gaussVal p F hρ0 hρ1) _ k,
      show teichPi p F ϖ = WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ)
        from rfl, gaussValue_teichmuller p F hρ1.le]
  have haval : gaussValue p F ρ (WittVector.teichmuller p a)
      = perfectoidValuation p F c * cϖ ^ k := by
    rw [gaussValue_teichmuller p F hρ1.le]
    have hacoe : ((a : OF F) : F) = c * ((ϖ.val : Fˣ) : F) ^ k := rfl
    rw [hacoe, Valuation.map_mul, map_pow]
    rfl
  rw [hyval, haval] at happ
  exact mul_right_cancel₀ (pow_pos hcϖ0 k).ne' happ

/-- **Powers of `p` shrink the Gauss value geometrically.** A Witt vector coming from
`O_F` has all Gauss terms `≤ 1`, and multiplying by `p` scales the Gauss value by `ρ`; so
`pᴹ · w` has Gauss value at most `ρᴹ`.  Proved by induction on `M`, carrying the
boundedness alongside since `gaussValueF_p_mul` needs it. -/
private theorem gaussValueF_p_pow_mul_map_le {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (z : WittVector p (OF F)) (M : ℕ) :
    BddAbove (Set.range (gaussTermF p F ρ ((p : WittVector p F) ^ M *
        WittVector.map ((powerBoundedSubring.toSubring F).subtype) z)))
      ∧ gaussValueF p F ρ ((p : WittVector p F) ^ M *
          WittVector.map ((powerBoundedSubring.toSubring F).subtype) z) ≤ ρ ^ M := by
  have hBz : BddAbove (Set.range (gaussTermF p F ρ
      (WittVector.map ((powerBoundedSubring.toSubring F).subtype) z))) := by
    refine ⟨1, ?_⟩
    rintro s ⟨m, rfl⟩
    rw [gaussTermF_map]
    exact gaussTerm_le_one p F hρ1.le z m
  have hzval : gaussValueF p F ρ
      (WittVector.map ((powerBoundedSubring.toSubring F).subtype) z) ≤ 1 := by
    rw [gaussValueF_map]
    exact gaussValue_le_one p F hρ1.le z
  induction M with
  | zero => exact ⟨by simpa using hBz, by simpa using hzval⟩
  | succ m ihm =>
    obtain ⟨ihB, ihv⟩ := ihm
    have hsplit : (p : WittVector p F) ^ (m + 1) *
        WittVector.map ((powerBoundedSubring.toSubring F).subtype) z
        = (p : WittVector p F) * ((p : WittVector p F) ^ m *
          WittVector.map ((powerBoundedSubring.toSubring F).subtype) z) := by
      ring
    refine ⟨by rw [hsplit]; exact bddAbove_gaussTermF_p_mul p F ihB, ?_⟩
    rw [hsplit, gaussValueF_p_mul p F ihB, pow_succ, mul_comm (ρ ^ m) ρ]
    exact mul_le_mul_of_nonneg_left ihv zero_le

include ϖ in
/-- **The scaled difference is a `p^N`-tail.** With `u · [ϖ♭]^k = A` in `A_inf` and `t`
the length-`N` Teichmüller prefix built from `A`'s coordinates rescaled by `ϖ_F^{-k}`,
multiplying `u − t` by `[ϖ_F^k]` lands exactly on `pᴺ` times an integral Witt vector: the
two images agree except in the tail of `A`'s Teichmüller expansion.

This is the algebraic half of `exists_finite_teichmuller_sum_close`; the analytic half only
has to bound that tail. -/
private theorem alocToWittF_sub_prefix_mul_teich {A : Ainf p F}
    {y : ↥(Submonoid.powers (teichPi p F ϖ))} {u : Aloc p F ϖ} {k N : ℕ} {z : Ainf p F}
    (hu : u * algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F)
      = algebraMap (Ainf p F) (Aloc p F ϖ) A)
    (hk' : teichPi p F ϖ ^ k = (y : Ainf p F))
    (hz : A = (∑ i ∈ Finset.range N,
        WittVector.teichmuller p (teichCoeff p F A i) * (p : Ainf p F) ^ i)
      + (p : Ainf p F) ^ N * z) :
    alocToWittF p F ϖ (u - ∑ n ∈ Finset.range N, (p : Aloc p F ϖ) ^ n *
          alocTeich p F ϖ (((teichCoeff p F A n : OF F) : F)
            * ((((ϖ.val : Fˣ) : F)) ^ k)⁻¹))
        * WittVector.teichmuller p ((((ϖ.val : Fˣ) : F)) ^ k)
      = (p : WittVector p F) ^ N *
        WittVector.map ((powerBoundedSubring.toSubring F).subtype) z := by
  set ϖFk : F := (((ϖ.val : Fˣ) : F)) ^ k with hϖFk
  set b : ℕ → F := fun n =>
    ((teichCoeff p F A n : OF F) : F) * (ϖFk)⁻¹ with hb
  set t : Aloc p F ϖ := ∑ n ∈ Finset.range N,
    (p : Aloc p F ϖ) ^ n * alocTeich p F ϖ (b n) with ht
  have hϖFkne : ϖFk ≠ 0 := pow_ne_zero _ (ϖ.val : Fˣ).ne_zero
  have himgu : alocToWittF p F ϖ u *
      WittVector.teichmuller p ϖFk
      = WittVector.map ((powerBoundedSubring.toSubring F).subtype) A := by
    have happ := congrArg (alocToWittF p F ϖ) hu
    rw [map_mul, alocToWittF_algebraMap, alocToWittF_algebraMap] at happ
    have hyW : WittVector.map ((powerBoundedSubring.toSubring F).subtype)
        ((y : Ainf p F)) = WittVector.teichmuller p ϖFk := by
      have hy' : (y : Ainf p F) = teichPi p F ϖ ^ k := hk'.symm
      rw [hy', map_pow]
      have hone : WittVector.map ((powerBoundedSubring.toSubring F).subtype)
          (teichPi p F ϖ) = WittVector.teichmuller p (((ϖ.val : Fˣ) : F)) := by
        rw [show teichPi p F ϖ = WittVector.teichmuller p (PseudoUniformizer.toOF F ϖ)
          from rfl, WittVector.map_teichmuller]
        rfl
      rw [hone, ← map_pow]
    rw [hyW] at happ
    exact happ
  have himgt : alocToWittF p F ϖ t * WittVector.teichmuller p ϖFk
      = ∑ n ∈ Finset.range N, (p : WittVector p F) ^ n *
          WittVector.teichmuller p (((teichCoeff p F A n : OF F) : F)) := by
    rw [ht, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_pow, alocToWittF_alocTeich, map_natCast]
    rw [mul_assoc, ← map_mul]
    congr 2
    rw [hb]
    field_simp
  rw [map_sub, sub_mul, himgu, himgt]
  have hmapA : WittVector.map ((powerBoundedSubring.toSubring F).subtype) A
      = (∑ n ∈ Finset.range N, (p : WittVector p F) ^ n *
          WittVector.teichmuller p (((teichCoeff p F A n : OF F) : F)))
        + (p : WittVector p F) ^ N *
          WittVector.map ((powerBoundedSubring.toSubring F).subtype) z := by
    conv_lhs => rw [hz]
    rw [map_add, map_sum, map_mul, map_pow, map_natCast]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun n _ => ?_) rfl
    rw [map_mul, WittVector.map_teichmuller, map_pow, map_natCast]
    rw [mul_comm]
    rfl
  rw [hmapA]
  ring

/-- **Finite-Teichmüller-sum density**: every `Aloc`-element is `wAloc`-approximated
by finite sums `Σ_{n<N} pⁿ·alocTeich(bₙ)` — the tails of the numerator's Teichmüller
expansion are `ρᴺ`-small, uniformly scaled by the denominator. -/
theorem exists_finite_teichmuller_sum_close {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (u : Aloc p F ϖ) {ε : NNReal} (hε : 0 < ε) :
    ∃ (N : ℕ) (b : ℕ → F),
      wAloc p F ϖ hρ0 hρ1 (u - ∑ n ∈ Finset.range N,
        (p : Aloc p F ϖ) ^ n * alocTeich p F ϖ (b n)) ≤ ε := by
  obtain ⟨⟨A, y⟩, hu⟩ := IsLocalization.surj (M := Submonoid.powers (teichPi p F ϖ)) u
  change u * algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F)
    = algebraMap (Ainf p F) (Aloc p F ϖ) A at hu
  obtain ⟨k, hk⟩ := y.2
  have hk' : teichPi p F ϖ ^ k = (y : Ainf p F) := hk
  set cϖ : NNReal := perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
    with hcϖ
  have hϖne : ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 :=
    fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  have hcϖ0 : 0 < cϖ := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
  -- choose N with (cϖ⁻¹)^k · ρ^N ≤ ε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (mul_pos hε (pow_pos hcϖ0 k)) hρ1
  set b : ℕ → F := fun n =>
    ((teichCoeff p F A n : OF F) : F) * ((((ϖ.val : Fˣ) : F)) ^ k)⁻¹ with hb
  refine ⟨N, b, ?_⟩
  set t : Aloc p F ϖ := ∑ n ∈ Finset.range N,
    (p : Aloc p F ϖ) ^ n * alocTeich p F ϖ (b n) with ht
  set ϖFk : F := (((ϖ.val : Fˣ) : F)) ^ k with hϖFk
  have hϖFkne : ϖFk ≠ 0 := pow_ne_zero _ (ϖ.val : Fˣ).ne_zero
  -- the W(F)-image of the difference, times [ϖF^k], is the p^N-tail of A
  obtain ⟨z, hz⟩ := exists_eq_sum_teichCoeff_add p F A N
  have hdiffW := alocToWittF_sub_prefix_mul_teich p F ϖ hu hk' hz
  -- values: cancel cϖ^k and bound the tail
  have hval : wAloc p F ϖ hρ0 hρ1 (u - t) * cϖ ^ k ≤ ρ ^ N := by
    have h1 : gaussValueF p F ρ ((alocToWittF p F ϖ (u - t)) *
        WittVector.teichmuller p ϖFk)
        = cϖ ^ k * gaussValueF p F ρ (alocToWittF p F ϖ (u - t)) := by
      rw [mul_comm (alocToWittF p F ϖ (u - t)) _, gaussValueF_teichmuller_mul]
      congr 1
      rw [hϖFk, map_pow]
      rfl
    have h2 : gaussValueF p F ρ ((p : WittVector p F) ^ N *
        WittVector.map ((powerBoundedSubring.toSubring F).subtype) z) ≤ ρ ^ N := by
      exact (gaussValueF_p_pow_mul_map_le p F hρ0 hρ1 z N).2
    have h3 := congrArg (gaussValueF p F ρ) hdiffW
    rw [h1] at h3
    rw [← gaussValueF_alocToWittF p F ϖ hρ0 hρ1 (u - t)]
    calc gaussValueF p F ρ (alocToWittF p F ϖ (u - t)) * cϖ ^ k
        = cϖ ^ k * gaussValueF p F ρ (alocToWittF p F ϖ (u - t)) := mul_comm _ _
      _ = gaussValueF p F ρ ((p : WittVector p F) ^ N *
            WittVector.map ((powerBoundedSubring.toSubring F).subtype) z) := h3
      _ ≤ ρ ^ N := h2
  have hεc : ρ ^ N < ε * cϖ ^ k := hN
  have hfinal : wAloc p F ϖ hρ0 hρ1 (u - t) * cϖ ^ k ≤ ε * cϖ ^ k :=
    hval.trans hεc.le
  exact le_of_mul_le_mul_right hfinal (pow_pos hcϖ0 k)

/-- Finite Teichmüller prefix sums in `Aloc` (the c₀-architecture's building blocks). -/
def prefixAloc (b : ℕ → F) (N : ℕ) : Aloc p F ϖ :=
  ∑ n ∈ Finset.range N, (p : Aloc p F ϖ) ^ n * alocTeich p F ϖ (b n)

theorem alocToWittF_prefixAloc (b : ℕ → F) (N : ℕ) :
    alocToWittF p F ϖ (prefixAloc p F ϖ b N)
      = ∑ n ∈ Finset.range N,
          WittVector.teichmuller p (b n) * (p : WittVector p F) ^ n := by
  rw [prefixAloc, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, map_pow, map_natCast, alocToWittF_alocTeich, mul_comm]

/-- Coordinates of prefix sums are the given coefficients. -/
theorem teichCoeffF_prefixAloc (b : ℕ → F) {N j : ℕ} (hj : j < N) :
    teichCoeffF p F (alocToWittF p F ϖ (prefixAloc p F ϖ b N)) j = b j := by
  rw [alocToWittF_prefixAloc]
  have h0 : (∑ n ∈ Finset.range N,
      WittVector.teichmuller p (b n) * (p : WittVector p F) ^ n)
      = (∑ n ∈ Finset.range N,
          WittVector.teichmuller p (b n) * (p : WittVector p F) ^ n)
        + (p : WittVector p F) ^ N * 0 := by
    rw [mul_zero, add_zero]
  rw [h0]
  exact teichCoeffF_sum_range_add p F b 0 hj

/-- **Prefix values are exact finite maxima** — the isometry identity on the dense
layer of the c₀ architecture. -/
theorem wAloc_prefixAloc {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (b : ℕ → F) (N : ℕ) :
    wAloc p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N)
      = (Finset.range N).sup (fun n => ρ ^ n * perfectoidValuation p F (b n)) := by
  rw [← gaussValueF_alocToWittF p F ϖ hρ0 hρ1, alocToWittF_prefixAloc]
  have hpiece : ∀ n : ℕ,
      BddAbove (Set.range (gaussTermF p F ρ
        (WittVector.teichmuller p (b n) * (p : WittVector p F) ^ n)))
      ∧ gaussValueF p F ρ (WittVector.teichmuller p (b n) * (p : WittVector p F) ^ n)
        = ρ ^ n * perfectoidValuation p F (b n) := by
    intro n
    constructor
    · rw [mul_comm]
      exact bddAbove_gaussTermF_p_pow_mul p F
        (bddAbove_gaussTermF_teichmuller p F (b n)) n
    · rw [mul_comm, gaussValueF_p_pow_mul p F
        (bddAbove_gaussTermF_teichmuller p F (b n)) n, gaussValueF_teichmuller]
  have hsum := gaussValueF_finset_sum_le p F hρ0 hρ1
    ((Finset.range N).sup (fun n => ρ ^ n * perfectoidValuation p F (b n)))
    (Finset.range N)
    (fun n => WittVector.teichmuller p (b n) * (p : WittVector p F) ^ n)
    (fun n hn => ⟨(hpiece n).1, by
      rw [(hpiece n).2]
      exact Finset.le_sup (f := fun m => ρ ^ m * perfectoidValuation p F (b m)) hn⟩)
  refine le_antisymm hsum.2 ?_
  refine Finset.sup_le fun n hn => ?_
  have hterm : gaussTermF p F ρ (∑ m ∈ Finset.range N,
      WittVector.teichmuller p (b m) * (p : WittVector p F) ^ m) n
      = ρ ^ n * perfectoidValuation p F (b n) := by
    rw [gaussTermF]
    congr 1
    have h0 : (∑ m ∈ Finset.range N,
        WittVector.teichmuller p (b m) * (p : WittVector p F) ^ m)
        = (∑ m ∈ Finset.range N,
            WittVector.teichmuller p (b m) * (p : WittVector p F) ^ m)
          + (p : WittVector p F) ^ N * 0 := by
      rw [mul_zero, add_zero]
    rw [h0, teichCoeffF_sum_range_add p F b 0 (Finset.mem_range.mp hn)]
  rw [← hterm]
  exact gaussTermF_le_gaussValueF p F hsum.1 n

/-- `wAloc` scales by `ρ` under multiplication by `p` (through the `W(F)`-side). -/
theorem wAloc_p_pow_mul {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (n : ℕ)
    (u : Aloc p F ϖ) :
    wAloc p F ϖ hρ0 hρ1 ((p : Aloc p F ϖ) ^ n * u)
      = ρ ^ n * wAloc p F ϖ hρ0 hρ1 u := by
  rw [← gaussValueF_alocToWittF p F ϖ hρ0 hρ1, map_mul, map_pow, map_natCast,
    gaussValueF_p_pow_mul p F (bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 u) n,
    gaussValueF_alocToWittF p F ϖ hρ0 hρ1]

/-- Cauchy criterion for sequences in the completed field, in plain `NNReal` terms
(the value-group γ-balls are reached through the strict-mono embedding). -/
theorem cauchySeq_of_valued_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (s : ℕ → hatK p F hρ0 hρ1)
    (h : ∀ ε : NNReal, 0 < ε → ∃ N₀ : ℕ, ∀ m n : ℕ, N₀ ≤ m → N₀ ≤ n →
      Valued.v (s m - s n) ≤ ε) :
    CauchySeq s := by
  rw [(Valued.hasBasis_uniformity (hatK p F hρ0 hρ1) NNReal).cauchySeq_iff]
  rintro γ -
  have hγpos : (0 : NNReal) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    refine pos_iff_ne_zero.mpr fun h0 => ?_
    have hinj := (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      (f := MonoidWithZeroHom.ofClass (Valued.v :
        Valuation (hatK p F hρ0 hρ1) NNReal))).injective
    have h00 : MonoidWithZeroHom.ValueGroup₀.embedding (0 :
        MonoidWithZeroHom.ValueGroup₀ (MonoidWithZeroHom.ofClass (Valued.v :
          Valuation (hatK p F hρ0 hρ1) NNReal))) = 0 := map_zero _
    have := hinj (h0.trans h00.symm)
    exact γ.ne_zero this
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hγpos hρ1
  obtain ⟨N₀, hN₀⟩ := h (ρ ^ K) (pow_pos hρ0 K)
  refine ⟨N₀, fun m hm n hn => ?_⟩
  have hle := hN₀ n m hn hm
  have hlt : Valued.v (s n - s m) < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 :=
    lt_of_le_of_lt hle hK
  have hres : (Valued.v).restrict (s n - s m) < γ.1 := by
    have hsm := MonoidWithZeroHom.ValueGroup₀.embedding_strictMono
      (f := MonoidWithZeroHom.ofClass (Valued.v :
        Valuation (hatK p F hρ0 hρ1) NNReal))
    refine hsm.lt_iff_lt.mp ?_
    rw [Valuation.embedding_restrict]
    exact hlt
  exact hres

/-- Segments of prefix sums factor as `p^N`-shifts of shifted prefixes. -/
theorem prefixAloc_sub (b : ℕ → F) {N M : ℕ} (hNM : N ≤ M) :
    prefixAloc p F ϖ b M - prefixAloc p F ϖ b N
      = (p : Aloc p F ϖ) ^ N * prefixAloc p F ϖ (fun j => b (N + j)) (M - N) := by
  rw [prefixAloc, prefixAloc, prefixAloc, ← Finset.sum_Ico_eq_sub _ hNM,
    Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_add]
  ring

/-- **Prefix images are Cauchy** for decaying coefficient sequences. -/
theorem cauchySeq_prefix_image {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F}
    (hb : Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F (b n))
      Filter.atTop (nhds 0)) :
    CauchySeq (fun N => AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N)) := by
  refine cauchySeq_of_valued_le p F _ fun ε hε => ?_
  have hev : ∀ᶠ n in Filter.atTop, ρ ^ n * perfectoidValuation p F (b n) < ε :=
    hb.eventually_lt_const hε
  obtain ⟨N₀, hN₀'⟩ := Filter.eventually_atTop.mp hev
  have hN₀ : ∀ n, N₀ ≤ n → ρ ^ n * perfectoidValuation p F (b n) ≤ ε :=
    fun n hn => (hN₀' n hn).le
  refine ⟨N₀, fun m n hm hn => ?_⟩
  -- by symmetry reduce to n ≤ m
  have key : ∀ {a c : ℕ}, N₀ ≤ a → N₀ ≤ c → c ≤ a →
      Valued.v (AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b a)
        - AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b c)) ≤ ε := by
    intro a c _ hc hca
    rw [← map_sub, valued_AlocToHatK, prefixAloc_sub p F ϖ b hca,
      wAloc_p_pow_mul p F ϖ hρ0 hρ1, wAloc_prefixAloc p F ϖ hρ0 hρ1]
    rcases Nat.eq_zero_or_pos (a - c) with hz | hpos
    · rw [hz]
      simp
    · obtain ⟨j, hjmem, hjeq⟩ := Finset.exists_mem_eq_sup (Finset.range (a - c))
        (Finset.nonempty_range_iff.mpr hpos.ne')
        (fun j => ρ ^ j * perfectoidValuation p F (b (c + j)))
      rw [hjeq, ← mul_assoc, ← pow_add]
      exact hN₀ (c + j) (le_trans hc (Nat.le_add_right c j))
  rcases le_total n m with hnm | hmn
  · exact key hm hn hnm
  · have h := key hn hm hmn
    rw [← Valuation.map_neg, neg_sub] at h
    exact h

/-- **The c₀-parametrization** `Φ`: the limit in `hatK` of the prefix images of a
decaying coefficient sequence. -/
def PhiHatK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (b : ℕ → F) :
    hatK p F hρ0 hρ1 :=
  Filter.limUnder Filter.atTop
    (fun N => AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N))

/-- The prefix images converge to `Φ b`. -/
theorem tendsto_PhiHatK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F}
    (hb : Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F (b n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun N => AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N))
      Filter.atTop (nhds (PhiHatK p F ϖ hρ0 hρ1 b)) := by
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_prefix_image p F ϖ hρ0 hρ1 hb)
  have heq : PhiHatK p F ϖ hρ0 hρ1 b = y := by
    rw [PhiHatK]
    exact hy.limUnder_eq
  rw [heq]
  exact hy

/-- `Φ b` lies in `A^r`. -/
theorem PhiHatK_mem_ArSub {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F}
    (hb : Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F (b n))
      Filter.atTop (nhds 0)) :
    PhiHatK p F ϖ hρ0 hρ1 b ∈ ArSub p F ϖ hρ0 hρ1 := by
  have hmem : ∀ N, AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N)
      ∈ (ArSub p F ϖ hρ0 hρ1 : Set (hatK p F hρ0 hρ1)) := fun N =>
    (AlocToHatK p F ϖ hρ0 hρ1).range.le_topologicalClosure ⟨prefixAloc p F ϖ b N, rfl⟩
  exact (Subring.isClosed_topologicalClosure
    (AlocToHatK p F ϖ hρ0 hρ1).range).mem_of_tendsto
    (tendsto_PhiHatK p F ϖ hρ0 hρ1 hb) (Filter.Eventually.of_forall hmem)

/-- Vanishing `NNReal` sequences have bounded range. -/
theorem bddAbove_range_of_tendsto_zero {f : ℕ → NNReal}
    (hf : Filter.Tendsto f Filter.atTop (nhds 0)) :
    BddAbove (Set.range f) := by
  obtain ⟨K₀, hK₀⟩ := Filter.eventually_atTop.mp (hf.eventually_lt_const one_pos)
  refine ⟨max 1 ((Finset.range (K₀ + 1)).sup f), ?_⟩
  rintro s ⟨n, rfl⟩
  rcases lt_or_ge n (K₀ + 1) with hn | hn
  · exact le_max_of_le_right (Finset.le_sup (Finset.mem_range.mpr hn))
  · exact le_max_of_le_left (hK₀ n (by omega)).le

include ϖ in
/-- **If the reconstruction vanishes, so does every scaled coordinate.** Suppose
`Φ b = 0`. If some term `ρⁿ·|bₙ|` were positive, pick `K` with `ρᴷ` below it; the partial
sums converge to `0`, so eventually `‖s_N‖ < ρᴷ` — yet `‖s_N‖` is a sup over `range N`
that already contains that term once `N > n`. Contradiction. -/
private theorem ciSup_gaussTerm_eq_zero_of_valued_PhiHatK_eq_zero {ρ : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F}
    (hb : Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F (b n))
      Filter.atTop (nhds 0))
    (h0 : Valued.v (PhiHatK p F ϖ hρ0 hρ1 b) = 0) :
    (0 : NNReal) = ⨆ n, ρ ^ n * perfectoidValuation p F (b n) := by
  set s : ℕ → hatK p F hρ0 hρ1 := fun N => AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N) with hs
  have hsval : ∀ N, Valued.v (s N)
      = (Finset.range N).sup (fun n => ρ ^ n * perfectoidValuation p F (b n)) := by
    intro N
    rw [hs, valued_AlocToHatK, wAloc_prefixAloc]
  have htendsto := tendsto_PhiHatK p F ϖ hρ0 hρ1 hb
  refine ((ciSup_le fun n => ?_).antisymm zero_le).symm
  by_contra hpos
  push Not at hpos
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hpos hρ1
  -- eventually v (s N) < ρ^K < term n, but term n ≤ v (s N) for N > n
  have hz : Valued.v (PhiHatK p F ϖ hρ0 hρ1 b) ≠ 0 → False := fun h => h h0
  have hzero : PhiHatK p F ϖ hρ0 hρ1 b = 0 := by
    by_contra hΦ
    exact hΦ ((Valuation.zero_iff (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)).mp h0)
  rw [hzero] at htendsto
  -- γ-ball at 0 with e-value ρ^K
  set z₀ : hatK p F hρ0 hρ1 := toHatK p F hρ0 hρ1 ((p : Ainf p F) ^ K) with hz₀
  have hvz₀ : Valued.v z₀ = ρ ^ K := by
    rw [hz₀]
    exact valued_toHatK_p_pow p F hρ0 hρ1 K
  have hrne : (Valued.v).restrict z₀ ≠ 0 := by
    refine fun hr0 => ?_
    have hpos2 := (Valuation.restrict_pos_iff (v := (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)) z₀).mpr
      (by rw [hvz₀]; exact pow_pos hρ0 K)
    exact absurd hpos2 (by rw [hr0]; exact lt_irrefl 0)
  have hball : {z : hatK p F hρ0 hρ1 |
      (Valued.v).restrict z < (Units.mk0 _ hrne : (MonoidWithZeroHom.ValueGroup₀
        (.ofClass (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)))ˣ).1}
      ∈ nhds (0 : hatK p F hρ0 hρ1) := by
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 _ hrne, fun z hz => ?_⟩
    simpa using hz
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (htendsto.eventually hball)
  have hcontr := hN₂ (max N₂ (n + 1)) (le_max_left _ _)
  have hvlt : Valued.v (s (max N₂ (n + 1))) < ρ ^ K := by
    have h1 : (Valued.v).restrict (s (max N₂ (n + 1))) < (Valued.v).restrict z₀ :=
      hcontr
    have h2 := (Valuation.restrict_lt_iff (v := (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal))).mp h1
    rwa [hvz₀] at h2
  have hterm_le : ρ ^ n * perfectoidValuation p F (b n)
      ≤ Valued.v (s (max N₂ (n + 1))) := by
    rw [hsval]
    exact Finset.le_sup (f := fun m => ρ ^ m * perfectoidValuation p F (b m))
      (Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)))
  exact absurd (lt_of_le_of_lt hterm_le hvlt) (not_lt.mpr hK.le)

/-- **The isometry identity for `Φ`**: the value of `Φ b` is the sup of the terms. -/
theorem valued_PhiHatK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F}
    (hb : Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F (b n))
      Filter.atTop (nhds 0)) :
    Valued.v (PhiHatK p F ϖ hρ0 hρ1 b)
      = ⨆ n, ρ ^ n * perfectoidValuation p F (b n) := by
  set s : ℕ → hatK p F hρ0 hρ1 :=
    fun N => AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N) with hs
  have hsval : ∀ N, Valued.v (s N)
      = (Finset.range N).sup (fun n => ρ ^ n * perfectoidValuation p F (b n)) := by
    intro N
    rw [hs, valued_AlocToHatK, wAloc_prefixAloc]
  have hBterms : BddAbove (Set.range
      (fun n => ρ ^ n * perfectoidValuation p F (b n))) :=
    bddAbove_range_of_tendsto_zero hb
  have htendsto := tendsto_PhiHatK p F ϖ hρ0 hρ1 hb
  rcases eq_or_ne (Valued.v (PhiHatK p F ϖ hρ0 hρ1 b)) 0 with h0 | hne
  · rw [h0]
    exact ciSup_gaussTerm_eq_zero_of_valued_PhiHatK_eq_zero p F ϖ hρ0 hρ1 hb h0
  · -- nonzero case: v(s N) is eventually exactly v(Φ b)
    have hball2 : {z : hatK p F hρ0 hρ1 |
        Valued.v (z - PhiHatK p F ϖ hρ0 hρ1 b) < Valued.v (PhiHatK p F ϖ hρ0 hρ1 b)}
        ∈ nhds (PhiHatK p F ϖ hρ0 hρ1 b) := by
      have hrne : (Valued.v).restrict (PhiHatK p F ϖ hρ0 hρ1 b) ≠ 0 := by
        refine fun hr0 => ?_
        have hpos2 := (Valuation.restrict_pos_iff (v := (Valued.v :
          Valuation (hatK p F hρ0 hρ1) NNReal)) _).mpr (pos_iff_ne_zero.mpr hne)
        exact absurd hpos2 (by rw [hr0]; exact lt_irrefl 0)
      rw [Valued.mem_nhds]
      refine ⟨Units.mk0 _ hrne, fun z hz => ?_⟩
      have h1 : (Valued.v).restrict (z - PhiHatK p F ϖ hρ0 hρ1 b)
          < (Valued.v).restrict (PhiHatK p F ϖ hρ0 hρ1 b) := hz
      exact (Valuation.restrict_lt_iff (v := (Valued.v :
        Valuation (hatK p F hρ0 hρ1) NNReal))).mp h1
    obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.mp (htendsto.eventually hball2)
    have hveq : ∀ N, N₃ ≤ N → Valued.v (s N) = Valued.v (PhiHatK p F ϖ hρ0 hρ1 b) := by
      intro N hN
      have hlt := hN₃ N hN
      have hdecomp : s N = PhiHatK p F ϖ hρ0 hρ1 b
          + (s N - PhiHatK p F ϖ hρ0 hρ1 b) := by ring
      rw [hdecomp]
      exact Valuation.map_add_eq_of_lt_left _ hlt
    refine le_antisymm ?_ ?_
    · rw [← hveq N₃ le_rfl, hsval]
      refine Finset.sup_le fun n hn => ?_
      exact le_ciSup hBterms n
    · refine ciSup_le fun n => ?_
      rw [← hveq (max N₃ (n + 1)) (le_max_left _ _), hsval]
      exact Finset.le_sup (f := fun m => ρ ^ m * perfectoidValuation p F (b m))
        (Finset.mem_range.mpr (lt_of_lt_of_le (Nat.lt_succ_self n) (le_max_right _ _)))

/-- **`Aloc`-images decay geometrically**: the Gauss terms of `alocToWittF u` are
bounded by `ρⁿ·c^{-k}` for the `[ϖ]^k`-denominator of `u`, hence tend to `0`. -/
theorem tendsto_gaussTermF_alocToWittF {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (u : Aloc p F ϖ) :
    Filter.Tendsto (gaussTermF p F ρ (alocToWittF p F ϖ u)) Filter.atTop (nhds 0) := by
  obtain ⟨⟨a, y⟩, hu⟩ := IsLocalization.surj (M := Submonoid.powers (teichPi p F ϖ)) u
  change u * algebraMap (Ainf p F) (Aloc p F ϖ) (y : Ainf p F)
    = algebraMap (Ainf p F) (Aloc p F ϖ) a at hu
  obtain ⟨k, hk⟩ := y.2
  have hk' : teichPi p F ϖ ^ k = (y : Ainf p F) := hk
  set ϖF : F := ((PseudoUniformizer.toOF F ϖ : OF F) : F) with hϖF
  set c : NNReal := perfectoidValuation p F ϖF with hc
  have hϖne : ϖF ≠ 0 := fun h => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h)
  have hc0 : 0 < c := pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr hϖne)
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
  have hbound : ∀ n, gaussTermF p F ρ (alocToWittF p F ϖ u) n ≤ ρ ^ n * (c ^ k)⁻¹ := by
    intro n
    have hterm : gaussTermF p F ρ (alocToWittF p F ϖ u) n * c ^ k
        = gaussTerm p F ρ a n := by
      have h1 := gaussTermF_teichmuller_mul p F (ρ := ρ) (w := ϖF ^ k)
        (s := alocToWittF p F ϖ u) n
      rw [mul_comm (WittVector.teichmuller p (ϖF ^ k)) _] at h1
      rw [himg, gaussTermF_map, map_pow] at h1
      rw [h1]
      ring
    have hle : gaussTermF p F ρ (alocToWittF p F ϖ u) n * c ^ k
        ≤ (ρ ^ n * (c ^ k)⁻¹) * c ^ k := by
      rw [hterm, mul_assoc, inv_mul_cancel₀ (pow_pos hc0 k).ne', mul_one, gaussTerm]
      calc ρ ^ n * perfectoidValuation p F ((teichCoeff p F a n : OF F) : F)
          ≤ ρ ^ n * 1 := mul_le_mul_of_nonneg_left
            (perfectoidValuation_le_one p F (teichCoeff p F a n)) zero_le
        _ = ρ ^ n := mul_one _
    exact le_of_mul_le_mul_right hle (pow_pos hc0 k)
  have hgeo : Filter.Tendsto (fun n => ρ ^ n * (c ^ k)⁻¹) Filter.atTop (nhds 0) := by
    have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one (zero_le : (0 : NNReal) ≤ ρ)
      hρ1).mul_const ((c ^ k)⁻¹)
    rwa [zero_mul] at h1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hgeo
    (fun n => zero_le) hbound

/-- **Closed value balls are neighbourhoods.** For every `ε > 0`, the set
`{z | v (z - x) ≤ ε}` is a neighbourhood of `x`. The witness is `v(pᴺ) = ρᴺ < ε`: it is a
nonzero element of the value group, so the open ball it cuts out sits inside the closed
`ε`-ball. -/
theorem valued_ball_mem_nhds {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (x : hatK p F hρ0 hρ1) {ε : NNReal} (hε : 0 < ε) :
    {z : hatK p F hρ0 hρ1 | Valued.v (z - x) ≤ ε} ∈ nhds x := by
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hρ1
  set z₀ : hatK p F hρ0 hρ1 := toHatK p F hρ0 hρ1 ((p : Ainf p F) ^ N) with hz₀
  have hvz₀ : Valued.v z₀ = ρ ^ N := by
    rw [hz₀]
    exact valued_toHatK_p_pow p F hρ0 hρ1 N
  have hvz₀ne : Valued.v z₀ ≠ 0 := by
    rw [hvz₀]
    exact (pow_pos hρ0 N).ne'
  have hrne : (Valued.v).restrict z₀ ≠ 0 := by
    refine fun h0 => hvz₀ne ?_
    rcases eq_or_ne (Valued.v z₀) 0 with h | h
    · exact h
    · exact absurd ((Valuation.restrict_pos_iff (v := (Valued.v :
        Valuation (hatK p F hρ0 hρ1) NNReal)) z₀).mpr (pos_iff_ne_zero.mpr h))
        (by rw [h0]; exact lt_irrefl 0)
  set γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal)))ˣ := Units.mk0 _ hrne with hγ
  have hball : {z : hatK p F hρ0 hρ1 |
      (Valued.v).restrict (z - x) < γ.1} ∈ nhds x := by
    rw [Valued.mem_nhds]
    exact ⟨γ, fun z hz => hz⟩
  refine Filter.mem_of_superset hball ?_
  intro z hz
  have hcast : (Units.mk0 ((Valued.v).restrict z₀) hrne).1
      = (Valued.v).restrict z₀ := rfl
  rw [Set.mem_setOf_eq, hγ, hcast] at hz
  have hlt : Valued.v (z - x) < Valued.v z₀ :=
    (Valuation.restrict_lt_iff (v := (Valued.v :
      Valuation (hatK p F hρ0 hρ1) NNReal))).mp hz
  rw [hvz₀] at hlt
  exact le_of_lt (lt_of_lt_of_le hlt hN.le)

/-- Approximants are eventually within any prescribed value of their target. -/
theorem eventually_valued_sub_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    (x : hatK p F hρ0 hρ1) {ε : NNReal} (hε : 0 < ε) :
    ∀ᶠ u in Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x),
      Valued.v (AlocToHatK p F ϖ hρ0 hρ1 u - x) ≤ ε :=
  Filter.eventually_comap.mpr
    (Filter.Eventually.mono (valued_ball_mem_nhds p F x hε)
      fun _ hz _ hu => by rw [hu]; exact hz)

/-- **Limit coordinates decay** (the decay-closure crux applied to `A^r`): for every
`x ∈ A^r` the scaled limit coordinates `ρⁿ·|xₙ|` tend to `0`. The proof perturbs a
single `ε`-close approximant `u₀`: uniformly over closer approximants `u`,
`T_n(u) ≤ max(T_n(u₀), H_n(u₀), ε)` by the moving-prefix estimate, and the bound
passes to the coordinate limits through closed valuation balls. -/
theorem tendsto_gaussTerm_teichCoeffAr {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) :
    Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 x n)) Filter.atTop (nhds 0) := by
  haveI hne := neBot_comap_of_mem_ArSub p F ϖ hx
  rw [tendsto_order]
  constructor
  · intro a ha
    simp at ha
  · intro a ha
    obtain ⟨b, hb0, hba⟩ := exists_between ha
    have hev := eventually_valued_sub_le p F ϖ (hρ0 := hρ0) (hρ1 := hρ1) x hb0
    obtain ⟨u₀, hu₀⟩ := hev.exists
    set w₀ := alocToWittF p F ϖ u₀ with hw₀
    have hdec₀ := tendsto_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 u₀
    have hB₀ := bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 u₀
    have hT₀ := tendsto_tailValueF_of_tendsto p F (σ := ρ) hdec₀
    have hH₀ := tendsto_headBoundF_of_tendsto p F hρ0 hρ1 hdec₀
    obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp (hT₀.eventually_lt_const hb0)
    obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp (hH₀.eventually_lt_const hb0)
    refine Filter.eventually_atTop.mpr ⟨max N₁ N₂, fun n hn => ?_⟩
    have hN₁n : N₁ ≤ n := le_trans (le_max_left _ _) hn
    have hN₂n : N₂ ≤ n := le_trans (le_max_right _ _) hn
    set r : NNReal := max (max (tailValueF p F ρ w₀ n) (headBoundF p F ρ w₀ n)) b
      with hr
    have hra : r < a :=
      max_lt (max_lt (lt_trans (hN₁ n hN₁n) hba) (lt_trans (hN₂ n hN₂n) hba)) hba
    have hr0 : 0 < r := lt_of_lt_of_le hb0 (le_max_right _ _)
    have hρn : (0 : NNReal) < ρ ^ n := pow_pos hρ0 n
    -- eventually, approximant coordinates at index n sit in the closed r-ball
    have hevn : ∀ᶠ u in Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x),
        teichCoeffF p F (alocToWittF p F ϖ u) n
          ∈ {s : F | perfectoidValuation p F s ≤ (ρ ^ n)⁻¹ * r} := by
      refine hev.mono fun u hu => ?_
      have hwAloc : wAloc p F ϖ hρ0 hρ1 (u - u₀) ≤ b := by
        rw [← valued_AlocToHatK p F ϖ hρ0 hρ1 (u - u₀), map_sub]
        have h1 : AlocToHatK p F ϖ hρ0 hρ1 u - AlocToHatK p F ϖ hρ0 hρ1 u₀
            = (AlocToHatK p F ϖ hρ0 hρ1 u - x) - (AlocToHatK p F ϖ hρ0 hρ1 u₀ - x) := by
          ring
        rw [h1]
        exact le_trans (Valuation.map_sub _ _ _) (max_le hu hu₀)
      have hval : gaussValueF p F ρ (alocToWittF p F ϖ u - w₀) ≤ b := by
        rw [hw₀, ← map_sub, gaussValueF_alocToWittF p F ϖ hρ0 hρ1 (u - u₀)]
        exact hwAloc
      have hBdiff : BddAbove (Set.range (gaussTermF p F ρ (alocToWittF p F ϖ u - w₀))) := by
        rw [hw₀, ← map_sub]
        exact bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 (u - u₀)
      have hBu := bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 u
      have hsplit : alocToWittF p F ϖ u = w₀ + (alocToWittF p F ϖ u - w₀) := by ring
      have hterm : gaussTermF p F ρ (alocToWittF p F ϖ u) n
          ≤ tailValueF p F ρ (alocToWittF p F ϖ u) n :=
        gaussTermF_le_tailValueF p F hBu n
      have htail : tailValueF p F ρ (alocToWittF p F ϖ u) n ≤ r := by
        conv_lhs => rw [hsplit]
        refine le_trans (tailValueF_add_le_gaussValueF p F hρ0 hρ1 hB₀ hBdiff n) ?_
        exact max_le_max le_rfl hval
      have h2 : ρ ^ n * perfectoidValuation p F
          (teichCoeffF p F (alocToWittF p F ϖ u) n) ≤ r := by
        rw [show ρ ^ n * perfectoidValuation p F
            (teichCoeffF p F (alocToWittF p F ϖ u) n)
          = gaussTermF p F ρ (alocToWittF p F ϖ u) n from rfl]
        exact hterm.trans htail
      have h3 : ρ ^ n * perfectoidValuation p F
          (teichCoeffF p F (alocToWittF p F ϖ u) n) ≤ ρ ^ n * ((ρ ^ n)⁻¹ * r) := by
        rw [← mul_assoc, mul_inv_cancel₀ hρn.ne', one_mul]
        exact h2
      exact le_of_mul_le_mul_left h3 hρn
    have hball : teichCoeffAr p F ϖ hρ0 hρ1 x n
        ∈ {s : F | perfectoidValuation p F s ≤ (ρ ^ n)⁻¹ * r} := by
      refine (isClosed_ball p F ϖ (mul_pos (inv_pos.mpr hρn) hr0)).mem_of_tendsto
        (tendsto_teichCoeffAr p F ϖ hx n) hevn
    have h4 : perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
        ≤ (ρ ^ n)⁻¹ * r := hball
    calc ρ ^ n * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n)
        ≤ ρ ^ n * ((ρ ^ n)⁻¹ * r) := mul_le_mul_of_nonneg_left h4 zero_le
      _ = r := by rw [← mul_assoc, mul_inv_cancel₀ hρn.ne', one_mul]
      _ < a := hra

/-- Values along any convergent filter are eventually within any prescribed bound. -/
theorem eventually_valued_sub_le_of_tendsto {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {ι : Type*} {l : Filter ι} {g : ι → hatK p F hρ0 hρ1} {y : hatK p F hρ0 hρ1}
    (hg : Filter.Tendsto g l (nhds y)) {ε : NNReal} (hε : 0 < ε) :
    ∀ᶠ i in l, Valued.v (g i - y) ≤ ε :=
  hg.eventually (valued_ball_mem_nhds p F y hε)

include ϖ in
/-- **A single Teichmüller piece is small.** If `[a] − [b]` already has Gauss value at
most `ε`, then so does `pⁱ · ([a] − [b])` for every `i`: multiplying by `pⁱ` scales the
Gauss value by `ρ ^ i ≤ 1`. This is what makes the prefix bound uniform in the index. -/
private theorem gaussValueF_p_pow_teichmuller_sub_le {ρ : NNReal} (hρ1 : ρ < 1)
    {ε : NNReal} (a b : F) (i : ℕ)
    (hHo : gaussValueF p F ρ
      (WittVector.teichmuller p a - WittVector.teichmuller p b) ≤ ε) :
    BddAbove (Set.range (gaussTermF p F ρ ((p : WittVector p F) ^ i *
        (WittVector.teichmuller p a - WittVector.teichmuller p b))))
      ∧ gaussValueF p F ρ ((p : WittVector p F) ^ i *
        (WittVector.teichmuller p a - WittVector.teichmuller p b)) ≤ ε := by
  have hBsub := bddAbove_gaussTermF_teichmuller_sub p F hρ1 ϖ a b
  refine ⟨bddAbove_gaussTermF_p_pow_mul p F hBsub i, ?_⟩
  rw [gaussValueF_p_pow_mul p F hBsub i]
  calc ρ ^ i * gaussValueF p F ρ
        (WittVector.teichmuller p a - WittVector.teichmuller p b)
      ≤ 1 * ε := mul_le_mul (pow_le_one₀ zero_le hρ1.le) hHo zero_le zero_le
    _ = ε := one_mul _

/-- **Every `NNReal` is dominated by a power of `c⁻¹`** when `0 < c < 1`, and that power
can be taken `≥ 1`. Used to cap a finite sup of coordinate values by a single scale, so
that one Hölder modulus works uniformly across the prefix. -/
private theorem exists_le_inv_pow {c : NNReal} (hc0 : 0 < c) (hc1 : c < 1) (s : NNReal) :
    ∃ m : ℕ, s ≤ (c⁻¹) ^ m ∧ (1 : NNReal) ≤ (c⁻¹) ^ m := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, s ≤ (c⁻¹) ^ m := by
    rcases eq_or_ne s 0 with h0 | hne0
    · exact ⟨0, by rw [h0]; exact zero_le⟩
    · obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
        (inv_pos.mpr (pos_iff_ne_zero.mpr hne0)) hc1
      refine ⟨m, ?_⟩
      rw [inv_pow]
      have h1 : s * c ^ m < 1 := by
        have h2 := mul_lt_mul_of_pos_left hm (pos_iff_ne_zero.mpr hne0)
        rwa [mul_inv_cancel₀ hne0] at h2
      exact le_of_lt ((NNReal.lt_inv_iff_mul_lt (pow_ne_zero m hc0.ne')).mpr h1)
  refine ⟨m, hm, ?_⟩
  rw [inv_pow]
  calc (1 : NNReal) = c ^ m * (c ^ m)⁻¹ :=
        (mul_inv_cancel₀ (pow_ne_zero m hc0.ne')).symm
    _ ≤ 1 * (c ^ m)⁻¹ := mul_le_mul_of_nonneg_right
        (pow_le_one₀ zero_le hc1.le) zero_le
    _ = (c ^ m)⁻¹ := one_mul _

/-- **Squeeze to zero in `hatK`**: two elements whose difference has value below every
positive bound are equal. The valuation is `NNReal`-valued, so halving the (nonzero)
value would contradict the hypothesis at that smaller bound. -/
private theorem eq_of_forall_valued_sub_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {a b : hatK p F hρ0 hρ1} (h : ∀ ε : NNReal, 0 < ε → Valued.v (a - b) ≤ ε) : a = b := by
  have hzero : Valued.v (a - b) = 0 := by
    by_contra hne0
    exact absurd (lt_of_le_of_lt (h _ (div_pos (pos_iff_ne_zero.mpr hne0) two_pos))
      (NNReal.half_lt_self hne0)) (lt_irrefl _)
  exact sub_eq_zero.mp ((Valuation.zero_iff (Valued.v :
    Valuation (hatK p F hρ0 hρ1) NNReal)).mp hzero)

include ϖ in
/-- **A Witt vector is close to the prefix of a nearby coordinate sequence.** If `w`'s
tail beyond `N` has Gauss value at most `ε`, and each of its first `N` Teichmüller
coordinates is within `ε` of `b`'s, then `w` differs from the `b`-prefix
`∑_{i<N} [b i]·pⁱ` by at most `ε`.

Split `w − Pb = (w − Pw) + (Pw − Pb)`: the first summand is exactly the tail, and the
second is a finite sum of the per-coordinate pieces, so the ultrametric max of the two
bounds is `ε`. -/
private theorem gaussValueF_sub_teich_prefix_le {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {ε : NNReal} (w : WittVector p F) (b : ℕ → F) (N : ℕ)
    (hBu : BddAbove (Set.range (gaussTermF p F ρ w)))
    (htail : tailValueF p F ρ w N ≤ ε)
    (hHo : ∀ i ∈ Finset.range N, gaussValueF p F ρ
      (WittVector.teichmuller p (teichCoeffF p F w i)
        - WittVector.teichmuller p (b i)) ≤ ε) :
    gaussValueF p F ρ (w - ∑ i ∈ Finset.range N,
      WittVector.teichmuller p (b i) * (p : WittVector p F) ^ i) ≤ ε := by
  set PbW := ∑ i ∈ Finset.range N,
    WittVector.teichmuller p (b i) * (p : WittVector p F) ^ i with hPbW
  set PuW := ∑ i ∈ Finset.range N,
    WittVector.teichmuller p (teichCoeffF p F w i) * (p : WittVector p F) ^ i
    with hPuW
  have htail_id : gaussValueF p F ρ (w - PuW) = tailValueF p F ρ w N :=
    gaussValueF_sub_prefix p F hρ0 hBu N
  obtain ⟨X, hX, hXc⟩ := exists_iter_splitF p F w N
  have hBt : BddAbove (Set.range (gaussTermF p F ρ (w - PuW))) := by
    rw [show w - PuW = (p : WittVector p F) ^ N * X from sub_eq_iff_eq_add'.mpr hX]
    exact bddAbove_gaussTermF_p_pow_mul p F
      (bddAbove_gaussTermF_of_coords_shift p F hρ0 hXc hBu) N
  have hsum := gaussValueF_finset_sum_le p F hρ0 hρ1 ε (Finset.range N)
    (fun i => (p : WittVector p F) ^ i *
      (WittVector.teichmuller p (teichCoeffF p F w i)
        - WittVector.teichmuller p (b i)))
    (fun i hi => gaussValueF_p_pow_teichmuller_sub_le p F ϖ hρ1
      (teichCoeffF p F w i) (b i) i (hHo i hi))
  have hdistrib : PuW - PbW = ∑ i ∈ Finset.range N,
      (p : WittVector p F) ^ i * (WittVector.teichmuller p (teichCoeffF p F w i)
        - WittVector.teichmuller p (b i)) := by
    rw [hPuW, hPbW, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [show w - PbW = (w - PuW) + (PuW - PbW) from by ring]
  refine le_trans (gaussValueF_add_le p F hρ0 hρ1 hBt
    (by rw [hdistrib]; exact hsum.1)) ?_
  refine max_le ?_ (by rw [hdistrib]; exact hsum.2)
  rw [htail_id]
  exact htail

/-- **A three-term ultrametric chain.** If `a → s → t → z` are each within `ε`, so is
`a → z`: the valuation of a sum is at most the max of the summands' valuations. -/
private theorem valued_sub_le_of_chain {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {a s t z : hatK p F hρ0 hρ1} {ε : NNReal} (h1 : Valued.v (a - s) ≤ ε)
    (h2 : Valued.v (s - t) ≤ ε) (h3 : Valued.v (t - z) ≤ ε) : Valued.v (a - z) ≤ ε := by
  rw [show a - z = (a - s) + ((s - t) + (t - z)) from by ring]
  exact le_trans (Valuation.map_add _ _ _)
    (max_le h1 (le_trans (Valuation.map_add _ _ _) (max_le h2 h3)))

include ϖ in
/-- **Approximants eventually match the limit coordinates.** Each limit coordinate is the
limit of the approximants' coordinates, so on any finite index range the approximants are
eventually uniformly `δ`-close to them. -/
private theorem eventually_teichCoeffF_sub_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (N : ℕ) {δ : NNReal}
    (hδ0 : 0 < δ) :
    ∀ᶠ u in Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x),
      ∀ i ∈ Finset.range N, perfectoidValuation p F
        (teichCoeffF p F (alocToWittF p F ϖ u) i
          - teichCoeffAr p F ϖ hρ0 hρ1 x i) ≤ δ := by
  have hball : {z : F | perfectoidValuation p F z ≤ δ} ∈ nhds (0 : F) := by
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hδ0
      (perfectoidValuation_toOF_lt_one p F ϖ)
    exact Filter.mem_of_superset (ball_mem_nhds_zero p F ϖ k)
      fun z hz => le_trans hz hk.le
  rw [Filter.eventually_all_finset]
  intro i _
  have ht2 := (tendsto_teichCoeffAr p F ϖ hx i).sub_const
    (teichCoeffAr p F ϖ hρ0 hρ1 x i)
  rw [sub_self] at ht2
  exact ht2.eventually hball

include ϖ in
/-- **A base approximant and a working index.** Picks an approximant `u₀` within `ε` of
`x`, then an index `N` past both its tail- and head-bound decay thresholds at which the
`Φ`-partial sums are also within `ε` of `Φ b`. The five facts are needed together, so they
are chosen together. -/
private theorem exists_base_approx_and_index {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} {b : ℕ → F} {ε : NNReal} (hεpos : 0 < ε)
    [(Filter.comap (AlocToHatK p F ϖ hρ0 hρ1) (nhds x)).NeBot]
    (hΦ : Filter.Tendsto (fun N => AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N))
      Filter.atTop (nhds (PhiHatK p F ϖ hρ0 hρ1 b))) :
    ∃ (u₀ : Aloc p F ϖ) (N : ℕ),
      Valued.v (AlocToHatK p F ϖ hρ0 hρ1 u₀ - x) ≤ ε ∧
      BddAbove (Set.range (gaussTermF p F ρ (alocToWittF p F ϖ u₀))) ∧
      tailValueF p F ρ (alocToWittF p F ϖ u₀) N ≤ ε ∧
      headBoundF p F ρ (alocToWittF p F ϖ u₀) N ≤ ε ∧
      Valued.v (AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N)
        - PhiHatK p F ϖ hρ0 hρ1 b) ≤ ε := by
  obtain ⟨u₀, hu₀⟩ :=
    (eventually_valued_sub_le p F ϖ (hρ0 := hρ0) (hρ1 := hρ1) x hεpos).exists
  have hdec₀ := tendsto_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 u₀
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_tailValueF_of_tendsto p F (σ := ρ) hdec₀).eventually_lt_const hεpos)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    ((tendsto_headBoundF_of_tendsto p F hρ0 hρ1 hdec₀).eventually_lt_const hεpos)
  obtain ⟨N, hΦN, hNge⟩ :=
    ((eventually_valued_sub_le_of_tendsto p F (hρ0 := hρ0) (hρ1 := hρ1) hΦ hεpos).and
      (Filter.eventually_ge_atTop (max N₁ N₂))).exists
  exact ⟨u₀, N, hu₀, bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 u₀,
    (hN₁ N (le_trans (le_max_left _ _) hNge)).le,
    (hN₂ N (le_trans (le_max_right _ _) hNge)).le, hΦN⟩

include ϖ in
/-- **The late approximant inherits the base approximant's tail bound.** Two approximants
each within `ε` of `x` have Witt vectors differing by at most `ε` in Gauss value, so the
late one's tail past `N` is controlled by the base one's tail, its head bound, and that
difference — all three `≤ ε`. -/
private theorem tailValueF_alocToWittF_le {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} {ε : NNReal} {u₀ u : Aloc p F ϖ} (N : ℕ)
    (hu₀ : Valued.v (AlocToHatK p F ϖ hρ0 hρ1 u₀ - x) ≤ ε)
    (hux : Valued.v (AlocToHatK p F ϖ hρ0 hρ1 u - x) ≤ ε)
    (hB₀ : BddAbove (Set.range (gaussTermF p F ρ (alocToWittF p F ϖ u₀))))
    (htail₀ : tailValueF p F ρ (alocToWittF p F ϖ u₀) N ≤ ε)
    (hhead₀ : headBoundF p F ρ (alocToWittF p F ϖ u₀) N ≤ ε) :
    tailValueF p F ρ (alocToWittF p F ϖ u) N ≤ ε := by
  have hval : gaussValueF p F ρ
      (alocToWittF p F ϖ u - alocToWittF p F ϖ u₀) ≤ ε := by
    rw [← map_sub, gaussValueF_alocToWittF p F ϖ hρ0 hρ1 (u - u₀),
      ← valued_AlocToHatK p F ϖ hρ0 hρ1 (u - u₀), map_sub,
      show AlocToHatK p F ϖ hρ0 hρ1 u - AlocToHatK p F ϖ hρ0 hρ1 u₀
        = (AlocToHatK p F ϖ hρ0 hρ1 u - x)
          - (AlocToHatK p F ϖ hρ0 hρ1 u₀ - x) from by ring]
    exact le_trans (Valuation.map_sub _ _ _) (max_le hux hu₀)
  have hBdiff : BddAbove (Set.range (gaussTermF p F ρ
      (alocToWittF p F ϖ u - alocToWittF p F ϖ u₀))) := by
    rw [← map_sub]
    exact bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 (u - u₀)
  conv_lhs => rw [show alocToWittF p F ϖ u = alocToWittF p F ϖ u₀
    + (alocToWittF p F ϖ u - alocToWittF p F ϖ u₀) from by ring]
  exact le_trans (tailValueF_add_le_gaussValueF p F hρ0 hρ1 hB₀ hBdiff N)
    (max_le (max_le htail₀ hhead₀) hval)

include ϖ in
/-- The pseudo-uniformizer has nonzero perfectoid valuation. -/
private theorem perfectoidValuation_toOF_pos :
    0 < perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) :=
  pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr fun h =>
    PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext h))

include ϖ in
/-- **A uniform Hölder modulus on a prefix.** For a coordinate sequence `b` and a cutoff
`N` there is `δ > 0` such that *any* Witt vector whose first `N` coordinates are within
`δ` of `b`'s has all the corresponding Teichmüller differences of Gauss value at most `ε`.

Uniformity is the point: the first `N` values of `b` are capped by a single power of
`|ϖ|⁻¹` (`exists_le_inv_pow`), and `gaussValueF_teichmuller_sub_le_of_le_scaled` supplies a
modulus at that one scale, so the same `δ` works for every index below `N`. -/
private theorem exists_holder_modulus_on_range {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (b : ℕ → F) (N : ℕ) {ε : NNReal} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ : NNReal, 0 < δ ∧ ∀ w : WittVector p F,
      (∀ i ∈ Finset.range N, perfectoidValuation p F
        (teichCoeffF p F w i - b i) ≤ δ) →
      ∀ i ∈ Finset.range N, gaussValueF p F ρ
        (WittVector.teichmuller p (teichCoeffF p F w i)
          - WittVector.teichmuller p (b i)) ≤ ε := by
  obtain ⟨m, hm, hcap1⟩ := exists_le_inv_pow (perfectoidValuation_toOF_pos p F ϖ)
    (perfectoidValuation_toOF_lt_one p F ϖ)
    ((Finset.range N).sup (fun i => perfectoidValuation p F (b i)))
  obtain ⟨δ, hδ0, hδ⟩ :=
    gaussValueF_teichmuller_sub_le_of_le_scaled p F hρ0 hρ1 ϖ m hε0 hε1
  refine ⟨min δ 1, lt_min hδ0 one_pos, fun w hclose i hi => ?_⟩
  have hbcap := le_trans
    (Finset.le_sup (f := fun i => perfectoidValuation p F (b i)) hi) hm
  refine hδ _ _ ?_ hbcap (le_trans (hclose i hi) (min_le_left δ 1))
  rw [show teichCoeffF p F w i = (teichCoeffF p F w i - b i) + b i from by ring]
  exact le_trans (Valuation.map_add _ _ _)
    (max_le (le_trans (hclose i hi) (le_trans (min_le_right δ 1) hcap1)) hbcap)

/-- **The `ε`-estimate behind `PhiHatK_teichCoeffAr`**: the reconstruction
`Φ(teichCoeffAr x)` differs from `x` by less than every positive bound.

The argument picks a base approximant `u₀` fixing decay thresholds, a working index
`N` past them, a cap and a Hölder modulus for the first `N` coordinates, and finally a
late approximant `u` that is simultaneously `ε`-close to `x` and coordinatewise close
to the limit coordinates; a three-term ultrametric chain then bounds `Φ(b) − x`. -/
private theorem valued_PhiHatK_teichCoeffAr_sub_le {ρ : NNReal} {hρ0 : 0 < ρ}
    {hρ1 : ρ < 1} {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1)
    (ε : NNReal) (hεpos : 0 < ε) :
    Valued.v (PhiHatK p F ϖ hρ0 hρ1 (teichCoeffAr p F ϖ hρ0 hρ1 x) - x) ≤ ε := by
  haveI hne := neBot_comap_of_mem_ArSub p F ϖ hx
  set b : ℕ → F := teichCoeffAr p F ϖ hρ0 hρ1 x with hb
  have hbdec := tendsto_gaussTerm_teichCoeffAr p F ϖ hx
  rw [← hb] at hbdec
  have hΦ := tendsto_PhiHatK p F ϖ hρ0 hρ1 hbdec
  set ε' : NNReal := min ε 1 with hε'def
  have hε'0 : 0 < ε' := lt_min hεpos one_pos
  have hε'1 : ε' ≤ 1 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  -- a base approximant and a working index past its decay thresholds
  obtain ⟨u₀, N, hu₀, hB₀, htail₀, hhead₀, hΦN⟩ :=
    exists_base_approx_and_index p F ϖ (x := x) hε'0 hΦ
  have hev := eventually_valued_sub_le p F ϖ (hρ0 := hρ0) (hρ1 := hρ1) x hε'0
  -- a Hölder modulus that works uniformly across the first N coordinates
  obtain ⟨δ', hδ'0, hHospec⟩ :=
    exists_holder_modulus_on_range p F ϖ hρ0 hρ1 b N hε'0 hε'1
  -- eventual coordinate closeness at every i < N
  have hcoordAll := eventually_teichCoeffF_sub_le p F ϖ hx N hδ'0
  -- the late approximant
  obtain ⟨u, hux, hucoord⟩ := (hev.and hcoordAll).exists
  set wu := alocToWittF p F ϖ u with hwu
  have hBu := bddAbove_gaussTermF_alocToWittF p F ϖ hρ0 hρ1 u
  have htailu : tailValueF p F ρ wu N ≤ ε' :=
    tailValueF_alocToWittF_le p F ϖ N hu₀ hux hB₀ htail₀ hhead₀
  have hHo := hHospec wu hucoord
  set PbW := ∑ i ∈ Finset.range N,
    WittVector.teichmuller p (b i) * (p : WittVector p F) ^ i with hPbW
  have hwuPb : gaussValueF p F ρ (wu - PbW) ≤ ε' :=
    gaussValueF_sub_teich_prefix_le p F ϖ hρ0 hρ1 wu b N hBu htailu hHo
  -- back to hatK, then the three-term ultrametric chain
  refine le_trans (valued_sub_le_of_chain p F
    (s := AlocToHatK p F ϖ hρ0 hρ1 (prefixAloc p F ϖ b N))
    (t := AlocToHatK p F ϖ hρ0 hρ1 u) ?_ ?_ hux) hε'ε
  · rw [Valuation.map_sub_swap]
    exact hΦN
  · rw [Valuation.map_sub_swap, ← map_sub, valued_AlocToHatK,
      ← gaussValueF_alocToWittF p F ϖ hρ0 hρ1, map_sub, alocToWittF_prefixAloc]
    exact hwuPb

/-- **The series realization** (T903 step 5; Kedlaya (2.2.1) on the completion,
existence direction): every element of `A^r` is `Φ` of its limit coordinates,
`x = Σₙ pⁿ·[xₙ]`. The quantitative core compares, for one late approximant `u`,
the prefix of its own coordinates (exact tail identity), the prefix of the limit
coordinates (finitely many scaled Hölder moduli), and the `Φ`-partial sums. -/
theorem PhiHatK_teichCoeffAr {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) :
    PhiHatK p F ϖ hρ0 hρ1 (teichCoeffAr p F ϖ hρ0 hρ1 x) = x :=
  eq_of_forall_valued_sub_le p F (valued_PhiHatK_teichCoeffAr_sub_le p F ϖ hx)

/-- **The value formula on `A^r`** (Kedlaya (2.2.1) on the completion): the value of
any element of `A^r` is the sup of its scaled coordinate values. -/
theorem valued_eq_iSup_teichCoeffAr {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) :
    Valued.v x = ⨆ n, ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 x n) := by
  conv_lhs => rw [← PhiHatK_teichCoeffAr p F ϖ hx]
  exact valued_PhiHatK p F ϖ hρ0 hρ1 (tendsto_gaussTerm_teichCoeffAr p F ϖ hx)

/-- **`wAr`** — the Gauss valuation on the completed ring `A^r`, the restriction of
the completed-field valuation to the closure subring (Kedlaya Definition 2.4 on the
completion). -/
def wAr {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Valuation (ArSub p F ϖ hρ0 hρ1) NNReal :=
  (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal).comap
    ((ArSub p F ϖ hρ0 hρ1).subtype)

@[simp]
theorem wAr_apply {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (z : ArSub p F ϖ hρ0 hρ1) :
    wAr p F ϖ hρ0 hρ1 z = Valued.v (z : hatK p F hρ0 hρ1) :=
  rfl

/-- **Attainment on `A^r`** (the degree exists, Kedlaya Definition 2.4): a nonzero
element attains its value at some coordinate, and that coordinate dominates all
others. -/
theorem exists_valued_eq_teichCoeffAr {ρ : NNReal} {hρ0 : 0 < ρ} {hρ1 : ρ < 1}
    {x : hatK p F hρ0 hρ1} (hx : x ∈ ArSub p F ϖ hρ0 hρ1) (hx0 : x ≠ 0) :
    ∃ n₀, Valued.v x = ρ ^ n₀ * perfectoidValuation p F
        (teichCoeffAr p F ϖ hρ0 hρ1 x n₀)
      ∧ ∀ m, ρ ^ m * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x m)
        ≤ ρ ^ n₀ * perfectoidValuation p F (teichCoeffAr p F ϖ hρ0 hρ1 x n₀) := by
  have hv := valued_eq_iSup_teichCoeffAr p F ϖ hx
  have hvne : Valued.v x ≠ 0 :=
    (Valuation.ne_zero_iff (Valued.v : Valuation (hatK p F hρ0 hρ1) NNReal)).mpr hx0
  obtain ⟨n₀, hn₀, hmax⟩ := exists_iSup_eq_of_tendsto_zero
    (tendsto_gaussTerm_teichCoeffAr p F ϖ hx) (by rw [← hv]; exact hvne)
  exact ⟨n₀, by rw [hv, hn₀], hmax⟩

/-- **Coordinate recovery for `Φ`**: the limit coordinates of a `Φ`-series are the
input coefficients (prefix approximants are eventually coordinate-constant). -/
theorem teichCoeffAr_PhiHatK {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) {b : ℕ → F}
    (hb : Filter.Tendsto (fun n => ρ ^ n * perfectoidValuation p F (b n))
      Filter.atTop (nhds 0)) (n : ℕ) :
    teichCoeffAr p F ϖ hρ0 hρ1 (PhiHatK p F ϖ hρ0 hρ1 b) n = b n := by
  haveI hcompl : CompleteSpace F := IsPerfectoidRing.complete (p := p) (A := F)
  haveI ht0 : T0Space F := IsPerfectoidRing.t0 (p := p) (A := F)
  haveI huag : IsUniformAddGroup F := IsPerfectoidRing.uniformAddGroup (p := p) (A := F)
  have hΦ := tendsto_PhiHatK p F ϖ hρ0 hρ1 hb
  have htend : Filter.Tendsto (fun N => prefixAloc p F ϖ b N) Filter.atTop
      (Filter.comap (AlocToHatK p F ϖ hρ0 hρ1)
        (nhds (PhiHatK p F ϖ hρ0 hρ1 b))) :=
    Filter.tendsto_comap_iff.mpr hΦ
  have hcoords := (tendsto_teichCoeffAr p F ϖ
    (PhiHatK_mem_ArSub p F ϖ hρ0 hρ1 hb) n).comp htend
  have hev : ∀ᶠ N in Filter.atTop,
      teichCoeffF p F (alocToWittF p F ϖ (prefixAloc p F ϖ b N)) n = b n :=
    Filter.eventually_atTop.mpr ⟨n + 1, fun N hN =>
      teichCoeffF_prefixAloc p F ϖ b (lt_of_lt_of_le (Nat.lt_succ_self n) hN)⟩
  have hconst : Filter.Tendsto (fun _ : ℕ => b n) Filter.atTop
      (nhds (teichCoeffAr p F ϖ hρ0 hρ1 (PhiHatK p F ϖ hρ0 hρ1 b) n)) :=
    hcoords.congr' hev
  exact tendsto_nhds_unique hconst tendsto_const_nhds

/-- Limit coordinates of `0` vanish. -/
theorem teichCoeffAr_zero {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (n : ℕ) :
    teichCoeffAr p F ϖ hρ0 hρ1 (0 : hatK p F hρ0 hρ1) n = 0 := by
  have hdec := tendsto_gaussTerm_teichCoeffAr p F ϖ
    (zero_mem (ArSub p F ϖ hρ0 hρ1))
  have hB : BddAbove (Set.range (fun m => ρ ^ m * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 (0 : hatK p F hρ0 hρ1) m))) := by
    have hev := hdec.eventually_lt_const one_pos
    obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max 1 ((Finset.range (K + 1)).sup (fun m => ρ ^ m * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 (0 : hatK p F hρ0 hρ1) m))), ?_⟩
    rintro s ⟨m, rfl⟩
    rcases lt_or_ge m (K + 1) with hm | hm
    · exact le_max_of_le_right (Finset.le_sup
        (f := fun m => ρ ^ m * perfectoidValuation p F
          (teichCoeffAr p F ϖ hρ0 hρ1 (0 : hatK p F hρ0 hρ1) m))
        (Finset.mem_range.mpr hm))
    · exact le_max_of_le_left (hK m (by omega)).le
  have hform := valued_eq_iSup_teichCoeffAr p F ϖ (zero_mem (ArSub p F ϖ hρ0 hρ1))
  rw [Valuation.map_zero] at hform
  have h1 := le_ciSup hB n
  rw [← hform] at h1
  have hterm : ρ ^ n * perfectoidValuation p F
      (teichCoeffAr p F ϖ hρ0 hρ1 (0 : hatK p F hρ0 hρ1) n) = 0 :=
    le_antisymm h1 zero_le
  rcases mul_eq_zero.mp hterm with h | h
  · exact absurd h (pow_pos hρ0 n).ne'
  · exact (Valuation.zero_iff _).mp h

end FarguesFontaine

end
