/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.RobbaLoc
import «Adic spaces».FarguesFontaine.IntervalRing
import «Adic spaces».FarguesFontaine.SheafyBI
import «Adic spaces».FarguesFontaine.UniformizerTwist
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Uniformizer-equivariance of `Bloc` and its Gauss valuations (D-i-t1)

If `[ϖ']^k = [ϖ]` then `p·[ϖ']` and `p·[ϖ]` generate the same saturation, so
the localizations agree and the Gauss valuations correspond:

* `FarguesFontaine.isLocalization_twist_Bloc` / `blocTwistEquiv` :
  `Bloc-in-ϖ' ≃+* Bloc-in-ϖ` canonically;
* `FarguesFontaine.wLoc_blocTwistEquiv` : `wLoc` is invariant through the
  change isomorphism (the Gauss value is uniformizer-free).

These feed the `B^I`-equivariance (D-i-t2) used to compare the two
circle-localizations in the chart-transition data of the curve.
-/

open TopologicalRing ValuationSpectrum WittVector NNReal

set_option linter.overlappingInstances false
set_option warn.classDefReducibility false

noncomputable section

namespace FarguesFontaine

variable (p : ℕ) [Fact (Nat.Prime p)]
variable (F : Type*) [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [UniformSpace F] [NonarchimedeanRing F] [IsPerfectoidField p F] [CharP F p]
variable (ϖ : PseudoUniformizer F)
variable {ρ₁ ρ₂ : NNReal} {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}

/-- **`Bloc` is uniformizer-invariant**: if `[ϖ']^k = [ϖ]` then `Bloc-in-ϖ` is
also the localization away from `p·[ϖ']`. -/
theorem isLocalization_twist_Bloc {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) :
    IsLocalization (Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ'))
      (Bloc p F ϖ) where
  map_units := by
    rintro ⟨y, m, rfl⟩
    have hϖ'unit : IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ')) := by
      refine isUnit_of_mul_isUnit_left
        (y := algebraMap (Ainf p F) (Bloc p F ϖ) (teichPi p F ϖ' ^ (k - 1))) ?_
      rw [← map_mul, ← pow_succ']
      rw [show k - 1 + 1 = k from by omega, h]
      exact isUnit_teichPi_image p F ϖ
    have hunit : IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ)
        ((p : Ainf p F) * teichPi p F ϖ')) := by
      rw [map_mul]
      exact (isUnit_p_image p F ϖ).mul hϖ'unit
    show IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ') ^ m))
    rw [map_pow]
    exact hunit.pow m
  surj := by
    intro z
    obtain ⟨⟨a, y⟩, hz⟩ := IsLocalization.surj
      (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) z
    obtain ⟨m, hm⟩ := y.2
    refine ⟨⟨a * (p : Ainf p F) ^ (k * m - m),
      ⟨((p : Ainf p F) * teichPi p F ϖ') ^ (k * m), k * m, rfl⟩⟩, ?_⟩
    show z * algebraMap (Ainf p F) (Bloc p F ϖ)
        (((p : Ainf p F) * teichPi p F ϖ') ^ (k * m))
      = algebraMap (Ainf p F) (Bloc p F ϖ) (a * (p : Ainf p F) ^ (k * m - m))
    have hexp : ((p : Ainf p F) * teichPi p F ϖ') ^ (k * m)
        = ((p : Ainf p F) * teichPi p F ϖ) ^ m * (p : Ainf p F) ^ (k * m - m) := by
      have hteich' : teichPi p F ϖ' ^ (k * m) = teichPi p F ϖ ^ m := by
        rw [pow_mul, h]
      have hpsplit : (p : Ainf p F) ^ (k * m)
          = (p : Ainf p F) ^ m * (p : Ainf p F) ^ (k * m - m) := by
        rw [← pow_add]
        congr 1
        have : m ≤ k * m := Nat.le_mul_of_pos_left m hk
        omega
      rw [mul_pow, mul_pow, hteich', hpsplit]
      ring
    rw [hexp, map_mul, ← mul_assoc,
      show ((p : Ainf p F) * teichPi p F ϖ) ^ m = (y : Ainf p F) from hm, hz,
      ← map_mul]
  exists_of_eq := by
    intro x y hxy
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) (S := Bloc p F ϖ) hxy
    obtain ⟨m, hm⟩ := c.2
    refine ⟨⟨((p : Ainf p F) * teichPi p F ϖ') ^ (k * m), k * m, rfl⟩, ?_⟩
    show ((p : Ainf p F) * teichPi p F ϖ') ^ (k * m) * x
      = ((p : Ainf p F) * teichPi p F ϖ') ^ (k * m) * y
    have hexp : ((p : Ainf p F) * teichPi p F ϖ') ^ (k * m)
        = ((p : Ainf p F) * teichPi p F ϖ) ^ m * (p : Ainf p F) ^ (k * m - m) := by
      have hteich' : teichPi p F ϖ' ^ (k * m) = teichPi p F ϖ ^ m := by
        rw [pow_mul, h]
      have hpsplit : (p : Ainf p F) ^ (k * m)
          = (p : Ainf p F) ^ m * (p : Ainf p F) ^ (k * m - m) := by
        rw [← pow_add]
        congr 1
        have : m ≤ k * m := Nat.le_mul_of_pos_left m hk
        omega
      rw [mul_pow, mul_pow, hteich', hpsplit]
      ring
    rw [hexp]
    have hc' : ((p : Ainf p F) * teichPi p F ϖ) ^ m * x
        = ((p : Ainf p F) * teichPi p F ϖ) ^ m * y := by
      rw [show ((p : Ainf p F) * teichPi p F ϖ) ^ m = (c : Ainf p F) from hm]
      exact hc
    calc ((p : Ainf p F) * teichPi p F ϖ) ^ m * (p : Ainf p F) ^ (k * m - m) * x
        = (p : Ainf p F) ^ (k * m - m) * (((p : Ainf p F) * teichPi p F ϖ) ^ m * x) := by
          ring
      _ = (p : Ainf p F) ^ (k * m - m) * (((p : Ainf p F) * teichPi p F ϖ) ^ m * y) := by
          rw [hc']
      _ = ((p : Ainf p F) * teichPi p F ϖ) ^ m * (p : Ainf p F) ^ (k * m - m) * y := by
          ring


/-- **The uniformizer-change isomorphism** `Bloc-in-ϖ' ≃+* Bloc-in-ϖ`. -/
noncomputable def blocTwistEquiv {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) :
    Bloc p F ϖ' ≃+* Bloc p F ϖ :=
  letI := isLocalization_twist_Bloc p F ϖ hk h
  (IsLocalization.algEquiv (Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ'))
    (Bloc p F ϖ') (Bloc p F ϖ)).toRingEquiv

@[simp]
theorem blocTwistEquiv_algebraMap {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) (y : Ainf p F) :
    blocTwistEquiv p F ϖ hk h (algebraMap (Ainf p F) (Bloc p F ϖ') y)
      = algebraMap (Ainf p F) (Bloc p F ϖ) y := by
  letI := isLocalization_twist_Bloc p F ϖ hk h
  exact (IsLocalization.algEquiv (Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ'))
    (Bloc p F ϖ') (Bloc p F ϖ)).commutes y

/-- Gauss value of powers of the localized element. -/
theorem gaussValue_p_teichPi_pow (ϖ'' : PseudoUniformizer F) {ρ : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (m : ℕ) :
    gaussValue p F ρ (((p : Ainf p F) * teichPi p F ϖ'') ^ m)
      = (ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ'' : OF F) : F)) ^ m := by
  induction m with
  | zero =>
    rw [pow_zero, pow_zero]
    exact gaussValue_one p F hρ1.le
  | succ n ih =>
    rw [pow_succ, pow_succ, gaussValue_mul p F hρ0 hρ1, ih,
      gaussValue_p_teichPi p F ϖ'' hρ1]

/-- **The Gauss valuations are uniformizer-invariant** through the change
isomorphism. -/
theorem wLoc_blocTwistEquiv {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) {ρ : NNReal} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (z : Bloc p F ϖ') :
    wLoc p F ϖ hρ0 hρ1 (blocTwistEquiv p F ϖ hk h z)
      = wLoc p F ϖ' hρ0 hρ1 z := by
  obtain ⟨⟨a, y⟩, hz⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ')) z
  obtain ⟨m, hm⟩ := y.2
  have hz' : z * algebraMap (Ainf p F) (Bloc p F ϖ')
      (((p : Ainf p F) * teichPi p F ϖ') ^ m) = algebraMap _ _ a := by
    rw [show ((p : Ainf p F) * teichPi p F ϖ') ^ m = (y : Ainf p F) from hm]
    exact hz
  have himg : blocTwistEquiv p F ϖ hk h z * algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ') ^ m) = algebraMap _ _ a := by
    have hmap := congrArg (blocTwistEquiv p F ϖ hk h) hz'
    rwa [map_mul, blocTwistEquiv_algebraMap, blocTwistEquiv_algebraMap] at hmap
  have hval := gaussValue_p_teichPi_pow p F ϖ' hρ0 hρ1 m
  have hπ0 : (0 : NNReal) < perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ' : OF F) : F) := by
    refine pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr ?_)
    exact fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ' (Subtype.ext hcon)
  have hne : (ρ * perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ' : OF F) : F)) ^ m ≠ 0 :=
    pow_ne_zero m (mul_ne_zero hρ0.ne' hπ0.ne')
  have h1 := congrArg (wLoc p F ϖ hρ0 hρ1) himg
  have h2 := congrArg (wLoc p F ϖ' hρ0 hρ1) hz'
  rw [Valuation.map_mul, wLoc_algebraMap, wLoc_algebraMap, hval] at h1
  rw [Valuation.map_mul, wLoc_algebraMap, wLoc_algebraMap, hval] at h2
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

/-- **`BlocToHatK` is uniformizer-equivariant**: the change isomorphism
intertwines the maps to the (uniformizer-free) completed field. -/
theorem BlocToHatK_twist {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) {ρ : NNReal} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (z : Bloc p F ϖ') :
    BlocToHatK p F ϖ hρ0 hρ1 (blocTwistEquiv p F ϖ hk h z)
      = BlocToHatK p F ϖ' hρ0 hρ1 z := by
  letI := isLocalization_twist_Bloc p F ϖ hk h
  have hext : (BlocToHatK p F ϖ hρ0 hρ1).comp
      ((blocTwistEquiv p F ϖ hk h).toRingHom)
      = BlocToHatK p F ϖ' hρ0 hρ1 := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ')) ?_
    ext y
    show BlocToHatK p F ϖ hρ0 hρ1 (blocTwistEquiv p F ϖ hk h
      (algebraMap (Ainf p F) (Bloc p F ϖ') y)) = BlocToHatK p F ϖ' hρ0 hρ1
        (algebraMap (Ainf p F) (Bloc p F ϖ') y)
    rw [blocTwistEquiv_algebraMap]
    rw [show BlocToHatK p F ϖ hρ0 hρ1 (algebraMap (Ainf p F) (Bloc p F ϖ) y)
        = toHatK p F hρ0 hρ1 y from IsLocalization.lift_eq _ y,
      show BlocToHatK p F ϖ' hρ0 hρ1 (algebraMap (Ainf p F) (Bloc p F ϖ') y)
        = toHatK p F hρ0 hρ1 y from IsLocalization.lift_eq _ y]
  exact congrFun (congrArg (fun f => f.toFun) hext) z

/-- **`B^I` is uniformizer-invariant on the nose**: the interval subrings for
`[ϖ']^k = [ϖ]` coincide as subrings of the (uniformizer-free) product of
completed fields. -/
theorem BISub_twist {ϖ' : PseudoUniformizer F} {k : ℕ} (hk : 0 < k)
    (h : teichPi p F ϖ' ^ k = teichPi p F ϖ) :
    BISub p F ϖ' hρ₁0 hρ₁1 hρ₂0 hρ₂1 = BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 := by
  have hrange : (BIProd p F ϖ' hρ₁0 hρ₁1 hρ₂0 hρ₂1).range
      = (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range := by
    ext w
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨blocTwistEquiv p F ϖ hk h z, ?_⟩
      show (BlocToHatK p F ϖ hρ₁0 hρ₁1 (blocTwistEquiv p F ϖ hk h z),
          BlocToHatK p F ϖ hρ₂0 hρ₂1 (blocTwistEquiv p F ϖ hk h z))
        = (BlocToHatK p F ϖ' hρ₁0 hρ₁1 z, BlocToHatK p F ϖ' hρ₂0 hρ₂1 z)
      rw [BlocToHatK_twist p F ϖ hk h hρ₁0 hρ₁1 z,
        BlocToHatK_twist p F ϖ hk h hρ₂0 hρ₂1 z]
    · rintro ⟨z, rfl⟩
      refine ⟨(blocTwistEquiv p F ϖ hk h).symm z, ?_⟩
      show (BlocToHatK p F ϖ' hρ₁0 hρ₁1 ((blocTwistEquiv p F ϖ hk h).symm z),
          BlocToHatK p F ϖ' hρ₂0 hρ₂1 ((blocTwistEquiv p F ϖ hk h).symm z))
        = (BlocToHatK p F ϖ hρ₁0 hρ₁1 z, BlocToHatK p F ϖ hρ₂0 hρ₂1 z)
      rw [← BlocToHatK_twist p F ϖ hk h hρ₁0 hρ₁1,
        ← BlocToHatK_twist p F ϖ hk h hρ₂0 hρ₂1,
        RingEquiv.apply_symm_apply]
  rw [BISub, BISub, hrange]

/-- The `wI`-uniformity on `Bloc`: the pullback of the product uniformity along
the diagonal map. -/
noncomputable def blocWIUniformSpace (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) : UniformSpace (Bloc p F ϖ) :=
  UniformSpace.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) inferInstance

/-- The corestricted diagonal `Bloc →+* ↥B^I`. -/
noncomputable def blocToBI (hρ₁0 : 0 < ρ₁) (hρ₁1 : ρ₁ < 1)
    (hρ₂0 : 0 < ρ₂) (hρ₂1 : ρ₂ < 1) :
    Bloc p F ϖ →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).codRestrict _
    (fun z => (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).range.le_topologicalClosure
      ⟨z, rfl⟩)

/-- The diagonal is uniformly inducing for the `wI`-uniformity. -/
theorem isUniformInducing_blocToBI :
    @IsUniformInducing _ _ (blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) _
      (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) := by
  letI : UniformSpace (Bloc p F ϖ) := blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  refine ⟨?_⟩
  show Filter.comap _ (uniformity ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) = _
  rw [uniformity_subtype, Filter.comap_comap]
  rfl

/-- The diagonal has dense range in `B^I`. -/
theorem denseRange_blocToBI :
    DenseRange (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) := by
  rw [DenseRange, dense_iff_closure_eq,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have himg : (Subtype.val '' Set.range (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
      = Set.range (⇑(BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) := by
    ext w
    constructor
    · rintro ⟨-, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z, ⟨z, rfl⟩, rfl⟩
  rw [himg]
  have hclos : closure (Set.range (⇑(BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)))
      = (BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
        : Set ((hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1))) := rfl
  rw [hclos]
  ext w
  simp [w.2]


/-- The `wI`-uniformity makes `Bloc` a uniform additive group. -/
theorem isUniformAddGroup_blocWI :
    @IsUniformAddGroup (Bloc p F ϖ)
      (blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) _ :=
  IsUniformAddGroup.comap
    (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).toAddMonoidHom

/-- **The interval-restriction is uniformly continuous on the dense layer**:
for interpolated radii `σⱼ = ρ₁^{θⱼ}·ρ₂^{1-θⱼ}`, the `J`-diagonal is
1-Lipschitz for the `I`-uniformity (three circles). -/
theorem uniformContinuous_blocToBI_interpolate {θ₁ θ₂ : ℝ}
    (hθ₁0 : 0 ≤ θ₁) (hθ₁1 : θ₁ ≤ 1) (hθ₂0 : 0 ≤ θ₂) (hθ₂1 : θ₂ ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁)) (hσ₁1 : ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁) < 1)
    (hσ₂0 : 0 < ρ₁ ^ θ₂ * ρ₂ ^ (1 - θ₂)) (hσ₂1 : ρ₁ ^ θ₂ * ρ₂ ^ (1 - θ₂) < 1) :
    @UniformContinuous _ _ (blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) _
      (blocToBI p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) := by
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  haveI : IsUniformAddGroup (Bloc p F ϖ) :=
    isUniformAddGroup_blocWI p F ϖ
  haveI : IsUniformAddGroup ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) :=
    isUniformAddGroup_BISub p F ϖ
  refine uniformContinuous_of_tendsto_zero ?_
  rw [tendsto_subtype_rng]
  have hcoe : (fun z => ((blocToBI p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 z :
      ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1))
        : (hatK p F hσ₁0 hσ₁1) × (hatK p F hσ₂0 hσ₂1)))
      = fun z => BIProd p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 z := rfl
  rw [hcoe]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨ε, hε, hball⟩ := exists_wI_ball_subset p F
    (hρ₁0 := hσ₁0) (hρ₁1 := hσ₁1) (hρ₂0 := hσ₂0) (hρ₂1 := hσ₂1) hU
  have hnhd : {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ ε} ∈ nhds
        (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
    have h := wI_ball_mem_nhds p F
      (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) hε
    simpa using h
  rw [show (nhds (0 : Bloc p F ϖ))
      = Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
        (nhds (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 0)) from nhds_induced _ _]
  rw [map_zero]
  refine Filter.mem_of_superset (Filter.preimage_mem_comap hnhd) ?_
  intro z hz
  refine hball ?_
  show wI p F hσ₁0 hσ₁1 hσ₂0 hσ₂1
    (BIProd p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 z) ≤ ε
  have hzI : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) ≤ ε := hz
  rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK] at hzI ⊢
  have h₁ := wLoc_le_max_of_interpolate p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hθ₁0 hθ₁1 hσ₁0 hσ₁1 z
  have h₂ := wLoc_le_max_of_interpolate p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hθ₂0 hθ₂1 hσ₂0 hσ₂1 z
  exact max_le (le_trans h₁ hzI) (le_trans h₂ hzI)

/-- **The interval-restriction map** `B^{[ρ₁,ρ₂]} →+* B^{[σ₁,σ₂]}` for
interpolated sub-radii (D-i-t3): the dense extension of the identity on
`Bloc`. -/
noncomputable def biRes {θ₁ θ₂ : ℝ}
    (hθ₁0 : 0 ≤ θ₁) (hθ₁1 : θ₁ ≤ 1) (hθ₂0 : 0 ≤ θ₂) (hθ₂1 : θ₂ ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁)) (hσ₁1 : ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁) < 1)
    (hσ₂0 : 0 < ρ₁ ^ θ₂ * ρ₂ ^ (1 - θ₂)) (hσ₂1 : ρ₁ ^ θ₂ * ρ₂ ^ (1 - θ₂) < 1) :
    ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) :=
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  haveI : CompleteSpace ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) :=
    (isComplete_BISub p F ϖ).completeSpace_coe
  IsDenseInducing.extendRingHom
    (isUniformInducing_blocToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1))
    (denseRange_blocToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1))
    (uniformContinuous_blocToBI_interpolate p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
      hθ₁0 hθ₁1 hθ₂0 hθ₂1 hσ₁0 hσ₁1 hσ₂0 hσ₂1)

/-- The restriction map is the identity on the dense `Bloc`-layer. -/
theorem biRes_blocToBI {θ₁ θ₂ : ℝ}
    (hθ₁0 : 0 ≤ θ₁) (hθ₁1 : θ₁ ≤ 1) (hθ₂0 : 0 ≤ θ₂) (hθ₂1 : θ₂ ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁)) (hσ₁1 : ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁) < 1)
    (hσ₂0 : 0 < ρ₁ ^ θ₂ * ρ₂ ^ (1 - θ₂)) (hσ₂1 : ρ₁ ^ θ₂ * ρ₂ ^ (1 - θ₂) < 1)
    (z : Bloc p F ϖ) :
    biRes p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
        hθ₁0 hθ₁1 hθ₂0 hθ₂1 hσ₁0 hσ₁1 hσ₂0 hσ₂1
        (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z)
      = blocToBI p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 z := by
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  haveI : CompleteSpace ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) :=
    (isComplete_BISub p F ϖ).completeSpace_coe
  exact IsDenseInducing.extend_eq
    ((isUniformInducing_blocToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)).isDenseInducing
      (denseRange_blocToBI p F ϖ))
    (uniformContinuous_blocToBI_interpolate p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
      hθ₁0 hθ₁1 hθ₂0 hθ₂1 hσ₁0 hσ₁1 hσ₂0 hσ₂1).continuous z

/-- The radius `|ϖ|^q` for a rational exponent `q` (irreducible: the radius
is an opaque atom for instance search — PERF). -/
@[irreducible] noncomputable def vpiQ (q : ℚ) : NNReal :=
  perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ (q : ℝ)

theorem vpiQ_pos (q : ℚ) : 0 < vpiQ p F ϖ q := by
  rw [vpiQ]
  refine NNReal.rpow_pos ?_
  refine pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr ?_)
  exact fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon)

theorem vpiQ_lt_one {q : ℚ} (hq : 0 < q) : vpiQ p F ϖ q < 1 := by
  rw [vpiQ]
  refine NNReal.rpow_lt_one (perfectoidValuation_toOF_lt_one p F ϖ) ?_
  exact_mod_cast hq

/-- Interpolation of the rational radii: `vpiQ r = (vpiQ q₁)^θ·(vpiQ q₂)^{1-θ}`
for the affine parameter `θ = (q₂ - r)/(q₂ - q₁)`. -/
theorem vpiQ_interpolate {q₁ q₂ r : ℚ} (hne : q₁ ≠ q₂) :
    vpiQ p F ϖ q₁ ^ (((q₂ - r) / (q₂ - q₁) : ℚ) : ℝ)
        * vpiQ p F ϖ q₂ ^ (1 - (((q₂ - r) / (q₂ - q₁) : ℚ) : ℝ))
      = vpiQ p F ϖ r := by
  have hπ0 : perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) ≠ 0 := by
    refine (Valuation.ne_zero_iff _).mpr ?_
    exact fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon)
  rw [vpiQ, vpiQ, vpiQ, ← NNReal.rpow_mul, ← NNReal.rpow_mul,
    ← NNReal.rpow_add hπ0]
  congr 1
  have hden : ((q₂ : ℝ) - (q₁ : ℝ)) ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    exact_mod_cast hne.symm
  push_cast
  field_simp
  ring


variable {ρ₁' ρ₂' : NNReal}

/-- Transport of `B^I` along radius equalities (the proofs are definitionally
irrelevant). -/
noncomputable def biCongr (h₁ : ρ₁ = ρ₁') (h₂ : ρ₂ = ρ₂')
    {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {hρ₁0' : 0 < ρ₁'} {hρ₁1' : ρ₁' < 1} {hρ₂0' : 0 < ρ₂'} {hρ₂1' : ρ₂' < 1} :
    ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      ≃+* ↥(BISub p F ϖ hρ₁0' hρ₁1' hρ₂0' hρ₂1') := by
  subst h₁
  subst h₂
  exact RingEquiv.refl _

@[simp]
theorem biCongr_blocToBI (h₁ : ρ₁ = ρ₁') (h₂ : ρ₂ = ρ₂')
    {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {hρ₁0' : 0 < ρ₁'} {hρ₁1' : ρ₁' < 1} {hρ₂0' : 0 < ρ₂'} {hρ₂1' : ρ₂' < 1}
    (z : Bloc p F ϖ) :
    biCongr p F ϖ h₁ h₂ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) (hρ₁0' := hρ₁0') (hρ₁1' := hρ₁1') (hρ₂0' := hρ₂0')
        (hρ₂1' := hρ₂1')
        (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z)
      = blocToBI p F ϖ hρ₁0' hρ₁1' hρ₂0' hρ₂1' z := by
  subst h₁
  subst h₂
  rfl

/-- **The rational-exponent interval ring** `B^{[|ϖ|^{q₂}... |ϖ|^{q₁}]}`
(NOTE the radius at exponent `q` is `|ϖ|^q`, decreasing in `q`). -/
noncomputable def BIQ (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    Subring ((hatK p F (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁))
      × (hatK p F (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂))) :=
  BISub p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
    (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)

/-- The interval-restriction map is continuous. -/
theorem biRes_continuous {θ₁ θ₂ : ℝ}
    (hθ₁0 : 0 ≤ θ₁) (hθ₁1 : θ₁ ≤ 1) (hθ₂0 : 0 ≤ θ₂) (hθ₂1 : θ₂ ≤ 1)
    (hσ₁0 : 0 < ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁)) (hσ₁1 : ρ₁ ^ θ₁ * ρ₂ ^ (1 - θ₁) < 1)
    (hσ₂0 : 0 < ρ₁ ^ θ₂ * ρ₂ ^ (1 - θ₂)) (hσ₂1 : ρ₁ ^ θ₂ * ρ₂ ^ (1 - θ₂) < 1) :
    Continuous (biRes p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) hθ₁0 hθ₁1 hθ₂0 hθ₂1 hσ₁0 hσ₁1 hσ₂0 hσ₂1) := by
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  haveI : CompleteSpace ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) :=
    (isComplete_BISub p F ϖ).completeSpace_coe
  exact (uniformContinuous_uniformly_extend
    (isUniformInducing_blocToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1))
    (denseRange_blocToBI p F ϖ)
    (uniformContinuous_blocToBI_interpolate p F ϖ (hρ₁0 := hρ₁0)
      (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
      hθ₁0 hθ₁1 hθ₂0 hθ₂1 hσ₁0 hσ₁1 hσ₂0 hσ₂1)).continuous

/-- The radius-transport is continuous. -/
theorem biCongr_continuous (h₁ : ρ₁ = ρ₁') (h₂ : ρ₂ = ρ₂')
    {hρ₁0 : 0 < ρ₁} {hρ₁1 : ρ₁ < 1} {hρ₂0 : 0 < ρ₂} {hρ₂1 : ρ₂ < 1}
    {hρ₁0' : 0 < ρ₁'} {hρ₁1' : ρ₁' < 1} {hρ₂0' : 0 < ρ₂'} {hρ₂1' : ρ₂' < 1} :
    Continuous (biCongr p F ϖ h₁ h₂ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) (hρ₁0' := hρ₁0') (hρ₁1' := hρ₁1')
      (hρ₂0' := hρ₂0') (hρ₂1' := hρ₂1')) := by
  subst h₁
  subst h₂
  exact continuous_id

/-- The rational radii are antitone in the exponent. -/
theorem vpiQ_antitone {q q' : ℚ} (h : q ≤ q') :
    vpiQ p F ϖ q' ≤ vpiQ p F ϖ q := by
  rw [vpiQ, vpiQ]
  exact NNReal.rpow_le_rpow_of_exponent_ge
    (by
      refine pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr ?_)
      exact fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon))
    (perfectoidValuation_toOF_lt_one p F ϖ).le
    (by exact_mod_cast h)

/-- The nat-power radii are the rational radii at nat exponents:
`vpiQ n = |ϖ|^n`. -/
theorem vpiQ_natCast (n : ℕ) :
    vpiQ p F ϖ (n : ℚ)
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) ^ n := by
  rw [vpiQ]
  rw [show (((n : ℚ) : ℝ)) = (n : ℝ) from by push_cast; rfl]
  exact NNReal.rpow_natCast _ n

/-- `vpiQ 1` is the base radius `|ϖ|`. -/
theorem vpiQ_one :
    vpiQ p F ϖ 1
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F) := by
  have h := vpiQ_natCast p F ϖ 1
  rwa [pow_one, Nat.cast_one] at h

/-- The valuation of the Frobenius root as an rpow of the base:
`|ϖ^{1/p^s}| = |ϖ|^{1/p^s}`. -/
theorem perfectoidValuation_frobRoot_rpow (s : ℕ) :
    perfectoidValuation p F
        ((PseudoUniformizer.toOF F (PseudoUniformizer.frobRoot p F ϖ s) : OF F) : F)
      = perfectoidValuation p F ((PseudoUniformizer.toOF F ϖ : OF F) : F)
          ^ (((p : ℝ) ^ s)⁻¹) := by
  have h := perfectoidValuation_frobRoot_pow p F ϖ s
  have hps : ((p : ℝ) ^ s) ≠ 0 := by
    have := Nat.Prime.pos (Fact.out : Nat.Prime p)
    positivity
  rw [← h, ← NNReal.rpow_natCast _ (p ^ s), ← NNReal.rpow_mul]
  rw [show ((p ^ s : ℕ) : ℝ) = (p : ℝ) ^ s from by push_cast; ring,
    mul_inv_cancel₀ hps, NNReal.rpow_one]

/-- **The twist bridge for rational radii (root side)**:
`vpiQ-in-ϖ^{1/p^s}(q) = vpiQ-in-ϖ(q/p^s)`. -/
theorem vpiQ_frobRoot (s : ℕ) (q : ℚ) :
    vpiQ p F (PseudoUniformizer.frobRoot p F ϖ s) q
      = vpiQ p F ϖ (q / (p ^ s : ℚ)) := by
  have hps : ((p : ℝ) ^ s) ≠ 0 := by
    have := Nat.Prime.pos (Fact.out : Nat.Prime p)
    positivity
  rw [vpiQ, vpiQ, perfectoidValuation_frobRoot_rpow p F ϖ s, ← NNReal.rpow_mul]
  congr 1
  push_cast
  field_simp

/-- **The twist bridge for rational radii (power side)**:
`vpiQ-in-ϖ^m(q) = vpiQ-in-ϖ(q·m)`. -/
theorem vpiQ_pPow (m : ℕ) (hm : 0 < m) (q : ℚ) :
    vpiQ p F (PseudoUniformizer.pPow F ϖ m hm) q
      = vpiQ p F ϖ (q * m) := by
  rw [vpiQ, vpiQ, perfectoidValuation_pPow p F ϖ m hm,
    ← NNReal.rpow_natCast _ m, ← NNReal.rpow_mul]
  congr 1
  push_cast
  ring

/-- The affine parameter is in `[0,1]` for the decreasing-exponent
orientation. -/
theorem theta_mem_unit {q₁ q₂ r : ℚ} (hlt : q₂ < q₁) (hr₁ : q₂ ≤ r)
    (hr₂ : r ≤ q₁) :
    (0 : ℝ) ≤ (((q₂ - r) / (q₂ - q₁) : ℚ) : ℝ)
      ∧ (((q₂ - r) / (q₂ - q₁) : ℚ) : ℝ) ≤ 1 := by
  have heq : (q₂ - r) / (q₂ - q₁) = (r - q₂) / (q₁ - q₂) := by
    rw [show q₂ - r = -(r - q₂) from by ring, show q₂ - q₁ = -(q₁ - q₂) from by
      ring, neg_div_neg_eq]
  have h1 : (0 : ℚ) ≤ (q₂ - r) / (q₂ - q₁) := by
    rw [heq]
    apply div_nonneg <;> linarith
  have h2 : (q₂ - r) / (q₂ - q₁) ≤ 1 := by
    rw [heq, div_le_one (by linarith)]
    linarith
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

/-- **The rational-exponent restriction map, decreasing orientation**
(`q₂ < q₁`, radius-ordered pairs): `B^{[q₁,q₂]} →+* B^{[r₁,r₂]}` for
`r₁, r₂ ∈ [q₂, q₁]`. -/
noncomputable def biResQ (q₁ q₂ r₁ r₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : q₂ < q₁)
    (hr₁m : q₂ ≤ r₁ ∧ r₁ ≤ q₁) (hr₂m : q₂ ≤ r₂ ∧ r₂ ≤ q₁) :
    ↥(BIQ p F ϖ q₁ q₂ h₁ h₂) →+* ↥(BIQ p F ϖ r₁ r₂ hr₁ hr₂) :=
  (biCongr p F ϖ (vpiQ_interpolate p F ϖ hlt.ne')
      (vpiQ_interpolate p F ϖ hlt.ne')
      (hρ₁0' := vpiQ_pos p F ϖ r₁) (hρ₁1' := vpiQ_lt_one p F ϖ hr₁)
      (hρ₂0' := vpiQ_pos p F ϖ r₂) (hρ₂1' := vpiQ_lt_one p F ϖ hr₂)).toRingHom.comp
    (biRes p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)
      (theta_mem_unit hlt hr₁m.1 hr₁m.2).1 (theta_mem_unit hlt hr₁m.1 hr₁m.2).2
      (theta_mem_unit hlt hr₂m.1 hr₂m.2).1 (theta_mem_unit hlt hr₂m.1 hr₂m.2).2
      (by rw [vpiQ_interpolate p F ϖ hlt.ne']
          exact vpiQ_pos p F ϖ r₁)
      (by rw [vpiQ_interpolate p F ϖ hlt.ne']
          exact vpiQ_lt_one p F ϖ hr₁)
      (by rw [vpiQ_interpolate p F ϖ hlt.ne']
          exact vpiQ_pos p F ϖ r₂)
      (by rw [vpiQ_interpolate p F ϖ hlt.ne']
          exact vpiQ_lt_one p F ϖ hr₂))

/-- The decreasing-orientation restriction is the identity on the dense
`Bloc`-layer. -/
theorem biResQ_blocToBI (q₁ q₂ r₁ r₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : q₂ < q₁)
    (hr₁m : q₂ ≤ r₁ ∧ r₁ ≤ q₁) (hr₂m : q₂ ≤ r₂ ∧ r₂ ≤ q₁) (z : Bloc p F ϖ) :
    biResQ p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m
        (blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
          (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z)
      = blocToBI p F ϖ (vpiQ_pos p F ϖ r₁) (vpiQ_lt_one p F ϖ hr₁)
          (vpiQ_pos p F ϖ r₂) (vpiQ_lt_one p F ϖ hr₂) z := by
  show (biCongr p F ϖ _ _) (biRes p F ϖ _ _ _ _ _ _ _ _
    (blocToBI p F ϖ _ _ _ _ z)) = _
  rw [biRes_blocToBI, biCongr_blocToBI]


/-- The decreasing-orientation restriction map is continuous. -/
theorem biResQ_continuous (q₁ q₂ r₁ r₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : q₂ < q₁)
    (hr₁m : q₂ ≤ r₁ ∧ r₁ ≤ q₁) (hr₂m : q₂ ≤ r₂ ∧ r₂ ≤ q₁) :
    Continuous (biResQ p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m) := by
  rw [biResQ]
  exact (biCongr_continuous p F ϖ (vpiQ_interpolate p F ϖ hlt.ne')
      (vpiQ_interpolate p F ϖ hlt.ne')).comp
    (biRes_continuous p F ϖ
      (theta_mem_unit hlt hr₁m.1 hr₁m.2).1 (theta_mem_unit hlt hr₁m.1 hr₁m.2).2
      (theta_mem_unit hlt hr₂m.1 hr₂m.2).1 (theta_mem_unit hlt hr₂m.1 hr₂m.2).2
      _ _ _ _)

/-- **Identity law, decreasing orientation.** -/
theorem biResQ_id (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) (hlt : q₂ < q₁) :
    biResQ p F ϖ q₁ q₂ q₁ q₂ h₁ h₂ h₁ h₂ hlt ⟨hlt.le, le_refl q₁⟩
        ⟨le_refl q₂, hlt.le⟩
      = RingHom.id ↥(BIQ p F ϖ q₁ q₂ h₁ h₂) := by
  have hfun : ⇑(biResQ p F ϖ q₁ q₂ q₁ q₂ h₁ h₂ h₁ h₂ hlt ⟨hlt.le, le_refl q₁⟩
      ⟨le_refl q₂, hlt.le⟩) = id := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)).equalizer
      (biResQ_continuous p F ϖ q₁ q₂ q₁ q₂ h₁ h₂ h₁ h₂ hlt
        ⟨hlt.le, le_refl q₁⟩ ⟨le_refl q₂, hlt.le⟩)
      continuous_id (funext fun z => ?_)
    show biResQ p F ϖ q₁ q₂ q₁ q₂ h₁ h₂ h₁ h₂ hlt ⟨hlt.le, le_refl q₁⟩
        ⟨le_refl q₂, hlt.le⟩ (blocToBI p F ϖ _ _ _ _ z)
      = blocToBI p F ϖ _ _ _ _ z
    rw [biResQ_blocToBI]
  exact RingHom.ext fun x => congrFun hfun x

/-- **Composition law, decreasing orientation.** -/
theorem biResQ_comp (q₁ q₂ r₁ r₂ s₁ s₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hlt : q₂ < q₁) (hlt' : r₂ < r₁)
    (hr₁m : q₂ ≤ r₁ ∧ r₁ ≤ q₁) (hr₂m : q₂ ≤ r₂ ∧ r₂ ≤ q₁)
    (hs₁m : r₂ ≤ s₁ ∧ s₁ ≤ r₁) (hs₂m : r₂ ≤ s₂ ∧ s₂ ≤ r₁) :
    (biResQ p F ϖ r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ hlt' hs₁m hs₂m).comp
        (biResQ p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m)
      = biResQ p F ϖ q₁ q₂ s₁ s₂ h₁ h₂ hs₁ hs₂ hlt
          ⟨le_trans hr₂m.1 hs₁m.1, le_trans hs₁m.2 hr₁m.2⟩
          ⟨le_trans hr₂m.1 hs₂m.1, le_trans hs₂m.2 hr₁m.2⟩ := by
  have hfun : ⇑((biResQ p F ϖ r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ hlt' hs₁m hs₂m).comp
      (biResQ p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m))
      = ⇑(biResQ p F ϖ q₁ q₂ s₁ s₂ h₁ h₂ hs₁ hs₂ hlt
          ⟨le_trans hr₂m.1 hs₁m.1, le_trans hs₁m.2 hr₁m.2⟩
          ⟨le_trans hr₂m.1 hs₂m.1, le_trans hs₂m.2 hr₁m.2⟩) := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)).equalizer
      ?_
      (biResQ_continuous p F ϖ q₁ q₂ s₁ s₂ h₁ h₂ hs₁ hs₂ hlt
        ⟨le_trans hr₂m.1 hs₁m.1, le_trans hs₁m.2 hr₁m.2⟩
        ⟨le_trans hr₂m.1 hs₂m.1, le_trans hs₂m.2 hr₁m.2⟩)
      (funext fun z => ?_)
    · exact (biResQ_continuous p F ϖ r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ hlt'
          hs₁m hs₂m).comp
        (biResQ_continuous p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m)
    · show biResQ p F ϖ r₁ r₂ s₁ s₂ hr₁ hr₂ hs₁ hs₂ hlt' hs₁m hs₂m
          (biResQ p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m
            (blocToBI p F ϖ _ _ _ _ z))
        = biResQ p F ϖ q₁ q₂ s₁ s₂ h₁ h₂ hs₁ hs₂ hlt
            ⟨le_trans hr₂m.1 hs₁m.1, le_trans hs₁m.2 hr₁m.2⟩
            ⟨le_trans hr₂m.1 hs₂m.1, le_trans hs₂m.2 hr₁m.2⟩
            (blocToBI p F ϖ _ _ _ _ z)
      rw [biResQ_blocToBI, biResQ_blocToBI, biResQ_blocToBI]
  exact RingHom.ext fun x => congrFun hfun x

end FarguesFontaine

end
