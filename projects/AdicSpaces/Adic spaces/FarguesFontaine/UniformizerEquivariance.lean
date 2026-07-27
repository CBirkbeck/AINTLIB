/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.RobbaLoc
import «Adic spaces».FarguesFontaine.IntervalRing
import «Adic spaces».FarguesFontaine.SheafyBI

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

end FarguesFontaine

end
