/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB AI workers
-/
import «Adic spaces».FarguesFontaine.FrobeniusAction
import «Adic spaces».FarguesFontaine.GaussNorm
import «Adic spaces».FarguesFontaine.RobbaLoc
import «Adic spaces».FarguesFontaine.UniformizerEquivariance

/-!
# Frobenius and the Gauss valuations (D-iii foundation)

The radius-change law of the Witt Frobenius on `A_inf = W(O_F)`:

* `FarguesFontaine.teichCoeff_frob` : `φ` is the coefficient-wise `p`-th power;
* `FarguesFontaine.gaussValue_frob` : `w_{ρ^p}(φ x) = w_ρ(x)^p` — Frobenius
  intertwines the Gauss valuations with the `p`-th power of the radius
  (κ ↦ p·κ on windows; `q ↦ q/p` on the `BIQ`-exponent indexing).
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

/-- Frobenius acts coefficient-wise as the `p`-th power on Teichmüller
coordinates. -/
theorem teichCoeff_frob (x : Ainf p F) (n : ℕ) :
    teichCoeff p F (frob p F x) n = teichCoeff p F x n ^ p := by
  rw [teichCoeff, teichCoeff]
  have hcoeff : (frob p F x).coeff n = x.coeff n ^ p := by
    show (WittVector.frobeniusEquiv p (OF F) x).coeff n = x.coeff n ^ p
    rw [WittVector.frobeniusEquiv_apply, frobenius_eq_map_frobenius,
      WittVector.map_coeff]
    exact frobenius_def _ _
  rw [hcoeff, map_pow]

/-- The Gauss term at the `p`-th-power radius of a Frobenius image is the
`p`-th power of the Gauss term. -/
theorem gaussTerm_frob (ρ : NNReal) (x : Ainf p F) (n : ℕ) :
    gaussTerm p F (ρ ^ p) (frob p F x) n = gaussTerm p F ρ x n ^ p := by
  rw [gaussTerm, gaussTerm, teichCoeff_frob, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm n p, pow_mul]
  congr 1
  push_cast
  rw [Valuation.map_pow]

/-- **The Frobenius radius-change law**: `w_{ρ^p}(φ x) = w_ρ(x)^p`. -/
theorem gaussValue_frob {ρ : NNReal} (hρ1 : ρ ≤ 1) (x : Ainf p F) :
    gaussValue p F (ρ ^ p) (frob p F x) = gaussValue p F ρ x ^ p := by
  rw [gaussValue, gaussValue]
  have hmono : Monotone (fun t : NNReal => t ^ p) :=
    fun a b hab => pow_le_pow_left₀ zero_le hab p
  have hcont : ContinuousAt (fun t : NNReal => t ^ p)
      (⨆ n, gaussTerm p F ρ x n) := (continuous_pow p).continuousAt
  rw [Monotone.map_ciSup_of_continuousAt hcont hmono
    (bddAbove_range_gaussTerm p F hρ1 x)]
  congr 1
  funext n
  exact gaussTerm_frob p F ρ x n

/-- Frobenius sends the inverted element to a unit of `Bloc`. -/
theorem isUnit_frob_p_teichPi_image (y : Submonoid.powers
    ((p : Ainf p F) * teichPi p F ϖ)) :
    IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ) (frob p F (y : Ainf p F))) := by
  obtain ⟨k, hk⟩ := y.2
  rw [show (y : Ainf p F) = ((p : Ainf p F) * teichPi p F ϖ) ^ k from hk.symm,
    map_pow, map_pow]
  refine IsUnit.pow k ?_
  rw [map_mul, frob_natCast, frob_teichPi, map_mul, map_pow]
  exact (isUnit_p_image p F ϖ).mul ((isUnit_teichPi_image p F ϖ).pow p)

/-- **Frobenius on `Bloc`**, by the universal property of the localization. -/
noncomputable def frobBloc : Bloc p F ϖ →+* Bloc p F ϖ :=
  IsLocalization.lift (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ))
    (g := (algebraMap (Ainf p F) (Bloc p F ϖ)).comp (frob p F).toRingHom)
    (fun y => isUnit_frob_p_teichPi_image p F ϖ y)

@[simp]
theorem frobBloc_algebraMap (x : Ainf p F) :
    frobBloc p F ϖ (algebraMap (Ainf p F) (Bloc p F ϖ) x)
      = algebraMap (Ainf p F) (Bloc p F ϖ) (frob p F x) :=
  IsLocalization.lift_eq _ x

/-- **The radius-change law on `Bloc`**: `w_{ρ^p}(φ z) = w_ρ(z)^p`. -/
theorem wLoc_frobBloc {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρp0 : 0 < ρ ^ p) (hρp1 : ρ ^ p < 1) (z : Bloc p F ϖ) :
    wLoc p F ϖ hρp0 hρp1 (frobBloc p F ϖ z) = wLoc p F ϖ hρ0 hρ1 z ^ p := by
  obtain ⟨⟨a, y⟩, hz⟩ := IsLocalization.surj
    (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) z
  obtain ⟨m, hm⟩ := y.2
  have hz' : z * algebraMap (Ainf p F) (Bloc p F ϖ)
      (((p : Ainf p F) * teichPi p F ϖ) ^ m) = algebraMap _ _ a := by
    rw [show ((p : Ainf p F) * teichPi p F ϖ) ^ m = (y : Ainf p F) from hm]
    exact hz
  have himg : frobBloc p F ϖ z * algebraMap (Ainf p F) (Bloc p F ϖ)
      (frob p F (((p : Ainf p F) * teichPi p F ϖ) ^ m))
      = algebraMap _ _ (frob p F a) := by
    have hmap := congrArg (frobBloc p F ϖ) hz'
    rwa [map_mul, frobBloc_algebraMap, frobBloc_algebraMap] at hmap
  have h1 := congrArg (wLoc p F ϖ hρp0 hρp1) himg
  have h2 := congrArg (wLoc p F ϖ hρ0 hρ1) hz'
  rw [Valuation.map_mul, wLoc_algebraMap, wLoc_algebraMap,
    gaussValue_frob p F hρ1.le, gaussValue_frob p F hρ1.le] at h1
  rw [Valuation.map_mul, wLoc_algebraMap, wLoc_algebraMap] at h2
  have hval : gaussValue p F ρ (((p : Ainf p F) * teichPi p F ϖ) ^ m)
      = (ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m :=
    gaussValue_p_teichPi_pow p F ϖ hρ0 hρ1 m
  have hπ0 : (0 : NNReal) < perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F) := by
    refine pos_iff_ne_zero.mpr ((Valuation.ne_zero_iff _).mpr ?_)
    exact fun hcon => PseudoUniformizer.toOF_ne_zero F ϖ (Subtype.ext hcon)
  have hne : ((ρ * perfectoidValuation p F
      ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m) ^ p ≠ 0 :=
    pow_ne_zero p (pow_ne_zero m (mul_ne_zero hρ0.ne' hπ0.ne'))
  rw [hval] at h1 h2
  -- h1 : wLoc_{ρ^p}(φz) * ((ρ·vπ)^m)^p = gaussValue_ρ(a)^p  (after the pow-collapse)
  -- h2 : wLoc_ρ(z) * (ρ·vπ)^m = gaussValue_ρ(a)
  refine mul_right_cancel₀ hne ?_
  calc wLoc p F ϖ hρp0 hρp1 (frobBloc p F ϖ z)
        * ((ρ * perfectoidValuation p F
            ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m) ^ p
      = gaussValue p F ρ a ^ p := h1
    _ = (wLoc p F ϖ hρ0 hρ1 z * (ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m) ^ p := by rw [h2]
    _ = wLoc p F ϖ hρ0 hρ1 z ^ p * ((ρ * perfectoidValuation p F
          ((PseudoUniformizer.toOF F ϖ : OF F) : F)) ^ m) ^ p := by
        rw [mul_pow]

/-- **The Frobenius is uniformly continuous** from the `[ρ₁,ρ₂]`-uniformity to
the `[ρ₁^p,ρ₂^p]`-diagonal (power modulus). -/
theorem uniformContinuous_frobToBI
    (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1) :
    @UniformContinuous _ _ (blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) _
      ((blocToBI p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1).comp (frobBloc p F ϖ)) := by
  letI : UniformSpace (Bloc p F ϖ) := blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  haveI : IsUniformAddGroup (Bloc p F ϖ) :=
    isUniformAddGroup_blocWI p F ϖ
  haveI : IsUniformAddGroup ↥(BISub p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) :=
    isUniformAddGroup_BISub p F ϖ
  refine uniformContinuous_of_tendsto_zero ?_
  rw [tendsto_subtype_rng]
  have hcoe : (fun z => (((blocToBI p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1).comp
      (frobBloc p F ϖ) z : ↥(BISub p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1))
        : (hatK p F hρ₁p0 hρ₁p1) × (hatK p F hρ₂p0 hρ₂p1)))
      = fun z => BIProd p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 (frobBloc p F ϖ z) := rfl
  rw [hcoe]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨ε, hε, hball⟩ := exists_wI_ball_subset p F
    (hρ₁0 := hρ₁p0) (hρ₁1 := hρ₁p1) (hρ₂0 := hρ₂p0) (hρ₂1 := hρ₂p1) hU
  set δ : NNReal := ε ^ ((p : ℝ)⁻¹) with hδdef
  have hδ : 0 < δ := NNReal.rpow_pos hε
  have hδp : δ ^ p ≤ ε := by
    rw [hδdef, ← NNReal.rpow_natCast (ε ^ ((p : ℝ)⁻¹)) p, ← NNReal.rpow_mul,
      inv_mul_cancel₀ (by
        have := Nat.Prime.pos (Fact.out : Nat.Prime p)
        exact_mod_cast this.ne'), NNReal.rpow_one]
  have hnhd : {w : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1) |
      wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1 w ≤ δ} ∈ nhds
        (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) := by
    have h := wI_ball_mem_nhds p F
      (0 : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)) hδ
    simpa using h
  rw [show (nhds (0 : Bloc p F ϖ))
      = Filter.comap (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
        (nhds (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 0)) from nhds_induced _ _]
  rw [map_zero]
  refine Filter.mem_of_superset (Filter.preimage_mem_comap hnhd) ?_
  intro z hz
  refine hball ?_
  show wI p F hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
    (BIProd p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 (frobBloc p F ϖ z)) ≤ ε
  have hzI : wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
      (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z) ≤ δ := hz
  rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK] at hzI ⊢
  rw [wLoc_frobBloc p F ϖ hρ₁0 hρ₁1 hρ₁p0 hρ₁p1,
    wLoc_frobBloc p F ϖ hρ₂0 hρ₂1 hρ₂p0 hρ₂p1]
  refine max_le ?_ ?_
  · refine le_trans (pow_le_pow_left₀ zero_le
      (le_trans (le_max_left _ _) hzI) p) hδp
  · refine le_trans (pow_le_pow_left₀ zero_le
      (le_trans (le_max_right _ _) hzI) p) hδp


/-- **Frobenius on the interval rings**: `φ : B^{[ρ₁,ρ₂]} →+* B^{[ρ₁^p,ρ₂^p]}`,
the dense extension of `frobBloc`. -/
noncomputable def biPhi (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1) :
    ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      →+* ↥(BISub p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) :=
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  haveI : CompleteSpace ↥(BISub p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) :=
    (isComplete_BISub p F ϖ).completeSpace_coe
  IsDenseInducing.extendRingHom
    (isUniformInducing_blocToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1))
    (denseRange_blocToBI p F ϖ)
    (uniformContinuous_frobToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)

/-- `φ` on the interval rings extends `frobBloc` on the dense layer. -/
theorem biPhi_blocToBI (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1) (z : Bloc p F ϖ) :
    biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
        hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
        (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 z)
      = blocToBI p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 (frobBloc p F ϖ z) := by
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  haveI : CompleteSpace ↥(BISub p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) :=
    (isComplete_BISub p F ϖ).completeSpace_coe
  exact IsDenseInducing.extend_eq
    ((isUniformInducing_blocToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)).isDenseInducing
      (denseRange_blocToBI p F ϖ))
    (uniformContinuous_frobToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1).continuous z

/-- The inverse Frobenius sends the inverted element to a unit of `Bloc`. -/
theorem isUnit_frobSymm_p_teichPi_image (y : Submonoid.powers
    ((p : Ainf p F) * teichPi p F ϖ)) :
    IsUnit (algebraMap (Ainf p F) (Bloc p F ϖ)
      ((frob p F).symm (y : Ainf p F))) := by
  obtain ⟨k, hk⟩ := y.2
  rw [show (y : Ainf p F) = ((p : Ainf p F) * teichPi p F ϖ) ^ k from hk.symm,
    map_pow, map_pow]
  refine IsUnit.pow k ?_
  rw [map_mul, map_natCast, map_mul]
  refine (isUnit_p_image p F ϖ).mul ?_
  -- the Teichmüller root is a unit since its p-th power is
  refine isUnit_of_mul_isUnit_left
    (y := algebraMap (Ainf p F) (Bloc p F ϖ)
      ((frob p F).symm (teichPi p F ϖ)) ^ (p - 1)) ?_
  rw [← pow_succ']
  rw [show p - 1 + 1 = p by
    have := Nat.Prime.pos (Fact.out : Nat.Prime p)
    omega]
  have hpow : (frob p F).symm (teichPi p F ϖ) ^ p = teichPi p F ϖ := by
    have h := congrArg (frob p F).symm (frob_teichPi p F ϖ)
    rw [RingEquiv.symm_apply_apply] at h
    rw [← map_pow, ← h]
  rw [← map_pow, hpow]
  exact isUnit_teichPi_image p F ϖ

/-- **The inverse Frobenius on `Bloc`.** -/
noncomputable def frobBlocSymm : Bloc p F ϖ →+* Bloc p F ϖ :=
  IsLocalization.lift (M := Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ))
    (g := (algebraMap (Ainf p F) (Bloc p F ϖ)).comp
      ((frob p F).symm : Ainf p F ≃+* Ainf p F).toRingHom)
    (fun y => isUnit_frobSymm_p_teichPi_image p F ϖ y)

@[simp]
theorem frobBlocSymm_algebraMap (x : Ainf p F) :
    frobBlocSymm p F ϖ (algebraMap (Ainf p F) (Bloc p F ϖ) x)
      = algebraMap (Ainf p F) (Bloc p F ϖ) ((frob p F).symm x) :=
  IsLocalization.lift_eq _ x

/-- The Frobenius round-trip on `Bloc` (forward-after-inverse). -/
theorem frobBloc_frobBlocSymm (z : Bloc p F ϖ) :
    frobBloc p F ϖ (frobBlocSymm p F ϖ z) = z := by
  have hext : (frobBloc p F ϖ).comp (frobBlocSymm p F ϖ)
      = RingHom.id (Bloc p F ϖ) := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) ?_
    ext x
    show frobBloc p F ϖ (frobBlocSymm p F ϖ
      (algebraMap (Ainf p F) (Bloc p F ϖ) x))
      = algebraMap (Ainf p F) (Bloc p F ϖ) x
    rw [frobBlocSymm_algebraMap, frobBloc_algebraMap,
      RingEquiv.apply_symm_apply]
  exact congrFun (congrArg (fun f => f.toFun) hext) z

/-- The Frobenius round-trip on `Bloc` (inverse-after-forward). -/
theorem frobBlocSymm_frobBloc (z : Bloc p F ϖ) :
    frobBlocSymm p F ϖ (frobBloc p F ϖ z) = z := by
  have hext : (frobBlocSymm p F ϖ).comp (frobBloc p F ϖ)
      = RingHom.id (Bloc p F ϖ) := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers ((p : Ainf p F) * teichPi p F ϖ)) ?_
    ext x
    show frobBlocSymm p F ϖ (frobBloc p F ϖ
      (algebraMap (Ainf p F) (Bloc p F ϖ) x))
      = algebraMap (Ainf p F) (Bloc p F ϖ) x
    rw [frobBloc_algebraMap, frobBlocSymm_algebraMap,
      RingEquiv.symm_apply_apply]
  exact congrFun (congrArg (fun f => f.toFun) hext) z

/-- **The inverse radius-change law**: `w_ρ(φ⁻¹ z)^p = w_{ρ^p}(z)`. -/
theorem wLoc_frobBlocSymm {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hρp0 : 0 < ρ ^ p) (hρp1 : ρ ^ p < 1) (z : Bloc p F ϖ) :
    wLoc p F ϖ hρ0 hρ1 (frobBlocSymm p F ϖ z) ^ p
      = wLoc p F ϖ hρp0 hρp1 z := by
  have h := wLoc_frobBloc p F ϖ hρ0 hρ1 hρp0 hρp1 (frobBlocSymm p F ϖ z)
  rw [frobBloc_frobBlocSymm] at h
  exact h.symm



/-- **The inverse Frobenius is uniformly continuous** from the
`[ρ₁^p,ρ₂^p]`-uniformity to the `[ρ₁,ρ₂]`-diagonal (root modulus). -/
theorem uniformContinuous_frobSymmToBI
    (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1) :
    @UniformContinuous _ _ (blocWIUniformSpace p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) _
      ((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).comp (frobBlocSymm p F ϖ)) := by
  have hppos : 0 < p := Nat.Prime.pos (Fact.out : Nat.Prime p)
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
  haveI : IsUniformAddGroup (Bloc p F ϖ) :=
    isUniformAddGroup_blocWI p F ϖ
  haveI : IsUniformAddGroup ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    isUniformAddGroup_BISub p F ϖ
  refine uniformContinuous_of_tendsto_zero ?_
  rw [tendsto_subtype_rng]
  have hcoe : (fun z => (((blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1).comp
      (frobBlocSymm p F ϖ) z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1))
        : (hatK p F hρ₁0 hρ₁1) × (hatK p F hρ₂0 hρ₂1)))
      = fun z => BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (frobBlocSymm p F ϖ z) := rfl
  rw [hcoe]
  intro U hU
  rw [Filter.mem_map]
  obtain ⟨ε, hε, hball⟩ := exists_wI_ball_subset p F
    (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hU
  have hδ : (0 : NNReal) < ε ^ p := pow_pos hε p
  have hnhd : {w : (hatK p F hρ₁p0 hρ₁p1) × (hatK p F hρ₂p0 hρ₂p1) |
      wI p F hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 w ≤ ε ^ p} ∈ nhds
        (0 : (hatK p F hρ₁p0 hρ₁p1) × (hatK p F hρ₂p0 hρ₂p1)) := by
    have h := wI_ball_mem_nhds p F
      (0 : (hatK p F hρ₁p0 hρ₁p1) × (hatK p F hρ₂p0 hρ₂p1)) hδ
    simpa using h
  rw [show (nhds (0 : Bloc p F ϖ))
      = Filter.comap (BIProd p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)
        (nhds (BIProd p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 0)) from nhds_induced _ _]
  rw [map_zero]
  refine Filter.mem_of_superset (Filter.preimage_mem_comap hnhd) ?_
  intro z hz
  refine hball ?_
  show wI p F hρ₁0 hρ₁1 hρ₂0 hρ₂1
    (BIProd p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (frobBlocSymm p F ϖ z)) ≤ ε
  have hzI : wI p F hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
      (BIProd p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 z) ≤ ε ^ p := hz
  rw [wI_BIProd, valued_BlocToHatK, valued_BlocToHatK] at hzI ⊢
  refine max_le ?_ ?_
  · refine le_of_pow_le_pow_left₀ hppos.ne' zero_le ?_
    rw [wLoc_frobBlocSymm p F ϖ hρ₁0 hρ₁1 hρ₁p0 hρ₁p1]
    exact le_trans (le_max_left _ _) hzI
  · refine le_of_pow_le_pow_left₀ hppos.ne' zero_le ?_
    rw [wLoc_frobBlocSymm p F ϖ hρ₂0 hρ₂1 hρ₂p0 hρ₂p1]
    exact le_trans (le_max_right _ _) hzI

/-- **The inverse Frobenius on the interval rings.** -/
noncomputable def biPhiInv (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1) :
    ↥(BISub p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)
      →+* ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
  haveI : CompleteSpace ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    (isComplete_BISub p F ϖ).completeSpace_coe
  IsDenseInducing.extendRingHom
    (isUniformInducing_blocToBI p F ϖ (hρ₁0 := hρ₁p0) (hρ₁1 := hρ₁p1)
      (hρ₂0 := hρ₂p0) (hρ₂1 := hρ₂p1))
    (denseRange_blocToBI p F ϖ)
    (uniformContinuous_frobSymmToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)

/-- `φ⁻¹` on the interval rings extends `frobBlocSymm` on the dense layer. -/
theorem biPhiInv_blocToBI (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1) (z : Bloc p F ϖ) :
    biPhiInv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
        (blocToBI p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 z)
      = blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 (frobBlocSymm p F ϖ z) := by
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
  haveI : CompleteSpace ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    (isComplete_BISub p F ϖ).completeSpace_coe
  exact IsDenseInducing.extend_eq
    ((isUniformInducing_blocToBI p F ϖ (hρ₁0 := hρ₁p0) (hρ₁1 := hρ₁p1)
      (hρ₂0 := hρ₂p0) (hρ₂1 := hρ₂p1)).isDenseInducing
      (denseRange_blocToBI p F ϖ))
    (uniformContinuous_frobSymmToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1).continuous z


/-- `φ` on the interval rings is continuous. -/
theorem biPhi_continuous (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1) :
    Continuous (biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) := by
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1
  haveI : CompleteSpace ↥(BISub p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) :=
    (isComplete_BISub p F ϖ).completeSpace_coe
  exact (uniformContinuous_uniformly_extend
    (isUniformInducing_blocToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1))
    (denseRange_blocToBI p F ϖ)
    (uniformContinuous_frobToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)).continuous

/-- `φ⁻¹` on the interval rings is continuous. -/
theorem biPhiInv_continuous (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1) :
    Continuous (biPhiInv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) := by
  letI : UniformSpace (Bloc p F ϖ) :=
    blocWIUniformSpace p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
  haveI : CompleteSpace ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1) :=
    (isComplete_BISub p F ϖ).completeSpace_coe
  exact (uniformContinuous_uniformly_extend
    (isUniformInducing_blocToBI p F ϖ (hρ₁0 := hρ₁p0) (hρ₁1 := hρ₁p1)
      (hρ₂0 := hρ₂p0) (hρ₂1 := hρ₂p1))
    (denseRange_blocToBI p F ϖ)
    (uniformContinuous_frobSymmToBI p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
      (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)).continuous

/-- The `φ`-round-trip on the interval rings (forward-after-inverse). -/
theorem biPhi_biPhiInv (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1)
    (z : ↥(BISub p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)) :
    biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)
        hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
        (biPhiInv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
          (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 z) = z := by
  have hfun : (⇑(biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)
      ∘ ⇑(biPhiInv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)) = id := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := hρ₁p0) (hρ₁1 := hρ₁p1) (hρ₂0 := hρ₂p0) (hρ₂1 := hρ₂p1)).equalizer
      (Continuous.comp
        (biPhi_continuous p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)
        (biPhiInv_continuous p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1))
      continuous_id (funext fun w => ?_)
    show biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
        (biPhiInv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
          (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
          (blocToBI p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 w))
      = blocToBI p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 w
    rw [biPhiInv_blocToBI, biPhi_blocToBI, frobBloc_frobBlocSymm]
  exact congrFun hfun z

/-- The `φ`-round-trip on the interval rings (inverse-after-forward). -/
theorem biPhiInv_biPhi (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1)
    (z : ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)) :
    biPhiInv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
        (biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
          (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1 z) = z := by
  have hfun : (⇑(biPhiInv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
      (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)
      ∘ ⇑(biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)) = id := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1)).equalizer
      (Continuous.comp
        (biPhiInv_continuous p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1)
        (biPhi_continuous p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
          (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1))
      continuous_id (funext fun w => ?_)
    show biPhiInv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
        (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
        (biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
          (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
          (blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 w))
      = blocToBI p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1 w
    rw [biPhi_blocToBI, biPhiInv_blocToBI, frobBlocSymm_frobBloc]
  exact congrFun hfun z

/-- **The Frobenius equivalence of interval rings**:
`φ : B^{[ρ₁,ρ₂]} ≃+* B^{[ρ₁^p,ρ₂^p]}` (D-iii). -/
noncomputable def biPhiEquiv (hρ₁p0 : 0 < ρ₁ ^ p) (hρ₁p1 : ρ₁ ^ p < 1)
    (hρ₂p0 : 0 < ρ₂ ^ p) (hρ₂p1 : ρ₂ ^ p < 1) :
    ↥(BISub p F ϖ hρ₁0 hρ₁1 hρ₂0 hρ₂1)
      ≃+* ↥(BISub p F ϖ hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) where
  toFun := biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
    (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
  invFun := biPhiInv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1) (hρ₂0 := hρ₂0)
    (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
  left_inv := biPhiInv_biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
  right_inv := biPhi_biPhiInv p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1
  map_mul' x y := map_mul (biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) x y
  map_add' x y := map_add (biPhi p F ϖ (hρ₁0 := hρ₁0) (hρ₁1 := hρ₁1)
    (hρ₂0 := hρ₂0) (hρ₂1 := hρ₂1) hρ₁p0 hρ₁p1 hρ₂p0 hρ₂p1) x y

/-- The `p`-th power of a rational radius is the radius at `p`-times the
exponent. -/
theorem vpiQ_pow_p (q : ℚ) :
    vpiQ p F ϖ q ^ p = vpiQ p F ϖ ((p : ℚ) * q) := by
  rw [vpiQ, vpiQ, ← NNReal.rpow_natCast (_ ^ (q : ℝ)) p, ← NNReal.rpow_mul]
  congr 1
  push_cast
  ring

theorem mulQ_pos {q : ℚ} (hq : 0 < q) : (0 : ℚ) < (p : ℚ) * q := by
  have hp : (0 : ℚ) < p := by
    exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
  positivity

/-- **Frobenius on the rational-exponent interval rings** (forward hom,
abstract-target form): for target radii `σᵢ` EQUAL to `vpiQ(qᵢ)^p`, Frobenius
maps `BIQ q₁ q₂` into `B^{[σ₁,σ₂]}`. The abstract `σ`-variables keep the
instance keys atomic (PERF). -/
noncomputable def biPhiQ (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
    {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
    (hσ₁ : vpiQ p F ϖ q₁ ^ p = σ₁) (hσ₂ : vpiQ p F ϖ q₂ ^ p = σ₂) :
    ↥(BIQ p F ϖ q₁ q₂ h₁ h₂) →+* ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) :=
  (biCongr p F ϖ hσ₁ hσ₂
      (hρ₁0' := hσ₁0) (hρ₁1' := hσ₁1) (hρ₂0' := hσ₂0) (hρ₂1' := hσ₂1)).toRingHom.comp
    (biPhi p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)
      (hσ₁ ▸ pow_pos (vpiQ_pos p F ϖ q₁) p)
      (hσ₁ ▸ pow_lt_one₀ zero_le (vpiQ_lt_one p F ϖ h₁)
        (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
      (hσ₂ ▸ pow_pos (vpiQ_pos p F ϖ q₂) p)
      (hσ₂ ▸ pow_lt_one₀ zero_le (vpiQ_lt_one p F ϖ h₂)
        (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))))


/-- `φ` on `BIQ` extends `frobBloc` on the dense layer (abstract-target
form). -/
theorem biPhiQ_blocToBI (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
    {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
    (hσ₁ : vpiQ p F ϖ q₁ ^ p = σ₁) (hσ₂ : vpiQ p F ϖ q₂ ^ p = σ₂)
    (z : Bloc p F ϖ) :
    biPhiQ p F ϖ q₁ q₂ h₁ h₂ hσ₁ hσ₂
        (blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
          (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z)
      = blocToBI p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 (frobBloc p F ϖ z) := by
  show (biCongr p F ϖ hσ₁ hσ₂) (biPhi p F ϖ _ _ _ _
    (blocToBI p F ϖ _ _ _ _ z)) = _
  rw [biPhi_blocToBI, biCongr_blocToBI]

/-- **Inverse Frobenius on the rational-exponent interval rings**
(abstract-source form). -/
noncomputable def biPhiInvQ (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
    {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
    (hσ₁ : vpiQ p F ϖ q₁ ^ p = σ₁) (hσ₂ : vpiQ p F ϖ q₂ ^ p = σ₂) :
    ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1) →+* ↥(BIQ p F ϖ q₁ q₂ h₁ h₂) :=
  (biPhiInv p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)
      (hσ₁ ▸ pow_pos (vpiQ_pos p F ϖ q₁) p)
      (hσ₁ ▸ pow_lt_one₀ zero_le (vpiQ_lt_one p F ϖ h₁)
        (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
      (hσ₂ ▸ pow_pos (vpiQ_pos p F ϖ q₂) p)
      (hσ₂ ▸ pow_lt_one₀ zero_le (vpiQ_lt_one p F ϖ h₂)
        (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))).comp
    (biCongr p F ϖ hσ₁.symm hσ₂.symm
      (hρ₁0' := hσ₁ ▸ pow_pos (vpiQ_pos p F ϖ q₁) p)
      (hρ₁1' := hσ₁ ▸ pow_lt_one₀ zero_le (vpiQ_lt_one p F ϖ h₁)
        (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
      (hρ₂0' := hσ₂ ▸ pow_pos (vpiQ_pos p F ϖ q₂) p)
      (hρ₂1' := hσ₂ ▸ pow_lt_one₀ zero_le (vpiQ_lt_one p F ϖ h₂)
        (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))).toRingHom

/-- The inverse extends `frobBlocSymm` on the dense layer. -/
theorem biPhiInvQ_blocToBI (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
    {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
    (hσ₁ : vpiQ p F ϖ q₁ ^ p = σ₁) (hσ₂ : vpiQ p F ϖ q₂ ^ p = σ₂)
    (z : Bloc p F ϖ) :
    biPhiInvQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂
        (blocToBI p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 z)
      = blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
          (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂)
          (frobBlocSymm p F ϖ z) := by
  show (biPhiInv p F ϖ _ _ _ _) ((biCongr p F ϖ hσ₁.symm hσ₂.symm)
    (blocToBI p F ϖ _ _ _ _ z)) = _
  rw [biCongr_blocToBI, biPhiInv_blocToBI]


/-- `biPhiQ` is continuous. -/
theorem biPhiQ_continuous (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
    {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
    (hσ₁ : vpiQ p F ϖ q₁ ^ p = σ₁) (hσ₂ : vpiQ p F ϖ q₂ ^ p = σ₂) :
    Continuous (biPhiQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂) := by
  rw [biPhiQ]
  exact (biCongr_continuous p F ϖ hσ₁ hσ₂).comp
    (biPhi_continuous p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)
      (hσ₁ ▸ pow_pos (vpiQ_pos p F ϖ q₁) p)
      (hσ₁ ▸ pow_lt_one₀ zero_le (vpiQ_lt_one p F ϖ h₁)
        (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
      (hσ₂ ▸ pow_pos (vpiQ_pos p F ϖ q₂) p)
      (hσ₂ ▸ pow_lt_one₀ zero_le (vpiQ_lt_one p F ϖ h₂)
        (Nat.Prime.ne_zero (Fact.out : Nat.Prime p))))

/-- `biPhiInvQ` is continuous. -/
theorem biPhiInvQ_continuous (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
    {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
    (hσ₁ : vpiQ p F ϖ q₁ ^ p = σ₁) (hσ₂ : vpiQ p F ϖ q₂ ^ p = σ₂) :
    Continuous (biPhiInvQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂) := by
  rw [biPhiInvQ]
  exact (biPhiInv_continuous p F ϖ
    (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
    (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)
    (hσ₁ ▸ pow_pos (vpiQ_pos p F ϖ q₁) p)
    (hσ₁ ▸ pow_lt_one₀ zero_le (vpiQ_lt_one p F ϖ h₁)
      (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))
    (hσ₂ ▸ pow_pos (vpiQ_pos p F ϖ q₂) p)
    (hσ₂ ▸ pow_lt_one₀ zero_le (vpiQ_lt_one p F ϖ h₂)
      (Nat.Prime.ne_zero (Fact.out : Nat.Prime p)))).comp
    (biCongr_continuous p F ϖ hσ₁.symm hσ₂.symm)

/-- The `Q`-level round-trip (inverse-after-forward). -/
theorem biPhiInvQ_biPhiQ (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
    {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
    (hσ₁ : vpiQ p F ϖ q₁ ^ p = σ₁) (hσ₂ : vpiQ p F ϖ q₂ ^ p = σ₂)
    (z : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)) :
    biPhiInvQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂
      (biPhiQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂ z) = z := by
  have hfun : (⇑(biPhiInvQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂)
      ∘ ⇑(biPhiQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂)) = id := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)).equalizer
      ((biPhiInvQ_continuous p F ϖ q₁ q₂ h₁ h₂ hσ₁ hσ₂).comp
        (biPhiQ_continuous p F ϖ q₁ q₂ h₁ h₂ hσ₁ hσ₂))
      continuous_id (funext fun w => ?_)
    show biPhiInvQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂
        (biPhiQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂
          (blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
            (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) w))
      = blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
          (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) w
    rw [biPhiQ_blocToBI, biPhiInvQ_blocToBI, frobBlocSymm_frobBloc]
  exact congrFun hfun z

/-- The `Q`-level round-trip (forward-after-inverse). -/
theorem biPhiQ_biPhiInvQ (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    {σ₁ σ₂ : NNReal} {hσ₁0 : 0 < σ₁} {hσ₁1 : σ₁ < 1}
    {hσ₂0 : 0 < σ₂} {hσ₂1 : σ₂ < 1}
    (hσ₁ : vpiQ p F ϖ q₁ ^ p = σ₁) (hσ₂ : vpiQ p F ϖ q₂ ^ p = σ₂)
    (z : ↥(BISub p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1)) :
    biPhiQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂
      (biPhiInvQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂ z) = z := by
  have hfun : (⇑(biPhiQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂)
      ∘ ⇑(biPhiInvQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂)) = id := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := hσ₁0) (hρ₁1 := hσ₁1) (hρ₂0 := hσ₂0) (hρ₂1 := hσ₂1)).equalizer
      ((biPhiQ_continuous p F ϖ q₁ q₂ h₁ h₂ hσ₁ hσ₂).comp
        (biPhiInvQ_continuous p F ϖ q₁ q₂ h₁ h₂ hσ₁ hσ₂))
      continuous_id (funext fun w => ?_)
    show biPhiQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂
        (biPhiInvQ p F ϖ q₁ q₂ h₁ h₂ (hσ₁0 := hσ₁0) (hσ₁1 := hσ₁1) (hσ₂0 := hσ₂0) (hσ₂1 := hσ₂1) hσ₁ hσ₂
          (blocToBI p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 w))
      = blocToBI p F ϖ hσ₁0 hσ₁1 hσ₂0 hσ₂1 w
    rw [biPhiInvQ_blocToBI, biPhiQ_blocToBI, frobBloc_frobBlocSymm]
  exact congrFun hfun z

/-- Frobenius at the `BIQ`-level with `p`-multiplied target exponents (the
`vpiQ_pow_p`-instantiation of the abstract form). -/
noncomputable def biPhiQP (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)
      →+* ↥(BIQ p F ϖ ((p : ℚ) * q₁) ((p : ℚ) * q₂)
          (mulQ_pos p h₁) (mulQ_pos p h₂)) :=
  biPhiQ p F ϖ q₁ q₂ h₁ h₂
    (hσ₁0 := vpiQ_pos p F ϖ ((p : ℚ) * q₁))
    (hσ₁1 := vpiQ_lt_one p F ϖ (mulQ_pos p h₁))
    (hσ₂0 := vpiQ_pos p F ϖ ((p : ℚ) * q₂))
    (hσ₂1 := vpiQ_lt_one p F ϖ (mulQ_pos p h₂))
    (vpiQ_pow_p p F ϖ q₁) (vpiQ_pow_p p F ϖ q₂)

theorem biPhiQP_blocToBI (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (z : Bloc p F ϖ) :
    biPhiQP p F ϖ q₁ q₂ h₁ h₂
        (blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
          (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) z)
      = blocToBI p F ϖ (vpiQ_pos p F ϖ ((p : ℚ) * q₁))
          (vpiQ_lt_one p F ϖ (mulQ_pos p h₁))
          (vpiQ_pos p F ϖ ((p : ℚ) * q₂))
          (vpiQ_lt_one p F ϖ (mulQ_pos p h₂)) (frobBloc p F ϖ z) :=
  biPhiQ_blocToBI p F ϖ q₁ q₂ h₁ h₂
    (hσ₁0 := vpiQ_pos p F ϖ ((p : ℚ) * q₁))
    (hσ₁1 := vpiQ_lt_one p F ϖ (mulQ_pos p h₁))
    (hσ₂0 := vpiQ_pos p F ϖ ((p : ℚ) * q₂))
    (hσ₂1 := vpiQ_lt_one p F ϖ (mulQ_pos p h₂))
    (vpiQ_pow_p p F ϖ q₁) (vpiQ_pow_p p F ϖ q₂) z

theorem biPhiQP_continuous (q₁ q₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂) :
    Continuous (biPhiQP p F ϖ q₁ q₂ h₁ h₂) :=
  biPhiQ_continuous p F ϖ q₁ q₂ h₁ h₂
    (hσ₁0 := vpiQ_pos p F ϖ ((p : ℚ) * q₁))
    (hσ₁1 := vpiQ_lt_one p F ϖ (mulQ_pos p h₁))
    (hσ₂0 := vpiQ_pos p F ϖ ((p : ℚ) * q₂))
    (hσ₂1 := vpiQ_lt_one p F ϖ (mulQ_pos p h₂))
    (vpiQ_pow_p p F ϖ q₁) (vpiQ_pow_p p F ϖ q₂)

/-- The scaled sub-interval conditions. -/
theorem mulQ_mem {q₁ q₂ r : ℚ} (h : q₂ ≤ r ∧ r ≤ q₁) :
    (p : ℚ) * q₂ ≤ (p : ℚ) * r ∧ (p : ℚ) * r ≤ (p : ℚ) * q₁ := by
  have hp : (0 : ℚ) < p := by
    exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
  exact ⟨by nlinarith [h.1], by nlinarith [h.2]⟩

theorem mulQ_lt {q₁ q₂ : ℚ} (h : q₂ < q₁) : (p : ℚ) * q₂ < (p : ℚ) * q₁ := by
  have hp : (0 : ℚ) < p := by
    exact_mod_cast Nat.Prime.pos (Fact.out : Nat.Prime p)
  nlinarith

/-- **The `φ`-restriction compatibility square** at the `BIQ`-level:
Frobenius commutes with the interval restrictions. -/
theorem biPhiQP_biResQ_comm (q₁ q₂ r₁ r₂ : ℚ) (h₁ : 0 < q₁) (h₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hlt : q₂ < q₁)
    (hr₁m : q₂ ≤ r₁ ∧ r₁ ≤ q₁) (hr₂m : q₂ ≤ r₂ ∧ r₂ ≤ q₁)
    (z : ↥(BIQ p F ϖ q₁ q₂ h₁ h₂)) :
    biPhiQP p F ϖ r₁ r₂ hr₁ hr₂
        (biResQ p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m z)
      = biResQ p F ϖ ((p : ℚ) * q₁) ((p : ℚ) * q₂)
          ((p : ℚ) * r₁) ((p : ℚ) * r₂)
          (mulQ_pos p h₁) (mulQ_pos p h₂) (mulQ_pos p hr₁) (mulQ_pos p hr₂)
          (mulQ_lt p hlt) (mulQ_mem p hr₁m) (mulQ_mem p hr₂m)
          (biPhiQP p F ϖ q₁ q₂ h₁ h₂ z) := by
  have hfun : (⇑(biPhiQP p F ϖ r₁ r₂ hr₁ hr₂)
      ∘ ⇑(biResQ p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m))
      = (⇑(biResQ p F ϖ ((p : ℚ) * q₁) ((p : ℚ) * q₂)
          ((p : ℚ) * r₁) ((p : ℚ) * r₂)
          (mulQ_pos p h₁) (mulQ_pos p h₂) (mulQ_pos p hr₁) (mulQ_pos p hr₂)
          (mulQ_lt p hlt) (mulQ_mem p hr₁m) (mulQ_mem p hr₂m))
        ∘ ⇑(biPhiQP p F ϖ q₁ q₂ h₁ h₂)) := by
    refine (denseRange_blocToBI p F ϖ
      (hρ₁0 := vpiQ_pos p F ϖ q₁) (hρ₁1 := vpiQ_lt_one p F ϖ h₁)
      (hρ₂0 := vpiQ_pos p F ϖ q₂) (hρ₂1 := vpiQ_lt_one p F ϖ h₂)).equalizer
      ((biPhiQP_continuous p F ϖ r₁ r₂ hr₁ hr₂).comp
        (biResQ_continuous p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m))
      ((biResQ_continuous p F ϖ ((p : ℚ) * q₁) ((p : ℚ) * q₂)
          ((p : ℚ) * r₁) ((p : ℚ) * r₂)
          (mulQ_pos p h₁) (mulQ_pos p h₂) (mulQ_pos p hr₁) (mulQ_pos p hr₂)
          (mulQ_lt p hlt) (mulQ_mem p hr₁m) (mulQ_mem p hr₂m)).comp
        (biPhiQP_continuous p F ϖ q₁ q₂ h₁ h₂))
      (funext fun w => ?_)
    show biPhiQP p F ϖ r₁ r₂ hr₁ hr₂
        (biResQ p F ϖ q₁ q₂ r₁ r₂ h₁ h₂ hr₁ hr₂ hlt hr₁m hr₂m
          (blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
            (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) w))
      = biResQ p F ϖ ((p : ℚ) * q₁) ((p : ℚ) * q₂)
          ((p : ℚ) * r₁) ((p : ℚ) * r₂)
          (mulQ_pos p h₁) (mulQ_pos p h₂) (mulQ_pos p hr₁) (mulQ_pos p hr₂)
          (mulQ_lt p hlt) (mulQ_mem p hr₁m) (mulQ_mem p hr₂m)
          (biPhiQP p F ϖ q₁ q₂ h₁ h₂
            (blocToBI p F ϖ (vpiQ_pos p F ϖ q₁) (vpiQ_lt_one p F ϖ h₁)
              (vpiQ_pos p F ϖ q₂) (vpiQ_lt_one p F ϖ h₂) w))
    rw [biResQ_blocToBI, biPhiQP_blocToBI, biPhiQP_blocToBI,
      biResQ_blocToBI]
  exact congrFun hfun z

end FarguesFontaine

end
