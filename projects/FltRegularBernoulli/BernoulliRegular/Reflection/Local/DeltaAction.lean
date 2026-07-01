module

public import BernoulliRegular.Reflection.Local.Filtration
public import BernoulliRegular.Reflection.Local.Completion
public import BernoulliRegular.Reflection.Local.UnitQuotient
public import BernoulliRegular.UnitQuotient.DeltaAction

/-!
# Cyclotomic action on lambda-local and completed units

This file starts REF-11b.  It proves that the cyclotomic
`Delta = (ZMod p)^*` automorphisms preserve the distinguished prime
`lambda = (zeta_p - 1)`, hence act on the localization at `lambda` and preserve
the local principal-unit filtration. It also lifts those automorphisms through
the lambda-adic completion.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular
namespace Reflection
namespace Local

section CompletionLift

variable {R : Type*} [CommRing R] (I : Ideal R)

theorem evalₐ_factor_pow_le {m n : ℕ} (hmn : m ≤ n)
    (x : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n x) =
      AdicCompletion.evalₐ I m x := by
  simp only [AdicCompletion.evalₐ, AlgHom.coe_comp, Function.comp_apply,
    AlgHom.ofLinearMap_apply]
  have htrans :
      AdicCompletion.transitionMap I R hmn ((AdicCompletion.eval I R n) x) =
        ((AdicCompletion.eval I R m) x) :=
    AdicCompletion.transitionMap_comp_eval_apply (I := I) (M := R) hmn x
  rw [← htrans]
  induction ((AdicCompletion.eval I R n) x) using Quotient.inductionOn' with
  | h r =>
    rfl

theorem ideal_pow_map_ringEquiv_eq_of_map_eq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) (n : ℕ) :
    (I ^ n).map (e : R →+* R) = I ^ n := by
  rw [Ideal.map_pow, he]

theorem ideal_pow_le_comap_ringEquiv_of_map_eq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) (n : ℕ) :
    I ^ n ≤ (I ^ n).comap (e : R →+* R) := by
  rw [← Ideal.map_le_iff_le_comap]
  exact (ideal_pow_map_ringEquiv_eq_of_map_eq (I := I) e he n).le

theorem ideal_map_ringEquiv_symm_eq_of_map_eq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) :
    I.map (e.symm : R →+* R) = I := by
  have h := congrArg (fun J : Ideal R ↦ J.map (e.symm : R →+* R)) he
  simpa using h.symm

noncomputable def adicCompletionRingHomOfIdealMapEqFamily
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) (n : ℕ) :
    AdicCompletion I R →+* R ⧸ I ^ n :=
  (Ideal.quotientMap (I ^ n) (e : R →+* R)
    (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)).comp
    (AdicCompletion.evalₐ I n).toRingHom

theorem adicCompletionRingHomOfIdealMapEqFamily_compatible
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I)
    {m n : ℕ} (hmn : m ≤ n) :
    (Ideal.Quotient.factorPow I hmn).comp
        (adicCompletionRingHomOfIdealMapEqFamily (I := I) e he n) =
      adicCompletionRingHomOfIdealMapEqFamily (I := I) e he m := by
  ext x
  simp only [RingHom.coe_comp, Function.comp_apply]
  change
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
        (Ideal.quotientMap (I ^ n) (e : R →+* R)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)
          (AdicCompletion.evalₐ I n x)) =
      Ideal.quotientMap (I ^ m) (e : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he m)
        (AdicCompletion.evalₐ I m x)
  rw [← evalₐ_factor_pow_le (I := I) hmn x]
  induction AdicCompletion.evalₐ I n x using Quotient.inductionOn' with
  | h r =>
    rfl

/-- A ring automorphism preserving `I` lifts to an endomorphism of the
`I`-adic completion. -/
noncomputable def adicCompletionRingHomOfIdealMapEq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) :
    AdicCompletion I R →+* AdicCompletion I R :=
  AdicCompletion.liftRingHom I
    (adicCompletionRingHomOfIdealMapEqFamily (I := I) e he)
    (adicCompletionRingHomOfIdealMapEqFamily_compatible (I := I) e he)

@[simp]
theorem evalₐ_adicCompletionRingHomOfIdealMapEq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I)
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (adicCompletionRingHomOfIdealMapEq (I := I) e he x) =
      Ideal.quotientMap (I ^ n) (e : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)
        (AdicCompletion.evalₐ I n x) :=
  AdicCompletion.evalₐ_liftRingHom I
    (adicCompletionRingHomOfIdealMapEqFamily (I := I) e he)
    (adicCompletionRingHomOfIdealMapEqFamily_compatible (I := I) e he)
    n x

theorem quotientMap_ringEquiv_symm_apply_quotientMap_ringEquiv
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I)
    (n : ℕ) (x : R ⧸ I ^ n) :
    Ideal.quotientMap (I ^ n) (e.symm : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e.symm
          (ideal_map_ringEquiv_symm_eq_of_map_eq (I := I) e he) n)
        (Ideal.quotientMap (I ^ n) (e : R →+* R)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n) x) =
      x := by
  induction x using Quotient.inductionOn' with
  | h r =>
    change Ideal.Quotient.mk (I ^ n) (e.symm (e r)) =
      Ideal.Quotient.mk (I ^ n) r
    rw [RingEquiv.symm_apply_apply]

theorem quotientMap_ringEquiv_apply_quotientMap_ringEquiv_symm
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I)
    (n : ℕ) (x : R ⧸ I ^ n) :
    Ideal.quotientMap (I ^ n) (e : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)
        (Ideal.quotientMap (I ^ n) (e.symm : R →+* R)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e.symm
            (ideal_map_ringEquiv_symm_eq_of_map_eq (I := I) e he) n) x) =
      x := by
  induction x using Quotient.inductionOn' with
  | h r =>
    change Ideal.Quotient.mk (I ^ n) (e (e.symm r)) =
      Ideal.Quotient.mk (I ^ n) r
    rw [RingEquiv.apply_symm_apply]

theorem quotientMap_ringEquiv_refl
    (n : ℕ) (x : R ⧸ I ^ n) :
    Ideal.quotientMap (I ^ n) (RingEquiv.refl R : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) (RingEquiv.refl R) (by simp) n)
        x =
      x := by
  induction x using Quotient.inductionOn' with
  | h r =>
    rfl

theorem quotientMap_ringEquiv_trans
    (e f : R ≃+* R)
    (he : I.map (e : R →+* R) = I)
    (hf : I.map (f : R →+* R) = I)
    (hef : I.map (f.trans e : R →+* R) = I)
    (n : ℕ) (x : R ⧸ I ^ n) :
    Ideal.quotientMap (I ^ n) (f.trans e : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) (f.trans e) hef n) x =
      Ideal.quotientMap (I ^ n) (e : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)
        (Ideal.quotientMap (I ^ n) (f : R →+* R)
          (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) f hf n) x) := by
  induction x using Quotient.inductionOn' with
  | h r =>
    change Ideal.Quotient.mk (I ^ n) (e (f r)) =
      Ideal.Quotient.mk (I ^ n) (e (f r))
    rfl

/-- A ring automorphism preserving `I` lifts to an automorphism of the
`I`-adic completion. -/
noncomputable def adicCompletionRingEquivOfIdealMapEq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I) :
    AdicCompletion I R ≃+* AdicCompletion I R where
  __ := adicCompletionRingHomOfIdealMapEq (I := I) e he
  invFun :=
    adicCompletionRingHomOfIdealMapEq (I := I) e.symm
      (ideal_map_ringEquiv_symm_eq_of_map_eq (I := I) e he)
  left_inv x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n
        (adicCompletionRingHomOfIdealMapEq (I := I) e.symm
          (ideal_map_ringEquiv_symm_eq_of_map_eq (I := I) e he)
          (adicCompletionRingHomOfIdealMapEq (I := I) e he x)) =
      AdicCompletion.evalₐ I n x
    rw [evalₐ_adicCompletionRingHomOfIdealMapEq,
      evalₐ_adicCompletionRingHomOfIdealMapEq,
      quotientMap_ringEquiv_symm_apply_quotientMap_ringEquiv (I := I) e he n]
  right_inv x := by
    apply AdicCompletion.ext_evalₐ
    intro n
    change AdicCompletion.evalₐ I n
        (adicCompletionRingHomOfIdealMapEq (I := I) e he
          (adicCompletionRingHomOfIdealMapEq (I := I) e.symm
            (ideal_map_ringEquiv_symm_eq_of_map_eq (I := I) e he) x)) =
      AdicCompletion.evalₐ I n x
    rw [evalₐ_adicCompletionRingHomOfIdealMapEq,
      evalₐ_adicCompletionRingHomOfIdealMapEq,
      quotientMap_ringEquiv_apply_quotientMap_ringEquiv_symm (I := I) e he n]

@[simp]
theorem evalₐ_adicCompletionRingEquivOfIdealMapEq
    (e : R ≃+* R) (he : I.map (e : R →+* R) = I)
    (n : ℕ) (x : AdicCompletion I R) :
    AdicCompletion.evalₐ I n (adicCompletionRingEquivOfIdealMapEq (I := I) e he x) =
      Ideal.quotientMap (I ^ n) (e : R →+* R)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he n)
        (AdicCompletion.evalₐ I n x) :=
  evalₐ_adicCompletionRingHomOfIdealMapEq (I := I) e he n x

end CompletionLift

section CyclotomicSetup

variable (p : ℕ) [Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The cyclotomic automorphism sends `zeta_p - 1` into the distinguished
prime `(zeta_p - 1)`. -/
theorem cyclotomicRingOfIntegersEquiv_zeta_sub_one_mem_lambda
    (a : CyclotomicUnitDelta p) :
    cyclotomicRingOfIntegersEquiv (p := p) K a
        ((zeta_spec p ℚ K).toInteger - 1) ∈ cyclotomicLambda p K := by
  have hdiv :
      ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
        ((zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (a : ZMod p).val - 1 := by
    simpa using
      sub_dvd_pow_sub_pow ((zeta_spec p ℚ K).toInteger : 𝓞 K) (1 : 𝓞 K)
        (a : ZMod p).val
  rw [cyclotomicLambda, zetaPrime, Ideal.mem_span_singleton]
  change ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
    cyclotomicRingOfIntegersEquiv (p := p) K a ((zeta_spec p ℚ K).toInteger - 1)
  rw [map_sub, map_one]
  change ((zeta_spec p ℚ K).toInteger : 𝓞 K) - 1 ∣
    cyclotomicSigmaOfUnit (p := p) K a • (zeta_spec p ℚ K).toInteger - 1
  rw [cyclotomicSigmaOfUnit_smul_zetaInteger]
  exact hdiv

theorem cyclotomicRingOfIntegersEquiv_map_lambda_le
    (a : CyclotomicUnitDelta p) :
    (cyclotomicLambda p K).map
        (cyclotomicRingOfIntegersEquiv (p := p) K a : 𝓞 K →+* 𝓞 K) ≤
      cyclotomicLambda p K := by
  rw [cyclotomicLambda, zetaPrime, Ideal.map_span, Ideal.span_le]
  rintro x ⟨y, hy, rfl⟩
  simp only [Set.mem_singleton_iff] at hy
  subst hy
  exact cyclotomicRingOfIntegersEquiv_zeta_sub_one_mem_lambda (p := p) (K := K) a

theorem cyclotomicRingOfIntegersEquiv_comap_lambda
    (a : CyclotomicUnitDelta p) :
    cyclotomicLambda p K =
      (cyclotomicLambda p K).comap
        (cyclotomicRingOfIntegersEquiv (p := p) K a : 𝓞 K →+* 𝓞 K) := by
  ext x
  constructor
  · intro hx
    exact cyclotomicRingOfIntegersEquiv_map_lambda_le (p := p) (K := K) a
      (Ideal.mem_map_of_mem _ hx)
  · intro hx
    rw [Ideal.mem_comap] at hx
    have hinv :
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
            (cyclotomicRingOfIntegersEquiv (p := p) K a x) ∈ cyclotomicLambda p K :=
      cyclotomicRingOfIntegersEquiv_map_lambda_le (p := p) (K := K) a⁻¹
        (Ideal.mem_map_of_mem
          (cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹ : 𝓞 K →+* 𝓞 K) hx)
    have hcomp :
        cyclotomicRingOfIntegersEquiv (p := p) K a⁻¹
            (cyclotomicRingOfIntegersEquiv (p := p) K a x) = x := by
      rw [← cyclotomicRingOfIntegersEquiv_mul_apply]
      simp
    simpa [hcomp] using hinv

/-- The cyclotomic automorphism of the localized ring at lambda. -/
noncomputable def localCyclotomicRingEquiv
    (a : CyclotomicUnitDelta p) :
    localCyclotomicRing p K ≃+* localCyclotomicRing p K :=
  Localization.localRingEquiv (cyclotomicLambda p K) (cyclotomicLambda p K)
    (cyclotomicRingOfIntegersEquiv (p := p) K a)
    (cyclotomicRingOfIntegersEquiv_comap_lambda (p := p) (K := K) a)

@[simp]
theorem localCyclotomicRingEquiv_algebraMap
    (a : CyclotomicUnitDelta p) (x : 𝓞 K) :
    localCyclotomicRingEquiv (p := p) K a
        (algebraMap (𝓞 K) (localCyclotomicRing p K) x) =
      algebraMap (𝓞 K) (localCyclotomicRing p K)
        (cyclotomicRingOfIntegersEquiv (p := p) K a x) :=
  Localization.localRingHom_to_map (I := cyclotomicLambda p K)
    (J := cyclotomicLambda p K)
    (f := cyclotomicRingOfIntegersEquiv (p := p) K a)
    (hIJ := cyclotomicRingOfIntegersEquiv_comap_lambda (p := p) (K := K) a) x

theorem localCyclotomicRingEquiv_one :
    localCyclotomicRingEquiv (p := p) K 1 = RingEquiv.refl (localCyclotomicRing p K) := by
  have hhom :
      (localCyclotomicRingEquiv (p := p) K 1 :
        localCyclotomicRing p K →+* localCyclotomicRing p K) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (cyclotomicLambda p K).primeCompl
    ext x
    simp [localCyclotomicRingEquiv_algebraMap]
  apply RingEquiv.ext
  intro x
  exact RingHom.congr_fun hhom x

theorem localCyclotomicRingEquiv_mul
    (a b : CyclotomicUnitDelta p) :
    localCyclotomicRingEquiv (p := p) K (a * b) =
      (localCyclotomicRingEquiv (p := p) K b).trans
        (localCyclotomicRingEquiv (p := p) K a) := by
  have hhom :
      (localCyclotomicRingEquiv (p := p) K (a * b) :
        localCyclotomicRing p K →+* localCyclotomicRing p K) =
        ((localCyclotomicRingEquiv (p := p) K a :
          localCyclotomicRing p K →+* localCyclotomicRing p K).comp
          (localCyclotomicRingEquiv (p := p) K b :
            localCyclotomicRing p K →+* localCyclotomicRing p K)) := by
    apply IsLocalization.ringHom_ext (cyclotomicLambda p K).primeCompl
    ext x
    simp [localCyclotomicRingEquiv_algebraMap,
      cyclotomicRingOfIntegersEquiv_mul_apply]
  apply RingEquiv.ext
  intro x
  exact RingHom.congr_fun hhom x

/-- The actual `Delta` action on the lambda-local cyclotomic ring. -/
noncomputable def localCyclotomicRingDeltaAction :
    CyclotomicUnitDelta p →* RingAut (localCyclotomicRing p K) where
  toFun a := localCyclotomicRingEquiv (p := p) K a
  map_one' := localCyclotomicRingEquiv_one (p := p) (K := K)
  map_mul' a b := localCyclotomicRingEquiv_mul (p := p) (K := K) a b

theorem localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
    (a : CyclotomicUnitDelta p) :
    (localCyclotomicMaximalIdeal p K).map
        (localCyclotomicRingEquiv (p := p) K a : localCyclotomicRing p K →+*
          localCyclotomicRing p K) =
      localCyclotomicMaximalIdeal p K := by
  rw [Ideal.map_comap_of_equiv (localCyclotomicRingEquiv (p := p) K a)]
  ext x
  rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal,
    mem_nonunits_iff, mem_nonunits_iff]
  constructor
  · intro hx hunit
    exact hx (by simpa using hunit.map (localCyclotomicRingEquiv (p := p) K a).symm)
  · intro hx hunit
    exact hx (by simpa using hunit.map (localCyclotomicRingEquiv (p := p) K a))

theorem localCyclotomicMaximalIdeal_pow_map_localCyclotomicRingEquiv
    (a : CyclotomicUnitDelta p) (n : ℕ) :
    (localCyclotomicMaximalIdeal p K ^ n).map
        (localCyclotomicRingEquiv (p := p) K a : localCyclotomicRing p K →+*
          localCyclotomicRing p K) =
      localCyclotomicMaximalIdeal p K ^ n := by
  rw [Ideal.map_pow, localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv]

/-- The cyclotomic action on lambda-local units. -/
noncomputable def localCyclotomicUnitEquiv
    (a : CyclotomicUnitDelta p) :
    localCyclotomicUnitGroup p K ≃* localCyclotomicUnitGroup p K :=
  Units.mapEquiv (localCyclotomicRingEquiv (p := p) K a).toMulEquiv

@[simp]
theorem localCyclotomicUnitEquiv_coe
    (a : CyclotomicUnitDelta p) (u : localCyclotomicUnitGroup p K) :
    (localCyclotomicUnitEquiv (p := p) K a u : localCyclotomicRing p K) =
      localCyclotomicRingEquiv (p := p) K a (u : localCyclotomicRing p K) :=
  rfl

theorem localCyclotomicUnitEquiv_mem_principalUnitSubgroup
    (a : CyclotomicUnitDelta p) {n : ℕ}
    {u : localCyclotomicUnitGroup p K}
    (hu : u ∈ principalUnitSubgroup p K n) :
    localCyclotomicUnitEquiv (p := p) K a u ∈ principalUnitSubgroup p K n := by
  rw [mem_principalUnitSubgroup_iff] at hu ⊢
  have hmem : localCyclotomicRingEquiv (p := p) K a ((u : localCyclotomicRing p K) - 1) ∈
      (localCyclotomicMaximalIdeal p K ^ n).map
        (localCyclotomicRingEquiv (p := p) K a :
          localCyclotomicRing p K →+* localCyclotomicRing p K) :=
    Ideal.mem_map_of_mem _ hu
  rw [localCyclotomicMaximalIdeal_pow_map_localCyclotomicRingEquiv] at hmem
  simpa [map_sub, map_one] using hmem

/-- The cyclotomic automorphism restricted to the local filtration step `U_n`. -/
noncomputable def localPrincipalUnitSubgroupEquiv
    (a : CyclotomicUnitDelta p) (n : ℕ) :
    principalUnitSubgroup p K n ≃* principalUnitSubgroup p K n where
  toFun u :=
    ⟨localCyclotomicUnitEquiv (p := p) K a u,
      localCyclotomicUnitEquiv_mem_principalUnitSubgroup (p := p) (K := K) a u.2⟩
  invFun u :=
    ⟨localCyclotomicUnitEquiv (p := p) K a⁻¹ u,
      localCyclotomicUnitEquiv_mem_principalUnitSubgroup (p := p) (K := K) a⁻¹ u.2⟩
  left_inv u := by
    apply Subtype.ext
    apply Units.ext
    change localCyclotomicRingEquiv (p := p) K a⁻¹
        (localCyclotomicRingEquiv (p := p) K a
          ((u : localCyclotomicUnitGroup p K) : localCyclotomicRing p K)) =
      ((u : localCyclotomicUnitGroup p K) : localCyclotomicRing p K)
    rw [← RingEquiv.trans_apply, ← localCyclotomicRingEquiv_mul]
    simp [localCyclotomicRingEquiv_one]
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    change localCyclotomicRingEquiv (p := p) K a
        (localCyclotomicRingEquiv (p := p) K a⁻¹
          ((u : localCyclotomicUnitGroup p K) : localCyclotomicRing p K)) =
      ((u : localCyclotomicUnitGroup p K) : localCyclotomicRing p K)
    rw [← RingEquiv.trans_apply, ← localCyclotomicRingEquiv_mul]
    simp [localCyclotomicRingEquiv_one]
  map_mul' u v :=
    Subtype.ext <| Units.ext <| map_mul (localCyclotomicRingEquiv (p := p) K a)
        ((u : localCyclotomicUnitGroup p K) : localCyclotomicRing p K)
        ((v : localCyclotomicUnitGroup p K) : localCyclotomicRing p K)

/-- The cyclotomic automorphism lifted to the completed lambda-local ring. -/
noncomputable def completedLocalCyclotomicRingEquiv
    (a : CyclotomicUnitDelta p) :
    completedLocalCyclotomicRing p K ≃+* completedLocalCyclotomicRing p K :=
  adicCompletionRingEquivOfIdealMapEq (I := localCyclotomicMaximalIdeal p K)
    (localCyclotomicRingEquiv (p := p) K a)
    (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv (p := p) (K := K) a)

@[simp]
theorem evalₐ_completedLocalCyclotomicRingEquiv
    (a : CyclotomicUnitDelta p) (n : ℕ)
    (x : completedLocalCyclotomicRing p K) :
    AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n
        (completedLocalCyclotomicRingEquiv (p := p) K a x) =
      Ideal.quotientMap (localCyclotomicMaximalIdeal p K ^ n)
        (localCyclotomicRingEquiv (p := p) K a : localCyclotomicRing p K →+*
          localCyclotomicRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := localCyclotomicMaximalIdeal p K)
          (localCyclotomicRingEquiv (p := p) K a)
          (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv (p := p) (K := K) a)
          n)
        (AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n x) :=
  evalₐ_adicCompletionRingEquivOfIdealMapEq (I := localCyclotomicMaximalIdeal p K)
    (localCyclotomicRingEquiv (p := p) K a)
    (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv (p := p) (K := K) a) n x

theorem completedLocalCyclotomicRingEquiv_one :
    completedLocalCyclotomicRingEquiv (p := p) K 1 =
      RingEquiv.refl (completedLocalCyclotomicRing p K) := by
  let M := localCyclotomicMaximalIdeal p K
  apply RingEquiv.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_completedLocalCyclotomicRingEquiv]
  change Ideal.quotientMap (M ^ n)
      (localCyclotomicRingEquiv (p := p) K 1 : localCyclotomicRing p K →+*
        localCyclotomicRing p K)
      (ideal_pow_le_comap_ringEquiv_of_map_eq (I := M)
        (localCyclotomicRingEquiv (p := p) K 1)
        (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv (p := p) (K := K) 1)
        n)
      (AdicCompletion.evalₐ M n x) =
    AdicCompletion.evalₐ M n x
  induction AdicCompletion.evalₐ M n x using Quotient.inductionOn' with
  | h r =>
    change Ideal.Quotient.mk (M ^ n)
        (localCyclotomicRingEquiv (p := p) K 1 r) =
      Ideal.Quotient.mk (M ^ n) r
    rw [RingEquiv.congr_fun (localCyclotomicRingEquiv_one (p := p) (K := K)) r]
    rfl

theorem completedLocalCyclotomicRingEquiv_mul
    (a b : CyclotomicUnitDelta p) :
    completedLocalCyclotomicRingEquiv (p := p) K (a * b) =
      (completedLocalCyclotomicRingEquiv (p := p) K b).trans
        (completedLocalCyclotomicRingEquiv (p := p) K a) := by
  let M := localCyclotomicMaximalIdeal p K
  let ea := localCyclotomicRingEquiv (p := p) K a
  let eb := localCyclotomicRingEquiv (p := p) K b
  apply RingEquiv.ext
  intro x
  apply AdicCompletion.ext_evalₐ
  intro n
  rw [evalₐ_completedLocalCyclotomicRingEquiv]
  change Ideal.quotientMap (M ^ n)
      (localCyclotomicRingEquiv (p := p) K (a * b) :
        localCyclotomicRing p K →+* localCyclotomicRing p K)
      (ideal_pow_le_comap_ringEquiv_of_map_eq (I := M)
        (localCyclotomicRingEquiv (p := p) K (a * b))
        (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
          (p := p) (K := K) (a * b))
        n)
      (AdicCompletion.evalₐ M n x) =
    AdicCompletion.evalₐ M n
      (completedLocalCyclotomicRingEquiv (p := p) K a
        (completedLocalCyclotomicRingEquiv (p := p) K b x))
  rw [evalₐ_completedLocalCyclotomicRingEquiv,
    evalₐ_completedLocalCyclotomicRingEquiv]
  induction AdicCompletion.evalₐ M n x using Quotient.inductionOn' with
  | h r =>
    change Ideal.Quotient.mk (M ^ n)
        (localCyclotomicRingEquiv (p := p) K (a * b) r) =
      Ideal.Quotient.mk (M ^ n) (ea (eb r))
    rw [RingEquiv.congr_fun (localCyclotomicRingEquiv_mul (p := p) (K := K) a b) r]
    rfl

/-- The actual `Delta` action on the completed lambda-local cyclotomic ring. -/
noncomputable def completedLocalCyclotomicRingDeltaAction :
    CyclotomicUnitDelta p →* RingAut (completedLocalCyclotomicRing p K) where
  toFun a := completedLocalCyclotomicRingEquiv (p := p) K a
  map_one' := completedLocalCyclotomicRingEquiv_one (p := p) (K := K)
  map_mul' a b := completedLocalCyclotomicRingEquiv_mul (p := p) (K := K) a b

/-- The cyclotomic action on completed lambda-local units. -/
noncomputable def completedLocalCyclotomicUnitEquiv
    (a : CyclotomicUnitDelta p) :
    completedLocalCyclotomicUnitGroup p K ≃* completedLocalCyclotomicUnitGroup p K :=
  Units.mapEquiv (completedLocalCyclotomicRingEquiv (p := p) K a).toMulEquiv

@[simp]
theorem completedLocalCyclotomicUnitEquiv_coe
    (a : CyclotomicUnitDelta p) (u : completedLocalCyclotomicUnitGroup p K) :
    (completedLocalCyclotomicUnitEquiv (p := p) K a u :
        completedLocalCyclotomicRing p K) =
      completedLocalCyclotomicRingEquiv (p := p) K a
        (u : completedLocalCyclotomicRing p K) :=
  rfl

theorem completedLocalCyclotomicUnitEquiv_one :
    completedLocalCyclotomicUnitEquiv (p := p) K 1 =
      MulEquiv.refl (completedLocalCyclotomicUnitGroup p K) := by
  apply MulEquiv.ext
  intro u
  apply Units.ext
  change completedLocalCyclotomicRingEquiv (p := p) K 1
      (u : completedLocalCyclotomicRing p K) =
    (u : completedLocalCyclotomicRing p K)
  rw [completedLocalCyclotomicRingEquiv_one]
  rfl

theorem completedLocalCyclotomicUnitEquiv_mul
    (a b : CyclotomicUnitDelta p) :
    completedLocalCyclotomicUnitEquiv (p := p) K (a * b) =
      (completedLocalCyclotomicUnitEquiv (p := p) K b).trans
        (completedLocalCyclotomicUnitEquiv (p := p) K a) := by
  apply MulEquiv.ext
  intro u
  apply Units.ext
  change completedLocalCyclotomicRingEquiv (p := p) K (a * b)
      (u : completedLocalCyclotomicRing p K) =
    completedLocalCyclotomicRingEquiv (p := p) K a
      (completedLocalCyclotomicRingEquiv (p := p) K b
        (u : completedLocalCyclotomicRing p K))
  rw [completedLocalCyclotomicRingEquiv_mul]
  rfl

/-- The actual `Delta` action on completed lambda-local units. -/
noncomputable def completedLocalCyclotomicUnitDeltaAction :
    CyclotomicUnitDelta p →* MulAut (completedLocalCyclotomicUnitGroup p K) where
  toFun a := completedLocalCyclotomicUnitEquiv (p := p) K a
  map_one' := completedLocalCyclotomicUnitEquiv_one (p := p) (K := K)
  map_mul' a b := completedLocalCyclotomicUnitEquiv_mul (p := p) (K := K) a b

theorem completedLocalCyclotomicUnitEquiv_mem_completedPrincipalUnitSubgroup
    (a : CyclotomicUnitDelta p) {n : ℕ}
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K n) :
    completedLocalCyclotomicUnitEquiv (p := p) K a u ∈
      completedPrincipalUnitSubgroup p K n := by
  rw [mem_completedPrincipalUnitSubgroup_iff] at hu ⊢
  rw [completedLocalCyclotomicMaximalIdeal_pow_eq_ker_evalₐ (p := p) (K := K) n] at hu ⊢
  rw [RingHom.mem_ker] at hu ⊢
  change AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n
    ((u : completedLocalCyclotomicUnitGroup p K) - 1) = 0 at hu
  have hsub :
      (completedLocalCyclotomicUnitEquiv (p := p) K a u :
          completedLocalCyclotomicRing p K) - 1 =
        completedLocalCyclotomicRingEquiv (p := p) K a
          ((u : completedLocalCyclotomicRing p K) - 1) := by
    rw [completedLocalCyclotomicUnitEquiv_coe, map_sub, map_one]
  rw [hsub]
  change AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n
      (completedLocalCyclotomicRingEquiv (p := p) K a
        ((u : completedLocalCyclotomicRing p K) - 1)) = 0
  rw [evalₐ_completedLocalCyclotomicRingEquiv, hu, map_zero]

@[simp]
theorem evalₐ_completedLocalCyclotomicRingEquiv_symm
    (a : CyclotomicUnitDelta p) (n : ℕ)
    (x : completedLocalCyclotomicRing p K) :
    AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n
        ((completedLocalCyclotomicRingEquiv (p := p) K a).symm x) =
      Ideal.quotientMap (localCyclotomicMaximalIdeal p K ^ n)
        ((localCyclotomicRingEquiv (p := p) K a).symm :
          localCyclotomicRing p K →+* localCyclotomicRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := localCyclotomicMaximalIdeal p K)
          (localCyclotomicRingEquiv (p := p) K a).symm
          (ideal_map_ringEquiv_symm_eq_of_map_eq (I := localCyclotomicMaximalIdeal p K)
            (localCyclotomicRingEquiv (p := p) K a)
            (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
              (p := p) (K := K) a))
          n)
        (AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n x) := by
  change AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n
      (adicCompletionRingHomOfIdealMapEq (I := localCyclotomicMaximalIdeal p K)
        (localCyclotomicRingEquiv (p := p) K a).symm
        (ideal_map_ringEquiv_symm_eq_of_map_eq (I := localCyclotomicMaximalIdeal p K)
          (localCyclotomicRingEquiv (p := p) K a)
          (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv
            (p := p) (K := K) a)) x) = _
  exact evalₐ_adicCompletionRingHomOfIdealMapEq (I := localCyclotomicMaximalIdeal p K)
    (localCyclotomicRingEquiv (p := p) K a).symm
    (ideal_map_ringEquiv_symm_eq_of_map_eq (I := localCyclotomicMaximalIdeal p K)
      (localCyclotomicRingEquiv (p := p) K a)
      (localCyclotomicMaximalIdeal_map_localCyclotomicRingEquiv (p := p) (K := K) a)) n x

@[simp]
theorem completedLocalCyclotomicUnitEquiv_symm_coe
    (a : CyclotomicUnitDelta p) (u : completedLocalCyclotomicUnitGroup p K) :
    ((completedLocalCyclotomicUnitEquiv (p := p) K a).symm u :
        completedLocalCyclotomicRing p K) =
      (completedLocalCyclotomicRingEquiv (p := p) K a).symm
        (u : completedLocalCyclotomicRing p K) :=
  rfl

theorem completedLocalCyclotomicUnitEquiv_symm_mem_completedPrincipalUnitSubgroup
    (a : CyclotomicUnitDelta p) {n : ℕ}
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitSubgroup p K n) :
    (completedLocalCyclotomicUnitEquiv (p := p) K a).symm u ∈
      completedPrincipalUnitSubgroup p K n := by
  rw [mem_completedPrincipalUnitSubgroup_iff] at hu ⊢
  rw [completedLocalCyclotomicMaximalIdeal_pow_eq_ker_evalₐ (p := p) (K := K) n] at hu ⊢
  rw [RingHom.mem_ker] at hu ⊢
  change AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n
    ((u : completedLocalCyclotomicUnitGroup p K) - 1) = 0 at hu
  have hsub :
      ((completedLocalCyclotomicUnitEquiv (p := p) K a).symm u :
          completedLocalCyclotomicRing p K) - 1 =
        (completedLocalCyclotomicRingEquiv (p := p) K a).symm
          ((u : completedLocalCyclotomicRing p K) - 1) := by
    rw [completedLocalCyclotomicUnitEquiv_symm_coe, map_sub, map_one]
  rw [hsub]
  change AdicCompletion.evalₐ (localCyclotomicMaximalIdeal p K) n
      ((completedLocalCyclotomicRingEquiv (p := p) K a).symm
        ((u : completedLocalCyclotomicRing p K) - 1)) = 0
  rw [evalₐ_completedLocalCyclotomicRingEquiv_symm, hu, map_zero]

/-- The cyclotomic automorphism restricted to the completed local filtration step
`completed U_n`. -/
noncomputable def completedPrincipalUnitSubgroupEquiv
    (a : CyclotomicUnitDelta p) (n : ℕ) :
    completedPrincipalUnitSubgroup p K n ≃* completedPrincipalUnitSubgroup p K n where
  toFun u :=
    ⟨completedLocalCyclotomicUnitEquiv (p := p) K a u,
      completedLocalCyclotomicUnitEquiv_mem_completedPrincipalUnitSubgroup
        (p := p) (K := K) a u.2⟩
  invFun u :=
    ⟨(completedLocalCyclotomicUnitEquiv (p := p) K a).symm u,
      completedLocalCyclotomicUnitEquiv_symm_mem_completedPrincipalUnitSubgroup
        (p := p) (K := K) a u.2⟩
  left_inv u :=
    Subtype.ext <| (completedLocalCyclotomicUnitEquiv (p := p) K a).left_inv u
  right_inv u :=
    Subtype.ext <| (completedLocalCyclotomicUnitEquiv (p := p) K a).right_inv u
  map_mul' u v :=
    Subtype.ext <| Units.ext <| map_mul (completedLocalCyclotomicRingEquiv (p := p) K a)
        ((u : completedLocalCyclotomicUnitGroup p K) : completedLocalCyclotomicRing p K)
        ((v : completedLocalCyclotomicUnitGroup p K) : completedLocalCyclotomicRing p K)

theorem completedPrincipalUnitSubgroupEquiv_one (n : ℕ) :
    completedPrincipalUnitSubgroupEquiv (p := p) K 1 n =
      MulEquiv.refl (completedPrincipalUnitSubgroup p K n) := by
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  change completedLocalCyclotomicUnitEquiv (p := p) K 1
      (u : completedLocalCyclotomicUnitGroup p K) =
    (u : completedLocalCyclotomicUnitGroup p K)
  rw [completedLocalCyclotomicUnitEquiv_one]
  rfl

theorem completedPrincipalUnitSubgroupEquiv_mul
    (a b : CyclotomicUnitDelta p) (n : ℕ) :
    completedPrincipalUnitSubgroupEquiv (p := p) K (a * b) n =
      (completedPrincipalUnitSubgroupEquiv (p := p) K b n).trans
        (completedPrincipalUnitSubgroupEquiv (p := p) K a n) := by
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  change completedLocalCyclotomicUnitEquiv (p := p) K (a * b)
      (u : completedLocalCyclotomicUnitGroup p K) =
    completedLocalCyclotomicUnitEquiv (p := p) K a
      (completedLocalCyclotomicUnitEquiv (p := p) K b
        (u : completedLocalCyclotomicUnitGroup p K))
  rw [completedLocalCyclotomicUnitEquiv_mul]
  rfl

theorem completedLocalCyclotomicUnitEquiv_mem_completedPrincipalUnitPowerSubgroup
    (a : CyclotomicUnitDelta p) {q n : ℕ}
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitPowerSubgroup p K q n) :
    completedLocalCyclotomicUnitEquiv (p := p) K a u ∈
      completedPrincipalUnitPowerSubgroup p K q n := by
  rw [mem_completedPrincipalUnitPowerSubgroup_iff] at hu ⊢
  rcases hu with ⟨v, hv, rfl⟩
  exact ⟨completedLocalCyclotomicUnitEquiv (p := p) K a v,
    completedLocalCyclotomicUnitEquiv_mem_completedPrincipalUnitSubgroup
      (p := p) (K := K) a hv,
    by rw [map_pow]⟩

theorem completedLocalCyclotomicUnitEquiv_symm_mem_completedPrincipalUnitPowerSubgroup
    (a : CyclotomicUnitDelta p) {q n : ℕ}
    {u : completedLocalCyclotomicUnitGroup p K}
    (hu : u ∈ completedPrincipalUnitPowerSubgroup p K q n) :
    (completedLocalCyclotomicUnitEquiv (p := p) K a).symm u ∈
      completedPrincipalUnitPowerSubgroup p K q n := by
  rw [mem_completedPrincipalUnitPowerSubgroup_iff] at hu ⊢
  rcases hu with ⟨v, hv, rfl⟩
  exact ⟨(completedLocalCyclotomicUnitEquiv (p := p) K a).symm v,
    completedLocalCyclotomicUnitEquiv_symm_mem_completedPrincipalUnitSubgroup
      (p := p) (K := K) a hv,
    by rw [map_pow]⟩

theorem completedPrincipalUnitModPSubgroup_map
    (a : CyclotomicUnitDelta p) :
    (completedPrincipalUnitModPSubgroup p K).map
        (completedPrincipalUnitSubgroupEquiv (p := p) K a 1).toMonoidHom =
      completedPrincipalUnitModPSubgroup p K := by
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    change v ∈ completedPrincipalUnitModPSubgroup p K at hv
    change completedPrincipalUnitSubgroupEquiv (p := p) K a 1 v ∈
      completedPrincipalUnitModPSubgroup p K
    rw [mem_completedPrincipalUnitModPSubgroup_iff] at hv ⊢
    exact completedLocalCyclotomicUnitEquiv_mem_completedPrincipalUnitPowerSubgroup
      (p := p) (K := K) a hv
  · intro hu
    refine ⟨(completedPrincipalUnitSubgroupEquiv (p := p) K a 1).symm u, ?_, ?_⟩
    · change u ∈ completedPrincipalUnitModPSubgroup p K at hu
      rw [mem_completedPrincipalUnitModPSubgroup_iff] at hu
      change ((completedPrincipalUnitSubgroupEquiv (p := p) K a 1).symm u :
          completedPrincipalUnitSubgroup p K 1) ∈
        completedPrincipalUnitModPSubgroup p K
      rw [mem_completedPrincipalUnitModPSubgroup_iff]
      exact completedLocalCyclotomicUnitEquiv_symm_mem_completedPrincipalUnitPowerSubgroup
        (p := p) (K := K) a hu
    · exact (completedPrincipalUnitSubgroupEquiv (p := p) K a 1).right_inv u

/-- The induced cyclotomic action on
`completed U_1 / completed U_1^p`. -/
noncomputable def completedPrincipalUnitModPQuotientEquiv
    (a : CyclotomicUnitDelta p) :
    completedPrincipalUnitModPQuotient p K ≃*
      completedPrincipalUnitModPQuotient p K :=
  QuotientGroup.congr
    (completedPrincipalUnitModPSubgroup p K)
    (completedPrincipalUnitModPSubgroup p K)
    (completedPrincipalUnitSubgroupEquiv (p := p) K a 1)
    (completedPrincipalUnitModPSubgroup_map (p := p) (K := K) a)

@[simp]
theorem completedPrincipalUnitModPQuotientEquiv_mk
    (a : CyclotomicUnitDelta p) (u : completedPrincipalUnitSubgroup p K 1) :
    completedPrincipalUnitModPQuotientEquiv (p := p) K a
        (completedPrincipalUnitModPClass p K u) =
      completedPrincipalUnitModPClass p K
        (completedPrincipalUnitSubgroupEquiv (p := p) K a 1 u) :=
  rfl

/-- The actual `Delta` action on `completed U_1 / completed U_1^p`. -/
noncomputable def completedPrincipalUnitModPDeltaAction :
    CyclotomicUnitDelta p →* MulAut (completedPrincipalUnitModPQuotient p K) where
  toFun a := completedPrincipalUnitModPQuotientEquiv (p := p) K a
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro u
    change completedPrincipalUnitModPQuotientEquiv (p := p) K 1
        (completedPrincipalUnitModPClass p K u) =
      completedPrincipalUnitModPClass p K u
    rw [completedPrincipalUnitModPQuotientEquiv_mk,
      completedPrincipalUnitSubgroupEquiv_one]
    rfl
  map_mul' a b := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro u
    change completedPrincipalUnitModPQuotientEquiv (p := p) K (a * b)
        (completedPrincipalUnitModPClass p K u) =
      completedPrincipalUnitModPQuotientEquiv (p := p) K a
        (completedPrincipalUnitModPQuotientEquiv (p := p) K b
          (completedPrincipalUnitModPClass p K u))
    rw [completedPrincipalUnitModPQuotientEquiv_mk,
      completedPrincipalUnitModPQuotientEquiv_mk,
      completedPrincipalUnitModPQuotientEquiv_mk,
      completedPrincipalUnitSubgroupEquiv_mul]
    rfl

@[simp]
theorem completedPrincipalUnitModPDeltaAction_apply_class
    (a : CyclotomicUnitDelta p) (u : completedPrincipalUnitSubgroup p K 1) :
    completedPrincipalUnitModPDeltaAction (p := p) K a
        (completedPrincipalUnitModPClass p K u) =
      completedPrincipalUnitModPClass p K
        (completedPrincipalUnitSubgroupEquiv (p := p) K a 1 u) :=
  completedPrincipalUnitModPQuotientEquiv_mk (p := p) (K := K) a u

end CyclotomicSetup

end Local
end Reflection
end BernoulliRegular

end

