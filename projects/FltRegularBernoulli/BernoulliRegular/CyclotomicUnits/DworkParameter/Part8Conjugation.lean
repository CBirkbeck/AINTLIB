module

public import BernoulliRegular.CyclotomicUnits.DworkParameter.Part8
public import BernoulliRegular.Reflection.Local.DeltaAction
public import Mathlib.Topology.Algebra.UniformRing

@[expose] public section

noncomputable section

open scoped NumberField WithZero
open PowerSeries

namespace BernoulliRegular
namespace CyclotomicUnits
namespace PadicLogSetup
namespace DworkParameter

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

local instance : CharZero (ValuedCompletion p K) :=
  algebraRat.charZero (ValuedCompletion p K)

namespace Conjugation

open Furtwaengler.KummerArtinHasse
open MonoidWithZeroHom.ValueGroup₀
open BernoulliRegular.Reflection.Local

set_option maxHeartbeats 800000 in
-- The proof compares value-group basic neighborhoods for two valuation type synonyms.
omit [NumberField K] in
theorem uniformContinuous_withValCongr_comap
    (v : Valuation K ℤᵐ⁰) (σ : K ≃+* K) :
    UniformContinuous
      (WithVal.congr (v.comap σ.toRingHom) v σ) := by
  refine uniformContinuous_of_continuousAt_zero
    (WithVal.congr (v.comap σ.toRingHom) v σ).toAddMonoidHom ?_
  simp_rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero _ _).tendsto_iff
      (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  let w : Valuation K ℤᵐ⁰ := v.comap σ.toRingHom
  obtain ⟨k, hk⟩ :=
    restrict₀_surjective
      (MonoidWithZeroHom.ofClass (Valued.v : Valuation (WithVal v) ℤᵐ⁰)) γ.1
  let δx : WithVal w := WithVal.toVal w (σ.symm k.ofVal)
  let δ₀ : MonoidWithZeroHom.ValueGroup₀
      (MonoidWithZeroHom.ofClass (Valued.v : Valuation (WithVal w) ℤᵐ⁰)) :=
    Valued.v.restrict δx
  have hδ₀_emb :
      MonoidWithZeroHom.ValueGroup₀.embedding δ₀ =
        MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    calc
      MonoidWithZeroHom.ValueGroup₀.embedding δ₀ =
          (v.comap σ.toRingHom) (σ.symm k.ofVal) := by
        change MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict δx) =
          (v.comap σ.toRingHom) (σ.symm k.ofVal)
        change MonoidWithZeroHom.ValueGroup₀.embedding
            (Valued.v.restrict (WithVal.toVal w (σ.symm k.ofVal))) =
          (v.comap σ.toRingHom) (σ.symm k.ofVal)
        rw [Valuation.embedding_restrict]
        exact WithVal.valued_toVal (v := w) (σ.symm k.ofVal)
      _ = v k.ofVal := by
        simp [Valuation.comap_apply]
      _ = MonoidWithZeroHom.ValueGroup₀.embedding
            ((MonoidWithZeroHom.ValueGroup₀.restrict₀
              (MonoidWithZeroHom.ofClass (Valued.v : Valuation (WithVal v) ℤᵐ⁰))) k) := by
        rw [MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
        exact WithVal.apply_ofVal (v := v) k
      _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by rw [hk]
  have hδ₀_ne : δ₀ ≠ 0 := by
    rw [← map_ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := MonoidWithZeroHom.ofClass (Valued.v : Valuation (WithVal w) ℤᵐ⁰))), hδ₀_emb]
    exact MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  refine ⟨Units.mk0 δ₀ hδ₀_ne, ?_⟩
  intro x hx
  change Valued.v.restrict x < δ₀ at hx
  change Valued.v.restrict
      ((WithVal.congr (v.comap σ.toRingHom) v σ).toAddMonoidHom x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  have hval :
      Valued.v ((WithVal.congr (v.comap σ.toRingHom) v σ).toAddMonoidHom x) =
        Valued.v x := by
    change v (σ x.ofVal) = (v.comap σ.toRingHom) x.ofVal
    rfl
  rw [hval, ← hδ₀_emb]
  exact hx

set_option maxHeartbeats 800000 in
-- The proof is the inverse-neighborhood version of `uniformContinuous_withValCongr_comap`.
omit [NumberField K] in
theorem uniformContinuous_withValCongr_comap_symm
    (v : Valuation K ℤᵐ⁰) (σ : K ≃+* K) :
    UniformContinuous
      (WithVal.congr (v.comap σ.toRingHom) v σ).symm := by
  refine uniformContinuous_of_continuousAt_zero
    (WithVal.congr (v.comap σ.toRingHom) v σ).symm.toAddMonoidHom ?_
  simp_rw [ContinuousAt, map_zero,
    (Valued.hasBasis_nhds_zero _ _).tendsto_iff
      (Valued.hasBasis_nhds_zero _ _), true_and, forall_const]
  intro γ
  let w : Valuation K ℤᵐ⁰ := v.comap σ.toRingHom
  obtain ⟨k, hk⟩ :=
    restrict₀_surjective
      (MonoidWithZeroHom.ofClass (Valued.v : Valuation (WithVal w) ℤᵐ⁰)) γ.1
  let δx : WithVal v := WithVal.toVal v (σ k.ofVal)
  let δ₀ : MonoidWithZeroHom.ValueGroup₀
      (MonoidWithZeroHom.ofClass (Valued.v : Valuation (WithVal v) ℤᵐ⁰)) :=
    Valued.v.restrict δx
  have hδ₀_emb :
      MonoidWithZeroHom.ValueGroup₀.embedding δ₀ =
        MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
    calc
      MonoidWithZeroHom.ValueGroup₀.embedding δ₀ = v (σ k.ofVal) := by
        change MonoidWithZeroHom.ValueGroup₀.embedding (Valued.v.restrict δx) = v (σ k.ofVal)
        change MonoidWithZeroHom.ValueGroup₀.embedding
            (Valued.v.restrict (WithVal.toVal v (σ k.ofVal))) = v (σ k.ofVal)
        rw [Valuation.embedding_restrict]
        exact WithVal.valued_toVal (v := v) (σ k.ofVal)
      _ = (v.comap σ.toRingHom) k.ofVal := rfl
      _ = MonoidWithZeroHom.ValueGroup₀.embedding
            ((MonoidWithZeroHom.ValueGroup₀.restrict₀
              (MonoidWithZeroHom.ofClass (Valued.v : Valuation (WithVal w) ℤᵐ⁰))) k) := by
        rw [MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀]
        exact WithVal.apply_ofVal (v := w) k
      _ = MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by rw [hk]
  have hδ₀_ne : δ₀ ≠ 0 := by
    rw [← map_ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding
      (f := MonoidWithZeroHom.ofClass (Valued.v : Valuation (WithVal v) ℤᵐ⁰))), hδ₀_emb]
    exact MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ
  refine ⟨Units.mk0 δ₀ hδ₀_ne, ?_⟩
  intro x hx
  change Valued.v.restrict x < δ₀ at hx
  change Valued.v.restrict
      ((WithVal.congr (v.comap σ.toRingHom) v σ).symm.toAddMonoidHom x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  have hval :
      Valued.v ((WithVal.congr (v.comap σ.toRingHom) v σ).symm.toAddMonoidHom x) =
        Valued.v x := by
    change (v.comap σ.toRingHom) (σ.symm x.ofVal) = v x.ofVal
    simp [Valuation.comap_apply]
  rw [hval, ← hδ₀_emb]
  exact hx

/-- The exact valued-field uniform equivalence induced by a field automorphism and
the pulled-back valuation. -/
def withValCongrComapUniformEquiv
    (v : Valuation K ℤᵐ⁰) (σ : K ≃+* K) :
    WithVal (v.comap σ.toRingHom) ≃ᵤ WithVal v where
  __ := (WithVal.congr (v.comap σ.toRingHom) v σ).toEquiv
  uniformContinuous_toFun := uniformContinuous_withValCongr_comap (K := K) v σ
  uniformContinuous_invFun := uniformContinuous_withValCongr_comap_symm (K := K) v σ

theorem map_cyclotomicRingOfIntegersEquiv_coe
    (a : CyclotomicUnitDelta p) (x : 𝓞 K) :
    ((cyclotomicRingOfIntegersEquiv (p := p) K a x : 𝓞 K) : K) =
      cyclotomicSigmaOfUnit (p := p) K a (x : K) := by
  unfold cyclotomicRingOfIntegersEquiv
  change (cyclotomicSigmaOfUnit (p := p) K a • x : K) =
    cyclotomicSigmaOfUnit (p := p) K a (x : K)
  exact algebraMap.coe_smul' (cyclotomicSigmaOfUnit (p := p) K a) x K

theorem cyclotomicRingOfIntegersEquiv_notMem_lambda
    (a : CyclotomicUnitDelta p) {x : 𝓞 K}
    (hx : x ∉ (lambdaHeightOneSpectrum p K).asIdeal) :
    cyclotomicRingOfIntegersEquiv (p := p) K a x ∉
      (lambdaHeightOneSpectrum p K).asIdeal := by
  intro hmem
  apply hx
  have hmem' :
      cyclotomicRingOfIntegersEquiv (p := p) K a x ∈
        Reflection.Local.cyclotomicLambda p K := by
    simpa [Reflection.Local.cyclotomicLambda, lambdaHeightOneSpectrum_asIdeal] using hmem
  have hx' : x ∈ Reflection.Local.cyclotomicLambda p K := by
    rw [cyclotomicRingOfIntegersEquiv_comap_lambda (p := p) (K := K) a]
    exact hmem'
  simpa [Reflection.Local.cyclotomicLambda, lambdaHeightOneSpectrum_asIdeal] using hx'

theorem lambdaValuation_cyclotomicSigma_le_one_of_le_one
    (a : CyclotomicUnitDelta p) {x : K}
    (hx : (lambdaHeightOneSpectrum p K).valuation K x ≤ 1) :
    (lambdaHeightOneSpectrum p K).valuation K
        (cyclotomicSigmaOfUnit (p := p) K a x) ≤ 1 := by
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 K) := lambdaHeightOneSpectrum p K
  let σ : Gal(K / ℚ) := cyclotomicSigmaOfUnit (p := p) K a
  let e : 𝓞 K ≃+* 𝓞 K := cyclotomicRingOfIntegersEquiv (p := p) K a
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (K := K) x hx
  have hd_not : (d : 𝓞 K) ∉ (lambdaHeightOneSpectrum p K).asIdeal := by
    simpa [v] using (Ideal.mem_primeCompl_iff.mp d.2)
  let d' : v.asIdeal.primeCompl :=
    ⟨e d.1, cyclotomicRingOfIntegersEquiv_notMem_lambda
      (p := p) (K := K) a hd_not⟩
  let n' : 𝓞 K := e n
  have hd'_ne : (d' : 𝓞 K) ≠ 0 := fun hd =>
    d'.2 (by simp [hd])
  have hmul :
      σ x * algebraMap (𝓞 K) K (d' : 𝓞 K) =
        algebraMap (𝓞 K) K n' := by
    have h := congrArg σ hnd
    change σ (x * algebraMap (𝓞 K) K (d : 𝓞 K)) =
      σ (algebraMap (𝓞 K) K n) at h
    change σ x * (e d.1 : K) = (e n : K)
    rw [map_cyclotomicRingOfIntegersEquiv_coe (p := p) (K := K) a d.1,
      map_cyclotomicRingOfIntegersEquiv_coe (p := p) (K := K) a n]
    simpa [map_mul] using h
  have hquot :
      σ x = algebraMap (𝓞 K) K n' / algebraMap (𝓞 K) K (d' : 𝓞 K) := by
    rw [eq_div_iff]
    · exact hmul
    · exact NumberField.RingOfIntegers.coe_ne_zero_iff.mpr hd'_ne
  rw [hquot]
  exact (v.valuation_div_le_one_iff K n' hd'_ne (fun hd => False.elim (d'.2 hd))).2 d'.2

theorem cyclotomicSigmaOfUnit_inv_apply_apply
    (a : CyclotomicUnitDelta p) (x : K) :
    cyclotomicSigmaOfUnit (p := p) K a⁻¹
        (cyclotomicSigmaOfUnit (p := p) K a x) = x := by
  have hmul :
      cyclotomicSigmaOfUnit (p := p) K a⁻¹ *
          cyclotomicSigmaOfUnit (p := p) K a = 1 := by
    rw [← cyclotomicSigmaOfUnit_mul, inv_mul_cancel, cyclotomicSigmaOfUnit_one]
  have h := congrArg (fun σ : Gal(K / ℚ) => σ x) hmul
  simpa using h

theorem lambdaValuation_cyclotomicSigma_le_one_iff
    (a : CyclotomicUnitDelta p) (x : K) :
    (lambdaHeightOneSpectrum p K).valuation K
        (cyclotomicSigmaOfUnit (p := p) K a x) ≤ 1 ↔
      (lambdaHeightOneSpectrum p K).valuation K x ≤ 1 := by
  constructor
  · intro hx
    have h :=
      lambdaValuation_cyclotomicSigma_le_one_of_le_one
        (p := p) (K := K) a⁻¹ (x := cyclotomicSigmaOfUnit (p := p) K a x) hx
    simpa [cyclotomicSigmaOfUnit_inv_apply_apply (p := p) (K := K) a x] using h
  · intro hx
    exact lambdaValuation_cyclotomicSigma_le_one_of_le_one
      (p := p) (K := K) a (x := x) hx

theorem lambdaValuation_isEquiv_comap_cyclotomicSigma
    (a : CyclotomicUnitDelta p) :
    ((lambdaHeightOneSpectrum p K).valuation K).IsEquiv
      (((lambdaHeightOneSpectrum p K).valuation K).comap
        (cyclotomicSigmaOfUnit (p := p) K a).toRingHom) := by
  apply Valuation.isEquiv_of_val_le_one
  intro x
  exact (lambdaValuation_cyclotomicSigma_le_one_iff (p := p) (K := K) a x).symm

omit [NumberField K] in
theorem valuedCompletion_withValCongrComap_le_one_iff
    (v : Valuation K ℤᵐ⁰) (σ : K ≃+* K)
    {x : (v.comap σ.toRingHom).Completion} :
    Valued.v
        (UniformSpace.Completion.mapRingEquiv
          (WithVal.congr (v.comap σ.toRingHom) v σ)
          (uniformContinuous_withValCongr_comap (K := K) v σ).continuous
          (uniformContinuous_withValCongr_comap_symm (K := K) v σ).continuous x) ≤ 1 ↔
      Valued.v x ≤ 1 := by
  let w : Valuation K ℤᵐ⁰ := v.comap σ.toRingHom
  let E : WithVal w ≃ᵤ WithVal v := withValCongrComapUniformEquiv (K := K) v σ
  change Valued.v ((UniformSpace.Completion.mapEquiv E) x) ≤ 1 ↔
      Valued.v x ≤ 1
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
      have h1 (y : (v.comap σ.toRingHom).Completion) :
          Valued.v y ≤ 1 ↔ Valued.v.restrict y ≤ 1 := by
        rw [Valuation.restrict_le_one_iff]
      have h2 (y : v.Completion) :
          Valued.v y ≤ 1 ↔ Valued.v.restrict y ≤ 1 := by
        rw [Valuation.restrict_le_one_iff]
      simp_rw [h1, h2]
      convert (UniformSpace.Completion.mapEquiv E).toHomeomorph.isClosed_setOf_iff
        (Valued.isClopen_closedBall _ one_ne_zero)
        (Valued.isClopen_closedBall _ one_ne_zero) using 1
      ext y
      constructor <;> intro h <;> exact h.symm
  | ih y =>
      rw [UniformSpace.Completion.mapEquiv_coe]
      rw [Valued.valuedCompletion_apply, Valued.valuedCompletion_apply]
      change v (σ y.ofVal) ≤ 1 ↔ (v.comap σ.toRingHom) y.ofVal ≤ 1
      rfl

/-- The cyclotomic automorphism of the valued lambda-completion. -/
noncomputable def valuedCompletionCyclotomicEquiv
    (a : CyclotomicUnitDelta p) :
    ValuedCompletion p K ≃+* ValuedCompletion p K := by
  let v : Valuation K ℤᵐ⁰ := (lambdaHeightOneSpectrum p K).valuation K
  let σ : K ≃+* K := (cyclotomicSigmaOfUnit (p := p) K a).toRingEquiv
  let w : Valuation K ℤᵐ⁰ := v.comap σ.toRingHom
  let h : v.IsEquiv w :=
    lambdaValuation_isEquiv_comap_cyclotomicSigma (p := p) (K := K) a
  exact
    (UniformSpace.Completion.mapRingEquiv
      (WithVal.congr v w (RingEquiv.refl K))
      h.uniformContinuous_congr.continuous
      h.symm.uniformContinuous_congr.continuous).trans
    (UniformSpace.Completion.mapRingEquiv
      (WithVal.congr w v σ)
      (uniformContinuous_withValCongr_comap (K := K) v σ).continuous
      (uniformContinuous_withValCongr_comap_symm (K := K) v σ).continuous)

theorem valuedCompletionCyclotomicEquiv_le_one_iff
    (a : CyclotomicUnitDelta p) {x : ValuedCompletion p K} :
    Valued.v (valuedCompletionCyclotomicEquiv (p := p) K a x) ≤ 1 ↔
      Valued.v x ≤ 1 := by
  let v : Valuation K ℤᵐ⁰ := (lambdaHeightOneSpectrum p K).valuation K
  let σ : K ≃+* K := (cyclotomicSigmaOfUnit (p := p) K a).toRingEquiv
  let w : Valuation K ℤᵐ⁰ := v.comap σ.toRingHom
  let h : v.IsEquiv w :=
    lambdaValuation_isEquiv_comap_cyclotomicSigma (p := p) (K := K) a
  change Valued.v
      (((UniformSpace.Completion.mapRingEquiv
        (WithVal.congr v w (RingEquiv.refl K))
        h.uniformContinuous_congr.continuous
        h.symm.uniformContinuous_congr.continuous).trans
      (UniformSpace.Completion.mapRingEquiv
        (WithVal.congr w v σ)
        (uniformContinuous_withValCongr_comap (K := K) v σ).continuous
        (uniformContinuous_withValCongr_comap_symm (K := K) v σ).continuous)) x) ≤ 1 ↔
    Valued.v x ≤ 1
  rw [RingEquiv.trans_apply]
  rw [valuedCompletion_withValCongrComap_le_one_iff (K := K) v σ]
  exact (h.valuedCompletion_le_one_iff (x := x)).symm

/-- The cyclotomic automorphism restricted to the valued integer ring. -/
noncomputable def valuedIntegerCyclotomicEquiv
    (a : CyclotomicUnitDelta p) :
    ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
  (valuedCompletionCyclotomicEquiv (p := p) K a).restrict
    ((lambdaHeightOneSpectrum p K).adicCompletionIntegers K)
    ((lambdaHeightOneSpectrum p K).adicCompletionIntegers K)
    (fun x => by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
        IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      exact (valuedCompletionCyclotomicEquiv_le_one_iff
        (p := p) (K := K) a (x := x)).symm)

/-- Complex conjugation on the valued integer ring, represented by
the cyclotomic automorphism indexed by `-1 ∈ (ZMod p)ˣ`. -/
noncomputable def valuedIntegerComplexConj :
    ValuedIntegerRing p K ≃+* ValuedIntegerRing p K :=
  valuedIntegerCyclotomicEquiv (p := p) K (-1)

@[simp]
theorem valuedCompletionCyclotomicEquiv_algebraMap
    (a : CyclotomicUnitDelta p) (x : K) :
    valuedCompletionCyclotomicEquiv (p := p) K a
        (algebraMap K (ValuedCompletion p K) x) =
      algebraMap K (ValuedCompletion p K)
        (cyclotomicSigmaOfUnit (p := p) K a x) := by
  let v : Valuation K ℤᵐ⁰ := (lambdaHeightOneSpectrum p K).valuation K
  let σ : K ≃+* K := (cyclotomicSigmaOfUnit (p := p) K a).toRingEquiv
  let w : Valuation K ℤᵐ⁰ := v.comap σ.toRingHom
  let h : v.IsEquiv w :=
    lambdaValuation_isEquiv_comap_cyclotomicSigma (p := p) (K := K) a
  change
    (((UniformSpace.Completion.mapRingEquiv
      (WithVal.congr v w (RingEquiv.refl K))
      h.uniformContinuous_congr.continuous
      h.symm.uniformContinuous_congr.continuous).trans
    (UniformSpace.Completion.mapRingEquiv
      (WithVal.congr w v σ)
      (uniformContinuous_withValCongr_comap (K := K) v σ).continuous
      (uniformContinuous_withValCongr_comap_symm (K := K) v σ).continuous))
        (WithVal.toVal v x : v.Completion)) =
      (WithVal.toVal v (σ x) : v.Completion)
  rw [RingEquiv.trans_apply]
  change UniformSpace.Completion.map (WithVal.congr w v σ)
      (UniformSpace.Completion.map (WithVal.congr v w (RingEquiv.refl K))
        (WithVal.toVal v x : v.Completion)) =
    (WithVal.toVal v (σ x) : v.Completion)
  rw [UniformSpace.Completion.map_coe h.uniformContinuous_congr,
    UniformSpace.Completion.map_coe (uniformContinuous_withValCongr_comap (K := K) v σ)]
  rfl

theorem zmodUnit_neg_one_val_eq_pred :
    ((-1 : CyclotomicUnitDelta p) : ZMod p).val = p - 1 := by
  change (-1 : ZMod p).val = p - 1
  have hp0 : p ≠ 0 := (Fact.out : Nat.Prime p).ne_zero
  cases p with
  | zero => exact (hp0 rfl).elim
  | succ n =>
      rw [ZMod.val_neg_one]
      rfl

@[simp]
theorem valuedIntegerComplexConj_valuedCyclotomicZetaInteger :
    valuedIntegerComplexConj (p := p) K (valuedCyclotomicZetaInteger p K) =
      valuedCyclotomicZetaInteger p K ^ (p - 1) := by
  ext
  change valuedCompletionCyclotomicEquiv (p := p) K (-1)
      (algebraMap (𝓞 K) (ValuedCompletion p K)
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger) =
    ((valuedCyclotomicZetaInteger p K ^ (p - 1) : ValuedIntegerRing p K) :
      ValuedCompletion p K)
  rw [show algebraMap (𝓞 K) (ValuedCompletion p K)
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger =
      algebraMap K (ValuedCompletion p K) (IsCyclotomicExtension.zeta p ℚ K) from rfl]
  rw [valuedCompletionCyclotomicEquiv_algebraMap]
  rw [cyclotomicSigmaOfUnit_apply_zeta]
  rw [zmodUnit_neg_one_val_eq_pred (p := p)]
  change algebraMap K (ValuedCompletion p K)
      (IsCyclotomicExtension.zeta p ℚ K ^ (p - 1)) =
    (algebraMap K (ValuedCompletion p K)
      (IsCyclotomicExtension.zeta p ℚ K)) ^ (p - 1)
  rw [map_pow]

@[simp]
theorem valuedIntegerComplexConj_valuedCyclotomicLambdaInteger :
    valuedIntegerComplexConj (p := p) K (valuedCyclotomicLambdaInteger p K) =
      valuedCyclotomicConjugateLambdaInteger p K := by
  have hlambda :
      valuedCyclotomicLambdaInteger p K =
        valuedCyclotomicZetaInteger p K - 1 := by
    rw [valuedCyclotomicZetaInteger_eq_one_add_lambda (p := p) (K := K)]
    ring_nf
  calc
    valuedIntegerComplexConj (p := p) K (valuedCyclotomicLambdaInteger p K) =
        valuedIntegerComplexConj (p := p) K (valuedCyclotomicZetaInteger p K - 1) := by
          rw [hlambda]
    _ = valuedCyclotomicZetaInteger p K ^ (p - 1) - 1 := by
          rw [map_sub, valuedIntegerComplexConj_valuedCyclotomicZetaInteger, map_one]
    _ = valuedCyclotomicConjugateLambdaInteger p K := rfl

theorem lambdaIdeal_eq_span_conjugateLambda :
    lambdaIdeal p K =
      Ideal.span ({valuedCyclotomicConjugateLambdaInteger p K} :
        Set (ValuedIntegerRing p K)) := by
  apply le_antisymm
  · rw [lambdaIdeal, Ideal.span_le]
    rintro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    let J : Ideal (ValuedIntegerRing p K) :=
      Ideal.span ({valuedCyclotomicConjugateLambdaInteger p K} :
        Set (ValuedIntegerRing p K))
    have hneg : -valuedCyclotomicLambdaInteger p K ∈ J := by
      rw [← valuedCyclotomicConjugateLambdaInteger_mul_one_add_lambda (p := p) (K := K)]
      exact J.mul_mem_right (1 + valuedCyclotomicLambdaInteger p K)
        (Ideal.mem_span_singleton_self (valuedCyclotomicConjugateLambdaInteger p K))
    simpa [J] using J.neg_mem hneg
  · rw [Ideal.span_le]
    rintro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    exact valuedCyclotomicConjugateLambdaInteger_mem_lambdaIdeal (p := p) (K := K)

theorem lambdaIdeal_map_valuedIntegerComplexConj :
    (lambdaIdeal p K).map (valuedIntegerComplexConj (p := p) K : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K) =
      lambdaIdeal p K := by
  rw [lambdaIdeal, Ideal.map_span]
  rw [Set.image_singleton]
  change Ideal.span ({valuedIntegerComplexConj (p := p) K
      (valuedCyclotomicLambdaInteger p K)} : Set (ValuedIntegerRing p K)) =
    lambdaIdeal p K
  rw [valuedIntegerComplexConj_valuedCyclotomicLambdaInteger]
  exact (lambdaIdeal_eq_span_conjugateLambda (p := p) (K := K)).symm

/-- Complex conjugation lifted to the `lambda`-adic Dwork completion. -/
noncomputable def dworkCompleteComplexConj :
    DworkCompleteIntegerRing p K ≃+* DworkCompleteIntegerRing p K :=
  adicCompletionRingEquivOfIdealMapEq (I := lambdaIdeal p K)
    (valuedIntegerComplexConj (p := p) K)
    (lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K))

@[simp]
theorem evalₐ_dworkCompleteComplexConj (N : ℕ) (x : DworkCompleteIntegerRing p K) :
    AdicCompletion.evalₐ (lambdaIdeal p K) N
        (dworkCompleteComplexConj (p := p) K x) =
      Ideal.quotientMap ((lambdaIdeal p K) ^ N)
        (valuedIntegerComplexConj (p := p) K : ValuedIntegerRing p K →+*
          ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerComplexConj (p := p) K)
          (lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K)) N)
        (AdicCompletion.evalₐ (lambdaIdeal p K) N x) :=
  evalₐ_adicCompletionRingEquivOfIdealMapEq (I := lambdaIdeal p K)
    (valuedIntegerComplexConj (p := p) K)
    (lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K)) N x

@[simp]
theorem dworkCompleteComplexConj_dworkCompleteLambda :
    dworkCompleteComplexConj (p := p) K (dworkCompleteLambda p K) =
      dworkCompleteConjugateLambda p K := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalₐ_dworkCompleteComplexConj]
  simp [dworkCompleteLambda, dworkCompleteConjugateLambda,
    valuedIntegerComplexConj_valuedCyclotomicLambdaInteger]

@[simp]
theorem valuedIntegerComplexConj_rIntegralRatToValuedInteger
    (q : Furtwaengler.DieudonneDwork.rIntegralRatSubring p) :
    valuedIntegerComplexConj (p := p) K (rIntegralRatToValuedInteger p K q) =
      rIntegralRatToValuedInteger p K q := by
  ext
  change valuedCompletionCyclotomicEquiv (p := p) K (-1)
      (algebraMap K (ValuedCompletion p K) (algebraMap ℚ K (q : ℚ))) =
    algebraMap K (ValuedCompletion p K) (algebraMap ℚ K (q : ℚ))
  rw [valuedCompletionCyclotomicEquiv_algebraMap]
  simp

@[simp]
theorem integralInverseSeries_map_valuedIntegerComplexConj :
    PowerSeries.map (valuedIntegerComplexConj (p := p) K : ValuedIntegerRing p K →+*
      ValuedIntegerRing p K) (integralInverseSeries p K) =
      integralInverseSeries p K := by
  ext n
  simp [integralInverseSeries, Furtwaengler.DieudonneDwork.IsRIntegralPS.coeff_mapTo]

theorem quotientMap_evalIntegralPowerSeriesMod_complexConj
    (F : PowerSeries (ValuedIntegerRing p K))
    (hF : PowerSeries.map
      (valuedIntegerComplexConj (p := p) K : ValuedIntegerRing p K →+*
        ValuedIntegerRing p K) F = F)
    (x : DworkCompleteIntegerRing p K) (N : ℕ) :
    Ideal.quotientMap ((lambdaIdeal p K) ^ N)
        (valuedIntegerComplexConj (p := p) K : ValuedIntegerRing p K →+*
          ValuedIntegerRing p K)
        (ideal_pow_le_comap_ringEquiv_of_map_eq (I := lambdaIdeal p K)
          (valuedIntegerComplexConj (p := p) K)
          (lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K)) N)
        (evalIntegralPowerSeriesMod p K F x N) =
      evalIntegralPowerSeriesMod p K F
        (dworkCompleteComplexConj (p := p) K x) N := by
  classical
  let R : Type _ := ValuedIntegerRing p K
  let I : Ideal R := lambdaIdeal p K
  let A : Type _ := R ⧸ I ^ N
  let q : R →+* A := Ideal.Quotient.mk (I ^ N)
  let e : R ≃+* R := valuedIntegerComplexConj (p := p) K
  let he : I.map (e : R →+* R) = I :=
    lambdaIdeal_map_valuedIntegerComplexConj (p := p) (K := K)
  let φ : A →+* A :=
    Ideal.quotientMap (I ^ N) (e : R →+* R)
      (ideal_pow_le_comap_ringEquiv_of_map_eq (I := I) e he N)
  let P : Polynomial A := PowerSeries.trunc N (PowerSeries.map q F)
  have hφq : φ.comp q = q.comp (e : R →+* R) := by
    ext r
    rfl
  have hPSmap :
      PowerSeries.map φ (PowerSeries.map q F) = PowerSeries.map q F := by
    ext n
    have hn : e (PowerSeries.coeff n F) = PowerSeries.coeff n F := by
      have h := congrArg (fun G : R⟦X⟧ => PowerSeries.coeff n G) hF
      simpa [PowerSeries.coeff_map] using h
    change φ (q (PowerSeries.coeff n F)) = q (PowerSeries.coeff n F)
    change (φ.comp q) (PowerSeries.coeff n F) = q (PowerSeries.coeff n F)
    rw [hφq]
    simp [hn]
  have hPmap : P.map φ = P := by
    change (PowerSeries.trunc N (PowerSeries.map q F)).map φ =
      PowerSeries.trunc N (PowerSeries.map q F)
    rw [← PowerSeries.trunc_map]
    rw [hPSmap]
  change φ (P.eval₂ (RingHom.id A) (AdicCompletion.evalₐ I N x)) =
    P.eval₂ (RingHom.id A)
      (AdicCompletion.evalₐ I N (dworkCompleteComplexConj (p := p) K x))
  rw [evalₐ_dworkCompleteComplexConj]
  change φ (P.eval₂ (RingHom.id A) (AdicCompletion.evalₐ I N x)) =
    P.eval₂ (RingHom.id A) (φ (AdicCompletion.evalₐ I N x))
  calc
    φ (P.eval₂ (RingHom.id A) (AdicCompletion.evalₐ I N x)) =
        P.eval₂ φ (φ (AdicCompletion.evalₐ I N x)) :=
          Polynomial.hom_eval₂ P (RingHom.id A) φ (AdicCompletion.evalₐ I N x)
    _ = P.eval₂ (RingHom.id A) (φ (AdicCompletion.evalₐ I N x)) := by
          rw [← Polynomial.eval_map, hPmap]
          rfl

theorem dworkCompleteLambda_evalₐ_one :
    AdicCompletion.evalₐ (lambdaIdeal p K) 1 (dworkCompleteLambda p K) = 0 := by
  rw [dworkCompleteLambda, AdicCompletion.evalₐ_of]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (by simp [valuedCyclotomicLambdaInteger_mem_lambdaIdeal (p := p) (K := K)])

theorem dworkParameter_eq_evalIntegralPowerSeries_lambda :
    dworkParameter p K =
      evalIntegralPowerSeries p K (integralInverseSeries p K) (dworkCompleteLambda p K)
        (dworkCompleteLambda_evalₐ_one (p := p) (K := K)) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [dworkParameter_evalₐ, evalIntegralPowerSeries_evalₐ]
  change Ideal.Quotient.mk ((lambdaIdeal p K) ^ N) (dworkParameterApprox p K N) =
    (PowerSeries.trunc N
        (PowerSeries.map (Ideal.Quotient.mk ((lambdaIdeal p K) ^ N))
          (integralInverseSeries p K))).eval₂
      (RingHom.id (ValuedIntegerRing p K ⧸ (lambdaIdeal p K) ^ N))
      (AdicCompletion.evalₐ (lambdaIdeal p K) N (dworkCompleteLambda p K))
  rw [dworkCompleteLambda, AdicCompletion.evalₐ_of]
  exact quotient_mk_dworkParameterApprox_eq_trunc_eval (p := p) (K := K) N

theorem dworkCompleteComplexConj_evalIntegralPowerSeries_inverse
    (x : DworkCompleteIntegerRing p K)
    (hx : AdicCompletion.evalₐ (lambdaIdeal p K) 1 x = 0) :
    dworkCompleteComplexConj (p := p) K
        (evalIntegralPowerSeries p K (integralInverseSeries p K) x hx) =
      evalIntegralPowerSeries p K (integralInverseSeries p K)
        (dworkCompleteComplexConj (p := p) K x)
        (by
          rw [evalₐ_dworkCompleteComplexConj, hx, map_zero]) := by
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalₐ_dworkCompleteComplexConj, evalIntegralPowerSeries_evalₐ,
    evalIntegralPowerSeries_evalₐ]
  exact quotientMap_evalIntegralPowerSeriesMod_complexConj (p := p) (K := K)
    (integralInverseSeries p K)
    (integralInverseSeries_map_valuedIntegerComplexConj (p := p) (K := K))
    x N

theorem dworkCompleteComplexConj_dworkParameter :
    dworkCompleteComplexConj (p := p) K (dworkParameter p K) =
      dworkConjugateParameter p K := by
  rw [dworkParameter_eq_evalIntegralPowerSeries_lambda (p := p) (K := K)]
  rw [dworkCompleteComplexConj_evalIntegralPowerSeries_inverse]
  apply AdicCompletion.ext_evalₐ
  intro N
  rw [evalIntegralPowerSeries_evalₐ, dworkConjugateParameter_evalₐ]
  exact congrArg (fun y : DworkCompleteIntegerRing p K =>
    evalIntegralPowerSeriesMod p K (integralInverseSeries p K) y N)
      (dworkCompleteComplexConj_dworkCompleteLambda (p := p) (K := K))

theorem dworkCompleteComplexConj_dworkParameter_eq_neg (hp_two : 2 < p) :
    dworkCompleteComplexConj (p := p) K (dworkParameter p K) =
      -dworkParameter p K := by
  rw [dworkCompleteComplexConj_dworkParameter,
    dworkConjugateParameter_eq_neg_dworkParameter (p := p) (K := K) hp_two]

end Conjugation

end DworkParameter
end PadicLogSetup
end CyclotomicUnits
end BernoulliRegular
