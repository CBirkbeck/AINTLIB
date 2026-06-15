module

public import BernoulliRegular.Reflection.Local.ComponentDimension
public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionEigen
public import BernoulliRegular.Reflection.SingularKummer.CyclotomicAction
public import BernoulliRegular.Reflection.SingularKummer.Localization

/-!
# Singular Kummer: choosing a class in the localization kernel

This file records the REF-13 dimension argument.  Once the localization map is
expressed on the `i`-th singular component with codomain the completed local
principal-unit `i`-component, the inequality

```text
  dim S_i >= 2,       dim (U / U^p)_i = 1
```

gives a nonzero singular class killed by localization.  The final theorem also
unwraps that class to a singular pair `(I, eta)`, recording the singular
principal-ideal relation and the `Delta` eigenrelation.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

namespace LinearDimensionKernel

variable {F U V W A : Type*} [Field F]
variable [AddCommGroup U] [Module F U]
variable [AddCommGroup V] [Module F V]
variable [AddCommGroup W] [Module F W]
variable [AddCommGroup A] [Module F A]

/-- If a linear map has target dimension strictly smaller than source
dimension, then its kernel contains a nonzero vector. -/
theorem exists_ne_zero_map_eq_zero_of_finrank_lt
    [FiniteDimensional F V] [FiniteDimensional F W]
    (f : V →ₗ[F] W) (h : Module.finrank F W < Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ f v = 0 := by
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (f := f) h
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨v, hv_ne, LinearMap.mem_ker.mp hv_mem⟩

/-- Rank-nullity form of the primary pseudo-unit dimension estimate. If the
class map `π` is onto and the local target is no larger than the class-map
kernel, then the kernel of any localization map has dimension at least the
class target. -/
theorem finrank_class_le_ker_localization_of_surjective_of_local_le_classKernel
    [FiniteDimensional F V] [FiniteDimensional F W] [FiniteDimensional F A]
    (π : V →ₗ[F] A) (loc : V →ₗ[F] W)
    (hπ_surj : Function.Surjective π)
    (hW_le_kerπ :
      Module.finrank F W ≤ Module.finrank F (LinearMap.ker π)) :
    Module.finrank F A ≤ Module.finrank F (LinearMap.ker loc) := by
  have hπ_range :
      Module.finrank F (LinearMap.range π) = Module.finrank F A := by
    rw [LinearMap.range_eq_top.mpr hπ_surj, finrank_top]
  have hπ_rank := LinearMap.finrank_range_add_finrank_ker π
  have hloc_rank := LinearMap.finrank_range_add_finrank_ker loc
  have hloc_range_le :
      Module.finrank F (LinearMap.range loc) ≤ Module.finrank F W :=
    (LinearMap.range loc).finrank_le
  omega

/-- Same estimate, with the unit kernel supplied by an injective left-hand
subspace. This is the abstract linear algebra behind the weak-reflection
primary-subspace route: the unit eigenspace pays for the local obstruction, so
the primary pseudo-units still dominate the class eigenspace. -/
theorem finrank_class_le_ker_localization_of_leftKernel
    [FiniteDimensional F U] [FiniteDimensional F V]
    [FiniteDimensional F W] [FiniteDimensional F A]
    (ι : U →ₗ[F] V) (π : V →ₗ[F] A) (loc : V →ₗ[F] W)
    (hπ_surj : Function.Surjective π)
    (hπι : ∀ u, π (ι u) = 0)
    (hι_inj : Function.Injective ι)
    (hU_finrank_eq_W : Module.finrank F U = Module.finrank F W) :
    Module.finrank F A ≤ Module.finrank F (LinearMap.ker loc) := by
  let ιker : U →ₗ[F] LinearMap.ker π := {
    toFun := fun u => ⟨ι u, hπι u⟩
    map_add' := by
      intro u v
      apply Subtype.ext
      simp
    map_smul' := by
      intro c u
      apply Subtype.ext
      simp }
  have hιker_inj : Function.Injective ιker := fun u v huv =>
    hι_inj <| congrArg Subtype.val huv
  have hU_le_kerπ :
      Module.finrank F U ≤ Module.finrank F (LinearMap.ker π) :=
    LinearMap.finrank_le_finrank_of_injective (f := ιker) hιker_inj
  have hW_le_kerπ :
      Module.finrank F W ≤ Module.finrank F (LinearMap.ker π) := by
    rwa [← hU_finrank_eq_W]
  exact
    finrank_class_le_ker_localization_of_surjective_of_local_le_classKernel
      π loc hπ_surj hW_le_kerπ

/-- If `π : V → A` is onto and its kernel is covered by a finite-dimensional
source `U`, then `V` is finite-dimensional whenever `A` is.

This is the finite-dimensionality half of the same exact-sequence argument
used below for localization kernels. -/
theorem finiteDimensional_of_surjective_of_leftKernel
    [FiniteDimensional F U] [FiniteDimensional F A]
    (ι : U →ₗ[F] V) (π : V →ₗ[F] A)
    (hπ_surj : Function.Surjective π)
    (hker : ∀ v : V, π v = 0 → ∃ u : U, ι u = v) :
    FiniteDimensional F V := by
  obtain ⟨σ, hσ⟩ :=
    LinearMap.exists_rightInverse_of_surjective π (LinearMap.range_eq_top.mpr hπ_surj)
  let cover : U × A →ₗ[F] V := {
    toFun := fun ua => ι ua.1 + σ ua.2
    map_add' := by
      intro x y
      simp [add_assoc, add_left_comm, add_comm]
    map_smul' := by
      intro c x
      simp [smul_add] }
  have hcover_surj : Function.Surjective cover := by
    intro v
    let a : A := π v
    have hπσ : π (σ a) = a := by
      have happ := LinearMap.congr_fun hσ a
      simpa [LinearMap.comp_apply] using happ
    have hker_elem : π (v - σ a) = 0 := by
      simp [a, hπσ]
    obtain ⟨u, hu⟩ := hker (v - σ a) hker_elem
    refine ⟨(u, a), ?_⟩
    change ι u + σ a = v
    rw [hu]
    abel
  exact FiniteDimensional.of_surjective cover hcover_surj

end LinearDimensionKernel

namespace SingularPair

open SingularLinearAction.SingularPair

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- A lambda-local unit becomes a principal unit after raising to `p - 1`.

The residue field at `lambda` has cardinality `p`, so every nonzero residue
class has `(p - 1)`-st power equal to one. -/
theorem localCyclotomicUnit_pow_primeSubOne_mem_principalUnitSubgroup_one
    (u : Local.localCyclotomicUnitGroup p K) :
    u ^ (p - 1) ∈ Local.principalUnitSubgroup p K 1 := by
  let R := Local.localCyclotomicRing p K
  let M := Local.localCyclotomicMaximalIdeal p K
  let k := R ⧸ M
  letI : M.IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  letI : Field k := Ideal.Quotient.field M
  have hcard : Nat.card k = p := Local.localCyclotomicResidueCard (p := p) (K := K)
  haveI : Finite k := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact (Fact.out : p.Prime).ne_zero)
  letI : Fintype k := Fintype.ofFinite k
  have hcardF : Fintype.card k = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  have hunit :
      IsUnit (Ideal.Quotient.mk M (u : R)) :=
    IsUnit.map (Ideal.Quotient.mk M) u.isUnit
  have hpow :
      (Ideal.Quotient.mk M (u : R)) ^ (p - 1) = 1 := by
    have hpow0 :=
      FiniteField.pow_card_sub_one_eq_one
        (Ideal.Quotient.mk M (u : R)) hunit.ne_zero
    rw [hcardF] at hpow0
    exact hpow0
  rw [Local.mem_principalUnitSubgroup_iff]
  rw [pow_one]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  change Ideal.Quotient.mk M (((u ^ (p - 1) : Local.localCyclotomicUnitGroup p K) : R) - 1) = 0
  rw [map_sub, map_one, Units.val_pow_eq_pow_val]
  simp [hpow]

/-- The local-to-completed unit map preserves the principal-unit filtration. -/
theorem completedLocalCyclotomicUnitMap_mem_completedPrincipalUnitSubgroup
    {n : ℕ} {u : Local.localCyclotomicUnitGroup p K}
    (hu : u ∈ Local.principalUnitSubgroup p K n) :
    Local.completedLocalCyclotomicUnitMap p K u ∈
      Local.completedPrincipalUnitSubgroup p K n := by
  let R := Local.localCyclotomicRing p K
  let S := Local.completedLocalCyclotomicRing p K
  let M := Local.localCyclotomicMaximalIdeal p K
  have hlocal :
      (u : R) - 1 ∈ M ^ n :=
    (Local.mem_principalUnitSubgroup_iff (p := p) (K := K) (n := n)
      (u := u)).mp hu
  have hmap :
      algebraMap R S ((u : R) - 1) ∈
        Ideal.map (algebraMap R S) (M ^ n) :=
    Ideal.mem_map_of_mem (algebraMap R S) hlocal
  rw [Local.mem_completedPrincipalUnitSubgroup_iff]
  simpa [R, S, M, Local.completedLocalCyclotomicUnitMap,
    Local.completedLocalCyclotomicMaximalIdeal, Ideal.map_pow, map_sub, map_one] using hmap

/-- Raise a lambda-local unit to `p - 1`, map it into the completion, and view
the result as a completed principal unit. -/
noncomputable def localCyclotomicUnitToCompletedPrincipalUnit
    (u : Local.localCyclotomicUnitGroup p K) :
    Local.completedPrincipalUnitSubgroup p K 1 :=
  ⟨Local.completedLocalCyclotomicUnitMap p K (u ^ (p - 1)),
    completedLocalCyclotomicUnitMap_mem_completedPrincipalUnitSubgroup
      (p := p) (K := K)
      (localCyclotomicUnit_pow_primeSubOne_mem_principalUnitSubgroup_one
        (p := p) (K := K) u)⟩

/-- The multiplicative map from lambda-local units to completed principal
units induced by `u ↦ u^(p-1)`. -/
noncomputable def localCyclotomicUnitToCompletedPrincipalUnitHom :
    Local.localCyclotomicUnitGroup p K →*
      Local.completedPrincipalUnitSubgroup p K 1 where
  toFun := localCyclotomicUnitToCompletedPrincipalUnit p K
  map_one' := by
    apply Subtype.ext
    simp [localCyclotomicUnitToCompletedPrincipalUnit]
  map_mul' u v := by
    apply Subtype.ext
    simp [localCyclotomicUnitToCompletedPrincipalUnit, map_mul, mul_pow]

/-- The local-to-completed principal-unit bridge is equivariant for the
cyclotomic action on lambda-local units. -/
theorem localCyclotomicUnitToCompletedPrincipalUnitHom_equivariant
    (a : CharacterProjection.Delta p) (u : Local.localCyclotomicUnitGroup p K) :
    localCyclotomicUnitToCompletedPrincipalUnitHom p K
        (Local.localCyclotomicUnitEquiv (p := p) K a u) =
      Local.completedPrincipalUnitSubgroupEquiv (p := p) K a 1
        (localCyclotomicUnitToCompletedPrincipalUnitHom p K u) := by
  apply Subtype.ext
  apply Units.ext
  simp [localCyclotomicUnitToCompletedPrincipalUnitHom,
    localCyclotomicUnitToCompletedPrincipalUnit, Local.completedLocalCyclotomicUnitMap,
    Local.completedPrincipalUnitSubgroupEquiv, map_pow]

/-- Local units modulo `p`-th powers map to the completed principal-unit
mod-`p` quotient by first taking the `(p - 1)`-st power. -/
noncomputable def localCyclotomicUnitToCompletedPrincipalUnitModPHom :
    Local.localCyclotomicUnitGroup p K →*
      Local.completedPrincipalUnitModPQuotient p K :=
  (Local.completedPrincipalUnitModPClass p K).comp
    (localCyclotomicUnitToCompletedPrincipalUnitHom p K)

/-- The local-to-completed bridge remains equivariant after quotienting by
`p`-th powers. -/
theorem localCyclotomicUnitToCompletedPrincipalUnitModPHom_equivariant
    (a : CharacterProjection.Delta p) (u : Local.localCyclotomicUnitGroup p K) :
    localCyclotomicUnitToCompletedPrincipalUnitModPHom p K
        (Local.localCyclotomicUnitEquiv (p := p) K a u) =
      Local.completedPrincipalUnitModPDeltaAction (p := p) K a
        (localCyclotomicUnitToCompletedPrincipalUnitModPHom p K u) := by
  change Local.completedPrincipalUnitModPClass p K
      (localCyclotomicUnitToCompletedPrincipalUnitHom p K
        (Local.localCyclotomicUnitEquiv (p := p) K a u)) =
    Local.completedPrincipalUnitModPDeltaAction (p := p) K a
      (Local.completedPrincipalUnitModPClass p K
        (localCyclotomicUnitToCompletedPrincipalUnitHom p K u))
  rw [localCyclotomicUnitToCompletedPrincipalUnitHom_equivariant]
  exact Local.completedPrincipalUnitModPDeltaAction_apply_class (p := p) (K := K) a
    (localCyclotomicUnitToCompletedPrincipalUnitHom p K u)

@[simp]
theorem localCyclotomicUnitToCompletedPrincipalUnitModPHom_pow_eq_one
    (u : Local.localCyclotomicUnitGroup p K) :
    localCyclotomicUnitToCompletedPrincipalUnitModPHom p K (u ^ p) = 1 := by
  rw [map_pow]
  exact Local.completedPrincipalUnitModPQuotient_pow_eq_one (p := p) (K := K)
    (localCyclotomicUnitToCompletedPrincipalUnitModPHom p K u)

/-- The canonical embedding of the lambda-local ring into the global fraction
field. -/
noncomputable abbrev localCyclotomicRingToField :
    Local.localCyclotomicRing p K →ₐ[𝓞 K] K :=
  Localization.mapToFractionRing K (Local.cyclotomicLambda p K).primeCompl
    (Local.localCyclotomicRing p K)
    (Ideal.primeCompl_le_nonZeroDivisors (Local.cyclotomicLambda p K))

theorem localCyclotomicRingToField_injective :
    Function.Injective (localCyclotomicRingToField p K) := by
  let S := (Local.cyclotomicLambda p K).primeCompl
  let hS : S ≤ (𝓞 K)⁰ :=
    Ideal.primeCompl_le_nonZeroDivisors (Local.cyclotomicLambda p K)
  change Function.Injective
    (Localization.mapToFractionRing K S (Local.localCyclotomicRing p K) hS)
  intro x y hxy
  exact
    (IsLocalization.lift_injective_iff
      (M := S) (S := Local.localCyclotomicRing p K)
      (P := K)
      (g := algebraMap (𝓞 K) K)
      (hg := Localization.map_isUnit_of_le K S hS)).2
      (fun a b =>
        ⟨fun h => congr_arg _ (IsLocalization.injective _ hS h),
          fun h => congr_arg _ (IsFractionRing.injective (𝓞 K) K h)⟩)
      hxy

/-- The embedding of the lambda-local ring into `K` intertwines the local
cyclotomic action with the global field automorphism. -/
theorem localCyclotomicRingToField_localCyclotomicRingEquiv
    (a : CharacterProjection.Delta p) (x : Local.localCyclotomicRing p K) :
    localCyclotomicRingToField p K
        (Local.localCyclotomicRingEquiv (p := p) K a x) =
      cyclotomicSigmaOfUnit (p := p) K a (localCyclotomicRingToField p K x) := by
  let S := (Local.cyclotomicLambda p K).primeCompl
  have hhom :
      (localCyclotomicRingToField p K).toRingHom.comp
          (Local.localCyclotomicRingEquiv (p := p) K a :
            Local.localCyclotomicRing p K →+* Local.localCyclotomicRing p K) =
        (cyclotomicSigmaOfUnit (p := p) K a).toRingHom.comp
          (localCyclotomicRingToField p K).toRingHom := by
    apply IsLocalization.ringHom_ext S
    ext r
    change localCyclotomicRingToField p K
        (Local.localCyclotomicRingEquiv (p := p) K a
          (algebraMap (𝓞 K) (Local.localCyclotomicRing p K) r)) =
      cyclotomicSigmaOfUnit (p := p) K a
        (localCyclotomicRingToField p K
          (algebraMap (𝓞 K) (Local.localCyclotomicRing p K) r))
    rw [Local.localCyclotomicRingEquiv_algebraMap]
    rw [(localCyclotomicRingToField p K).commutes
        ((cyclotomicRingOfIntegersEquiv (p := p) K a) r),
      (localCyclotomicRingToField p K).commutes r]
    exact
      (RingOfIntegers.mapRingEquiv_apply
        ((cyclotomicSigmaOfUnit (p := p) K a).toRingEquiv) r).symm
  exact RingHom.congr_fun hhom x

/-- The image of the lambda-local ring in `K` lies in the valuation subring at
the lambda prime. -/
theorem localCyclotomicRingToField_mem_valuationSubring
    (x : Local.localCyclotomicRing p K) :
    localCyclotomicRingToField p K x ∈
      ((cyclotomicLambdaHeightOne (p := p) K).valuation K).valuationSubring := by
  let v := cyclotomicLambdaHeightOne (p := p) K
  have hrange :
      localCyclotomicRingToField p K x ∈
        (Localization.mapToFractionRing K (Local.cyclotomicLambda p K).primeCompl
          (Local.localCyclotomicRing p K)
          (Ideal.primeCompl_le_nonZeroDivisors (Local.cyclotomicLambda p K))).range :=
    ⟨x, rfl⟩
  rw [Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField] at hrange
  have hloc :
      localCyclotomicRingToField p K x ∈
        (Localization.subalgebra.ofField K v.asIdeal.primeCompl
          v.asIdeal.primeCompl_le_nonZeroDivisors : Subalgebra (𝓞 K) K).toSubring := by
    simpa [Localization.subalgebra.ofField, v, cyclotomicLambdaHeightOne] using hrange
  change localCyclotomicRingToField p K x ∈ (v.valuation K).valuationSubring.toSubring
  rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
    (K := K) (v := v)]
  rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring
    (K := K) (v := v)]
  simpa [Localization.subalgebra.ofField] using hloc

/-- A lambda-local unit maps to a global field unit with valuation one at
lambda. -/
theorem localCyclotomicUnit_fieldUnit_mem_cyclotomicLocalUnitSubgroup
    (u : Local.localCyclotomicUnitGroup p K) (y : Kˣ)
    (hy : localCyclotomicRingToField p K (u : Local.localCyclotomicRing p K) =
      (y : K)) :
    y ∈ cyclotomicLocalUnitSubgroup (p := p) K := by
  let v := cyclotomicLambdaHeightOne (p := p) K
  let A := (v.valuation K).valuationSubring
  have hy_mem : (y : K) ∈ A := by
    simpa [A, v, hy.symm] using
      localCyclotomicRingToField_mem_valuationSubring (p := p) (K := K)
        (u : Local.localCyclotomicRing p K)
  have hy_inv :
      localCyclotomicRingToField p K ((u⁻¹ : Local.localCyclotomicUnitGroup p K) :
        Local.localCyclotomicRing p K) = ((y⁻¹ : Kˣ) : K) := by
    have hmul :
        localCyclotomicRingToField p K
            ((u⁻¹ : Local.localCyclotomicUnitGroup p K) :
              Local.localCyclotomicRing p K) * (y : K) = 1 := by
      rw [← hy, ← map_mul]
      simp
    simpa using (mul_eq_one_iff_eq_inv₀ y.ne_zero).mp hmul
  have hy_inv_mem : ((y⁻¹ : Kˣ) : K) ∈ A := by
    simpa [A, v, hy_inv.symm] using
      localCyclotomicRingToField_mem_valuationSubring (p := p) (K := K)
        ((u⁻¹ : Local.localCyclotomicUnitGroup p K) : Local.localCyclotomicRing p K)
  let yA : Aˣ :=
    {
      val := ⟨(y : K), hy_mem⟩
      inv := ⟨((y⁻¹ : Kˣ) : K), hy_inv_mem⟩
      val_inv := by
        ext
        simp
      inv_val := by
        ext
        simp
    }
  have hunit : y ∈ A.unitGroup := by
    have hpre : (A.unitGroupMulEquiv.symm yA : Kˣ) = y := by
      apply Units.ext
      rfl
    simpa [hpre] using (A.unitGroupMulEquiv.symm yA).2
  rw [mem_localUnitSubgroupAt_iff]
  exact (Valuation.mem_unitGroup_iff (v := v.valuation K) (x := y)).mp hunit

theorem cyclotomicLocalUnitSubgroup_exists_local_preimage
    (u : cyclotomicLocalUnitSubgroup (p := p) K) :
    ∃ x : Local.localCyclotomicRing p K,
      localCyclotomicRingToField p K x = ((u : Kˣ) : K) := by
  let v := cyclotomicLambdaHeightOne (p := p) K
  have huval :
      v.valuation K ((u : Kˣ) : K) = 1 :=
    (mem_localUnitSubgroupAt_iff (R := 𝓞 K) (K := K) v
      (x := (u : Kˣ))).mp u.2
  have hval :
      ((u : Kˣ) : K) ∈ (v.valuation K).valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff]
    exact le_of_eq huval
  have hloc :
      ((u : Kˣ) : K) ∈
        (Localization.subalgebra.ofField K v.asIdeal.primeCompl
          v.asIdeal.primeCompl_le_nonZeroDivisors : Subalgebra (𝓞 K) K) := by
    change ((u : Kˣ) : K) ∈
      (Localization.subalgebra.ofField K v.asIdeal.primeCompl
        v.asIdeal.primeCompl_le_nonZeroDivisors : Subalgebra (𝓞 K) K).toSubring
    rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_toSubring
      (K := K) (v := v)]
    rw [IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring
      (K := K) (v := v)]
    exact hval
  have hrange :
      ((u : Kˣ) : K) ∈
        (localCyclotomicRingToField p K).toRingHom.range := by
    change ((u : Kˣ) : K) ∈
      (Localization.mapToFractionRing K (Local.cyclotomicLambda p K).primeCompl
        (Local.localCyclotomicRing p K)
        (Ideal.primeCompl_le_nonZeroDivisors (Local.cyclotomicLambda p K))).range
    rw [Localization.subalgebra.mem_range_mapToFractionRing_iff_ofField]
    exact hloc
  rcases hrange with ⟨x, hx⟩
  exact ⟨x, hx⟩

/-- Choose the lambda-local representative of a REF-12 cyclotomic local unit. -/
noncomputable def cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit
    (u : cyclotomicLocalUnitSubgroup (p := p) K) :
    Local.localCyclotomicUnitGroup p K :=
  let x := Classical.choose
    (cyclotomicLocalUnitSubgroup_exists_local_preimage (p := p) (K := K) u)
  let y := Classical.choose
    (cyclotomicLocalUnitSubgroup_exists_local_preimage (p := p) (K := K)
      (u⁻¹ : cyclotomicLocalUnitSubgroup (p := p) K))
  {
    val := x
    inv := y
    val_inv := by
      apply localCyclotomicRingToField_injective (p := p) (K := K)
      have hx := Classical.choose_spec
        (cyclotomicLocalUnitSubgroup_exists_local_preimage (p := p) (K := K) u)
      have hy := Classical.choose_spec
        (cyclotomicLocalUnitSubgroup_exists_local_preimage (p := p) (K := K)
          (u⁻¹ : cyclotomicLocalUnitSubgroup (p := p) K))
      rw [map_mul, hx, hy, map_one]
      simp
    inv_val := by
      apply localCyclotomicRingToField_injective (p := p) (K := K)
      have hx := Classical.choose_spec
        (cyclotomicLocalUnitSubgroup_exists_local_preimage (p := p) (K := K) u)
      have hy := Classical.choose_spec
        (cyclotomicLocalUnitSubgroup_exists_local_preimage (p := p) (K := K)
          (u⁻¹ : cyclotomicLocalUnitSubgroup (p := p) K))
      rw [map_mul, hx, hy, map_one]
      simp
  }

@[simp]
theorem localCyclotomicRingToField_cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit
    (u : cyclotomicLocalUnitSubgroup (p := p) K) :
    localCyclotomicRingToField p K
        (cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit (p := p) (K := K) u :
          Local.localCyclotomicRing p K) =
      ((u : Kˣ) : K) :=
  Classical.choose_spec
    (cyclotomicLocalUnitSubgroup_exists_local_preimage (p := p) (K := K) u)

/-- The global cyclotomic automorphism preserves the lambda-local unit
subgroup. -/
theorem cyclotomicFieldUnitEquiv_mem_cyclotomicLocalUnitSubgroup
    (a : CharacterProjection.Delta p) (u : cyclotomicLocalUnitSubgroup (p := p) K) :
    cyclotomicFieldUnitEquiv K p a (u : Kˣ) ∈
      cyclotomicLocalUnitSubgroup (p := p) K := by
  let uloc :=
    cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit (p := p) (K := K) u
  have hfield :
      localCyclotomicRingToField p K
          (Local.localCyclotomicUnitEquiv (p := p) K a uloc :
            Local.localCyclotomicRing p K) =
        ((cyclotomicFieldUnitEquiv K p a (u : Kˣ) : Kˣ) : K) := by
    rw [Local.localCyclotomicUnitEquiv_coe,
      localCyclotomicRingToField_localCyclotomicRingEquiv]
    rw [localCyclotomicRingToField_cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit]
    rfl
  exact localCyclotomicUnit_fieldUnit_mem_cyclotomicLocalUnitSubgroup
    (p := p) (K := K) (Local.localCyclotomicUnitEquiv (p := p) K a uloc)
    (cyclotomicFieldUnitEquiv K p a (u : Kˣ)) hfield

/-- The cyclotomic action restricted to REF-12 lambda-local units. -/
noncomputable def cyclotomicLocalUnitSubgroupEquiv
    (a : CharacterProjection.Delta p) :
    cyclotomicLocalUnitSubgroup (p := p) K ≃*
      cyclotomicLocalUnitSubgroup (p := p) K where
  toFun u :=
    ⟨cyclotomicFieldUnitEquiv K p a (u : Kˣ),
      cyclotomicFieldUnitEquiv_mem_cyclotomicLocalUnitSubgroup
        (p := p) (K := K) a u⟩
  invFun u :=
    ⟨cyclotomicFieldUnitEquiv K p a⁻¹ (u : Kˣ),
      cyclotomicFieldUnitEquiv_mem_cyclotomicLocalUnitSubgroup
        (p := p) (K := K) a⁻¹ u⟩
  left_inv u := by
    apply Subtype.ext
    change cyclotomicFieldUnitEquiv K p a⁻¹
        (cyclotomicFieldUnitEquiv K p a (u : Kˣ)) = (u : Kˣ)
    rw [← cyclotomicFieldUnitEquiv_mul_apply]
    simp
  right_inv u := by
    apply Subtype.ext
    change cyclotomicFieldUnitEquiv K p a
        (cyclotomicFieldUnitEquiv K p a⁻¹ (u : Kˣ)) = (u : Kˣ)
    rw [← cyclotomicFieldUnitEquiv_mul_apply]
    simp
  map_mul' u v := by
    apply Subtype.ext
    change cyclotomicFieldUnitEquiv K p a ((u : Kˣ) * (v : Kˣ)) =
      cyclotomicFieldUnitEquiv K p a (u : Kˣ) *
        cyclotomicFieldUnitEquiv K p a (v : Kˣ)
    exact map_mul (cyclotomicFieldUnitEquiv K p a) (u : Kˣ) (v : Kˣ)

@[simp]
theorem cyclotomicLocalUnitSubgroupEquiv_coe
    (a : CharacterProjection.Delta p) (u : cyclotomicLocalUnitSubgroup (p := p) K) :
    (cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a u : Kˣ) =
      cyclotomicFieldUnitEquiv K p a (u : Kˣ) :=
  rfl

/-- The chosen local representative is multiplicative because it is
multiplicative after embedding in the fraction field. -/
noncomputable def cyclotomicLocalUnitSubgroupToLocalCyclotomicUnitHom :
    cyclotomicLocalUnitSubgroup (p := p) K →*
      Local.localCyclotomicUnitGroup p K where
  toFun := cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit (p := p) (K := K)
  map_one' := by
    apply Units.ext
    apply localCyclotomicRingToField_injective (p := p) (K := K)
    change localCyclotomicRingToField p K
        (cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit (p := p) (K := K)
          (1 : cyclotomicLocalUnitSubgroup (p := p) K) :
          Local.localCyclotomicRing p K) =
      localCyclotomicRingToField p K (1 : Local.localCyclotomicRing p K)
    rw [localCyclotomicRingToField_cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit,
      map_one]
    rfl
  map_mul' u v := by
    apply Units.ext
    apply localCyclotomicRingToField_injective (p := p) (K := K)
    change localCyclotomicRingToField p K
        (cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit (p := p) (K := K) (u * v) :
          Local.localCyclotomicRing p K) =
      localCyclotomicRingToField p K
        ((cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit (p := p) (K := K) u :
            Local.localCyclotomicUnitGroup p K) *
          cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit (p := p) (K := K) v :
          Local.localCyclotomicRing p K)
    rw [map_mul,
      localCyclotomicRingToField_cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit,
      localCyclotomicRingToField_cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit,
      localCyclotomicRingToField_cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit]
    rfl

/-- The chosen lambda-local representative intertwines the restricted global
action with the actual action on the localized ring. -/
theorem cyclotomicLocalUnitSubgroupToLocalCyclotomicUnitHom_equivariant
    (a : CharacterProjection.Delta p) (u : cyclotomicLocalUnitSubgroup (p := p) K) :
    cyclotomicLocalUnitSubgroupToLocalCyclotomicUnitHom (p := p) (K := K)
        (cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a u) =
      Local.localCyclotomicUnitEquiv (p := p) K a
        (cyclotomicLocalUnitSubgroupToLocalCyclotomicUnitHom (p := p) (K := K) u) := by
  apply Units.ext
  apply localCyclotomicRingToField_injective (p := p) (K := K)
  change localCyclotomicRingToField p K
      (cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit (p := p) (K := K)
        (cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a u) :
        Local.localCyclotomicRing p K) =
    localCyclotomicRingToField p K
      (Local.localCyclotomicUnitEquiv (p := p) K a
        (cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit (p := p) (K := K) u) :
        Local.localCyclotomicRing p K)
  rw [localCyclotomicRingToField_cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit,
    Local.localCyclotomicUnitEquiv_coe,
    localCyclotomicRingToField_localCyclotomicRingEquiv,
    localCyclotomicRingToField_cyclotomicLocalUnitSubgroupToLocalCyclotomicUnit]
  rfl

/-- The concrete bridge from REF-12 local units to the completed REF-11
principal-unit quotient. -/
noncomputable def cyclotomicLocalUnitToCompletedPrincipalUnitModPHom :
    cyclotomicLocalUnitSubgroup (p := p) K →*
      Local.completedPrincipalUnitModPQuotient p K :=
  (localCyclotomicUnitToCompletedPrincipalUnitModPHom p K).comp
    (cyclotomicLocalUnitSubgroupToLocalCyclotomicUnitHom (p := p) (K := K))

/-- The concrete bridge from REF-12 local units to completed principal units is
equivariant once the REF-12 local-unit subgroup is acted on by the restricted
global cyclotomic action. -/
theorem cyclotomicLocalUnitToCompletedPrincipalUnitModPHom_equivariant
    (a : CharacterProjection.Delta p) (u : cyclotomicLocalUnitSubgroup (p := p) K) :
    cyclotomicLocalUnitToCompletedPrincipalUnitModPHom p K
        (cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a u) =
      Local.completedPrincipalUnitModPDeltaAction (p := p) K a
        (cyclotomicLocalUnitToCompletedPrincipalUnitModPHom p K u) := by
  change localCyclotomicUnitToCompletedPrincipalUnitModPHom p K
      (cyclotomicLocalUnitSubgroupToLocalCyclotomicUnitHom (p := p) (K := K)
        (cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a u)) =
    Local.completedPrincipalUnitModPDeltaAction (p := p) K a
      (localCyclotomicUnitToCompletedPrincipalUnitModPHom p K
        (cyclotomicLocalUnitSubgroupToLocalCyclotomicUnitHom (p := p) (K := K) u))
  rw [cyclotomicLocalUnitSubgroupToLocalCyclotomicUnitHom_equivariant,
    localCyclotomicUnitToCompletedPrincipalUnitModPHom_equivariant]

@[simp]
theorem cyclotomicLocalUnitToCompletedPrincipalUnitModPHom_pow_eq_one
    (u : cyclotomicLocalUnitSubgroup (p := p) K) :
    cyclotomicLocalUnitToCompletedPrincipalUnitModPHom p K (u ^ p) = 1 := by
  rw [map_pow]
  exact Local.completedPrincipalUnitModPQuotient_pow_eq_one (p := p) (K := K)
    (cyclotomicLocalUnitToCompletedPrincipalUnitModPHom p K u)

/-- The subgroup of `p`-th powers in the REF-12 cyclotomic local-unit group. -/
abbrev cyclotomicLocalUnitPowerSubgroup :
    Subgroup (cyclotomicLocalUnitSubgroup (p := p) K) :=
  (powMonoidHom p : cyclotomicLocalUnitSubgroup (p := p) K →*
    cyclotomicLocalUnitSubgroup (p := p) K).range

/-- The subgroup of local `p`-th powers is stable under the restricted
cyclotomic action. -/
theorem cyclotomicLocalUnitPowerSubgroup_map
    (a : CharacterProjection.Delta p) :
    (cyclotomicLocalUnitPowerSubgroup (p := p) K).map
        (cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a).toMonoidHom =
      cyclotomicLocalUnitPowerSubgroup (p := p) K := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, rfl⟩, rfl⟩
    exact ⟨cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a z, by simp [map_pow]⟩
  · intro hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨(cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a).symm z ^ p, ?_, ?_⟩
    · exact ⟨(cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a).symm z, rfl⟩
    · rw [map_pow]
      change cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a
          ((cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a).symm z) ^ p =
        z ^ p
      rw [MulEquiv.apply_symm_apply]

/-- The restricted cyclotomic action on `U_lambda / U_lambda^p`. -/
noncomputable def cyclotomicLocalUnitPowerQuotientEquiv
    (a : CharacterProjection.Delta p) :
    cyclotomicLocalUnitPowerQuotient (p := p) K ≃*
      cyclotomicLocalUnitPowerQuotient (p := p) K :=
  QuotientGroup.congr
    (cyclotomicLocalUnitPowerSubgroup (p := p) K)
    (cyclotomicLocalUnitPowerSubgroup (p := p) K)
    (cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a)
    (cyclotomicLocalUnitPowerSubgroup_map (p := p) (K := K) a)

@[simp]
theorem cyclotomicLocalUnitPowerQuotientEquiv_mk
    (a : CharacterProjection.Delta p) (u : cyclotomicLocalUnitSubgroup (p := p) K) :
    cyclotomicLocalUnitPowerQuotientEquiv (p := p) (K := K) a
        (QuotientGroup.mk u : cyclotomicLocalUnitPowerQuotient (p := p) K) =
      (QuotientGroup.mk (cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a u) :
        cyclotomicLocalUnitPowerQuotient (p := p) K) :=
  rfl

/-- REF-12 localization is equivariant on singular-pair generators.  The
normalization uniformizer need not be fixed by `Delta`; the point is that both
normalization exponents are divisible by `p` for singular generators, so the
uniformizer discrepancy is a local `p`-th power in the quotient. -/
theorem fieldUnitToCyclotomicLocalUnitPowerQuotient_equivariant_generator
    (a : CharacterProjection.Delta p) (s : SingularPair (𝓞 K) K p) :
    fieldUnitToLocalUnitPowerQuotient (R := 𝓞 K) (K := K)
        (cyclotomicLambdaHeightOne (p := p) K) p
        (cyclotomicFieldUnitEquiv K p a (generator s)) =
      cyclotomicLocalUnitPowerQuotientEquiv (p := p) (K := K) a
        (fieldUnitToLocalUnitPowerQuotient (R := 𝓞 K) (K := K)
          (cyclotomicLambdaHeightOne (p := p) K) p (generator s)) := by
  let v := cyclotomicLambdaHeightOne (p := p) K
  let σ := cyclotomicFieldUnitEquiv K p a
  let π := localUniformizerUnit (R := 𝓞 K) (K := K) v
  let γ := generator s
  obtain ⟨m, hm⟩ : ∃ m : ℤ,
      localUniformizerExponent (R := 𝓞 K) (K := K) v γ = (p : ℤ) * m :=
    localUniformizerExponent_generator_dvd (R := 𝓞 K) (K := K) v p s
  obtain ⟨n, hn⟩ : ∃ n : ℤ,
      localUniformizerExponent (R := 𝓞 K) (K := K) v (σ γ) = (p : ℤ) * n := by
    let A := cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a
    have h := localUniformizerExponent_generator_dvd (R := 𝓞 K) (K := K) v p
      (A.singularPairEquiv p s)
    simp only [A, σ, γ, v, cyclotomicPrincipalIdealPreservingEquiv] at h
    obtain ⟨n, hn'⟩ := h
    exact ⟨n, hn'⟩
  change localUnitPowerClassAt (R := 𝓞 K) (K := K) v p
        (localUnitNormalization (R := 𝓞 K) (K := K) v (σ γ)) =
      cyclotomicLocalUnitPowerQuotientEquiv (p := p) (K := K) a
        (localUnitPowerClassAt (R := 𝓞 K) (K := K) v p
          (localUnitNormalization (R := 𝓞 K) (K := K) v γ))
  rw [localUnitPowerClassAt_apply, localUnitPowerClassAt_apply,
    cyclotomicLocalUnitPowerQuotientEquiv_mk]
  apply (QuotientGroup.eq).2
  change ((localUnitNormalization (R := 𝓞 K) (K := K) v (σ γ))⁻¹ *
      cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a
        (localUnitNormalization (R := 𝓞 K) (K := K) v γ)) ∈
    cyclotomicLocalUnitPowerSubgroup (p := p) K
  let ratio : cyclotomicLocalUnitSubgroup (p := p) K :=
    (localUnitNormalization (R := 𝓞 K) (K := K) v (σ γ))⁻¹ *
      cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a
        (localUnitNormalization (R := 𝓞 K) (K := K) v γ)
  let y : Kˣ := π ^ n / (σ π) ^ m
  refine ⟨localUnitNormalizationHom (R := 𝓞 K) (K := K) v y, ?_⟩
  apply Subtype.ext
  change (((localUnitNormalizationHom (R := 𝓞 K) (K := K) v y) ^ p :
      localUnitSubgroupAt (R := 𝓞 K) (K := K) v) : Kˣ) = (ratio : Kˣ)
  rw [← map_pow (localUnitNormalizationHom (R := 𝓞 K) (K := K) v) y p]
  rw [localUnitNormalizationHom_apply]
  have hy_pow : y ^ p = (ratio : Kˣ) := by
    symm
    dsimp [ratio, y, localUnitNormalization]
    change (σ γ / π ^ localUniformizerExponent (R := 𝓞 K) (K := K) v (σ γ))⁻¹ *
        (σ (γ / π ^ localUniformizerExponent (R := 𝓞 K) (K := K) v γ)) =
      (π ^ n / (σ π) ^ m) ^ p
    rw [hm, hn]
    rw [map_div, map_zpow]
    rw [div_pow]
    rw [← zpow_natCast (π ^ n) p, ← zpow_natCast ((σ π) ^ m) p]
    rw [← zpow_mul, ← zpow_mul]
    have hncomm : n * (p : ℤ) = (p : ℤ) * n := by ring
    have hmcomm : m * (p : ℤ) = (p : ℤ) * m := by ring
    rw [hncomm, hmcomm]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    simp only [mul_inv_rev, inv_inv, mul_inv_mul_mul_cancel]
    exact (div_eq_mul_inv _ _).symm
  have hratio_mem : (y ^ p : Kˣ) ∈ localUnitSubgroupAt (R := 𝓞 K) (K := K) v := by
    rw [hy_pow]
    exact ratio.2
  rw [localUnitNormalization_of_mem (R := 𝓞 K) (K := K) v hratio_mem]
  exact hy_pow

/-- REF-12 localization to `U_lambda / U_lambda^p` is equivariant for the
cyclotomic action on singular classes and the restricted action on local
units. -/
theorem singularGroupLocalizationToCyclotomicLocalUnits_equivariant
    (a : CharacterProjection.Delta p)
    (x : SingularGroup (R := 𝓞 K) (K := K) p) :
    singularGroupLocalizationToCyclotomicLocalUnits (p := p) K
        (cyclotomicSingularGroupAction K p a x) =
      cyclotomicLocalUnitPowerQuotientEquiv (p := p) (K := K) a
        (singularGroupLocalizationToCyclotomicLocalUnits (p := p) K x) := by
  refine QuotientGroup.induction_on x ?_
  intro s
  change singularGroupLocalizationToCyclotomicLocalUnits (p := p) K
      (((cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).singularGroupEquiv p)
        (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p)) =
    cyclotomicLocalUnitPowerQuotientEquiv (p := p) (K := K) a
      (singularGroupLocalizationToCyclotomicLocalUnits (p := p) K
        (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p))
  rw [SingularPair.PrincipalIdealPreservingEquiv.singularGroupEquiv_mk]
  change fieldUnitToLocalUnitPowerQuotient (R := 𝓞 K) (K := K)
      (cyclotomicLambdaHeightOne (p := p) K) p
      (generator ((cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).singularPairEquiv
        p s)) =
    cyclotomicLocalUnitPowerQuotientEquiv (p := p) (K := K) a
      (fieldUnitToLocalUnitPowerQuotient (R := 𝓞 K) (K := K)
        (cyclotomicLambdaHeightOne (p := p) K) p (generator s))
  simpa [cyclotomicPrincipalIdealPreservingEquiv] using
    fieldUnitToCyclotomicLocalUnitPowerQuotient_equivariant_generator
      (p := p) (K := K) a s

set_option maxHeartbeats 800000 in
-- `QuotientGroup.lift` unfolds the cyclotomic local-unit quotient and the
-- completed principal-unit quotient; keep the larger budget local to this
-- descent.
/-- The induced bridge `U_lambda / U_lambda^p -> completed U_1 / completed U_1^p`. -/
noncomputable def cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP :
    (cyclotomicLocalUnitSubgroup (p := p) K ⧸
      cyclotomicLocalUnitPowerSubgroup (p := p) K) →*
      Local.completedPrincipalUnitModPQuotient p K :=
  QuotientGroup.lift
    (cyclotomicLocalUnitPowerSubgroup (p := p) K)
    (cyclotomicLocalUnitToCompletedPrincipalUnitModPHom p K)
    (by
      intro u hu
      obtain ⟨v, rfl⟩ := hu
      exact cyclotomicLocalUnitToCompletedPrincipalUnitModPHom_pow_eq_one
        (p := p) (K := K) v)

/-- The quotient bridge from REF-12 local units to completed principal units is
equivariant for the induced quotient actions. -/
theorem cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP_equivariant
    (a : CharacterProjection.Delta p)
    (x : cyclotomicLocalUnitPowerQuotient (p := p) K) :
    cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP p K
        (cyclotomicLocalUnitPowerQuotientEquiv (p := p) (K := K) a x) =
      Local.completedPrincipalUnitModPDeltaAction (p := p) K a
        (cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP p K x) := by
  refine QuotientGroup.induction_on x ?_
  intro u
  change cyclotomicLocalUnitToCompletedPrincipalUnitModPHom p K
      (cyclotomicLocalUnitSubgroupEquiv (p := p) (K := K) a u) =
    Local.completedPrincipalUnitModPDeltaAction (p := p) K a
      (cyclotomicLocalUnitToCompletedPrincipalUnitModPHom p K u)
  exact cyclotomicLocalUnitToCompletedPrincipalUnitModPHom_equivariant
    (p := p) (K := K) a u

/-- The completed-principal-unit localization map obtained by composing the
REF-12 localization with the concrete completion bridge. -/
noncomputable def singularGroupLocalizationToCompletedPrincipalUnits :
    SingularGroup (R := 𝓞 K) (K := K) p →*
      Local.completedPrincipalUnitModPQuotient p K :=
  (cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP p K).comp
    (singularGroupLocalizationToCyclotomicLocalUnits (p := p) K)

/-- If the REF-12 localization to `U_lambda / U_lambda^p` is equivariant for
the restricted local-unit quotient action, then the concrete completed
localization is equivariant. -/
theorem singularGroupLocalizationToCompletedPrincipalUnits_equivariant_of_cyclotomicLocalUnits
    (hloc : ∀ (a : CharacterProjection.Delta p)
        (x : SingularGroup (R := 𝓞 K) (K := K) p),
      singularGroupLocalizationToCyclotomicLocalUnits (p := p) K
          (cyclotomicSingularGroupAction K p a x) =
        cyclotomicLocalUnitPowerQuotientEquiv (p := p) (K := K) a
          (singularGroupLocalizationToCyclotomicLocalUnits (p := p) K x))
    (a : CharacterProjection.Delta p)
    (x : SingularGroup (R := 𝓞 K) (K := K) p) :
    singularGroupLocalizationToCompletedPrincipalUnits (p := p) K
        (cyclotomicSingularGroupAction K p a x) =
      Local.completedPrincipalUnitModPDeltaAction (p := p) K a
        (singularGroupLocalizationToCompletedPrincipalUnits (p := p) K x) := by
  change cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP p K
      (singularGroupLocalizationToCyclotomicLocalUnits (p := p) K
        (cyclotomicSingularGroupAction K p a x)) =
    Local.completedPrincipalUnitModPDeltaAction (p := p) K a
      (cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP p K
        (singularGroupLocalizationToCyclotomicLocalUnits (p := p) K x))
  rw [hloc]
  exact cyclotomicLocalUnitPowerQuotientToCompletedPrincipalUnitModP_equivariant
    (p := p) (K := K) a
    (singularGroupLocalizationToCyclotomicLocalUnits (p := p) K x)

/-- The concrete completed localization map is equivariant for the cyclotomic
action. -/
theorem singularGroupLocalizationToCompletedPrincipalUnits_equivariant
    (a : CharacterProjection.Delta p)
    (x : SingularGroup (R := 𝓞 K) (K := K) p) :
    singularGroupLocalizationToCompletedPrincipalUnits (p := p) K
        (cyclotomicSingularGroupAction K p a x) =
      Local.completedPrincipalUnitModPDeltaAction (p := p) K a
        (singularGroupLocalizationToCompletedPrincipalUnits (p := p) K x) :=
  singularGroupLocalizationToCompletedPrincipalUnits_equivariant_of_cyclotomicLocalUnits
    (p := p) (K := K)
    (singularGroupLocalizationToCyclotomicLocalUnits_equivariant (p := p) (K := K)) a x

set_option synthInstance.maxHeartbeats 80000 in
-- The completed quotient's `ZMod p` module is synthesized through additive
-- and quotient-group wrappers.
/-- Linear form of the concrete completed localization map. -/
noncomputable def singularGroupLocalizationToCompletedPrincipalUnitsLinear :
    Additive (SingularGroup (R := 𝓞 K) (K := K) p) →ₗ[ZMod p]
      Additive (Local.completedPrincipalUnitModPQuotient p K) :=
  (singularGroupLocalizationToCompletedPrincipalUnits (p := p) K).toAdditive.toZModLinearMap p

/-- Linear equivariance of the concrete completed localization, assuming the
REF-12 local-unit quotient equivariance statement. -/
theorem singularGroupLocalizationToCompletedPrincipalUnitsLinear_equivariant_of_cyclotomicLocalUnits
    (hloc : ∀ (a : CharacterProjection.Delta p)
        (x : SingularGroup (R := 𝓞 K) (K := K) p),
      singularGroupLocalizationToCyclotomicLocalUnits (p := p) K
          (cyclotomicSingularGroupAction K p a x) =
        cyclotomicLocalUnitPowerQuotientEquiv (p := p) (K := K) a
          (singularGroupLocalizationToCyclotomicLocalUnits (p := p) K x))
    (a : CharacterProjection.Delta p)
    (x : Additive (SingularGroup (R := 𝓞 K) (K := K) p)) :
    singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
        (SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
          (cyclotomicSingularGroupAction K p) a x) =
      Local.completedPrincipalUnitModPDeltaActionZMod (p := p) K a
        (singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K x) := by
  apply Additive.ext
  change singularGroupLocalizationToCompletedPrincipalUnits (p := p) K
      (cyclotomicSingularGroupAction K p a x.toMul) =
    Local.completedPrincipalUnitModPDeltaAction (p := p) K a
      (singularGroupLocalizationToCompletedPrincipalUnits (p := p) K x.toMul)
  exact singularGroupLocalizationToCompletedPrincipalUnits_equivariant_of_cyclotomicLocalUnits
    (p := p) (K := K) hloc a x.toMul

/-- Linear equivariance of the concrete completed localization. -/
theorem singularGroupLocalizationToCompletedPrincipalUnitsLinear_equivariant
    (a : CharacterProjection.Delta p)
    (x : Additive (SingularGroup (R := 𝓞 K) (K := K) p)) :
    singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K
        (SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
          (cyclotomicSingularGroupAction K p) a x) =
      Local.completedPrincipalUnitModPDeltaActionZMod (p := p) K a
        (singularGroupLocalizationToCompletedPrincipalUnitsLinear (p := p) K x) :=
  singularGroupLocalizationToCompletedPrincipalUnitsLinear_equivariant_of_cyclotomicLocalUnits
    (p := p) (K := K)
    (singularGroupLocalizationToCyclotomicLocalUnits_equivariant (p := p) (K := K)) a x

end SingularPair
end SingularKummer
end Reflection
end BernoulliRegular

end

end
