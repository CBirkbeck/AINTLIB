module

public import BernoulliRegular.Reflection.SingularKummer.Equivariance
public import BernoulliRegular.Reflection.SingularKummer.DimensionLowerBound
public import BernoulliRegular.Reflection.SingularKummer.CharacterProjectionIdempotent
public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelCharacterLift
public import BernoulliRegular.UnitQuotient.DeltaAction

/-!
# Singular Kummer: cyclotomic actions on `S` and `A[p]`

This file instantiates the abstract `PrincipalIdealPreservingEquiv` package for
the actual cyclotomic `Delta = (ZMod p)ˣ` action on `K = Q(ζ_p)`.  The output
is a concrete `Delta`-action on the singular quotient `S` and on the torsion
target `A[p]`, together with the corresponding equivariance of the map

```text
E/E^p -> S -> A[p].
```
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension Pointwise
open scoped NumberField nonZeroDivisors

namespace BernoulliRegular
namespace Reflection
namespace SingularKummer

set_option linter.unusedSectionVars false

namespace SingularPair

variable (K : Type*) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} ℚ K]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

noncomputable abbrev cyclotomicRingOfIntegersAuto
    (a : CharacterProjection.Delta p) : 𝓞 K ≃+* 𝓞 K :=
  cyclotomicRingOfIntegersEquiv (p := p) K a

theorem cyclotomicRingOfIntegersAuto_le_comap_nonZeroDivisors
    (a : CharacterProjection.Delta p) :
    (𝓞 K)⁰ ≤
      Submonoid.comap ((cyclotomicRingOfIntegersAuto (K := K) (p := p) a).toRingHom)
        (𝓞 K)⁰ :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (cyclotomicRingOfIntegersAuto (K := K) (p := p) a).injective

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm in
noncomputable def cyclotomicFieldSemilinearEquiv
    (a : CharacterProjection.Delta p) :
  K ≃ₛₗ[RingHomClass.toRingHom (cyclotomicRingOfIntegersAuto (K := K) (p := p) a)] K where
  toFun := cyclotomicSigmaOfUnit (p := p) K a
  invFun := (cyclotomicSigmaOfUnit (p := p) K a).symm
  left_inv := fun x => (cyclotomicSigmaOfUnit (p := p) K a).left_inv x
  right_inv := fun x => (cyclotomicSigmaOfUnit (p := p) K a).right_inv x
  map_add' := fun x y => map_add _ x y
  map_smul' := fun r x => by
    change cyclotomicSigmaOfUnit (p := p) K a ((r : K) * x) =
      (((cyclotomicRingOfIntegersAuto (K := K) (p := p) a) r : 𝓞 K) : K) *
        cyclotomicSigmaOfUnit (p := p) K a x
    rw [map_mul]
    congr 1

theorem cyclotomicFieldSemilinearEquiv_eq_map
    (a : CharacterProjection.Delta p) :
    (cyclotomicSigmaOfUnit (p := p) K a).toRingHom =
      IsLocalization.map K
        ((cyclotomicRingOfIntegersAuto (K := K) (p := p) a).toRingHom)
        (cyclotomicRingOfIntegersAuto_le_comap_nonZeroDivisors
          (K := K) (p := p) a) := by
  apply (IsFractionRing.ringHom_ext (A := 𝓞 K) (K := K))
  intro r
  rw [IsLocalization.map_eq]
  exact
    (RingOfIntegers.mapRingEquiv_apply
      ((cyclotomicSigmaOfUnit (p := p) K a).toRingEquiv) r).symm

theorem cyclotomicRingOfIntegersAuto_symm_le_comap_nonZeroDivisors
    (a : CharacterProjection.Delta p) :
    (𝓞 K)⁰ ≤
      Submonoid.comap ((cyclotomicRingOfIntegersAuto (K := K) (p := p) a).symm.toRingHom)
        (𝓞 K)⁰ :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _
    (cyclotomicRingOfIntegersAuto (K := K) (p := p) a).symm.injective

theorem cyclotomicFieldSemilinearEquiv_symm_eq_map
    (a : CharacterProjection.Delta p) :
    (cyclotomicSigmaOfUnit (p := p) K a).symm.toRingHom =
      IsLocalization.map K
        ((cyclotomicRingOfIntegersAuto (K := K) (p := p) a).symm.toRingHom)
        (cyclotomicRingOfIntegersAuto_symm_le_comap_nonZeroDivisors
          (K := K) (p := p) a) := by
  apply (IsFractionRing.ringHom_ext (A := 𝓞 K) (K := K))
  intro r
  rw [IsLocalization.map_eq]
  exact
    (RingOfIntegers.mapRingEquiv_symm_apply
      ((cyclotomicSigmaOfUnit (p := p) K a).toRingEquiv) r).symm

noncomputable def cyclotomicFractionalIdealHom
    (a : CharacterProjection.Delta p) :
    FractionalIdeal (𝓞 K)⁰ K →+* FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.extendedHom' K
    (cyclotomicRingOfIntegersAuto_le_comap_nonZeroDivisors (K := K) (p := p) a)

noncomputable def cyclotomicFractionalIdealInvHom
    (a : CharacterProjection.Delta p) :
    FractionalIdeal (𝓞 K)⁰ K →+* FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.extendedHom' K
    (cyclotomicRingOfIntegersAuto_symm_le_comap_nonZeroDivisors (K := K) (p := p) a)

theorem cyclotomicFractionalIdealHom_coe
    (a : CharacterProjection.Delta p) (I : FractionalIdeal (𝓞 K)⁰ K) :
    ((cyclotomicFractionalIdealHom (K := K) (p := p) a) I : Submodule (𝓞 K) K) =
      Submodule.map (cyclotomicFieldSemilinearEquiv K p a).toLinearMap
        (I : Submodule (𝓞 K) K) := by
  rw [cyclotomicFractionalIdealHom, FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.coe_extended_eq_span]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, rfl⟩
    have hmap : cyclotomicFieldSemilinearEquiv K p a x =
        IsLocalization.map K
          ((cyclotomicRingOfIntegersAuto (K := K) (p := p) a).toRingHom)
          (cyclotomicRingOfIntegersAuto_le_comap_nonZeroDivisors (K := K) (p := p) a) x :=
      congrArg (fun f : K →+* K => f x)
        (cyclotomicFieldSemilinearEquiv_eq_map (K := K) (p := p) a)
    exact Submodule.mem_map.mpr ⟨x, hx, hmap⟩
  · rintro y ⟨x, hx, rfl⟩
    have hmap : cyclotomicFieldSemilinearEquiv K p a x =
        IsLocalization.map K
          ((cyclotomicRingOfIntegersAuto (K := K) (p := p) a).toRingHom)
          (cyclotomicRingOfIntegersAuto_le_comap_nonZeroDivisors (K := K) (p := p) a) x :=
      congrArg (fun f : K →+* K => f x)
        (cyclotomicFieldSemilinearEquiv_eq_map (K := K) (p := p) a)
    exact Submodule.subset_span ⟨x, hx, hmap.symm⟩

theorem cyclotomicFractionalIdealInvHom_coe
    (a : CharacterProjection.Delta p) (I : FractionalIdeal (𝓞 K)⁰ K) :
    ((cyclotomicFractionalIdealInvHom (K := K) (p := p) a) I : Submodule (𝓞 K) K) =
      Submodule.map (cyclotomicFieldSemilinearEquiv K p a).symm.toLinearMap
        (I : Submodule (𝓞 K) K) := by
  rw [cyclotomicFractionalIdealInvHom, FractionalIdeal.extendedHom'_apply,
    FractionalIdeal.coe_extended_eq_span]
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, rfl⟩
    have hmap : (cyclotomicFieldSemilinearEquiv K p a).symm x =
        IsLocalization.map K
          ((cyclotomicRingOfIntegersAuto (K := K) (p := p) a).symm.toRingHom)
          (cyclotomicRingOfIntegersAuto_symm_le_comap_nonZeroDivisors (K := K) (p := p) a) x :=
      congrArg (fun f : K →+* K => f x)
        (cyclotomicFieldSemilinearEquiv_symm_eq_map (K := K) (p := p) a)
    exact Submodule.mem_map.mpr ⟨x, hx, hmap⟩
  · rintro y ⟨x, hx, rfl⟩
    have hmap : (cyclotomicFieldSemilinearEquiv K p a).symm x =
        IsLocalization.map K
          ((cyclotomicRingOfIntegersAuto (K := K) (p := p) a).symm.toRingHom)
          (cyclotomicRingOfIntegersAuto_symm_le_comap_nonZeroDivisors (K := K) (p := p) a) x :=
      congrArg (fun f : K →+* K => f x)
        (cyclotomicFieldSemilinearEquiv_symm_eq_map (K := K) (p := p) a)
    exact Submodule.subset_span ⟨x, hx, hmap.symm⟩

theorem cyclotomicFractionalIdealInvHom_apply_apply
    (a : CharacterProjection.Delta p) (I : FractionalIdeal (𝓞 K)⁰ K) :
    cyclotomicFractionalIdealInvHom (K := K) (p := p) a
      ((cyclotomicFractionalIdealHom (K := K) (p := p) a) I) = I := by
  apply FractionalIdeal.coeToSubmodule_injective
  change
    (((cyclotomicFractionalIdealInvHom (K := K) (p := p) a)
        ((cyclotomicFractionalIdealHom (K := K) (p := p) a) I)) : Submodule (𝓞 K) K) =
      (I : Submodule (𝓞 K) K)
  rw [cyclotomicFractionalIdealInvHom_coe (K := K) (p := p),
    cyclotomicFractionalIdealHom_coe (K := K) (p := p)]
  rw [← Submodule.map_comp]
  change Submodule.map
      ((cyclotomicFieldSemilinearEquiv K p a).symm.toLinearMap.comp
        (cyclotomicFieldSemilinearEquiv K p a).toLinearMap)
      (I : Submodule (𝓞 K) K) = I
  have hcomp :
      (cyclotomicFieldSemilinearEquiv K p a).symm.toLinearMap.comp
        (cyclotomicFieldSemilinearEquiv K p a).toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [hcomp, Submodule.map_id]

theorem cyclotomicFractionalIdealHom_inv_apply_apply
    (a : CharacterProjection.Delta p) (I : FractionalIdeal (𝓞 K)⁰ K) :
    cyclotomicFractionalIdealHom (K := K) (p := p) a
      ((cyclotomicFractionalIdealInvHom (K := K) (p := p) a) I) = I := by
  apply FractionalIdeal.coeToSubmodule_injective
  change
    (((cyclotomicFractionalIdealHom (K := K) (p := p) a)
        ((cyclotomicFractionalIdealInvHom (K := K) (p := p) a) I)) : Submodule (𝓞 K) K) =
      (I : Submodule (𝓞 K) K)
  rw [cyclotomicFractionalIdealHom_coe (K := K) (p := p),
    cyclotomicFractionalIdealInvHom_coe (K := K) (p := p)]
  rw [← Submodule.map_comp]
  change Submodule.map
      ((cyclotomicFieldSemilinearEquiv K p a).toLinearMap.comp
        (cyclotomicFieldSemilinearEquiv K p a).symm.toLinearMap)
      (I : Submodule (𝓞 K) K) = I
  have hcomp :
      (cyclotomicFieldSemilinearEquiv K p a).toLinearMap.comp
        (cyclotomicFieldSemilinearEquiv K p a).symm.toLinearMap = LinearMap.id := by
    ext x
    simp
  rw [hcomp, Submodule.map_id]

/-- The cyclotomic Galois action on `Kˣ`. -/
noncomputable def cyclotomicFieldUnitEquiv (a : CharacterProjection.Delta p) :
    Kˣ ≃* Kˣ :=
  Units.mapEquiv ((cyclotomicSigmaOfUnit (p := p) K a).toRingEquiv.toMulEquiv)

@[simp]
theorem cyclotomicFieldUnitEquiv_one_apply (u : Kˣ) :
    cyclotomicFieldUnitEquiv K p 1 u = u := by
  apply Units.ext
  change cyclotomicSigmaOfUnit (p := p) K 1 (u : K) = u
  simp [cyclotomicSigmaOfUnit_one]

@[simp]
theorem cyclotomicFieldUnitEquiv_mul_apply
    (a b : CharacterProjection.Delta p) (u : Kˣ) :
    cyclotomicFieldUnitEquiv K p (a * b) u =
      cyclotomicFieldUnitEquiv K p a (cyclotomicFieldUnitEquiv K p b u) := by
  apply Units.ext
  change cyclotomicSigmaOfUnit (p := p) K (a * b) (u : K) =
    cyclotomicSigmaOfUnit (p := p) K a
      (cyclotomicSigmaOfUnit (p := p) K b (u : K))
  simp [cyclotomicSigmaOfUnit_mul]

/-- The cyclotomic Galois action on fractional ideals of `O_K`. -/
noncomputable def cyclotomicFractionalIdealEquiv
    (a : CharacterProjection.Delta p) :
    (FractionalIdeal (𝓞 K)⁰ K)ˣ ≃* (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  { toFun := fun I => Units.map (cyclotomicFractionalIdealHom K p a) I
    invFun := fun I => Units.map (cyclotomicFractionalIdealInvHom K p a) I
    left_inv := fun I => by
      exact Units.ext <|
        cyclotomicFractionalIdealInvHom_apply_apply K p a
          (I : FractionalIdeal (𝓞 K)⁰ K)
    right_inv := fun I => by
      exact Units.ext <|
        cyclotomicFractionalIdealHom_inv_apply_apply K p a
          (I : FractionalIdeal (𝓞 K)⁰ K)
    map_mul' := fun I J => by
      apply Units.ext
      simp [cyclotomicFractionalIdealHom] }

@[simp]
theorem cyclotomicFractionalIdealEquiv_one_apply
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    cyclotomicFractionalIdealEquiv K p 1 I = I := by
  apply Units.ext
  apply FractionalIdeal.coeToSubmodule_injective
  change
    (((cyclotomicFractionalIdealHom K p 1) (I : FractionalIdeal (𝓞 K)⁰ K)) : Submodule (𝓞 K) K) =
      (I : Submodule (𝓞 K) K)
  rw [cyclotomicFractionalIdealHom_coe]
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change cyclotomicSigmaOfUnit (p := p) K 1 x ∈ (I : Submodule (𝓞 K) K)
    rw [cyclotomicSigmaOfUnit_one]
    exact hx
  · intro y hy
    refine Submodule.mem_map.mpr ⟨y, hy, ?_⟩
    change cyclotomicSigmaOfUnit (p := p) K 1 y = y
    simp

@[simp]
theorem cyclotomicFractionalIdealEquiv_mul_apply
    (a b : CharacterProjection.Delta p) (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    cyclotomicFractionalIdealEquiv K p (a * b) I =
      cyclotomicFractionalIdealEquiv K p a
        (cyclotomicFractionalIdealEquiv K p b I) := by
  apply Units.ext
  apply FractionalIdeal.coeToSubmodule_injective
  change
    (((cyclotomicFractionalIdealHom K p (a * b)) (I : FractionalIdeal (𝓞 K)⁰ K)) :
        Submodule (𝓞 K) K) =
      (((cyclotomicFractionalIdealHom K p a)
          ((cyclotomicFractionalIdealHom K p b) (I : FractionalIdeal (𝓞 K)⁰ K))) :
        Submodule (𝓞 K) K)
  rw [cyclotomicFractionalIdealHom_coe, cyclotomicFractionalIdealHom_coe,
    cyclotomicFractionalIdealHom_coe]
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact Submodule.mem_map.mpr ⟨cyclotomicSigmaOfUnit (p := p) K b x,
      Submodule.mem_map.mpr ⟨x, hx, by rfl⟩, by
        change cyclotomicSigmaOfUnit (p := p) K a (cyclotomicSigmaOfUnit (p := p) K b x) =
          cyclotomicFieldSemilinearEquiv K p (a * b) x
        change cyclotomicSigmaOfUnit (p := p) K a (cyclotomicSigmaOfUnit (p := p) K b x) =
          cyclotomicSigmaOfUnit (p := p) K (a * b) x
        rw [cyclotomicSigmaOfUnit_mul]
        rfl⟩
  · rintro y ⟨x, hx, rfl⟩
    rcases Submodule.mem_map.mp hx with ⟨z, hz, rfl⟩
    exact Submodule.mem_map.mpr ⟨z, hz, by
      change cyclotomicSigmaOfUnit (p := p) K (a * b) z =
        cyclotomicSigmaOfUnit (p := p) K a (cyclotomicSigmaOfUnit (p := p) K b z)
      rw [cyclotomicSigmaOfUnit_mul]
      rfl⟩

@[simp]
theorem cyclotomicFractionalIdealEquiv_toPrincipalIdeal
    (a : CharacterProjection.Delta p) (gamma : Kˣ) :
    cyclotomicFractionalIdealEquiv K p a
        (toPrincipalIdeal (𝓞 K) K gamma) =
      toPrincipalIdeal (𝓞 K) K (cyclotomicFieldUnitEquiv K p a gamma) := by
  apply Units.ext
  apply FractionalIdeal.coeToSubmodule_injective
  change
    (((cyclotomicFractionalIdealHom K p a)
        ((toPrincipalIdeal (𝓞 K) K gamma : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K)) : Submodule (𝓞 K) K) =
      ((((toPrincipalIdeal (𝓞 K) K (cyclotomicFieldUnitEquiv K p a gamma) :
            (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K)) :
        Submodule (𝓞 K) K)
  rw [cyclotomicFractionalIdealHom_coe, coe_toPrincipalIdeal, coe_toPrincipalIdeal]
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    rcases (FractionalIdeal.mem_spanSingleton _).mp hx with ⟨r, rfl⟩
    refine (FractionalIdeal.mem_spanSingleton _).mpr ?_
    refine ⟨cyclotomicRingOfIntegersAuto (K := K) (p := p) a r, ?_⟩
    exact ((cyclotomicFieldSemilinearEquiv K p a).map_smulₛₗ r (gamma : K)).symm
  · intro y hy
    rcases (FractionalIdeal.mem_spanSingleton _).mp hy with ⟨r, rfl⟩
    refine Submodule.mem_map.mpr ?_
    refine ⟨(cyclotomicRingOfIntegersAuto (K := K) (p := p) a).symm r • (gamma : K), ?_, ?_⟩
    · exact (FractionalIdeal.mem_spanSingleton _).mpr ⟨
        (cyclotomicRingOfIntegersAuto (K := K) (p := p) a).symm r, rfl⟩
    · exact ((cyclotomicFieldSemilinearEquiv K p a).map_smulₛₗ
          ((cyclotomicRingOfIntegersAuto (K := K) (p := p) a).symm r) (gamma : K)).trans <|
        by
          congr 1
          exact (cyclotomicRingOfIntegersAuto (K := K) (p := p) a).apply_symm_apply r

/-- The cyclotomic action as a `PrincipalIdealPreservingEquiv`. -/
noncomputable def cyclotomicPrincipalIdealPreservingEquiv
    (a : CharacterProjection.Delta p) :
    PrincipalIdealPreservingEquiv (𝓞 K) K where
  idealEquiv := cyclotomicFractionalIdealEquiv K p a
  unitEquiv := cyclotomicFieldUnitEquiv K p a
  map_principal := cyclotomicFractionalIdealEquiv_toPrincipalIdeal K p a

/-- The actual cyclotomic `Delta`-action on the singular quotient `S`. -/
noncomputable def cyclotomicSingularGroupAction :
    CharacterProjection.Delta p →*
      SingularGroup (R := 𝓞 K) (K := K) p ≃*
        SingularGroup (R := 𝓞 K) (K := K) p where
  toFun a :=
    (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).singularGroupEquiv p
  map_one' := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro s
    rw [SingularPair.PrincipalIdealPreservingEquiv.singularGroupEquiv_mk]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · change cyclotomicFractionalIdealEquiv K p 1 (ideal s) = ideal s
      exact cyclotomicFractionalIdealEquiv_one_apply K p (ideal s)
    · change cyclotomicFieldUnitEquiv K p 1 (generator s) = generator s
      exact cyclotomicFieldUnitEquiv_one_apply K p (generator s)
  map_mul' a b := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro s
    let equivA := cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a
    let equivB := cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) b
    let equivAB := cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) (a * b)
    rw [SingularPair.PrincipalIdealPreservingEquiv.singularGroupEquiv_mk]
    change
      (QuotientGroup.mk
          (equivAB.singularPairEquiv p s) :
        SingularGroup (R := 𝓞 K) (K := K) p) =
        equivA.singularGroupEquiv p
          (equivB.singularGroupEquiv p
            (QuotientGroup.mk s : SingularGroup (R := 𝓞 K) (K := K) p))
    rw [SingularPair.PrincipalIdealPreservingEquiv.singularGroupEquiv_mk,
      SingularPair.PrincipalIdealPreservingEquiv.singularGroupEquiv_mk]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · change
        cyclotomicFractionalIdealEquiv K p (a * b) (ideal s) =
          cyclotomicFractionalIdealEquiv K p a (cyclotomicFractionalIdealEquiv K p b (ideal s))
      exact cyclotomicFractionalIdealEquiv_mul_apply K p a b (ideal s)
    · change
        cyclotomicFieldUnitEquiv K p (a * b) (generator s) =
          cyclotomicFieldUnitEquiv K p a (cyclotomicFieldUnitEquiv K p b (generator s))
      exact cyclotomicFieldUnitEquiv_mul_apply K p a b (generator s)

/-- The actual cyclotomic `Delta`-action on the torsion target `A[p]`. -/
noncomputable def cyclotomicClassGroupPTorsionAction :
    CharacterProjection.Delta p →*
      classGroupPTorsion (R := 𝓞 K) p ≃*
        classGroupPTorsion (R := 𝓞 K) p where
  toFun a :=
    (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).classGroupPTorsionEquiv p
  map_one' := by
    ext x
    change
      (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) 1).classGroupEquiv
        (x : ClassGroup (𝓞 K)) = x
    let y := (ClassGroup.equiv (R := 𝓞 K) K) x.1
    obtain ⟨I, hI⟩ := QuotientGroup.mk_surjective y
    have hx : x.1 = ClassGroup.mk (R := 𝓞 K) (K := K) I := by
      apply (ClassGroup.equiv (R := 𝓞 K) K).injective
      change y =
        (ClassGroup.equiv (R := 𝓞 K) K) (ClassGroup.mk (R := 𝓞 K) (K := K) I)
      rw [ClassGroup.equiv_mk]
      simp only [FractionalIdeal.canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl,
        QuotientGroup.mk'_apply] at hI ⊢
      exact hI.symm
    rw [hx, SingularPair.PrincipalIdealPreservingEquiv.classGroupEquiv_mk]
    exact congrArg (ClassGroup.mk (R := 𝓞 K) (K := K))
      (cyclotomicFractionalIdealEquiv_one_apply K p I)
  map_mul' a b := by
    ext x
    change
      (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) (a * b)).classGroupEquiv
        (x : ClassGroup (𝓞 K)) =
          (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).classGroupEquiv
            ((cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) b).classGroupEquiv
              (x : ClassGroup (𝓞 K)))
    let y := (ClassGroup.equiv (R := 𝓞 K) K) x.1
    obtain ⟨I, hI⟩ := QuotientGroup.mk_surjective y
    have hx : x.1 = ClassGroup.mk (R := 𝓞 K) (K := K) I := by
      apply (ClassGroup.equiv (R := 𝓞 K) K).injective
      change y =
        (ClassGroup.equiv (R := 𝓞 K) K) (ClassGroup.mk (R := 𝓞 K) (K := K) I)
      rw [ClassGroup.equiv_mk]
      simp only [FractionalIdeal.canonicalEquiv_self, RingEquiv.coe_mulEquiv_refl,
        QuotientGroup.mk'_apply] at hI ⊢
      exact hI.symm
    rw [hx, SingularPair.PrincipalIdealPreservingEquiv.classGroupEquiv_mk,
      SingularPair.PrincipalIdealPreservingEquiv.classGroupEquiv_mk,
      SingularPair.PrincipalIdealPreservingEquiv.classGroupEquiv_mk]
    exact congrArg (ClassGroup.mk (R := 𝓞 K) (K := K))
      (cyclotomicFractionalIdealEquiv_mul_apply K p a b I)

/-- The singular exact-sequence map is equivariant for the actual cyclotomic
`Delta`-actions. -/
theorem cyclotomicSingularGroupClassMapToPTorsion_equivariant
    (a : CharacterProjection.Delta p)
    (x : SingularGroup (R := 𝓞 K) (K := K) p) :
    cyclotomicClassGroupPTorsionAction K p a
        (singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p x) =
      singularGroupClassMapToPTorsion (R := 𝓞 K) (K := K) p
        (cyclotomicSingularGroupAction K p a x) := by
  unfold cyclotomicSingularGroupAction cyclotomicClassGroupPTorsionAction
  exact
    PrincipalIdealPreservingEquiv.singularGroupClassMapToPTorsion_equivariant
      (A := cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a) p x

@[simp]
theorem cyclotomicFractionalUnitEquiv_globalUnitToFractionalUnit
    (a : CharacterProjection.Delta p) (u : CyclotomicUnitGroup K) :
    (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).fractionalUnitEquiv
        (globalUnitToFractionalUnit K u) =
      globalUnitToFractionalUnit K (cyclotomicUnitEquiv (p := p) K a u) := by
  apply Subtype.ext
  apply Units.ext
  rw [SingularPair.PrincipalIdealPreservingEquiv.fractionalUnitEquiv_apply_coe,
    globalUnitToFractionalUnit_apply_val, globalUnitToFractionalUnit_apply_val]
  change
    cyclotomicSigmaOfUnit (p := p) K a (algebraMap (𝓞 K) K (u : 𝓞 K)) =
      algebraMap (𝓞 K) K ((cyclotomicUnitEquiv (p := p) K a u : CyclotomicUnitGroup K) : 𝓞 K)
  exact (cyclotomicUnitEquiv_coe (p := p) (K := K) a u).symm

theorem globalUnitPowerQuotientToSingularGroup_equivariant
    (a : CharacterProjection.Delta p)
    (x : CyclotomicUnitPowerQuotient (p := p) (N := 1) K) :
    globalUnitPowerQuotientToSingularGroup K p
        ((cyclotomicUnitModPDeltaAction (p := p) K).act a x) =
      cyclotomicSingularGroupAction K p a
        (globalUnitPowerQuotientToSingularGroup K p x) := by
  refine QuotientGroup.induction_on x ?_
  intro u
  change
    globalUnitPowerQuotientToSingularGroup K p
        ((cyclotomicUnitModPDeltaAction (p := p) K).act a
          (cyclotomicUnitPowerClass (p := p) (N := 1) K u)) =
      cyclotomicSingularGroupAction K p a
        (globalUnitPowerQuotientToSingularGroup K p
          (cyclotomicUnitPowerClass (p := p) (N := 1) K u))
  rw [cyclotomicUnitPowerQuotientDeltaAction_act_mk,
    globalUnitPowerQuotientToSingularGroup_mk,
    globalUnitPowerQuotientToSingularGroup_mk]
  change
    unitToSingularGroup (R := 𝓞 K) (K := K) p
        (globalUnitToFractionalUnit K (cyclotomicUnitEquiv (p := p) K a u)) =
      (cyclotomicPrincipalIdealPreservingEquiv (K := K) (p := p) a).singularGroupEquiv p
        (unitToSingularGroup (R := 𝓞 K) (K := K) p (globalUnitToFractionalUnit K u))
  rw [SingularPair.PrincipalIdealPreservingEquiv.unitToSingularGroup_equivariant,
    cyclotomicFractionalUnitEquiv_globalUnitToFractionalUnit]

theorem globalUnitPowerQuotientToSingularGroupLinear_equivariant
    (a : CharacterProjection.Delta p)
    (x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)) :
    globalUnitPowerQuotientToSingularGroupLinear K p
        (cyclotomicUnitPowerQuotientDeltaActionZMod (p := p) K a x) =
      SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
          (cyclotomicSingularGroupAction K p) a
        (globalUnitPowerQuotientToSingularGroupLinear K p x) := by
  apply Additive.ext
  change
    globalUnitPowerQuotientToSingularGroup K p
        ((cyclotomicUnitModPDeltaAction (p := p) K).act a x.toMul) =
      cyclotomicSingularGroupAction K p a
        (globalUnitPowerQuotientToSingularGroup K p x.toMul)
  exact globalUnitPowerQuotientToSingularGroup_equivariant K p a x.toMul

theorem globalUnitPowerQuotientToSingularGroupLinear_mem_characterProjectionComponent
    [NeZero p] {i : ℕ}
    {x : Additive (CyclotomicUnitPowerQuotient (p := p) (N := 1) K)}
    (hx : x ∈ cyclotomicUnitPowerQuotientDeltaCharacterEigenspace (p := p) K
      (cyclotomicUnitDeltaPowerCharacter (p := p) i)) :
    globalUnitPowerQuotientToSingularGroupLinear K p x ∈
      singularGroupCharacterProjectionComponent (K := K) (p := p) i
        (cyclotomicSingularGroupAction K p) := by
  refine CharacterProjection.mem_characterProjection_range_of_forall_apply_eq_smul
    (p := p) (FiniteLevelCharacterLift.isUnit_card_delta_zmod (p := p)) i
    (SingularLinearAction.mulActionToAdditiveLinearAction (p := p)
      (cyclotomicSingularGroupAction K p)) ?_
  intro a
  rw [← globalUnitPowerQuotientToSingularGroupLinear_equivariant (K := K) (p := p) a x,
    hx a, map_smul, cyclotomicUnitDeltaPowerCharacter_apply]

/-- REF-08c: the concrete cyclotomic `S_j` component has dimension at least two
once the matching `A[p]_j` component is nonzero. -/
theorem cyclotomicSingularGroupCharacterProjectionComponent_finrank_ge_two_of_even_power_character
    [NeZero p] (hp_gt_two : 2 < p) {j : ℕ}
    (hj_even : Even j) (hj_low : 2 ≤ j) (hj_high : j ≤ p - 3)
    [Module.Finite (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) j
        (cyclotomicSingularGroupAction K p))]
    (hA_ne_bot :
      classGroupPTorsionCharacterProjectionComponent (K := K) (p := p) j
        (cyclotomicClassGroupPTorsionAction K p) ≠ ⊥) :
    2 ≤ Module.finrank (ZMod p)
      (singularGroupCharacterProjectionComponent (K := K) (p := p) j
        (cyclotomicSingularGroupAction K p)) := by
  apply singularGroupCharacterProjectionComponent_finrank_ge_two_of_even_power_character
    (K := K) (p := p) hp_gt_two hj_even hj_low hj_high
    (ρS := cyclotomicSingularGroupAction K p)
    (ρA := cyclotomicClassGroupPTorsionAction K p)
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact globalUnitPowerQuotientToSingularGroupLinear_mem_characterProjectionComponent
      (K := K) (p := p) (i := j) hx
  · intro d x
    exact (cyclotomicSingularGroupClassMapToPTorsion_equivariant K p d x).symm
  · exact hA_ne_bot

end SingularPair

end SingularKummer
end Reflection
end BernoulliRegular

end
