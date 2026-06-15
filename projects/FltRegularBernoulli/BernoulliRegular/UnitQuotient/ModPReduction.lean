module

public import BernoulliRegular.UnitQuotient.PermutationCharacters
public import BernoulliRegular.UnitQuotient.TorsionCharacter
public import Mathlib.LinearAlgebra.FreeModule.ModN

/-!
# Unit quotients: reduction of the free quotient modulo `p`

This file proves the formal reduction step used in `REF-07c4`.

There is no natural map in the direction

```text
E/E_tors -> E/E^p,
```

because torsion units can have nontrivial image modulo `p`-th powers.  The
canonical map goes the other way after removing the torsion contribution:

```text
E/E^p -> (E/E_tors) / p.
```

It is obtained by sending a unit to its class in the Dirichlet free quotient
and then reducing that additive quotient modulo `p`.  The map kills `p`-th
powers, contains the torsion image in its kernel, and is equivariant for the
actual cyclotomic `Delta = (ZMod p)^*` action.
-/

@[expose] public section

noncomputable section

open NumberField IsCyclotomicExtension
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (p : ℕ) [Fact p.Prime]
variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

/-- The subgroup `p * (E/E_tors)` inside the additive Dirichlet free quotient. -/
abbrev CyclotomicUnitFreePartPMultipleSubmodule :
    Submodule ℤ (CyclotomicUnitFreePart K) :=
  LinearMap.range (LinearMap.lsmul ℤ (CyclotomicUnitFreePart K) p)

/-- The mod-`p` reduction of the additive Dirichlet free quotient. -/
abbrev CyclotomicUnitFreePartModP : Type _ :=
  ModN (CyclotomicUnitFreePart K) p

/-- The quotient map `(E/E_tors) -> (E/E_tors)/p`. -/
abbrev cyclotomicUnitFreePartModPClass :
    CyclotomicUnitFreePart K →+ CyclotomicUnitFreePartModP (p := p) K :=
  ModN.mkQ p

/-- The free quotient map, with the multiplicative unit group written
additively. -/
def cyclotomicUnitFreeClassAdd :
    Additive (CyclotomicUnitGroup K) →+ CyclotomicUnitFreePart K :=
  (cyclotomicUnitFreeClass K).toAdditive

@[simp]
theorem cyclotomicUnitFreeClassAdd_apply (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreeClassAdd K (Additive.ofMul u) =
      Additive.ofMul (cyclotomicUnitFreeClass K u) :=
  rfl

/-- Units mapped to the free quotient and then reduced modulo `p`. -/
def cyclotomicUnitToFreePartModPAdd :
    Additive (CyclotomicUnitGroup K) →+ CyclotomicUnitFreePartModP (p := p) K :=
  (cyclotomicUnitFreePartModPClass (p := p) K).comp
    (cyclotomicUnitFreeClassAdd K)

@[simp]
theorem cyclotomicUnitToFreePartModPAdd_apply (u : CyclotomicUnitGroup K) :
    cyclotomicUnitToFreePartModPAdd (p := p) K (Additive.ofMul u) =
      cyclotomicUnitFreePartModPClass (p := p) K
        (Additive.ofMul (cyclotomicUnitFreeClass K u)) :=
  rfl

/-- Multiplicative form of the map from units to the mod-`p` free quotient. -/
def cyclotomicUnitToFreePartModPMul :
    CyclotomicUnitGroup K →*
      Multiplicative (CyclotomicUnitFreePartModP (p := p) K) :=
  AddMonoidHom.toMultiplicativeRight
    (cyclotomicUnitToFreePartModPAdd (p := p) K)

@[simp]
theorem cyclotomicUnitToFreePartModPMul_apply (u : CyclotomicUnitGroup K) :
    cyclotomicUnitToFreePartModPMul (p := p) K u =
      Multiplicative.ofAdd
        (cyclotomicUnitFreePartModPClass (p := p) K
          (Additive.ofMul (cyclotomicUnitFreeClass K u))) :=
  rfl

/-- The map to the reduced free quotient kills `p`-th powers. -/
theorem cyclotomicUnitToFreePartModPMul_pow_eq_one
    (u : CyclotomicUnitGroup K) :
    cyclotomicUnitToFreePartModPMul (p := p) K (u ^ p) = 1 := by
  apply Multiplicative.ext
  change cyclotomicUnitFreePartModPClass (p := p) K
      (Additive.ofMul (cyclotomicUnitFreeClass K (u ^ p))) = 0
  rw [map_pow, ofMul_pow]
  change ModN.mkQ p (p • Additive.ofMul (cyclotomicUnitFreeClass K u)) = 0
  change (Submodule.Quotient.mk (p • Additive.ofMul (cyclotomicUnitFreeClass K u)) :
      CyclotomicUnitFreePartModP (p := p) K) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨Additive.ofMul (cyclotomicUnitFreeClass K u), by simp [LinearMap.lsmul_apply]⟩

/-- The canonical map `E/E^p -> (E/E_tors)/p`. -/
def cyclotomicUnitPowerQuotientToFreePartModP :
    CyclotomicUnitPowerQuotient (p := p) (N := 1) K →*
      Multiplicative (CyclotomicUnitFreePartModP (p := p) K) :=
  QuotientGroup.lift
    (CyclotomicUnitPowerSubgroup (p := p) (N := 1) K)
    (cyclotomicUnitToFreePartModPMul (p := p) K)
    (by
      rintro _ ⟨u, rfl⟩
      simpa using cyclotomicUnitToFreePartModPMul_pow_eq_one (p := p) (K := K) u)

@[simp]
theorem cyclotomicUnitPowerQuotientToFreePartModP_apply_class
    (u : CyclotomicUnitGroup K) :
    cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
        (cyclotomicUnitPowerClass (p := p) (N := 1) K u) =
      Multiplicative.ofAdd
        (cyclotomicUnitFreePartModPClass (p := p) K
          (Additive.ofMul (cyclotomicUnitFreeClass K u))) := by
  rfl

/-- The torsion image in `E/E^p` maps trivially to the reduced free quotient. -/
theorem cyclotomicTorsionPowerClassSubgroup_le_freePartModP_ker :
    cyclotomicTorsionPowerClassSubgroup (p := p) K ≤
      (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K).ker := by
  rintro _ ⟨u, hu, rfl⟩
  rw [MonoidHom.mem_ker, cyclotomicUnitPowerQuotientToFreePartModP_apply_class]
  apply Multiplicative.ext
  change cyclotomicUnitFreePartModPClass (p := p) K
      (Additive.ofMul (cyclotomicUnitFreeClass K u)) = 0
  have hu_free : cyclotomicUnitFreeClass K u = 1 := by
    rw [← MonoidHom.mem_ker, cyclotomicUnitFreeClass_ker]
    exact hu
  rw [hu_free]
  rfl

/-- The map `E/E^p -> (E/E_tors)/p` is onto. -/
theorem cyclotomicUnitPowerQuotientToFreePartModP_surjective :
    Function.Surjective (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K) := by
  intro y
  induction y using Multiplicative.rec with
  | ofAdd y =>
      refine Submodule.Quotient.induction_on
        (CyclotomicUnitFreePartPMultipleSubmodule (p := p) K) y ?_
      intro x
      induction x using Additive.rec with
      | ofMul q =>
          refine QuotientGroup.induction_on q ?_
          intro u
          refine ⟨cyclotomicUnitPowerClass (p := p) (N := 1) K u, ?_⟩
          change cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
              (cyclotomicUnitPowerClass (p := p) (N := 1) K u) =
            Multiplicative.ofAdd
              (cyclotomicUnitFreePartModPClass (p := p) K
                (Additive.ofMul (cyclotomicUnitFreeClass K u)))
          exact cyclotomicUnitPowerQuotientToFreePartModP_apply_class
            (p := p) (K := K) u

/-- Exactness at `E/E^p`: the kernel of
`E/E^p -> (E/E_tors)/p` is precisely the torsion image. -/
theorem cyclotomicUnitPowerQuotientToFreePartModP_ker :
    (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K).ker =
      cyclotomicTorsionPowerClassSubgroup (p := p) K := by
  apply le_antisymm
  · intro x hx
    revert hx
    refine QuotientGroup.induction_on x ?_
    intro u hx
    change cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
        (cyclotomicUnitPowerClass (p := p) (N := 1) K u) = 1 at hx
    rw [cyclotomicUnitPowerQuotientToFreePartModP_apply_class] at hx
    have hx_add :
        cyclotomicUnitFreePartModPClass (p := p) K
          (Additive.ofMul (cyclotomicUnitFreeClass K u)) = 0 := by
      simpa using congrArg Multiplicative.toAdd hx
    change (Submodule.Quotient.mk (Additive.ofMul (cyclotomicUnitFreeClass K u)) :
        CyclotomicUnitFreePartModP (p := p) K) = 0 at hx_add
    rw [Submodule.Quotient.mk_eq_zero] at hx_add
    obtain ⟨y, hy⟩ := hx_add
    change (p : ℤ) • y = Additive.ofMul (cyclotomicUnitFreeClass K u) at hy
    induction y using Additive.rec with
    | ofMul q =>
        revert hy
        refine QuotientGroup.induction_on q ?_
        intro v hy
        have hfree_zpow :
            (cyclotomicUnitFreeClass K v) ^ (p : ℤ) =
              cyclotomicUnitFreeClass K u := by
          simpa [toMul_zsmul] using congrArg Additive.toMul hy
        have hfree_pow :
            cyclotomicUnitFreeClass K (v ^ p) =
              cyclotomicUnitFreeClass K u := by
          simpa [map_pow] using hfree_zpow
        have htorsion : u * (v ^ p)⁻¹ ∈ CyclotomicUnitTorsion K := by
          rw [← cyclotomicUnitFreeClass_ker, MonoidHom.mem_ker]
          rw [map_mul, map_inv, hfree_pow, mul_inv_cancel]
        refine ⟨u * (v ^ p)⁻¹, htorsion, ?_⟩
        have hpow_class :
            cyclotomicUnitPowerClass (p := p) (N := 1) K (v ^ p) = 1 := by
          simpa using cyclotomicUnitPowerClass_pow_eq_one (p := p) (N := 1) K v
        rw [map_mul, map_inv, hpow_class, inv_one, mul_one]
        rfl
  · exact cyclotomicTorsionPowerClassSubgroup_le_freePartModP_ker (p := p) (K := K)

/-- The actual cyclotomic action preserves the subgroup of `p`-multiples in
the additive free quotient. -/
theorem cyclotomicUnitFreePartPMultipleSubmodule_map
    (a : CyclotomicUnitDelta p) :
    (CyclotomicUnitFreePartPMultipleSubmodule (p := p) K).map
        (cyclotomicUnitFreePartLinearEquiv (p := p) K a : CyclotomicUnitFreePart K →ₗ[ℤ]
          CyclotomicUnitFreePart K) =
      CyclotomicUnitFreePartPMultipleSubmodule (p := p) K := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := hy
    exact ⟨cyclotomicUnitFreePartLinearEquiv (p := p) K a z, by
      simp [LinearMap.lsmul_apply]⟩
  · rintro x hx
    obtain ⟨z, rfl⟩ := hx
    refine ⟨p • (cyclotomicUnitFreePartLinearEquiv (p := p) K a).symm z, ?_, ?_⟩
    · exact ⟨(cyclotomicUnitFreePartLinearEquiv (p := p) K a).symm z, by
        simp [LinearMap.lsmul_apply]⟩
    · simp

/-- The cyclotomic action on the free quotient reduced modulo `p`. -/
def cyclotomicUnitFreePartModPLinearEquiv
    (a : CyclotomicUnitDelta p) :
    CyclotomicUnitFreePartModP (p := p) K ≃ₗ[ℤ]
      CyclotomicUnitFreePartModP (p := p) K :=
  Submodule.Quotient.equiv
    (CyclotomicUnitFreePartPMultipleSubmodule (p := p) K)
    (CyclotomicUnitFreePartPMultipleSubmodule (p := p) K)
    (cyclotomicUnitFreePartLinearEquiv (p := p) K a)
    (cyclotomicUnitFreePartPMultipleSubmodule_map (p := p) (K := K) a)

@[simp]
theorem cyclotomicUnitFreePartModPLinearEquiv_apply_class
    (a : CyclotomicUnitDelta p) (x : CyclotomicUnitFreePart K) :
    cyclotomicUnitFreePartModPLinearEquiv (p := p) K a
        (cyclotomicUnitFreePartModPClass (p := p) K x) =
      cyclotomicUnitFreePartModPClass (p := p) K
        (cyclotomicUnitFreePartLinearEquiv (p := p) K a x) :=
  rfl

/-- Multiplicative form of the mod-`p` free quotient action. -/
def cyclotomicUnitFreePartModPMulEquiv
    (a : CyclotomicUnitDelta p) :
    MulAut (Multiplicative (CyclotomicUnitFreePartModP (p := p) K)) :=
  AddEquiv.toMultiplicative
    (cyclotomicUnitFreePartModPLinearEquiv (p := p) K a).toAddEquiv

@[simp]
theorem cyclotomicUnitFreePartModPMulEquiv_apply_class
    (a : CyclotomicUnitDelta p) (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreePartModPMulEquiv (p := p) K a
        (Multiplicative.ofAdd
          (cyclotomicUnitFreePartModPClass (p := p) K
            (Additive.ofMul (cyclotomicUnitFreeClass K u)))) =
      Multiplicative.ofAdd
        (cyclotomicUnitFreePartModPClass (p := p) K
          (Additive.ofMul
            (cyclotomicUnitFreeClass K (cyclotomicUnitEquiv (p := p) K a u)))) :=
  rfl

/-- The canonical map `E/E^p -> (E/E_tors)/p` is equivariant for the actual
cyclotomic action. -/
theorem cyclotomicUnitPowerQuotientToFreePartModP_equivariant
    (a : CyclotomicUnitDelta p)
    (x : CyclotomicUnitPowerQuotient (p := p) (N := 1) K) :
    cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
        ((cyclotomicUnitModPDeltaAction (p := p) K).act a x) =
      cyclotomicUnitFreePartModPMulEquiv (p := p) K a
        (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K x) := by
  refine QuotientGroup.induction_on x ?_
  intro u
  change cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
      ((cyclotomicUnitModPDeltaAction (p := p) K).act a
        (cyclotomicUnitPowerClass (p := p) (N := 1) K u)) =
    cyclotomicUnitFreePartModPMulEquiv (p := p) K a
      (cyclotomicUnitPowerQuotientToFreePartModP (p := p) K
        (cyclotomicUnitPowerClass (p := p) (N := 1) K u))
  rw [cyclotomicUnitPowerQuotientDeltaAction_act_mk,
    cyclotomicUnitPowerQuotientToFreePartModP_apply_class,
    cyclotomicUnitPowerQuotientToFreePartModP_apply_class,
    cyclotomicUnitFreePartModPMulEquiv_apply_class]

end BernoulliRegular

end
