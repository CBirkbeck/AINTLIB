module

public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Unit quotients: torsion and free parts

This file starts the `T040` unit-quotient layer.  It records the part of
Dirichlet's unit theorem used before quotienting by powers: the unit group
splits into roots of unity and a free quotient with the standard Dirichlet
basis.

The actual reflection argument only needs this API for cyclotomic fields, but
the torsion/free decomposition is available for every number field.
-/

@[expose] public section

noncomputable section

open Module NumberField
open scoped NumberField

namespace BernoulliRegular

set_option linter.unusedSectionVars false

variable (K : Type*) [Field K] [NumberField K]

/-- The unit group `E = 𝒪_Kˣ` used in the reflection unit quotient. -/
abbrev CyclotomicUnitGroup : Type _ :=
  (𝓞 K)ˣ

/-- The roots-of-unity subgroup of the unit group. -/
abbrev CyclotomicUnitTorsion : Subgroup (CyclotomicUnitGroup K) :=
  NumberField.Units.torsion K

/-- The torsion-free quotient of the unit group, written additively so it
inherits the `ℤ`-module structure from Dirichlet's unit theorem. -/
abbrev CyclotomicUnitFreePart : Type _ :=
  Additive ((𝓞 K)ˣ ⧸ NumberField.Units.torsion K)

/-- The quotient map from units to the torsion-free quotient. -/
def cyclotomicUnitFreeClass : CyclotomicUnitGroup K →* (𝓞 K)ˣ ⧸ CyclotomicUnitTorsion K :=
  QuotientGroup.mk' (CyclotomicUnitTorsion K)

@[simp]
theorem cyclotomicUnitFreeClass_apply (u : CyclotomicUnitGroup K) :
    cyclotomicUnitFreeClass K u = QuotientGroup.mk u :=
  rfl

/-- The kernel of the free quotient map is exactly the torsion subgroup. -/
theorem cyclotomicUnitFreeClass_ker :
    (cyclotomicUnitFreeClass K).ker = CyclotomicUnitTorsion K :=
  QuotientGroup.ker_mk' (CyclotomicUnitTorsion K)

/-- The Dirichlet basis of the torsion-free quotient. -/
def cyclotomicUnitFreeBasis :
    Basis (Fin (NumberField.Units.rank K)) ℤ (CyclotomicUnitFreePart K) :=
  NumberField.Units.basisModTorsion K

/-- The free quotient has the Dirichlet unit rank. -/
theorem cyclotomicUnitFreePart_finrank :
    Module.finrank ℤ (CyclotomicUnitFreePart K) = NumberField.Units.rank K :=
  NumberField.Units.finrank_modTorsion K

/-- The chosen fundamental units map to the Dirichlet basis. -/
theorem cyclotomicUnitFreeBasis_apply_fundSystem
    (i : Fin (NumberField.Units.rank K)) :
    Additive.ofMul
        (cyclotomicUnitFreeClass K (NumberField.Units.fundSystem K i)) =
      cyclotomicUnitFreeBasis K i :=
  NumberField.Units.fundSystem_mk K i

/-- Torsion together with the chosen fundamental units generates all units. -/
theorem cyclotomicUnit_closure_fundSystem_sup_torsion_eq_top :
    Subgroup.closure (Set.range (NumberField.Units.fundSystem K)) ⊔
        CyclotomicUnitTorsion K = ⊤ :=
  NumberField.Units.closure_fundSystem_sup_torsion_eq_top K

/-- Dirichlet's unique decomposition of a unit into a root of unity and powers
of the chosen fundamental units. -/
theorem cyclotomicUnit_exists_unique_eq_torsion_mul_prod
    (u : CyclotomicUnitGroup K) :
    ∃! ζe : CyclotomicUnitTorsion K × (Fin (NumberField.Units.rank K) → ℤ),
      u = ζe.1 * ∏ i, (NumberField.Units.fundSystem K i) ^ (ζe.2 i) :=
  NumberField.Units.exist_unique_eq_mul_prod K u

/-- Packaged torsion/free decomposition used by later unit-quotient tickets. -/
structure CyclotomicUnitDecomposition where
  torsionSubgroup : Subgroup (CyclotomicUnitGroup K)
  torsionSubgroup_eq : torsionSubgroup = CyclotomicUnitTorsion K
  freeBasis : Basis (Fin (NumberField.Units.rank K)) ℤ (CyclotomicUnitFreePart K)

namespace CyclotomicUnitDecomposition

variable {K}

/-- The roots-of-unity subgroup in a packaged decomposition. -/
theorem torsionSubgroup_eq_torsion (D : CyclotomicUnitDecomposition K) :
    D.torsionSubgroup = CyclotomicUnitTorsion K :=
  D.torsionSubgroup_eq

/-- The Dirichlet-rank index set of the packaged free basis. -/
abbrev FreeIndex (_D : CyclotomicUnitDecomposition K) : Type :=
  Fin (NumberField.Units.rank K)

end CyclotomicUnitDecomposition

/-- The canonical torsion/free decomposition supplied by mathlib's Dirichlet
unit theorem. -/
def cyclotomicUnitDecomposition : CyclotomicUnitDecomposition K where
  torsionSubgroup := CyclotomicUnitTorsion K
  torsionSubgroup_eq := rfl
  freeBasis := cyclotomicUnitFreeBasis K

end BernoulliRegular
