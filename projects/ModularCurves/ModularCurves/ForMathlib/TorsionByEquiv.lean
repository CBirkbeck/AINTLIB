/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Transport equivalences for `Submodule.torsionBy`

This file provides equivalences for transporting torsion submodules along additive equivalences
and identifying nested torsion conditions.

## Main definitions

* `Submodule.torsionByCongr`: torsion subgroups transport along additive equivalences.
* `Submodule.torsionByNsmulKerEquiv`: for `d ∣ N`, the `d`-killed part of the `N`-torsion
  is the `d`-torsion.
-/

universe u

namespace ModularCurves

namespace Submodule

/-- Torsion subgroups transport along additive equivalences. -/
def torsionByCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A ≃+ B) (n : ℤ) :
    Submodule.torsionBy ℤ A n ≃ Submodule.torsionBy ℤ B n :=
  φ.toEquiv.subtypeEquiv fun a ↦ by
    simp only [Submodule.mem_torsionBy_iff, AddEquiv.toEquiv_eq_coe, EquivLike.coe_coe,
      ← map_zsmul φ, EmbeddingLike.map_eq_zero_iff]

/-- For `d ∣ N`, the `d`-killed part of the `N`-torsion is the `d`-torsion. -/
def torsionByNsmulKerEquiv (G : Type u) [AddCommGroup G] (N d : ℕ) (hdN : d ∣ N) :
    {x : Submodule.torsionBy ℤ G (N : ℤ) // d • x = 0} ≃
      Submodule.torsionBy ℤ G (d : ℤ) :=
  (Equiv.subtypeEquivRight fun x ↦ by
    simp only [Subtype.ext_iff, SetLike.val_smul_of_tower, ZeroMemClass.coe_zero,
      Submodule.mem_torsionBy_iff, natCast_zsmul]).trans <|
    Equiv.subtypeSubtypeEquivSubtype (Submodule.torsionBy_le_torsionBy_of_dvd _ _ hdN.natCast ·)

end Submodule

end ModularCurves
