/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Transport equivalences for `Submodule.torsionBy`

Two general `AddCommGroup` facts about `Submodule.torsionBy ℤ`, relocated from the
`EllipticCurve/` torsion cluster (#6996) where they had no elliptic-curve content
(statements byte-identical; proofs golfed to compositions of mathlib primitives).

## Main definitions

* `Submodule.torsionByCongr`: torsion subgroups transport along additive equivalences.
* `Submodule.torsionByNsmulKerEquiv`: for `d ∣ N`, the `d`-killed part of the `N`-torsion
  is the `d`-torsion.

## Implementation notes

Mathlib audit (2026-07-15): no `torsionBy`-transport exists upstream (loogle
`Submodule.torsionBy, AddEquiv` and `Submodule.torsionBy, Submodule.map` are both empty;
nearest is `AddEquiv.addSubgroupMap`, which is subgroup-level, not `torsionBy`).
`torsionByCongr` is a mathlib-PR candidate for `Mathlib.Algebra.Module.Torsion.Basic`
(`torsionByNsmulKerEquiv` is composable from upstream combinators, so PR it only in the
generalised form). Both statements compile verbatim in the R-linear generality
`[CommSemiring R] [AddCommMonoid M] [Module R M]` with `(φ : M ≃ₗ[R] N)` resp. `(a b : R)`,
`a ∣ b` — the intended shape for the upstream PR, possibly in the `AddSubgroup.torsionBy`
(`A[n]`) vocabulary.
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
    {x : Submodule.torsionBy ℤ G (N : ℤ) // d • x = 0} ≃ Submodule.torsionBy ℤ G (d : ℤ) :=
  (Equiv.subtypeEquivRight fun x ↦ by
    simp only [Subtype.ext_iff, SetLike.val_smul_of_tower, ZeroMemClass.coe_zero,
      Submodule.mem_torsionBy_iff, natCast_zsmul]).trans <|
    Equiv.subtypeSubtypeEquivSubtype (Submodule.torsionBy_le_torsionBy_of_dvd _ _ hdN.natCast ·)

end Submodule

end ModularCurves
