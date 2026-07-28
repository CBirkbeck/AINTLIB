/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.Moduli.FullLevelTautSection
import ModularCurves.EllipticCurve.PointVanishingClopen

/-!
# The full-level locus is open (YFULL route γ, [YF-U])

Over the ambient `E[N] ×_S E[N]` the tautological pair `(tautPt₁, tautPt₂)` generates, for
each `(c, d) ∈ (ℤ/N)²`, the combination point `combPoint c d = [c]·tautPt₁ + [d]·tautPt₂`,
each an `N`-torsion point. For `N` invertible the vanishing locus of each nonzero
combination is clopen (`isClopen_range_pointVanish`), so the union of these finitely many
clopen loci is closed, and its complement — the locus `fullLevelOpenSet` where every
nonzero combination is nonvanishing — is **open**.

`fullLevelOpenSet` is the Drinfeld full-level locus for `N` invertible (the `N²`
combinations are then distinct fibrewise), packaged as `fullLevelOpens : ambient.Opens`.
It supplies the open `U` of the clopen leaf `isOpenImmersion_levelSpaceΓι_of_taut`; the two
remaining inputs are the image bound `[YF-⊆]` (`range levelSpaceΓι ⊆ U`) and the full-level
witness `[YF-⊇]` (the taut pair is full-level over `U`).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-- The tautological combination point `[c]·tautPt₁ + [d]·tautPt₂` over `E[N] ×_S E[N]`. -/
noncomputable def combPoint (c d : ℤ) : E.Point (tautBase E N) :=
  c • tautPt₁ E N + d • tautPt₂ E N

theorem tautPt₁_smul_eq_zero : (N : ℤ) • tautPt₁ E N = 0 :=
  (E.smul_eq_zero_iff_comp_mulByHom (tautBase E N) N (tautPt₁ E N)).mpr (tautPt₁_killed E N)

theorem tautPt₂_smul_eq_zero : (N : ℤ) • tautPt₂ E N = 0 :=
  (E.smul_eq_zero_iff_comp_mulByHom (tautBase E N) N (tautPt₂ E N)).mpr (tautPt₂_killed E N)

theorem combPoint_smul_eq_zero (c d : ℤ) : (N : ℤ) • combPoint E N c d = 0 := by
  rw [combPoint, smul_add, smul_comm (N : ℤ) c, smul_comm (N : ℤ) d,
    tautPt₁_smul_eq_zero, tautPt₂_smul_eq_zero, smul_zero, smul_zero, add_zero]

/-- Every combination point is killed by `N` (comp form, for `pointToTorsion`). -/
theorem combPoint_killed (c d : ℤ) :
    (combPoint E N c d).1 ≫ E.mulByHom N = tautBase E N ≫ E.zero :=
  (E.smul_eq_zero_iff_comp_mulByHom (tautBase E N) N (combPoint E N c d)).mp
    (combPoint_smul_eq_zero E N c d)

/-- The **full-level open locus**: the complement of the union of the clopen vanishing loci
of the nonzero combination points. Open (`fullLevelOpenSet_isOpen`). -/
def fullLevelOpenSet (hN : NIsInvertible S N) :
    Set ↥(pullback (E.torsionπ N) (E.torsionπ N)) :=
  (⋃ (cd : Fin N × Fin N) (_ : cd ≠ 0),
    E.pointVanishSet N (tautBase E N) (combPoint E N (cd.1 : ℤ) (cd.2 : ℤ))
      (combPoint_killed E N (cd.1 : ℤ) (cd.2 : ℤ)))ᶜ

theorem fullLevelOpenSet_isOpen (hN : NIsInvertible S N) :
    IsOpen (fullLevelOpenSet E N hN) := by
  rw [fullLevelOpenSet, isOpen_compl_iff]
  refine isClosed_iUnion_of_finite fun cd => ?_
  refine isClosed_iUnion_of_finite fun _ => ?_
  exact (E.isClopen_pointVanishSet N hN (tautBase E N)
    (combPoint E N (cd.1 : ℤ) (cd.2 : ℤ))
    (combPoint_killed E N (cd.1 : ℤ) (cd.2 : ℤ))).isClosed

/-- The full-level open locus as a `Scheme.Opens` of the ambient `E[N] ×_S E[N]`. -/
-- `private`: `GroupScheme/TorsionCombination.lean` defines the same name in the same
-- namespace and both are imported together by the root index; this copy has no
-- consumers outside this file (which itself has no dependents).
private def fullLevelOpens (hN : NIsInvertible S N) :
    (pullback (E.torsionπ N) (E.torsionπ N)).Opens :=
  ⟨fullLevelOpenSet E N hN, fullLevelOpenSet_isOpen E N hN⟩

end EllipticCurve

end ModularCurves
