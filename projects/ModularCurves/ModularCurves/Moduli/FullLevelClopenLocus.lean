/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.PointVanishingClopen
import ModularCurves.Moduli.FullLevelTautSection

/-!
# [YF-U] The open full-level locus (YFULL route γ)

Over the ambient `E[N] ×_S E[N] = pullback (torsionπ N) (torsionπ N)`, the tautological pair
`(u₁, u₂)` (`tautPt₁`/`tautPt₂`) generates, for each `(c,d) ∈ (ℤ/N)²`, the combination
`σ_{c,d} := [c]•u₁ + [d]•u₂`, an `N`-torsion point. Its **vanishing locus** — where `σ_{c,d}`
agrees with `0` in the finite-étale `E[N]` — is clopen (`isClopen_range_pointVanish`, the landed
route-γ engine). The **open full-level locus** `U` is the complement of the (finite) union of the
vanishing loci over the nonzero `(c,d)`: the locus where no nontrivial combination of the
tautological pair vanishes. It is open because a finite union of closed sets is closed.

`U` is the `[YF-U]` datum consumed by `isOpenImmersion_levelSpaceΓι_of_taut`
(`Moduli/FullLevelTautSection.lean`) once `[YF-⊆]` (range bound) and `[YF-⊇]` (full-level over `U`)
are supplied.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]

/-- The `(c,d)`-combination `[c]•u₁ + [d]•u₂` of the tautological pair over `E[N] ×_S E[N]`. -/
noncomputable def tautCombo (cd : ZMod N × ZMod N) : E.Point (tautBase E N) :=
  (cd.1.val : ℤ) • tautPt₁ E N + (cd.2.val : ℤ) • tautPt₂ E N

/-- Each tautological combination is `N`-killed: `[c]•u₁ + [d]•u₂` dies under `[N]` because `u₁`,
`u₂` do. -/
theorem tautCombo_killed (cd : ZMod N × ZMod N) :
    (tautCombo E N cd).1 ≫ E.mulByHom N = tautBase E N ≫ E.zero := by
  rw [← E.smul_eq_zero_iff_comp_mulByHom (tautBase E N) N (tautCombo E N cd), tautCombo, smul_add,
    smul_comm (N : ℤ) (cd.1.val : ℤ) (tautPt₁ E N),
    smul_comm (N : ℤ) (cd.2.val : ℤ) (tautPt₂ E N),
    (E.smul_eq_zero_iff_comp_mulByHom (tautBase E N) N (tautPt₁ E N)).mpr (tautPt₁_killed E N),
    (E.smul_eq_zero_iff_comp_mulByHom (tautBase E N) N (tautPt₂ E N)).mpr (tautPt₂_killed E N),
    smul_zero, smul_zero, add_zero]

/-- **[YF-U]** The open full-level locus in `E[N] ×_S E[N]`: the complement of the union, over the
nonzero `(c,d) ∈ (ℤ/N)²`, of the vanishing loci of the tautological combinations `[c]•u₁ + [d]•u₂`.
Open because `(ℤ/N)²` is finite and each vanishing locus is clopen (`isClopen_range_pointVanish`). -/
noncomputable def fullLevelOpenLocus (hN : NIsInvertible S N) :
    (pullback (E.torsionπ N) (E.torsionπ N)).Opens :=
  ⟨(⋃ cd ∈ ({0}ᶜ : Set (ZMod N × ZMod N)), Set.range
      (AlgebraicGeometry.agreementι (E.torsionπ N)
        (E.pointToTorsion (tautCombo E N cd) (tautCombo_killed E N cd))
        (E.pointToTorsion (0 : E.Point (tautBase E N)) (E.zero_comp_mulByHom N (tautBase E N)))
        (by rw [E.pointToTorsion_torsionπ, E.pointToTorsion_torsionπ])).base)ᶜ, by
    rw [isOpen_compl_iff]
    refine Set.Finite.isClosed_biUnion (Set.toFinite _) (fun cd _ => ?_)
    exact (isClopen_range_pointVanish E N hN (tautBase E N) (tautCombo E N cd)
      (tautCombo_killed E N cd)).1⟩

end EllipticCurve

end ModularCurves
