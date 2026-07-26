/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import ModularCurves.ForMathlib.SmoothRegularLocal
import ModularCurves.ForMathlib.IrreducibleConnected

/-!
# A connected smooth curve over an algebraically closed field is irreducible (T-G4a)

The scheme-level assembly of the `T-SMOOTH-REG` stream:

* `exists_isOpen_isIrreducible_nbhd_of_smooth` — every point of a scheme smooth of relative
  dimension one over `Spec k`, `k` algebraically closed, has an **irreducible open
  neighbourhood**: pass to a standard-smooth affine chart (`SmoothOfRelativeDimension`;
  over `Spec k` the base chart is forced to be `⊤`, so the chart algebra is standard smooth
  over `k` itself), and apply `exists_isIrreducible_basicOpen_nbhd` there;
* `irreducibleSpace_of_connectedSpace_of_smooth_curve` — hence a nonempty **connected** such
  scheme is irreducible (`irreducibleSpace_of_connected_of_locallyIrreducible`).

This discharges the leaf `L1` of the geometric-irreducibility decomposition
(`ModularCurve/IrreducibilityScoping.lean`).
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ModularCurves

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}

/-- **(T-G4a brick 7 ★)** Every point of a scheme smooth of relative dimension one over
`Spec k` (`k` algebraically closed) has an irreducible open neighbourhood. -/
theorem exists_isOpen_isIrreducible_nbhd_of_smooth (sX : X ⟶ Spec (CommRingCat.of k))
    [SmoothOfRelativeDimension 1 sX] (x : ↥X) :
    ∃ W : Set ↥X, IsOpen W ∧ x ∈ W ∧ IsIrreducible W := by
  classical
  obtain ⟨U, hU, V, hV, hxV, e, hss⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := sX) x
  -- over `Spec k` the base chart is everything
  have hUtop : U = ⊤ := by
    refine TopologicalSpace.Opens.ext (Set.eq_univ_of_forall fun y => ?_)
    have hxU : sX.base x ∈ U := e hxV
    exact (Subsingleton.elim y (sX.base x) : y = sX.base x) ▸ hxU
  subst hUtop
  -- so the chart algebra is standard smooth over `k` itself
  letI : Algebra k Γ(X, V) := ((sX.appLE ⊤ V e).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 k Γ(X, V) := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
    exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right _
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv hss
  -- the affine chart as `Spec Γ(X, V)`
  set h : ↥(↑V : Scheme.{u}) ≃ₜ ↥(Spec Γ(X, V)) := Scheme.homeoOfIso hV.isoSpec with hh
  obtain ⟨f, hqf, hirr⟩ :=
    exists_isIrreducible_basicOpen_nbhd k (h ⟨x, hxV⟩ : PrimeSpectrum Γ(X, V))
  -- pull the irreducible basic open back to the chart, then push it into `X`
  set W' : Set ↥(↑V : Scheme.{u}) :=
    h ⁻¹' (PrimeSpectrum.basicOpen f : Set (PrimeSpectrum Γ(X, V))) with hW'
  have hW'open : IsOpen W' := (PrimeSpectrum.basicOpen f).2.preimage h.continuous
  have hW'mem : (⟨x, hxV⟩ : ↥(↑V : Scheme.{u})) ∈ W' := hqf
  have hW'irr : IsIrreducible W' := by
    rw [hW', ← h.image_symm]
    exact hirr.image h.symm h.symm.continuous.continuousOn
  refine ⟨V.ι.base '' W', ?_, ?_, ?_⟩
  · exact V.ι.isOpenEmbedding.isOpenMap _ hW'open
  · exact ⟨⟨x, hxV⟩, hW'mem, rfl⟩
  · exact hW'irr.image _ V.ι.isOpenEmbedding.continuous.continuousOn

/-- **(T-G4a ★★ — leaf L1 of the geometric-irreducibility decomposition)** A nonempty
**connected** scheme smooth of relative dimension one over an algebraically closed field is
**irreducible**. -/
theorem irreducibleSpace_of_connectedSpace_of_smooth_curve
    (sX : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 sX]
    [Nonempty ↥X] [ConnectedSpace ↥X] : IrreducibleSpace ↥X :=
  irreducibleSpace_of_connected_of_locallyIrreducible fun x => by
    obtain ⟨W, hWo, hxW, hWirr⟩ := exists_isOpen_isIrreducible_nbhd_of_smooth sX x
    exact ⟨W, hWo, hxW, hWirr⟩

end ModularCurves
