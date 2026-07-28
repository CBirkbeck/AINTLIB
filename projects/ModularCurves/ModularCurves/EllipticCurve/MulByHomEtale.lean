/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.TorsionUnramifiedFibre
import ModularCurves.EllipticCurve.MulByHomQuasiFinite
import ModularCurves.EllipticCurve.MulByHomSmooth

/-!
# Étaleness of `[N]` and of the torsion, rewired through the proven quasi-finiteness

Primed variants of the `MulByHomUnramified.lean` étale chain in which the finiteness
input is the PROVEN invertible-case quasi-finiteness
(`Torsionπ.isFinite_of_nIsInvertible`, `MulByHomQuasiFinite.lean`) instead of the sorried
full-generality box BB-QF. The remaining sorried input on this chain is BB-FLAT
(`mulByHom_flat`), to be discharged by the formal-smoothness route (L3 board v10.145).

This file exists (rather than editing `MulByHomUnramified.lean` in place) so that the
`HasseWeil`/`IsoTransport` import closure of the quasi-finiteness proof does not enter
sibling-lane files upstream.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

set_option backward.isDefEq.respectTransparency false in
/-- **(L-BC, proven-finiteness variant — Y1-CLOSER L3)** `Torsionπ.formallyUnramified` with
the finiteness input supplied by `Torsionπ.isFinite_of_nIsInvertible`. Proof body as in
`TorsionUnramifiedFibre.lean`. -/
theorem Torsionπ.formallyUnramified_of_nIsInvertible' (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.torsionπ N) := by
  rcases eq_or_ne N 0 with rfl | hN0
  · have hS : IsEmpty S := ModularCurves.isEmpty_of_nIsInvertible_zero h
    have hT : IsEmpty (E.torsion 0) := ⟨fun x ↦ hS.false ((E.torsionπ 0).base x)⟩
    infer_instance
  · have : NeZero N := ⟨hN0⟩
    have := Torsionπ.isFinite_of_nIsInvertible E N h
    apply FormallyUnramified.of_finite_fiberToSpecResidueField
    intro y
    have hbc : FormallyUnramified ((E.baseChange (S.fromSpecResidueField y)).torsionπ N) :=
      Torsionπ.formallyUnramified_of_isUnit
        (E.baseChange (S.fromSpecResidueField y)) N (nIsInvertible_residueField h y)
    have h1 : IsPullback (E.torsionBaseChangeHom N (S.fromSpecResidueField y))
        ((E.baseChange (S.fromSpecResidueField y)).torsionπ N)
        (E.torsionπ N) (S.fromSpecResidueField y) :=
      E.torsion_baseChange_isPullback N (S.fromSpecResidueField y)
    have h2 : IsPullback ((E.torsionπ N).fiberι y) ((E.torsionπ N).fiberToSpecResidueField y)
        (E.torsionπ N) (S.fromSpecResidueField y) :=
      IsPullback.of_hasPullback (E.torsionπ N) (S.fromSpecResidueField y)
    rw [← h2.isoIsPullback_hom_snd _ _ h1,
      MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.FormallyUnramified)]
    exact hbc

/-- **(BB-DIFF master, proven-finiteness variant)** `[N]` formally unramified when `N` is
invertible, through the proven quasi-finiteness. -/
theorem MulByHom.formallyUnramified'' (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.mulByHom N) :=
  MulByHom.formallyUnramified_of_torsionπ E N
    (Torsionπ.formallyUnramified_of_nIsInvertible' E N h)

/-- **(T-B5, proven-finiteness variant)** `[N]` étale when `N` is invertible. All inputs
proven: flatness by `MulByHom.flat_of_nIsInvertible` (BB-FLAT, route (G)). -/
theorem MulByHom.etale' (N : ℕ) (h : NIsInvertible S N) :
    Etale (E.mulByHom N) := by
  rcases eq_or_ne N 0 with rfl | hN
  · have hS : IsEmpty S := ModularCurves.isEmpty_of_nIsInvertible_zero h
    have hE : IsEmpty E.E := ⟨fun x ↦ hS.false (E.π.base x)⟩
    infer_instance
  · have : NeZero N := ⟨hN⟩
    have := MulByHom.flat_of_nIsInvertible E N h
    have := MulByHom.formallyUnramified'' E N h
    have := MulByHom.locallyOfFinitePresentation E N
    exact Etale.of_formallyUnramified_of_flat (E.mulByHom N)

set_option backward.isDefEq.respectTransparency false in
/-- **(T-B5′, proven-finiteness variant)** `E[N] ⟶ S` étale when `N` is invertible. -/
theorem Torsionπ.etale' (N : ℕ) (h : NIsInvertible S N) :
    Etale (E.torsionπ N) := by
  have he := MulByHom.etale' E N h
  exact MorphismProperty.pullback_snd _ _ he

end EllipticCurve

end ModularCurves
