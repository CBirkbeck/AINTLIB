/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.MulByHomFlatFibre
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# BB-DIFF fibre leg: `[N]` on the model over a field is formally unramified

The exact `FormallyUnramified` mirror of the BB-FLAT fibre leg (`MulByHomFlatFibre`):

* `modelMulByHom_formallyUnramified_of_field` — **the single mathematical leaf of
  BB-DIFF** (Loeffler 3.4.2(2) over a field, = Silverman III.5.4 separability of `[N]`
  when `(N : k) ≠ 0`, geometrised). Currently `sorry`; everything else in the BB-DIFF
  chain (`formallyUnramified_torsionπ` → `mulByHom_formallyUnramified` → `mulBy_etale` /
  `torsionπ_etale`) is discharged from it.
* `formallyUnramified_mulByHom_of_isMonHom_iso` — transport across a pointed group-object
  iso (verbatim mirror of `flat_mulByHom_of_isMonHom_iso`).
* `formallyUnramified_mulByHom_baseChange_residueField` — the fibre input at residue
  points of an arbitrary base, from the leaf via `fibrewiseElliptic`/`fibreModelIsoAsOver`
  (verbatim mirror of `flat_mulByHom_baseChange_residueField`, with the `N`-invertibility
  hypothesis threaded through the residue field).
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

open EllipticCurve WeierstrassCurve

section FieldLevelUnramified

variable {k : Type u} [Field k]

/-- **(BB-DIFF fibre leg — the field-level leaf, T-B5 = Loeffler 3.4.2(2) over a field)**
Over a field `k` in which `N` is invertible, multiplication by `N` on the projective
model of an elliptic Weierstrass curve is **formally unramified** — `[N]` multiplies the
invariant differential by `N ≠ 0`, so it is separable (HasseWeil
`mulByInt_isSeparable`), and a separable finite self-isogeny of the homogeneous smooth
curve is unramified everywhere. -/
theorem modelMulByHom_formallyUnramified_of_field (W : WeierstrassCurve k) [W.IsElliptic]
    (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0) :
    FormallyUnramified ((modelEllipticCurve W).mulByHom (N : ℤ)) := by
  sorry

end FieldLevelUnramified

section UnramifiedTransport

variable {S : Scheme.{u}}

/-- **(Unramified transport across a group-object iso)** If `φ : E ≅ F` as group objects
over `S` (`IsMonHom`), formal unramifiedness of `[n]` transports from `F` to `E`:
`[n]_E` is the conjugate `φ ≫ [n]_F ≫ φ⁻¹`. -/
theorem formallyUnramified_mulByHom_of_isMonHom_iso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] (n : ℤ)
    (hF : FormallyUnramified (F.mulByHom n)) : FormallyUnramified (E.mulByHom n) := by
  -- ascribe the underlying scheme morphisms to the `.E`-types (defeq)
  let ψ : E.E ⟶ F.E := φ.hom.left
  let ψ' : F.E ⟶ E.E := φ.inv.left
  have hc : E.mulByHom n ≫ ψ = ψ ≫ F.mulByHom n :=
    mulByHom_comp_left_of_isMonHom E F φ.hom n
  have hinv : ψ ≫ ψ' = 𝟙 E.E := by
    show φ.hom.left ≫ φ.inv.left = 𝟙 _
    rw [← Over.comp_left, φ.hom_inv_id, Over.id_left]
  have hinv' : ψ' ≫ ψ = 𝟙 F.E := by
    show φ.inv.left ≫ φ.hom.left = 𝟙 _
    rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]
  let eIso : E.E ≅ F.E := ⟨ψ, ψ', hinv, hinv'⟩
  exact (MorphismProperty.arrow_mk_iso_iff (P := @FormallyUnramified)
    (Arrow.isoMk eIso eIso hc.symm)).mpr hF

/-- **(BB-DIFF fibre input at residue points)** `[N]` on the fibre curve
`E ×_S Spec κ(s)` is formally unramified when `N ≠ 0` in `κ(s)`: the fibre is
pointed-isomorphic to a projective Weierstrass model over `κ(s)`
(`fibreModelIsoAsOver`), whose `[N]` is formally unramified by the field-level leaf. -/
theorem formallyUnramified_mulByHom_baseChange_residueField (E : EllipticCurve S)
    (N : ℕ) [NeZero N] (s : S) (hN : (N : S.residueField s) ≠ 0) :
    FormallyUnramified ((E.baseChange (S.fromSpecResidueField s)).mulByHom (N : ℤ)) := by
  obtain ⟨W, hWell, e, heπ, hez⟩ := fibrewiseElliptic E s
  haveI := hWell
  obtain ⟨φ, hφ⟩ := fibreModelIsoAsOver E s W e heπ hez
  haveI := hφ
  exact formallyUnramified_mulByHom_of_isMonHom_iso φ (N : ℤ)
    (modelMulByHom_formallyUnramified_of_field W N hN)

end UnramifiedTransport

end ModularCurves
