/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.MulByHomFlatFibre
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# Unramified transport across pointed group-object isomorphisms

The `FormallyUnramified` mirror of `flat_mulByHom_of_isMonHom_iso`: `[n]` conjugates
across a pointed group-object isomorphism, so its formal unramifiedness transports.

This is the transport leg shared by the whole BB-DIFF chain; the field-level statements
themselves (`modelMulByHom_formallyUnramified_of_isAlgClosed` — the kernel-count
argument — and its κ̄-descent to arbitrary fields) live in
`EllipticCurve/TorsionFibre.lean`, downstream of the torsion machinery they consume.
-/

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

open EllipticCurve WeierstrassCurve

section UnramifiedIsoTransport

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

end UnramifiedIsoTransport

end ModularCurves
