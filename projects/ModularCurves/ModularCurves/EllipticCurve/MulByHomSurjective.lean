/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.EllipticCurve.Torsion
import ModularCurves.EllipticCurve.MulByHomDegree

/-!
# Surjectivity of `[N] : E ⟶ E` over an arbitrary base

The any-field model surjectivity (`mulByHom_surjective`, `MulByHomDegree.lean` — the
locally-constant-finrank argument) transports to an arbitrary base by the same
fibrewise BETA pattern as the finite-fibre count (`mulByHom_finite_preimage_singleton`,
`MulByHomFibresGlobal.lean`): a point `y` of `E` lies in the `π`-fibre over `s := π y`,
the fibre is the base-changed record over `κ(s)` which is pointed-isomorphic to a
Weierstrass model (`fibrewiseElliptic` + `fibreModelIsoAsOver`), the iso conjugates the
`[N]`s (`mulByHom_comp_left_of_isMonHom`), and `mulByHom_baseChange_fst` carries the
model preimage back up through `pullback.fst`.

Consumed by the Weil-pairing alternation reduction (`WeilPairing/AlternationReduction`):
`[2]` flat (`mulByHom_flat`) + surjective (here) makes the `[2]`-fibre product over any
point a flat surjective halving cover.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}}

/-- Surjectivity of `[n]` transports across a pointed (monoid-object) isomorphism of
elliptic records: the iso conjugates `[n]_E` to `[n]_F`
(`mulByHom_comp_left_of_isMonHom`), so a preimage on the `F`-side pulls back through the
inverse homeomorphism. The surjectivity sibling of
`finite_fibres_mulByHom_of_isMonHom_iso`. -/
theorem surjective_mulByHom_of_isMonHom_iso {E F : EllipticCurve S}
    (φ : E.asOver ≅ F.asOver) [IsMonHom φ.hom] (n : ℤ)
    (hF : Function.Surjective ⇑(F.mulByHom n)) :
    Function.Surjective ⇑(E.mulByHom n) := by
  have hc := mulByHom_comp_left_of_isMonHom E F φ.hom n
  have hbase : ∀ x' : E.E,
      (F.mulByHom n) (φ.hom.left x') = φ.hom.left ((E.mulByHom n) x') := by
    intro x'
    exact (congrArg (fun f : E.E ⟶ F.E => f x') hc).symm
  have h1 : φ.hom.left ≫ φ.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, φ.hom_inv_id, Over.id_left]
  have h2 : φ.inv.left ≫ φ.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, φ.inv_hom_id, Over.id_left]
  have hinj : Function.Injective (⇑φ.hom.left) := by
    refine Function.LeftInverse.injective (g := ⇑φ.inv.left) fun z => ?_
    rw [← Scheme.Hom.comp_apply, h1]; simp
  have hsec : ∀ z : F.E, φ.hom.left (φ.inv.left z) = z := by
    intro z
    rw [← Scheme.Hom.comp_apply, h2]; simp
  intro x
  obtain ⟨w, hw⟩ := hF (φ.hom.left x)
  refine ⟨φ.inv.left w, hinj ?_⟩
  rw [← hbase, hsec, hw]

/-- **`[N]` is surjective over an arbitrary base, in every characteristic**: fibrewise
reduction to the any-field model surjectivity, BETA-transported exactly as the global
fibre-count. -/
theorem mulByHom_base_surjective (E : EllipticCurve S) (N : ℕ) [NeZero N] :
    Function.Surjective ⇑(E.mulByHom N) := by
  intro y
  set s := E.π.base y with hs
  have hrange : Set.range ⇑(pullback.fst E.π (S.fromSpecResidueField s))
      = ⇑E.π ⁻¹' {s} := E.π.range_fiberι s
  have hyr : y ∈ Set.range ⇑(pullback.fst E.π (S.fromSpecResidueField s)) := by
    rw [hrange]
    exact hs.symm
  obtain ⟨ytil, hytil⟩ := hyr
  obtain ⟨W, hWell, e, heπ, hez⟩ := fibrewiseElliptic E s
  haveI := hWell
  obtain ⟨φ, hφ⟩ := fibreModelIsoAsOver E s W e heπ hez
  haveI := hφ
  -- the model-side instance pack for `mulByHom_surjective`
  haveI := modelMulByHom_locallyQuasiFinite_of_field W N
  haveI hp : IsProper ((modelEllipticCurve W).mulByHom N) := by
    haveI h : IsProper ((modelEllipticCurve W).mulByHom N ≫ (modelEllipticCurve W).π) := by
      rw [mulByHom_π]
      exact (modelEllipticCurve W).proper
    exact IsProper.of_comp ((modelEllipticCurve W).mulByHom N) (modelEllipticCurve W).π
  haveI : IsFinite ((modelEllipticCurve W).mulByHom N) :=
    IsFinite.of_isProper_of_locallyQuasiFinite _
  haveI : Flat ((modelEllipticCurve W).mulByHom N) :=
    (modelEllipticCurve W).mulByHom_flat N
  haveI : IsLocallyNoetherian (modelEllipticCurve W).E :=
    LocallyOfFiniteType.isLocallyNoetherian (modelEllipticCurve W).π
  have hmodel : Function.Surjective ⇑((modelEllipticCurve W).mulByHom N) :=
    (mulByHom_surjective W N).surj
  have hbc : Function.Surjective
      ⇑((E.baseChange (S.fromSpecResidueField s)).mulByHom (N : ℤ)) :=
    surjective_mulByHom_of_isMonHom_iso φ (N : ℤ) hmodel
  obtain ⟨xtil, hxtil⟩ := hbc ytil
  refine ⟨(pullback.fst E.π (S.fromSpecResidueField s)) xtil, ?_⟩
  have key : (E.mulByHom (N : ℤ)) ((pullback.fst E.π (S.fromSpecResidueField s)) xtil)
      = (pullback.fst E.π (S.fromSpecResidueField s))
          (((E.baseChange (S.fromSpecResidueField s)).mulByHom (N : ℤ)) xtil) := by
    have h1 := congrFun (congrArg
      (fun f : (E.baseChange (S.fromSpecResidueField s)).E ⟶ E.E => ⇑f)
      (mulByHom_baseChange_fst E (S.fromSpecResidueField s) (N : ℤ))) xtil
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans
      (h1.symm.trans (Scheme.Hom.comp_apply _ _ _))
  rw [key, hxtil]
  exact hytil

/-- `[N] : E ⟶ E` is surjective as a scheme morphism, over an arbitrary base. -/
theorem mulByHom_surjective_global (E : EllipticCurve S) (N : ℕ) [NeZero N] :
    AlgebraicGeometry.Surjective (E.mulByHom N) :=
  ⟨mulByHom_base_surjective E N⟩

end EllipticCurve

end ModularCurves
