/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.GroupScheme.GroupRingFree
import ModularCurves.GroupScheme.StableChartData
import ModularCurves.ForMathlib.HopfGaloisQuotient

/-!
# The subgroup-scheme quotient, per-patch layer (`[HG-C4a]`)

The first brick of the `[HG-C4]` glue (design: board v10.184-G0). For an affine chart patch
`P` with free group ring, the categorical quotient of the chart by the translation action is
the affine scheme of the co-invariants of the chart co-action:
`P.localQuotient := Spec (coinvariants P.chartCoaction)`, with quotient map
`P.localQuotientπ := isoSpec ≫ specEqualizerπ`. Its universal property is
`existsUnique_lift_of_isHopfGalois` applied to the M6 Hopf–Galois datum
(`isHopfGalois_chartCoaction`), whose lone `Module.Free` hypothesis is supplied around every
point of `E` by `[HG-C3f]` (`exists_affineChartPatch_free`).

The geometry bridge (invariant morphisms coequalize the chart pair — `[HG-C4b]`) and the
two-stage glue (`[HG-C4c]`) consume this layer.
-/

open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct

universe u

namespace ModularCurves

namespace EllipticCurve

namespace FiniteLocallyFreeSubgroup

namespace AffineChartPatch

variable {S : Scheme.{u}} {E : EllipticCurve S} {G : FiniteLocallyFreeSubgroup E}
  (P : G.AffineChartPatch) [Module.Free P.baseRing P.groupRing]

/-- **`[HG-C4a]` — the per-patch quotient**: the affine scheme of the co-invariants of the
chart co-action. -/
noncomputable def localQuotient : Scheme.{u} :=
  Spec (CommRingCat.of (coinvariants P.chartCoaction))

/-- The per-patch quotient map: the chart, identified with the `Spec` of its sections,
mapped to the co-invariants spectrum. -/
noncomputable def localQuotientπ : P.U.toScheme ⟶ P.localQuotient :=
  P.hU.isoSpec.hom ≫
    specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft

/-- **The per-patch universal property** (`existsUnique_lift_of_isHopfGalois` at the M6
datum): every morphism out of the chart that coequalizes the chart pair
`(Spec chartCoaction, Spec includeLeft)` factors uniquely through the per-patch quotient. -/
theorem localQuotient_existsUnique_lift {Y : Scheme.{u}} (f : P.U.toScheme ⟶ Y)
    (hf : Spec.map (CommRingCat.ofHom P.chartCoaction.toRingHom) ≫ P.hU.isoSpec.inv ≫ f
        = Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeLeft :
              P.chartRing →ₐ[P.baseRing] P.chartRing ⊗[P.baseRing] P.groupRing).toRingHom) ≫
          P.hU.isoSpec.inv ≫ f) :
    ∃! g : P.localQuotient ⟶ Y, P.localQuotientπ ≫ g = f := by
  obtain ⟨g, hg, huniq⟩ := existsUnique_lift_of_isHopfGalois P.chartCoaction
    P.isHopfGalois_chartCoaction (P.hU.isoSpec.inv ≫ f) hf
  refine ⟨g, ?_, fun g' hg' => ?_⟩
  · show (P.hU.isoSpec.hom ≫
        specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft) ≫ g = f
    exact (Category.assoc _ _ _).trans
      ((congrArg (P.hU.isoSpec.hom ≫ ·) hg).trans (P.hU.isoSpec.hom_inv_id_assoc f))
  · refine huniq g' ?_
    have hg'' : (P.hU.isoSpec.hom ≫
        specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft) ≫ g' = f := hg'
    have hA : P.hU.isoSpec.hom ≫
        specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft ≫ g' = f :=
      (Category.assoc _ _ _).symm.trans hg''
    show specEqualizerπ P.chartCoaction Algebra.TensorProduct.includeLeft ≫ g'
        = P.hU.isoSpec.inv ≫ f
    exact (P.hU.isoSpec.inv_hom_id_assoc _).symm.trans (congrArg (P.hU.isoSpec.inv ≫ ·) hA)

/-! ### `[HG-C4b]` — the geometry bridge, coaction leg -/

/-- **The coaction leg of the geometry bridge**: the `Spec` of the ring-level chart
co-action, composed back to the chart, is the scheme-level chart co-action morphism
(`chartCoactionSpec` = Künneth ≫ restricted action). Affine `isoSpec` naturality applied
to `coactionRing_eq_appTop`. -/
theorem spec_coactionRing_isoSpec_inv :
    Spec.map P.coactionRing ≫ P.hU.isoSpec.inv = P.chartCoactionSpec := by
  haveI : IsAffine P.U.toScheme := P.hU
  have hnat := Scheme.isoSpec_inv_naturality (X := Spec (.of
      (P.groupRing ⊗[P.baseRing] P.chartRing))) (Y := P.U.toScheme) P.chartCoactionSpec
  -- unfold the affine-open `isoSpec` into the scheme-level one
  have hiso : P.hU.isoSpec.inv
      = (Scheme.Spec.mapIso P.U.topIso.symm.op).inv ≫ P.U.toScheme.isoSpec.inv := by
    rw [IsAffineOpen.isoSpec, Iso.trans_inv]
    rfl
  rw [coactionRing_eq_appTop, Spec.map_comp, Spec.map_comp, hiso]
  simp only [Category.assoc, Functor.mapIso_inv, Iso.op_inv, Iso.symm_inv]
  -- cancel the `topIso` conjugation
  have htop : Spec.map P.U.topIso.inv ≫ Spec.map P.U.topIso.hom.op.unop = 𝟙 _ := by
    rw [← Spec.map_comp]
    show Spec.map (P.U.topIso.hom ≫ P.U.topIso.inv) = _
    rw [Iso.hom_inv_id, Spec.map_id]
  -- assemble: the `ΓSpecIso` factor is the inverse of `(Spec _).isoSpec.inv`
  rw [show Spec.map P.U.topIso.hom.op.unop = Spec.map P.U.topIso.hom from rfl] at htop
  calc Spec.map (Scheme.ΓSpecIso _).hom ≫ Spec.map P.chartCoactionSpec.appTop ≫
        Spec.map P.U.topIso.inv ≫ Spec.map P.U.topIso.hom ≫ P.U.toScheme.isoSpec.inv
      = Spec.map (Scheme.ΓSpecIso _).hom ≫ Spec.map P.chartCoactionSpec.appTop ≫
        P.U.toScheme.isoSpec.inv := by
        rw [← Category.assoc (Spec.map P.U.topIso.inv), htop, Category.id_comp]
    _ = Spec.map (Scheme.ΓSpecIso _).hom ≫ (Spec (.of
          (P.groupRing ⊗[P.baseRing] P.chartRing))).isoSpec.inv ≫ P.chartCoactionSpec := by
        rw [hnat]
    _ = P.chartCoactionSpec := by
        rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp_assoc, Iso.inv_hom_id, Spec.map_id,
          Category.id_comp]

end AffineChartPatch

end FiniteLocallyFreeSubgroup

end EllipticCurve

end ModularCurves
