/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

STREAM-FIN [KVC-consumer] (board v10.327/v10.328): the geometric-point consumer layer of
the Hasse-free keystone core.
-/
import ModularCurves.EllipticCurve.AutFixedPoints
import ModularCurves.EllipticCurve.AffineSectionSpecPoints
import ModularCurves.EllipticCurve.EndomorphismDegree
import ModularCurves.LevelStructure.IsoTransport

/-!
# [KVC] Keystone consumers at a geometric point (THE RULING v10.320)

THE RULING: every headline keystone consumer is a ∀-geometric-point pin over
`S = Spec k̄`. This file turns the LANDED Hasse-free KVC master
(`pointedAuto_hom_eq_id_of_fixes_points`, `EllipticCurve/AutFixedPoints.lean`) into
`k̄`-point-ready drop-ins for the F4 pin sites:

* **[KVC-model]** `EllipticCurve.exists_projModelIso_of_field` — over a field the
  `LocallyWeierstrass` chart of the working record is global and strictly pointed:
  `E.E ≅ projModel W` for a Weierstrass curve `W` over `k` itself, compatible with `π`
  and the zero section on the nose (the `IntegralOverField` extraction upgraded to the
  pointed iso, with the chart-ring corner transported down to `k` through the
  base-change pullback square).
* **[KVC-pts]** the geometric-point dictionary readouts: a section of `projModel W`
  over `Spec k` whose `projModelPointsEquiv`-value is the affine point `some x y` IS
  the marked affine-point section at `(x, y)`
  (`sectionSpecPoint_eq_affineSection_of_pointsEquiv_eq_some`), hence lies in the
  `Z`-chart with `zChartCoordEval`-readouts exactly `(x, y)`
  (`zChart_readout_of_pointsEquiv_eq_some`) — the master's `hxpair`/`hypair`/`hxne`
  inputs. The `0`-value case is the zero section
  (`sectionSpecPoint_eq_zeroSection_of_pointsEquiv_eq_zero`), completing the
  sections ↔ (affine chart solutions + ∞) dictionary.
* **[KVC-conj]** conjugation transport (`conjModelIso` + compat lemmas): a pointed
  scheme automorphism of `E.E` conjugates through the model iso to a pointed
  automorphism of `projModel W` satisfying the master's `heπ`/`hez` hypotheses,
  point-fixing transports along the conjugation, and `= 𝟙` transports back.
  `EllipticCurve.pointCongr` and `EllipticCurve.fixes_zsmul_of_fixes` /
  `fixes_neg_of_fixes` supply the record-side transport (pointed ⟹ additive via
  `endMonHom`, so fixing `P` fixes every `n • P`).
* **[KVC-drop-ins]** the `*_kvc` corollaries in the F4 pin shapes:
  `EllipticCurve.pointedAuto_eq_id_of_fixes_points_kvc` (three-point supply: a
  `±`-pair anchor `P` with `2 • P ≠ 0` plus one point `Q ∉ {0, P, -P}` — the shape the
  hH design (3) consumes with its rank-2 torsion supply),
  `EllipticCurve.pointedAuto_eq_id_of_fixes_point_kvc` (single-point cyclic supply,
  `2 • P ≠ 0` and `3 • P ≠ 0` — the hbound design (2)), and `hbound_pointwise_of_kvc` /
  `hbound_of_kvc` (the literal `hbound` pin statements of GammaHMaster:1206 and
  GammaHClosure:152, dischargeable verbatim). NO Hasse, NO degree theory, NO
  `IsAlgClosed` in the mathematics — `hbound_of_kvc` carries `[IsAlgClosed k]` only to
  match the pin verbatim.

The EDIT-SITE LIST for the F4 pin-discharge builder is the comment block at the end of
this file.
-/

open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve HomogeneousIdeal
  MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] MvPolynomial.gradedAlgebra

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

/-! ## [KVC-model] — the global model of a record over a field -/

namespace EllipticCurve

/-- **([KVC-model])** Over a field the local Weierstrass model of the working record is
global and strictly pointed: there is a Weierstrass curve `W` over `k` itself and an
isomorphism `ψ : E.E ≅ projModel W` with `ψ.hom ≫ projModelπ W = E.π` and
`E.zero ≫ ψ.hom = projModelZero W`. The single-point base makes the
`LocallyWeierstrass` chart global (its affine open is `⊤`, its inclusion an
isomorphism, its ring a field), and the chart-ring corner is transported down to `k`
through the base-change pullback square `isPullback_projModelBaseChange` along the
`Spec`-preimage of the corner identification. -/
theorem exists_projModelIso_of_field {k : Type u} [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k))) :
    ∃ W : WeierstrassCurve k, W.IsElliptic ∧
      ∃ ψ : E.E ≅ projModel W,
        ψ.hom ≫ projModelπ W = E.π ∧ E.zero ≫ ψ.hom = projModelZero W := by
  haveI hsub : Subsingleton ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  haveI hne : Nonempty ↥(Spec (CommRingCat.of k)) :=
    inferInstanceAs (Nonempty (PrimeSpectrum k))
  obtain ⟨U, hsU, W₀, hell₀, e, heπ, hez⟩ := E.localModel hne.some
  haveI := hell₀
  -- the chart is the whole (single-point) base, so its inclusion is an isomorphism
  have hUtop : U.1 = ⊤ := by
    refine top_unique fun x _ => ?_
    rwa [Subsingleton.elim x hne.some]
  haveI : IsIso U.1.ι := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    rw [Scheme.Opens.opensRange_ι, hUtop]
  haveI : IsIso (pullback.fst E.π U.1.ι) := inferInstance
  -- the chart ring is a field
  have hf : IsField ↑Γ(Spec (CommRingCat.of k), U.1) := by
    have e1 : Γ(Spec (CommRingCat.of k), U.1) ≅ Γ(Spec (CommRingCat.of k), ⊤) :=
      (Spec (CommRingCat.of k)).presheaf.mapIso (eqToIso (congrArg Opposite.op hUtop))
    have e2 : Γ(Spec (CommRingCat.of k), ⊤) ≅ CommRingCat.of k :=
      Scheme.ΓSpecIso (CommRingCat.of k)
    exact MulEquiv.isField (Field.toIsField k)
      (e1 ≪≫ e2).commRingCatIsoToRingEquiv.toMulEquiv
  letI : Field ↑Γ(Spec (CommRingCat.of k), U.1) := hf.toField
  -- the base identification and the induced algebra structure on `k`
  set ρ : Spec (CommRingCat.of k) ⟶
      Spec (CommRingCat.of ↑Γ(Spec (CommRingCat.of k), U.1)) :=
    inv U.1.ι ≫ U.2.isoSpec.hom with hρ
  haveI : IsIso ρ := by rw [hρ]; infer_instance
  letI : Algebra ↑Γ(Spec (CommRingCat.of k), U.1) k := (Spec.preimage ρ).hom.toAlgebra
  have halg : Spec.map (CommRingCat.ofHom
      (algebraMap ↑Γ(Spec (CommRingCat.of k), U.1) k)) = ρ := by
    rw [show CommRingCat.ofHom (algebraMap ↑Γ(Spec (CommRingCat.of k), U.1) k) =
      Spec.preimage ρ from CommRingCat.ofHom_hom _, Spec.map_preimage]
  -- the base-changed curve over `k` and the comparison of the two pullback squares
  set W : WeierstrassCurve k :=
    W₀.map (algebraMap ↑Γ(Spec (CommRingCat.of k), U.1) k) with hW
  haveI hellW : W.IsElliptic := by rw [hW]; infer_instance
  have hpb : IsPullback
      (projModelBaseChange (algebraMap ↑Γ(Spec (CommRingCat.of k), U.1) k) W₀)
      (projModelπ W) (projModelπ W₀) ρ := by
    have h := isPullback_projModelBaseChange
      (R := ↑Γ(Spec (CommRingCat.of k), U.1)) (R' := k) W₀
    rwa [halg] at h
  have hsq2 : IsPullback (𝟙 (projModel W₀)) (projModelπ W₀ ≫ inv ρ)
      (projModelπ W₀) ρ := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    rw [Category.id_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  set θ : projModel W₀ ≅ projModel W := hsq2.isoIsPullback _ _ hpb with hθ
  have hθfst : θ.hom ≫
      projModelBaseChange (algebraMap ↑Γ(Spec (CommRingCat.of k), U.1) k) W₀ =
      𝟙 (projModel W₀) := hsq2.isoIsPullback_hom_fst _ _ hpb
  have hθπ : θ.hom ≫ projModelπ W = projModelπ W₀ ≫ inv ρ :=
    hsq2.isoIsPullback_hom_snd _ _ hpb
  have hpbcinv :
      projModelBaseChange (algebraMap ↑Γ(Spec (CommRingCat.of k), U.1) k) W₀ =
      θ.inv := (Iso.hom_comp_eq_id θ).mp hθfst
  have hzbc : projModelZero W ≫
      projModelBaseChange (algebraMap ↑Γ(Spec (CommRingCat.of k), U.1) k) W₀ =
      ρ ≫ projModelZero W₀ := by
    have h := projModelZero_baseChange
      (R := ↑Γ(Spec (CommRingCat.of k), U.1)) (R' := k) W₀
    rwa [halg] at h
  have hθz : projModelZero W₀ ≫ θ.hom = inv ρ ≫ projModelZero W := by
    rw [← cancel_epi ρ, IsIso.hom_inv_id_assoc, ← Category.assoc, ← hzbc,
      Category.assoc, hpbcinv, Iso.inv_hom_id, Category.comp_id]
  -- the inverse of the base identification, explicitly
  have hinvρ : inv ρ = U.2.isoSpec.inv ≫ U.1.ι :=
    IsIso.inv_eq_of_hom_inv_id (by
      rw [hρ, Category.assoc, ← Category.assoc U.2.isoSpec.hom, Iso.hom_inv_id,
        Category.id_comp, IsIso.inv_hom_id])
  -- assemble the pointed global model iso
  refine ⟨W, hellW, (asIso (pullback.fst E.π U.1.ι)).symm ≪≫ e ≪≫ θ, ?_, ?_⟩
  · -- π-compatibility
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc,
      Category.assoc, hθπ, ← Category.assoc e.hom (projModelπ W₀) (inv ρ), heπ, hinvρ,
      Category.assoc, Iso.hom_inv_id_assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  · -- zero-compatibility
    have h1 : E.zero ≫ inv (pullback.fst E.π U.1.ι) =
        inv U.1.ι ≫ pullback.lift (U.1.ι ≫ E.zero) (𝟙 _)
          (by rw [Category.assoc, E.zero_π, Category.comp_id, Category.id_comp]) := by
      rw [← cancel_mono (pullback.fst E.π U.1.ι), Category.assoc, Category.assoc,
        IsIso.inv_hom_id, Category.comp_id, pullback.lift_fst, ← Category.assoc,
        IsIso.inv_hom_id, Category.id_comp]
    have h2 : pullback.lift (U.1.ι ≫ E.zero) (𝟙 _)
        (by rw [Category.assoc, E.zero_π, Category.comp_id, Category.id_comp]) ≫ e.hom
        = U.2.isoSpec.hom ≫ projModelZero W₀ := by
      rw [← Iso.inv_comp_eq, ← Category.assoc]
      exact hez
    rw [Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, asIso_inv, ← Category.assoc, h1,
      Category.assoc, ← Category.assoc _ e.hom θ.hom, h2, Category.assoc, hθz,
      ← Category.assoc, ← hρ, IsIso.hom_inv_id_assoc]

end EllipticCurve

/-! ## [KVC-pts] — the geometric-point dictionary readouts over `Spec k` -/

section KVCPoints

variable {k : Type u} [Field k]

/-- **([KVC-pts], the `∞`-side)** A section of the projective model over `Spec k` whose
dictionary value is the group identity IS the zero section. -/
theorem sectionSpecPoint_eq_zeroSection_of_pointsEquiv_eq_zero
    (W : WeierstrassCurve k) [W.IsElliptic]
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (h : projModelPointsEquiv W k ⟨g, section_comp_projModelπ_specMap W g hgπ⟩ = 0) :
    g = Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫ projModelZero W :=
  congrArg Subtype.val
    ((projModelPointsEquiv W k).injective (h.trans (projModelPointsEquiv_zero W k).symm))

/-- **([KVC-pts], the affine side — normal form)** A section of the projective model
over `Spec k` whose dictionary value is the affine point `some x y` IS the evaluated
marked affine-point section `[x : y : 1]`. Via injectivity of `projModelPointsEquiv`
against the Stage-B fibre evaluation `projModelPointsEquiv_affineSectionSpecPoint`. -/
theorem sectionSpecPoint_eq_affineSection_of_pointsEquiv_eq_some
    (W : WeierstrassCurve k) [W.IsElliptic]
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (x y : k) (hxy : (W.baseChange k).toAffine.Nonsingular x y)
    (h : projModelPointsEquiv W k ⟨g, section_comp_projModelπ_specMap W g hgπ⟩ =
      WeierstrassCurve.Affine.Point.some x y hxy) :
    ∃ hEq : W.toAffine.Equation x y,
      g = Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫
        projModelAffineSection W x y hEq := by
  have hid : ∀ a : k, algebraMap k k a = a := fun a => by
    rw [Algebra.algebraMap_self, RingHom.id_apply]
  have hbc : W.baseChange k = W := by
    rw [show W.baseChange k = W.map (algebraMap k k) from rfl, Algebra.algebraMap_self,
      WeierstrassCurve.map_id]
  have hEq : W.toAffine.Equation x y := by
    have h1 : (W.baseChange k).toAffine.Equation x y := hxy.1
    rwa [hbc] at h1
  have hns : (W.baseChange k).toAffine.Nonsingular
      (algebraMap k k x) (algebraMap k k y) := by
    rwa [hid x, hid y]
  have h2 := projModelPointsEquiv_affineSectionSpecPoint W (K := k) x y hEq hns
  have hsome : WeierstrassCurve.Affine.Point.some (algebraMap k k x)
      (algebraMap k k y) hns = WeierstrassCurve.Affine.Point.some x y hxy := by
    have key : ∀ x' y' : k, x' = x → y' = y →
        ∀ hns' : (W.baseChange k).toAffine.Nonsingular x' y',
        WeierstrassCurve.Affine.Point.some x' y' hns' =
          WeierstrassCurve.Affine.Point.some x y hxy := by
      rintro x' y' rfl rfl hns'; rfl
    exact key _ _ (hid x) (hid y) hns
  exact ⟨hEq, congrArg Subtype.val ((projModelPointsEquiv W k).injective
    (h.trans (h2.trans hsome).symm))⟩

/-- **([KVC-pts] ★, the readout package)** A section of the projective model over
`Spec k` whose dictionary value is the affine point `some x y` lies in the `Z`-chart
and its coordinate-ring evaluations read exactly `(x, y)` — the master's
`hxpair`/`hypair`/`hxne` inputs in `zChartCoordEval` form. -/
theorem zChart_readout_of_pointsEquiv_eq_some
    (W : WeierstrassCurve k) [W.IsElliptic]
    (g : Spec (CommRingCat.of k) ⟶ projModel W)
    (hgπ : g ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)))
    (x y : k) (hxy : (W.baseChange k).toAffine.Nonsingular x y)
    (h : projModelPointsEquiv W k ⟨g, section_comp_projModelπ_specMap W g hgπ⟩ =
      WeierstrassCurve.Affine.Point.some x y hxy) :
    ∃ hmem : Set.range ⇑g.base ⊆ (Proj.basicOpen (quotientGrading (projIdeal W))
      ((quotientGradingHom (projIdeal W)) (MvPolynomial.X 2)) : Set (projModel W)),
      zChartCoordEval W g hmem (coordX W) = x ∧
        zChartCoordEval W g hmem (coordY W) = y := by
  obtain ⟨hEq, hg⟩ :=
    sectionSpecPoint_eq_affineSection_of_pointsEquiv_eq_some W g hgπ x y hxy h
  subst hg
  have hid : ∀ a : k, algebraMap k k a = a := fun a => by
    rw [Algebra.algebraMap_self, RingHom.id_apply]
  have hZ : InZChart W ⟨Spec.map (CommRingCat.ofHom (algebraMap k k)) ≫
      projModelAffineSection W x y hEq, section_comp_projModelπ_specMap W _ hgπ⟩ :=
    inZChart_affineSectionSpecPoint W k x y hEq
  have hmem := range_subset_of_inZChart W _ (section_comp_projModelπ_specMap W _ hgπ) hZ
  refine ⟨hmem, ?_, ?_⟩
  · have h0 := affineSectionSpecPoint_coord W (K := k) x y hEq ⟨0, by decide⟩
    have h1 := (zChartCoordEval_coordX W _ hgπ hmem hZ).trans h0
    rwa [show (![x, y, 1] (0 : Fin 3)) = x from rfl, hid x] at h1
  · have h0 := affineSectionSpecPoint_coord W (K := k) x y hEq ⟨1, by decide⟩
    have h1 := (zChartCoordEval_coordY W _ hgπ hmem hZ).trans h0
    rwa [show (![x, y, 1] (1 : Fin 3)) = y from rfl, hid y] at h1

end KVCPoints

/-! ## [KVC-conj] — conjugation transport through the model iso -/

section Conj

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R} {X : Scheme.{u}}

/-- **([KVC-conj])** Conjugation of a scheme automorphism through a model iso. -/
noncomputable def conjModelIso (ψ : X ≅ projModel W) (φ : X ≅ X) :
    projModel W ≅ projModel W :=
  ψ.symm ≪≫ φ ≪≫ ψ

@[simp] lemma conjModelIso_hom (ψ : X ≅ projModel W) (φ : X ≅ X) :
    (conjModelIso ψ φ).hom = ψ.inv ≫ φ.hom ≫ ψ.hom := rfl

/-- The conjugated automorphism is compatible with the structure morphism — the
master's `heπ` input. -/
lemma conjModelIso_comp_projModelπ {p : X ⟶ Spec (CommRingCat.of R)}
    (ψ : X ≅ projModel W) (hψπ : ψ.hom ≫ projModelπ W = p)
    (φ : X ≅ X) (hφπ : φ.hom ≫ p = p) :
    (conjModelIso ψ φ).hom ≫ projModelπ W = projModelπ W := by
  rw [conjModelIso_hom, Category.assoc, Category.assoc, hψπ, hφπ, ← hψπ,
    Iso.inv_hom_id_assoc]

/-- The conjugated automorphism fixes the zero section — the master's `hez` input. -/
lemma projModelZero_comp_conjModelIso {z : Spec (CommRingCat.of R) ⟶ X}
    (ψ : X ≅ projModel W) (hψz : z ≫ ψ.hom = projModelZero W)
    (φ : X ≅ X) (hφz : z ≫ φ.hom = z) :
    projModelZero W ≫ (conjModelIso ψ φ).hom = projModelZero W := by
  rw [conjModelIso_hom, ← hψz, Category.assoc, Iso.hom_inv_id_assoc,
    ← Category.assoc, hφz]

/-- Point-fixing transports along the conjugation: a `φ`-fixed morphism into `X`
conjugates to a fixed point of the conjugated automorphism. -/
lemma comp_conjModelIso_of_fix {T : Scheme.{u}} (ψ : X ≅ projModel W) (φ : X ≅ X)
    (u : T ⟶ X) (hu : u ≫ φ.hom = u) :
    (u ≫ ψ.hom) ≫ (conjModelIso ψ φ).hom = u ≫ ψ.hom := by
  rw [conjModelIso_hom, Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, hu]

/-- `= 𝟙` transports back through the conjugation. -/
lemma hom_eq_id_of_conjModelIso_eq_id (ψ : X ≅ projModel W) (φ : X ≅ X)
    (h : (conjModelIso ψ φ).hom = 𝟙 (projModel W)) : φ.hom = 𝟙 X := by
  have h2 : ψ.hom ≫ (conjModelIso ψ φ).hom ≫ ψ.inv = ψ.hom ≫ 𝟙 (projModel W) ≫ ψ.inv :=
    by rw [h]
  rw [conjModelIso_hom] at h2
  simpa using h2

end Conj

/-! ## [KVC-conj] — the record-side transport helpers -/

namespace EllipticCurve

variable {S : Scheme.{u}}

/-- Transport of the point group along an equality of base morphisms (the additive
form of `Equiv.subtypeEquivProp`; additivity by `point_add_val_congr_base`). -/
noncomputable def pointCongr {T : Scheme.{u}} (E : EllipticCurve S) {g g' : T ⟶ S}
    (h : g = g') : E.Point g ≃+ E.Point g' where
  toFun P := ⟨P.1, P.2.trans h⟩
  invFun P := ⟨P.1, P.2.trans h.symm⟩
  left_inv P := rfl
  right_inv P := rfl
  map_add' P Q := Subtype.ext
    (E.point_add_val_congr_base h P ⟨P.1, P.2.trans h⟩ Q ⟨Q.1, Q.2.trans h⟩ rfl rfl)

@[simp] lemma pointCongr_apply_coe {T : Scheme.{u}} (E : EllipticCurve S)
    {g g' : T ⟶ S} (h : g = g') (P : E.Point g) :
    ((E.pointCongr h P : E.Point g') : T ⟶ E.E) = (P : T ⟶ E.E) := rfl

/-- **([KVC-conj], record side)** A pointed endomorphism of `E/S` fixing the point `P`
fixes every `ℤ`-multiple of `P`: pointed ⟹ additive (`endMonHom`), and postcomposition
by an additive endomorphism is a monoid homomorphism of the point hom-groups. -/
theorem fixes_zsmul_of_fixes [IsLocallyNoetherian S] (E : EllipticCurve S)
    (ε : E.asOver ⟶ E.asOver) (hη : η[E.asOver] ≫ ε = η[E.asOver])
    (P : E.Point (𝟙 S))
    (hfix : (E.pointEquivOverHom (𝟙 S)) P ≫ ε = (E.pointEquivOverHom (𝟙 S)) P)
    (n : ℤ) :
    (E.pointEquivOverHom (𝟙 S)) (n • P) ≫ ε = (E.pointEquivOverHom (𝟙 S)) (n • P) := by
  letI : CommGroup (E.asOver ⟶ E.asOver) := Hom.commGroup
  letI : CommGroup (Over.mk (𝟙 S) ⟶ E.asOver) := Hom.commGroup
  haveI : IsMonHom ε := { one_hom := hη, mul_hom := E.endMonHom ε hη }
  have htrans : (E.pointEquivOverHom (𝟙 S)) (n • P) =
      ((E.pointEquivOverHom (𝟙 S)) P) ^ n := rfl
  have hmap := (IsMonHom.monoidHom ε (Over.mk (𝟙 S))).map_zpow
    ((E.pointEquivOverHom (𝟙 S)) P) n
  simp only [IsMonHom.monoidHom_apply] at hmap
  rw [htrans, hmap, hfix]

/-- A pointed endomorphism fixing `P` fixes `-P`. -/
theorem fixes_neg_of_fixes [IsLocallyNoetherian S] (E : EllipticCurve S)
    (ε : E.asOver ⟶ E.asOver) (hη : η[E.asOver] ≫ ε = η[E.asOver])
    (P : E.Point (𝟙 S))
    (hfix : (E.pointEquivOverHom (𝟙 S)) P ≫ ε = (E.pointEquivOverHom (𝟙 S)) P) :
    (E.pointEquivOverHom (𝟙 S)) (-P) ≫ ε = (E.pointEquivOverHom (𝟙 S)) (-P) := by
  have h := E.fixes_zsmul_of_fixes ε hη P hfix (-1)
  rwa [neg_one_zsmul] at h

/-! ## [KVC-drop-ins] — the F4 pin-shape corollaries -/

/-- **([KVC-drop-in A] ★★, the record-level keystone master)** Over a field, a pointed
automorphism `ε` of the working record `E` fixing a point `P` with `2 • P ≠ 0` and a
point `Q ∉ {0, P, -P}` is the identity. This is the KVC master
`pointedAuto_hom_eq_id_of_fixes_points` pulled through [KVC-model]+[KVC-conj]+[KVC-pts]:
the supply points are `{P, -P}` (the `±`-pair: same `x`, distinct `y` since `2 • P ≠ 0`)
and `Q` (distinct `x` by the `Y_eq_of_X_eq` dichotomy since `Q ≠ ±P`), with `-P`
automatically `ε`-fixed (`fixes_neg_of_fixes`). NO Hasse bound, NO degree theory, NO
algebraic closure.

The hH design (3) consumes this with its rank-2 torsion supply (independent `P`, `Q` in
`E[n](k̄)`, `n ∈ {3, 4}`); the hbound design (2) via the single-point corollary
`pointedAuto_eq_id_of_fixes_point_kvc`. -/
theorem pointedAuto_eq_id_of_fixes_points_kvc {k : Type u} [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (ε : E.asOver ⟶ E.asOver) (hIso : IsIso ε)
    (hη : η[E.asOver] ≫ ε = η[E.asOver])
    (P Q : E.Point (𝟙 (Spec (CommRingCat.of k))))
    (hP2 : (2 : ℤ) • P ≠ 0) (hQ0 : Q ≠ 0) (hQP : Q ≠ P) (hQPneg : Q ≠ -P)
    (hfixP : (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P ≫ ε =
      (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P)
    (hfixQ : (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) Q ≫ ε =
      (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) Q) :
    ε = 𝟙 E.asOver := by
  classical
  haveI : IsIso ε := hIso
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := by
    haveI : IsNoetherianRing k := inferInstance
    infer_instance
  obtain ⟨W, hell, ψ, hψπ, hψz⟩ := exists_projModelIso_of_field E
  haveI := hell
  -- [KVC-conj] the pointed record iso onto the model record
  have hΦw : ψ.hom ≫ (modelEllipticCurve W).asOver.hom = E.asOver.hom := hψπ
  set Φ : E.asOver ≅ (modelEllipticCurve W).asOver := Over.isoMk ψ hΦw with hΦ
  have hΦη : (η[E.asOver] : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ E.asOver) ≫ Φ.hom =
      η[(modelEllipticCurve W).asOver] := by
    apply Over.OverMorphism.ext
    rw [Over.comp_left, E.one_eq_zero, (modelEllipticCurve W).one_eq_zero]
    show ((𝟙_ (Over (Spec (CommRingCat.of k)))).hom ≫ E.zero) ≫ ψ.hom = _
    rw [Category.assoc, hψz]
    rfl
  have hΦμ := isMonHom_of_pointedIso_records E (modelEllipticCurve W) Φ hΦη
  -- [KVC-pts] the additive geometric-point dictionary
  have heq : 𝟙 (Spec (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  set Ψ : E.Point (𝟙 (Spec (CommRingCat.of k))) ≃+ (W.baseChange k).toAffine.Point :=
    ((pointAddEquiv Φ hΦμ (𝟙 (Spec (CommRingCat.of k)))).trans
      ((modelEllipticCurve W).pointCongr heq)).trans (modelPointAddEquiv W) with hΨ
  have hgπ : ∀ P' : E.Point (𝟙 (Spec (CommRingCat.of k))),
      (P'.1 ≫ ψ.hom) ≫ projModelπ W = 𝟙 (Spec (CommRingCat.of k)) := fun P' => by
    rw [Category.assoc, hψπ]; exact P'.2
  have hΨval : ∀ P' : E.Point (𝟙 (Spec (CommRingCat.of k))),
      Ψ P' = projModelPointsEquiv W k
        ⟨P'.1 ≫ ψ.hom, section_comp_projModelπ_specMap W _ (hgπ P')⟩ := fun P' => rfl
  -- the dictionary values of the supply points are affine
  have hP0 : P ≠ 0 := fun h0 => hP2 (by rw [h0, smul_zero])
  have hΨP0 : Ψ P ≠ 0 := fun h0 => hP0 ((AddEquiv.map_eq_zero_iff Ψ).mp h0)
  have hΨQ0 : Ψ Q ≠ 0 := fun h0 => hQ0 ((AddEquiv.map_eq_zero_iff Ψ).mp h0)
  have someCongr : ∀ x₁ y₁ x₂ y₂ : k, x₁ = x₂ → y₁ = y₂ →
      ∀ (h₁ : (W.baseChange k).toAffine.Nonsingular x₁ y₁)
        (h₂ : (W.baseChange k).toAffine.Nonsingular x₂ y₂),
      WeierstrassCurve.Affine.Point.some x₁ y₁ h₁ =
        WeierstrassCurve.Affine.Point.some x₂ y₂ h₂ := by
    rintro x₁ y₁ x₂ y₂ rfl rfl h₁ h₂; rfl
  rcases hPv : Ψ P with _ | ⟨x, y, hxy⟩
  · exact absurd hPv hΨP0
  rcases hQv : Ψ Q with _ | ⟨xQ, yQ, hxyQ⟩
  · exact absurd hQv hΨQ0
  -- the `±`-pair partner
  have hPneg : Ψ (-P) = WeierstrassCurve.Affine.Point.some x
      ((W.baseChange k).toAffine.negY x y)
      ((WeierstrassCurve.Affine.nonsingular_neg x y).mpr hxy) := by
    rw [map_neg, hPv, WeierstrassCurve.Affine.Point.neg_some]
  -- the coordinate configuration
  have hyneg : y ≠ (W.baseChange k).toAffine.negY x y := by
    intro hy
    apply hP2
    have h1 : Ψ (-P) = Ψ P := by
      rw [hPneg, hPv]
      exact someCongr _ _ _ _ rfl hy.symm _ _
    have h3 : P + -P = 0 := add_neg_cancel P
    rw [Ψ.injective h1] at h3
    rw [two_zsmul]
    exact h3
  have hxQne : x ≠ xQ := by
    intro hxx
    rcases WeierstrassCurve.Affine.Y_eq_of_X_eq hxyQ.1 hxy.1 hxx.symm with hyy | hyy
    · exact hQP (Ψ.injective (by
        rw [hQv, hPv]
        exact someCongr _ _ _ _ hxx.symm hyy _ _))
    · exact hQPneg (Ψ.injective (by
        rw [hQv, hPneg]
        exact someCongr _ _ _ _ hxx.symm hyy _ _))
  -- [KVC-pts] the readout packages for the three conjugated sections
  obtain ⟨hmemP, hPx, hPy⟩ := zChart_readout_of_pointsEquiv_eq_some W _ (hgπ P)
    x y hxy ((hΨval P).symm.trans hPv)
  obtain ⟨hmemN, hNx, hNy⟩ := zChart_readout_of_pointsEquiv_eq_some W _ (hgπ (-P))
    x ((W.baseChange k).toAffine.negY x y)
    ((WeierstrassCurve.Affine.nonsingular_neg x y).mpr hxy)
    ((hΨval (-P)).symm.trans hPneg)
  obtain ⟨hmemQ, hQx, hQy⟩ := zChart_readout_of_pointsEquiv_eq_some W _ (hgπ Q)
    xQ yQ hxyQ ((hΨval Q).symm.trans hQv)
  -- the scheme-level fixes
  have hfixNeg := E.fixes_neg_of_fixes ε hη P hfixP
  have hfixP' : P.1 ≫ ε.left = P.1 := by
    have h := congrArg CommaMorphism.left hfixP
    simp only [Over.comp_left, pointEquivOverHom, Equiv.coe_fn_mk, Over.homMk_left] at h
    exact h
  have hfixN' : (-P).1 ≫ ε.left = (-P).1 := by
    have h := congrArg CommaMorphism.left hfixNeg
    simp only [Over.comp_left, pointEquivOverHom, Equiv.coe_fn_mk, Over.homMk_left] at h
    exact h
  have hfixQ' : Q.1 ≫ ε.left = Q.1 := by
    have h := congrArg CommaMorphism.left hfixQ
    simp only [Over.comp_left, pointEquivOverHom, Equiv.coe_fn_mk, Over.homMk_left] at h
    exact h
  -- [KVC-conj] conjugate and fire the master
  set c : E.E ≅ E.E := schemeIsoOfOverIso (asIso ε) with hc
  have hcπ : c.hom ≫ E.π = E.π := Over.w ε
  have hcz : E.zero ≫ c.hom = E.zero := zero_comp_monHom ε hη
  have hmaster := pointedAuto_hom_eq_id_of_fixes_points W (conjModelIso ψ c)
    (conjModelIso_comp_projModelπ ψ hψπ c hcπ)
    (projModelZero_comp_conjModelIso ψ hψz c hcz)
    (P.1 ≫ ψ.hom) ((-P).1 ≫ ψ.hom) (Q.1 ≫ ψ.hom)
    (hgπ P) (hgπ (-P)) (hgπ Q) hmemP hmemN hmemQ
    (comp_conjModelIso_of_fix ψ c P.1 hfixP')
    (comp_conjModelIso_of_fix ψ c (-P).1 hfixN')
    (comp_conjModelIso_of_fix ψ c Q.1 hfixQ')
    (by rw [hPx, hNx]) (by rw [hPy, hNy]; exact hyneg) (by rw [hPx, hQx]; exact hxQne)
  have hchom : c.hom = 𝟙 E.E := hom_eq_id_of_conjModelIso_eq_id ψ c hmaster
  apply Over.OverMorphism.ext
  rw [Over.id_left]
  exact hchom

/-- **([KVC-drop-in B], the single-point cyclic supply — the hbound design (2))** Over
a field, a pointed automorphism fixing ONE point `P` with `2 • P ≠ 0` and `3 • P ≠ 0`
is the identity: the cyclic subgroup `⟨P⟩` supplies all three master points
(`{P, -P}` the pair, `2 • P` the distinct-`x` point, all `ε`-fixed by
`fixes_zsmul_of_fixes`). -/
theorem pointedAuto_eq_id_of_fixes_point_kvc {k : Type u} [Field k]
    (E : EllipticCurve (Spec (CommRingCat.of k)))
    (ε : E.asOver ⟶ E.asOver) (hIso : IsIso ε)
    (hη : η[E.asOver] ≫ ε = η[E.asOver])
    (P : E.Point (𝟙 (Spec (CommRingCat.of k))))
    (hP2 : (2 : ℤ) • P ≠ 0) (hP3 : (3 : ℤ) • P ≠ 0)
    (hfixP : (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P ≫ ε =
      (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P) :
    ε = 𝟙 E.asOver := by
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of k)) := by
    haveI : IsNoetherianRing k := inferInstance
    infer_instance
  have hP0 : P ≠ 0 := fun h0 => hP2 (by rw [h0, smul_zero])
  refine pointedAuto_eq_id_of_fixes_points_kvc E ε hIso hη P ((2 : ℤ) • P) hP2 hP2
    ?_ ?_ hfixP (E.fixes_zsmul_of_fixes ε hη P hfixP 2)
  · -- `2 • P ≠ P`
    intro h
    apply hP0
    have h1 : (2 : ℤ) • P - P = 0 := by rw [h]; exact sub_self P
    rwa [two_zsmul, add_sub_cancel_right] at h1
  · -- `2 • P ≠ -P`
    intro h
    apply hP3
    have h1 : (2 : ℤ) • P + P = 0 := by rw [h]; exact neg_add_cancel P
    calc (3 : ℤ) • P = (2 : ℤ) • P + P := by
          rw [show (3 : ℤ) = 2 + 1 by norm_num, add_zsmul, one_zsmul]
      _ = 0 := h1

/-- **([KVC-drop-in D], the full-torsion supply — the STRAND-3 degree-cone bypass)** Over
an algebraically closed field with `N ≥ 3` invertible, a pointed automorphism `ε` fixing
EVERY `N`-torsion point is the identity. This is the Hasse- and degree-free replacement
for `aut_endo_eq_one` at the sole degree-cone entry `gammaFullNaive_eq_refl_of_fix_sections`:
`E[N](k̄) ≅ (ℤ/N)²` (`torsion_geometricFibre_rank_two`) supplies a basis `P, Q`; for
`N ≥ 3` the standard basis has `2 • P ≠ 0` and `Q ∉ {0, P, -P}`, and both are `ε`-fixed by
hypothesis, so `pointedAuto_eq_id_of_fixes_points_kvc` closes. -/
theorem pointedAuto_eq_id_of_fixes_torsion_kvc {k : Type u} [Field k]
    [IsAlgClosed k] (E : EllipticCurve (Spec (CommRingCat.of k)))
    (ε : E.asOver ⟶ E.asOver) (hIso : IsIso ε)
    (hη : η[E.asOver] ≫ ε = η[E.asOver])
    (N : ℕ) [NeZero N] (hN : 3 ≤ N) (hNk : (N : k) ≠ 0)
    (hfix : ∀ x : E.Point (𝟙 (Spec (CommRingCat.of k))), (N : ℤ) • x = 0 →
      (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) x ≫ ε =
        (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) x) :
    ε = 𝟙 E.asOver := by
  classical
  obtain ⟨φ⟩ := E.torsion_geometricFibre_rank_two N k (𝟙 (Spec (CommRingCat.of k))) hNk
  set sP := φ.symm (Pi.single (0 : Fin 2) (1 : ZMod N)) with hsP
  set sQ := φ.symm (Pi.single (1 : Fin 2) (1 : ZMod N)) with hsQ
  have hφP : φ sP = Pi.single (0 : Fin 2) (1 : ZMod N) := φ.apply_symm_apply _
  have hφQ : φ sQ = Pi.single (1 : Fin 2) (1 : ZMod N) := φ.apply_symm_apply _
  have h1 : (1 : ZMod N) ≠ 0 := by
    rw [show (1 : ZMod N) = ((1 : ℕ) : ZMod N) by push_cast; ring, Ne,
      CharP.cast_eq_zero_iff (ZMod N) N]
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have h2 : (2 : ZMod N) ≠ 0 := by
    rw [show (2 : ZMod N) = ((2 : ℕ) : ZMod N) by push_cast; ring, Ne,
      CharP.cast_eq_zero_iff (ZMod N) N]
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  -- an element of the torsion submodule is zero iff its `φ`-image is zero
  have hzero : ∀ s : Submodule.torsionBy ℤ (E.Point (𝟙 (Spec (CommRingCat.of k)))) (N : ℤ),
      s.1 = 0 → φ s = 0 := by
    intro s hs
    rw [show s = 0 from Subtype.ext (by rw [hs, ZeroMemClass.coe_zero])]
    exact φ.map_zero
  have hPtor : (N : ℤ) • sP.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp sP.2
  have hQtor : (N : ℤ) • sQ.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp sQ.2
  refine pointedAuto_eq_id_of_fixes_points_kvc E ε hIso hη sP.1 sQ.1 ?_ ?_ ?_ ?_
    (hfix _ hPtor) (hfix _ hQtor)
  · -- `2 • P ≠ 0`
    intro h0
    apply h2
    have hsp0 : sP + sP = 0 := by
      apply Subtype.ext
      rw [AddMemClass.coe_add, ZeroMemClass.coe_zero, ← two_zsmul]
      exact h0
    have hz : (Pi.single (0 : Fin 2) (1 : ZMod N) : Fin 2 → ZMod N)
        + Pi.single (0 : Fin 2) (1 : ZMod N) = 0 := by
      rw [← hφP, ← φ.map_add, hsp0, φ.map_zero]
    have hev := congrFun hz (0 : Fin 2)
    simp only [Pi.add_apply, Pi.single_eq_same, Pi.zero_apply] at hev
    rw [show (2 : ZMod N) = 1 + 1 from by ring]
    exact hev
  · -- `Q ≠ 0`
    intro h0
    apply h1
    have hz : φ sQ = 0 := hzero _ h0
    rw [hφQ] at hz
    have hev := congrFun hz (1 : Fin 2)
    simpa using hev
  · -- `Q ≠ P`
    intro h0
    apply h1
    have hz : φ sQ = φ sP := congrArg φ (Subtype.ext h0)
    rw [hφP, hφQ] at hz
    have hev := congrFun hz (1 : Fin 2)
    simpa using hev
  · -- `Q ≠ -P`
    intro h0
    apply h1
    have hz : φ sQ = φ (-sP) := congrArg φ (Subtype.ext (by rw [h0, NegMemClass.coe_neg]))
    rw [hφQ, φ.map_neg, hφP] at hz
    have hev := congrFun hz (1 : Fin 2)
    simpa using hev

end EllipticCurve

/-! ## [KVC-drop-ins] — the literal `hbound` pin shapes -/

/-- **([KVC-drop-in C′], the per-`k` `hbound` shape — GammaHMaster:1206)** The
narrowed [RIG-2′] keystone contract at a fixed field: an ISO pointed `ε` fixing a point
whose first `N - 1` multiples are nonzero (`N ≥ 4`) is the identity. Consumable
verbatim as the `hbound` argument of `gammaOneDrinfeld_fix_absurd`. -/
theorem hbound_pointwise_of_kvc {k : Type u} [Field k] (N : ℕ) (hN : 4 ≤ N)
    (E : EllipticCurve (Spec (CommRingCat.of k))) :
    ∀ ε : E.asOver ⟶ E.asOver, IsIso ε → η[E.asOver] ≫ ε = η[E.asOver] →
      ∀ P : E.Point (𝟙 (Spec (CommRingCat.of k))),
        (∀ a : ℕ, 0 < a → a < N → (a : ℤ) • P ≠ 0) →
        (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P ≫ ε
          = (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P →
        ε = 𝟙 E.asOver := by
  intro ε hIso hη P hord hfix
  have h2 : (2 : ℤ) • P ≠ 0 := by
    have h := hord 2 (by norm_num) (by omega)
    rwa [Nat.cast_ofNat] at h
  have h3 : (3 : ℤ) • P ≠ 0 := by
    have h := hord 3 (by norm_num) (by omega)
    rwa [Nat.cast_ofNat] at h
  exact EllipticCurve.pointedAuto_eq_id_of_fixes_point_kvc E ε hIso hη P h2 h3 hfix

/-- **([KVC-drop-in C] ★★, the literal `hbound` pin — GammaHClosure:152,
GammaHMaster:1291/:1329/:1348)** The KM kernel-degree keystone `hbound` in its exact
∀-geometric-point pin shape, discharged unconditionally for `N ≥ 4` — NO Hasse, NO
degree theory (`[IsAlgClosed k]` is carried only to match the pin verbatim; the
mathematics needs none). The `sm` leg is not consumed. -/
theorem hbound_of_kvc (R : CommRingCat.{u}) (N : ℕ) (hN : 4 ≤ N) :
    ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (_ : Spec (CommRingCat.of k) ⟶ Spec R)
      (E : EllipticCurve (Spec (CommRingCat.of k)))
      (ε : E.asOver ⟶ E.asOver), IsIso ε → η[E.asOver] ≫ ε = η[E.asOver] →
      ∀ P : E.Point (𝟙 (Spec (CommRingCat.of k))),
        (∀ a : ℕ, 0 < a → a < N → (a : ℤ) • P ≠ 0) →
        (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P ≫ ε
          = (E.pointEquivOverHom (𝟙 (Spec (CommRingCat.of k)))) P →
        ε = 𝟙 E.asOver :=
  fun k _ _ _ E => hbound_pointwise_of_kvc N hN E

/-!
## [EDIT-SITE LIST] — the F4 pin-discharge map (LIST ONLY; no downstream file is
edited here)

The drop-ins above target the following pin sites (paths relative to
`projects/ModularCurves/ModularCurves/`). The F4 pin-discharge builder (fired per the
v10.328 FIRING RULE) consumes them as follows.

### hbound sites (design (2) — DISCHARGED OUTRIGHT by this file)

* `Moduli/GammaHClosure.lean:150-165`
  (`gammaOneDrinfeld_rigid_and_representable_of_hbound`): the `hbound` hypothesis is
  EXACTLY `hbound_of_kvc R N hN` (its `∀ k [Field k] [IsAlgClosed k] sm E ε …` shape
  matches verbatim, `hN : 4 ≤ N` available). Intended consumption: add an
  unconditional corollary
  `gammaOneDrinfeld_rigid_and_representable (N) [NeZero N] (hN : 4 ≤ N) (hinv) : … :=
    gammaOneDrinfeld_rigid_and_representable_of_hbound R N hN hinv
      (hbound_of_kvc R N hN)` — either in that file (needs import of this file; no
  cycle: this file imports nothing from `Moduli/`) or in the capstone.
* `Moduli/GammaHMaster.lean:1196-1211` (`gammaOneDrinfeld_fix_absurd`, per-`k`
  `hbound` argument at :1206): supply `hbound_pointwise_of_kvc N hN _`.
* `Moduli/GammaHMaster.lean:1290-1299` (`gammaOneDrinfeld_rigidNoeth`),
  `:1327-1339` (`gammaOneDrinfeld_rigid`), `:1346-1360`
  (`gammaOneDrinfeld_representable_prep`): same ∀-form pin — supply
  `hbound_of_kvc R N hN`; unpinned corollaries then state receipt 3's headline with
  the pin GONE (the T-D6b `HasExactOrder.pull_nsmul_ne_zero` box remains inside the
  statement chain, unaffected).

### hH sites (design (3) — the builder's remaining work, on top of drop-in A)

* `Moduli/GammaHMaster.lean:1124-1139` (`gammaH_rigidNoeth_of_orderOf`),
  `:1144-1158` (`gammaH_rigid_of_orderOf`), `:1167-1182`
  (`gammaH_representable_of_orderOf`): the `hH` pin (`e` base-identical EllObj
  self-iso, `e ≠ refl`, `isoPow e (orderOf γ) = refl → False`). Discharge route
  (v10.328 (3), with the unpinned corollary carrying
  `∀ γ : H, Nat.Coprime (orderOf γ) 6`): extract the pointed `Over`-auto `εO` from `e`
  as in `gammaOneDrinfeld_fix_absurd` (:1217-1275), take `e' := εO^(ord/p)` of prime
  order `p ≥ 5` (coprimality), let `e'` act on `E[n](k̄)` for `n := 3` (char `≠ 3`,
  `|GL₂(𝔽₃)| = 48`) or `n := 4` (char `3`, `|GL₂(ℤ/4)| = 96`); `gcd(p, 48·96) = 1`
  forces the action trivial, so `e'` fixes independent `P, Q ∈ E[n](k̄)` from the
  rank-2 supply (`torsion_geometricFibre_rank_two`); then
  **`EllipticCurve.pointedAuto_eq_id_of_fixes_points_kvc`** (drop-in A) with
  `hP2 : 2 • P ≠ 0` (P has order `n ∈ {3,4}` — for `n = 4` pick `P` of exact order 4),
  `hQ0/hQP/hQPneg` from independence, gives `e' = 𝟙`, contradicting `e ≠ refl` via
  primality. The supply lemmas (`fixes_zsmul_of_fixes`, `fixes_neg_of_fixes`,
  `pointCongr`) live in this file.

### engine-side receipt sites (context, NOT this file's targets)

* `Moduli/EllCategory.lean:293-298` (`representable_iff`, sorried `⇐`) and
  `:310-324` (`representable_iff_rigidNoeth`, sorried `⇐`): the shared KM 4.7.0
  engine gate (T-Q6d.γ/T-E14/T-E15 + recollement) — NOT touched by the KVC layer;
  after the F4 re-point plan (v10.327 (4)) these become one-line corollaries of the
  downstream-proved `⇐`.
* `Moduli/GammaHClosure.lean:119, :137` and `Moduli/GammaHMaster.lean:1180, :1358`
  (the four `representable_iff_rigidNoeth _ _ .mpr` code sites): the 4-site re-point
  of the F4 plan consumes the engine `⇐` downstream; the KVC drop-ins above remove
  the `hbound` pin from :1358's input and (via the hH discharge) the `hH` pin from
  :1180's, so the re-pointed receipts 3/5/6 close pin-free once the engine lands.
-/

end ModularCurves
