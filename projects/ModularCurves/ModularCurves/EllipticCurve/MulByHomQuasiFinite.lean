/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.RecordGroupUnique
import ModularCurves.LevelStructure.IsoTransport
import ModularCurves.ForMathlib.GeometricFibreComparison
import ModularCurves.ForMathlib.JacobsonPointCount
import HasseWeil.NTorsion.TorsionGeneralN

/-!
# Quasi-finiteness of `[N]` for `N` invertible (BB-QF, invertible case)

The KM 2.3.1 quasi-finiteness box, in the invertible-`N` strength consumed by the
`Y₁(N)` MASTER trail: `[N] : E ⟶ E` is locally quasi-finite when `N` is invertible on the
base.

Route: `LocallyQuasiFinite.of_finite_preimage_singleton` reduces to topological fibre
finiteness; the fibre over `y` is covered by the `k̄`-points of the base-changed fibre at a
geometric point over `y` (`Scheme.Pullback.exists_preimage_pullback`), which biject with a
coset of the `N`-torsion of the geometric point group (`pullbackSndSectionEquiv` + the
`smul`/`mulByHom` dictionary); the torsion is finite by the chart reduction — the atlas
chart pins the base change of `E` to the projective model (`chartOverIso`, whose pointed
group-compatibility is the K3 primitive `isMonHom_of_pointedIso_records`), the model's
geometric points are the affine Weierstrass points (`geomFibrePointAddEquiv`, [T-B6′]), and
HasseWeil's `torsion_genN_addEquiv` counts those (`E[N] ≃+ (ZMod N)²`, the cross-project
anchor). Finitely many sections force a finite fibre space by the Jacobson bridge
(`Scheme.finite_of_finite_sections`).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj WeierstrassCurve

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- Torsion subgroups transport along additive equivalences. -/
def torsionByCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A ≃+ B) (n : ℤ) :
    Submodule.torsionBy ℤ A n ≃ Submodule.torsionBy ℤ B n where
  toFun x := ⟨φ x.1, by
    rw [Submodule.mem_torsionBy_iff]
    have h0 : n • x.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
    have h := congrArg φ h0
    rwa [map_zsmul, map_zero] at h⟩
  invFun y := ⟨φ.symm y.1, by
    rw [Submodule.mem_torsionBy_iff]
    have h0 : n • y.1 = 0 := (Submodule.mem_torsionBy_iff _ _).mp y.2
    have h := congrArg φ.symm h0
    rwa [map_zsmul, map_zero] at h⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (φ.apply_symm_apply y.1)

/-- **(BB-QF core count)** The `N`-torsion of the point group of `E` at a geometric point
is finite, for `N` nonzero in the (algebraically closed) residue field. Chart reduction to
the projective model, then [T-B6′] + HasseWeil. -/
theorem point_torsionBy_finite_of_geometric {k : Type u} [Field k] [IsAlgClosed k]
    (t : Spec (CommRingCat.of k) ⟶ S) (N : ℕ) (hN : (N : k) ≠ 0) :
    Finite (Submodule.torsionBy ℤ (E.Point t) (N : ℤ)) := by
  classical
  -- the chart at the image of the geometric point
  set A := E.toEllipticCurveGeom.atlas with hA
  obtain ⟨pt⟩ : Nonempty ↑(Spec (CommRingCat.of k)) := inferInstance
  obtain ⟨i, hi⟩ := A.covers (t.base pt)
  -- `t` factors through the chart base
  have hrange : Set.range t.base ⊆ Set.range (A.U i).1.ι.base := by
    rintro _ ⟨p, rfl⟩
    have hp : t.base p = t.base pt := by
      have : p = pt := Subsingleton.elim _ _
      rw [this]
    rw [hp, Scheme.Opens.range_ι]
    exact hi
  set tU : Spec (CommRingCat.of k) ⟶ (A.U i).1 :=
    IsOpenImmersion.lift (A.U i).1.ι t hrange with htU
  have htUfac : tU ≫ (A.U i).1.ι = t := IsOpenImmersion.lift_fac _ _ hrange
  set tB : Spec (CommRingCat.of k) ⟶ Spec Γ(S, (A.U i).1) :=
    tU ≫ (A.U i).2.isoSpec.hom with htB
  have htfac : tB ≫ chartToBase A i = t := by
    rw [htB, chartToBase, Category.assoc, Iso.hom_inv_id_assoc, htUfac]
  -- transport the point group to the chart base change, then to the model record
  haveI := A.elliptic i
  have eq1 : (E.baseChange (chartToBase A i)).Point tB ≃+ E.Point t :=
    htfac ▸ Point.baseChangeEquiv E (chartToBase A i) tB
  -- the pointed chart isomorphism of records, and its K3 group-compatibility
  have hη : (η[(E.baseChange (chartToBase A i)).asOver] :
      𝟙_ (Over (Spec Γ(S, (A.U i).1))) ⟶ (E.baseChange (chartToBase A i)).asOver) ≫
      (chartOverIso A i).hom = η[(modelEllipticCurve (A.W i)).asOver] :=
    chartGrp_one A E.grp E.one_eq_zero i
  have hμ := isMonHom_of_pointedIso_records (E.baseChange (chartToBase A i))
    (modelEllipticCurve (A.W i)) (chartOverIso A i) hη
  have eq2 : (E.baseChange (chartToBase A i)).Point tB ≃+
      (modelEllipticCurve (A.W i)).Point tB :=
    pointAddEquiv (chartOverIso A i) hμ tB
  -- the geometric-fibre dictionary onto the affine Weierstrass points
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective tB
  letI : Algebra ↑Γ(S, (A.U i).1) k := ψ.hom.toAlgebra
  haveI : ((A.W i).baseChange k).IsElliptic := by
    constructor
    have hΔ : ((A.W i).baseChange k).Δ = algebraMap _ k (A.W i).Δ := by
      show ((A.W i).map _).Δ = _
      rw [WeierstrassCurve.map_Δ]
    rw [hΔ]
    exact (A.W i).isUnit_Δ.map _
  have eq3 : (modelEllipticCurve (A.W i)).Point (geomPoint ↑Γ(S, (A.U i).1) k) ≃+
      ((A.W i).baseChange k).toAffine.Point :=
    geomFibrePointAddEquiv (A.W i) (modelEllipticCurve (A.W i)) rfl
      ((Category.id_comp _).symm) (Category.comp_id _) k
  have hgeom : geomPoint ↑Γ(S, (A.U i).1) k = tB := by
    rw [geomPoint, ← hψ]
    rfl
  -- assemble the equivalence chain and transport torsion finiteness from HasseWeil
  have eqchain : E.Point t ≃+ ((A.W i).baseChange k).toAffine.Point :=
    (eq1.symm.trans eq2).trans (hgeom ▸ eq3)
  have hker : ∀ P : ((A.W i).baseChange k).toAffine.Point,
      P ∈ Submodule.torsionBy ℤ (((A.W i).baseChange k).toAffine.Point) (N : ℤ) ↔
      P ∈ HasseWeil.torsionSubgroup ((A.W i).baseChange k).toAffine (N : ℤ) := by
    intro P
    rw [Submodule.mem_torsionBy_iff, HasseWeil.mem_torsionSubgroup]
  haveI : NeZero N := ⟨fun h => hN (by rw [h, Nat.cast_zero])⟩
  haveI hfin : Finite (HasseWeil.torsionSubgroup ((A.W i).baseChange k).toAffine (N : ℤ)) :=
    Finite.of_equiv _ (HasseWeil.NTorsion.torsion_genN_addEquiv
      ((A.W i).baseChange k).toAffine N hN).symm.toEquiv
  haveI hfin2 : Finite
      (Submodule.torsionBy ℤ (((A.W i).baseChange k).toAffine.Point) (N : ℤ)) := by
    refine Finite.of_injective
      (fun x => (⟨x.1, (hker x.1).mp x.2⟩ :
        HasseWeil.torsionSubgroup ((A.W i).baseChange k).toAffine (N : ℤ)))
      (fun x y hxy => Subtype.ext (congrArg Subtype.val hxy))
  exact Finite.of_equiv _ (torsionByCongr eqchain (N : ℤ)).symm

end EllipticCurve

end ModularCurves
