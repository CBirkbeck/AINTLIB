/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.RecordGroupUnique
import ModularCurves.LevelStructure.IsoTransport
import ModularCurves.ForMathlib.GeometricFibreComparison
import ModularCurves.ForMathlib.JacobsonPointCount
import ModularCurves.ForMathlib.TorsionByEquiv
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

/- `torsionByCongr` RELOCATED to `ForMathlib/TorsionByEquiv.lean` as
`Submodule.torsionByCongr` (#6996; statement byte-identical, proof golfed) — a general
`AddCommGroup` fact with no elliptic-curve content. -/

/-- **(BB-QF core count)** The `N`-torsion of the point group of `E` at a geometric point
is finite, for `N` nonzero in the (algebraically closed) residue field. Chart reduction to
the projective model, then [T-B6′] + HasseWeil. -/
theorem Point.torsionBy_finite_of_geometric {k : Type u} [Field k] [IsAlgClosed k]
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
  exact Finite.of_equiv _
    ((Submodule.torsionByCongr eqchain (N : ℤ)).trans (Equiv.subtypeEquivRight hker)).symm

/-- The `N`-division points `h : Spec K ⟶ E.E` of a geometric point `g` (sections with
`h ≫ [N] = g`) form a finite set, for `N` nonzero in the algebraically closed field `K`:
any two differ by an `N`-torsion point, and the `N`-torsion at a geometric point is finite
(`Point.torsionBy_finite_of_geometric`). Extracted from
`MulByHom.locallyQuasiFinite_of_nIsInvertible`. -/
private lemma finite_sections_mulByHom {K : Type u} [Field K] [IsAlgClosed K]
    (N : ℕ) (hNk : (N : K) ≠ 0) (g : Spec (CommRingCat.of K) ⟶ E.E) :
    Finite {h : Spec (CommRingCat.of K) ⟶ E.E // h ≫ E.mulByHom N = g} := by
  by_cases hne : Nonempty {h : Spec (CommRingCat.of K) ⟶ E.E // h ≫ E.mulByHom N = g}
  · obtain ⟨h₀⟩ := hne
    set t : Spec (CommRingCat.of K) ⟶ S := g ≫ E.π with ht
    have hpt : ∀ hh : {h : Spec (CommRingCat.of K) ⟶ E.E // h ≫ E.mulByHom N = g},
        hh.1 ≫ E.π = t := by
      rintro ⟨hv, hp⟩
      show hv ≫ E.π = t
      rw [ht, ← hp, Category.assoc, E.mulByHom_π]
    have hsmul : ∀ hh : {h : Spec (CommRingCat.of K) ⟶ E.E // h ≫ E.mulByHom N = g},
        ((N : ℤ) • (⟨hh.1, hpt hh⟩ : E.Point t) : E.Point t) = ⟨g, rfl⟩ := fun hh => by
      apply Subtype.ext
      rw [E.point_smul_eq_comp_mulBy]
      exact hh.2
    haveI := Point.torsionBy_finite_of_geometric E t N hNk
    refine Finite.of_injective (fun hh => (⟨(⟨hh.1, hpt hh⟩ : E.Point t) -
      (⟨h₀.1, hpt h₀⟩ : E.Point t), ?_⟩ :
        Submodule.torsionBy ℤ (E.Point t) (N : ℤ))) ?_
    · rw [Submodule.mem_torsionBy_iff, smul_sub, hsmul hh, hsmul h₀, sub_self]
    · intro h₁ h₂ h12
      have h3 := congrArg Subtype.val h12
      have h4 : (⟨h₁.1, hpt h₁⟩ : E.Point t) = ⟨h₂.1, hpt h₂⟩ :=
        sub_left_injective (G := E.Point t) h3
      have h5 : h₁.1 = h₂.1 := congrArg (fun P : E.Point t => P.1) h4
      exact Subtype.ext h5
  · haveI := not_nonempty_iff.mp hne
    infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- **(BB-QF, invertible case — KM 2.3.1 quasi-finiteness)** `[N] : E ⟶ E` is locally
quasi-finite when `N` is invertible on the base. -/
theorem MulByHom.locallyQuasiFinite_of_nIsInvertible (N : ℕ) [NeZero N]
    (h : NIsInvertible S N) : LocallyQuasiFinite (E.mulByHom N) := by
  classical
  haveI : Smooth E.π := SmoothOfRelativeDimension.smooth (n := 1) E.π
  haveI := MulByHom.locallyOfFinitePresentation E N
  haveI hlft : LocallyOfFiniteType (E.mulByHom N) := inferInstance
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ (fun y => ?_)
  -- the geometric point over `y`
  set k : Type u := AlgebraicClosure ↑(E.E.residueField y) with hk
  set yg : Spec (CommRingCat.of k) ⟶ E.E :=
    Spec.map (CommRingCat.ofHom (algebraMap ↑(E.E.residueField y) k)) ≫
      E.E.fromSpecResidueField y with hyg
  have hygy : ∀ p, yg.base p = y := fun p => by
    rw [hyg, Scheme.Hom.comp_apply]
    have h2 := Scheme.range_fromSpecResidueField (X := E.E) y
    have h3 : (E.E.fromSpecResidueField y).base
        ((Spec.map (CommRingCat.ofHom (algebraMap ↑(E.E.residueField y) k))).base p) ∈
        ({y} : Set E.E) := h2 ▸ Set.mem_range_self _
    exact h3
  -- `N` is invertible in `k`
  have hNk : (N : k) ≠ 0 := by
    have hEE : NIsInvertible E.E N := by
      have h2 := h.map (E.π.appTop).hom
      rwa [map_natCast] at h2
    have h1 : IsUnit (N : ↑(E.E.residueField y)) := by
      have h1' := ((E.E.presheaf.germ ⊤ y trivial) ≫ E.E.residue y).hom.isUnit_map hEE
      rwa [map_natCast] at h1'
    have h2 := h1.map (algebraMap ↑(E.E.residueField y) k)
    rw [map_natCast] at h2
    exact isUnit_iff_ne_zero.mp h2
  -- the preimage is the range of the first projection of the geometric fibre
  have hpre : (E.mulByHom N).base ⁻¹' {y} =
      Set.range (pullback.fst (E.mulByHom N) yg).base := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨pt⟩ : Nonempty ↑(Spec (CommRingCat.of k)) := inferInstance
      obtain ⟨z, hz1, hz2⟩ := Scheme.Pullback.exists_preimage_pullback x pt
        (by rw [Set.mem_preimage, Set.mem_singleton_iff] at hx; rw [hx, hygy pt])
      exact ⟨z, hz1⟩
    · rintro _ ⟨z, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      have hc : (pullback.fst (E.mulByHom N) yg ≫ E.mulByHom N).base z =
          (pullback.snd (E.mulByHom N) yg ≫ yg).base z := by
        rw [pullback.condition]
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at hc
      rw [hc, hygy]
  rw [hpre]
  -- the geometric fibre has finitely many sections, hence finite space
  haveI : LocallyOfFiniteType (pullback.snd (E.mulByHom N) yg) :=
    MorphismProperty.pullback_snd _ _ hlft
  haveI hsol : Finite {h : Spec (CommRingCat.of k) ⟶ E.E // h ≫ E.mulByHom N = yg} :=
    E.finite_sections_mulByHom N hNk yg
  haveI hFfin : Finite ↑(pullback (E.mulByHom N) yg) := by
    refine Scheme.finite_of_finite_sections (pullback.snd (E.mulByHom N) yg) ?_
    exact Finite.of_equiv _ (Scheme.pullbackSndSectionEquiv (E.mulByHom N) yg).symm
  exact Set.finite_range _

/-- **(KM 2.3.1 finiteness, invertible case)** `[N]` is finite when `N` is invertible:
proper + quasi-finite via Zariski's Main Theorem. -/
theorem MulByHom.isFinite_of_nIsInvertible (N : ℕ) [NeZero N] (h : NIsInvertible S N) :
    IsFinite (E.mulByHom N) := by
  haveI := MulByHom.locallyQuasiFinite_of_nIsInvertible E N h
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

set_option backward.isDefEq.respectTransparency false in
/-- **(T-B4 finiteness, invertible case)** `E[N] ⟶ S` is finite when `N` is invertible. -/
theorem Torsionπ.isFinite_of_nIsInvertible (N : ℕ) [NeZero N] (h : NIsInvertible S N) :
    IsFinite (E.torsionπ N) :=
  MorphismProperty.pullback_snd _ _ (MulByHom.isFinite_of_nIsInvertible E N h)

end EllipticCurve

end ModularCurves
