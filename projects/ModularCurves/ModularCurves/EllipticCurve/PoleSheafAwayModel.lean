import ModularCurves.EllipticCurve.PoleSheafAwaySections
import ModularCurves.EllipticCurve.PoleSheafModel

/-!
# The marked-point complement of a Weierstrass model

This file identifies the complement of the zero section in a projective Weierstrass model
with its standard affine `Z`-chart.
-/

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

variable {R : Type u} [CommRing R]

/-- A residue-field fibre of a separated morphism is separated over the residue field. -/
theorem isSeparated_fiberToSpecResidueField
    {E S : Scheme.{u}} (π : E ⟶ S) [IsSeparated π] (s : S) :
    IsSeparated (π.fiberToSpecResidueField s) := by
  change IsSeparated (pullback.snd π (S.fromSpecResidueField s))
  exact AlgebraicGeometry.IsSeparated.isStableUnderBaseChange.of_isPullback
    (IsPullback.of_hasPullback π (S.fromSpecResidueField s))
    (show IsSeparated π from inferInstance)

/-- The complement of the zero section in a projective Weierstrass model is its affine
`Z`-chart. -/
theorem sectionAway_projModelZero_eq_zChart (W : WeierstrassCurve R) :
    sectionAway (projModelZero W) (projModelZero_projModelπ W) =
      (projModelZChart W : (projModel W).Opens) := by
  ext p
  change p ∉ Set.range ⇑(projModelZero W) ↔
    p ∈ (projModelZChart W : (projModel W).Opens)
  constructor
  · intro hp
    by_contra hpZ
    exact hp (mem_range_zero_of_not_mem_zChart hpZ)
  · intro hpZ hp
    exact not_mem_zChart_of_mem_range_zero hp hpZ

/-- A pointed isomorphism pulls the complement of the target section back to the complement
of the source section. -/
theorem preimage_sectionAway_eq_of_pointedIso
    {X Y T : Scheme.{u}} {πX : X ⟶ T} {πY : Y ⟶ T}
    [IsSeparated πX] [IsSeparated πY]
    (zX : T ⟶ X) (hzX : zX ≫ πX = 𝟙 T)
    (zY : T ⟶ Y) (hzY : zY ≫ πY = 𝟙 T)
    (e : X ≅ Y) (hez : zX ≫ e.hom = zY) :
    e.hom ⁻¹ᵁ sectionAway zY hzY = sectionAway zX hzX := by
  ext x
  change e.hom.base x ∉ Set.range ⇑zY ↔ x ∉ Set.range ⇑zX
  constructor
  · intro h hx
    obtain ⟨t, rfl⟩ := hx
    apply h
    refine ⟨t, ?_⟩
    symm
    rw [show e.hom.base (zX t) = (zX ≫ e.hom) t from rfl, hez]
  · intro h hx
    obtain ⟨t, ht⟩ := hx
    apply h
    refine ⟨t, e.hom.homeomorph.injective ?_⟩
    change e.hom.base (zX t) = e.hom.base x
    rw [show e.hom.base (zX t) = (zX ≫ e.hom) t from rfl, hez, ht]

/-- Pulling back the complement of a section to a residue fibre gives the complement of the
induced fibre point. -/
theorem fiberι_preimage_sectionAway
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    (z : S ⟶ E) (hz : z ≫ π = 𝟙 S) (s : S) :
    (π.fiberι s) ⁻¹ᵁ sectionAway z hz =
      @sectionAway (π.fiber s) (Spec (S.residueField s))
        (π.fiberToSpecResidueField s) (isSeparated_fiberToSpecResidueField π s)
        (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _) := by
  letI : IsSeparated (π.fiberToSpecResidueField s) :=
    isSeparated_fiberToSpecResidueField π s
  have hsec : sectionFiberPoint π z hz s ≫ π.fiberι s =
      S.fromSpecResidueField s ≫ z := by
    exact pullback.lift_fst _ _ _
  ext x
  change π.fiberι s x ∉ Set.range ⇑z ↔
    x ∉ Set.range ⇑(sectionFiberPoint π z hz s)
  constructor
  · intro hx hxs
    obtain ⟨t, rfl⟩ := hxs
    apply hx
    refine ⟨s, ?_⟩
    symm
    change (sectionFiberPoint π z hz s ≫ π.fiberι s) t = z s
    rw [hsec]
    simp
  · intro hx hxs
    obtain ⟨t, ht⟩ := hxs
    apply hx
    let p : Spec (S.residueField s) := IsLocalRing.closedPoint _
    refine ⟨p, (π.fiberι s).isEmbedding.injective ?_⟩
    have hxs_base : π (π.fiberι s x) = s := by
      change (π.fiberι s ≫ π) x = s
      rw [π.fiber_fac]
      simp
    have hts : s = t := by
      calc
        s = π (π.fiberι s x) := hxs_base.symm
        _ = π (z t) := congrArg (fun q : E => π q) ht.symm
        _ = t := by
          change (z ≫ π) t = t
          rw [hz]
          rfl
    subst t
    calc
      π.fiberι s (sectionFiberPoint π z hz s p) = z s := by
        change (sectionFiberPoint π z hz s ≫ π.fiberι s) p = z s
        rw [hsec]
        simp
      _ = π.fiberι s x := ht

/-- In every residue fibre of a fibrewise-elliptic family, the complement of the marked
point is affine. -/
theorem FibrewiseElliptic.sectionAway_fiber_isAffineOpen
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    {z : S ⟶ E} {hz : z ≫ π = 𝟙 S}
    (h : FibrewiseElliptic π z hz) (s : S) :
    IsAffineOpen
      (@sectionAway (π.fiber s) (Spec (S.residueField s))
        (π.fiberToSpecResidueField s) (isSeparated_fiberToSpecResidueField π s)
        (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _)) := by
  letI : IsSeparated (π.fiberToSpecResidueField s) :=
    isSeparated_fiberToSpecResidueField π s
  obtain ⟨W, _, e, _, hez⟩ := h s
  rw [← preimage_sectionAway_eq_of_pointedIso
    (πX := π.fiberToSpecResidueField s) (πY := projModelπ W)
    (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _)
    (projModelZero W) (projModelZero_projModelπ W) e hez,
    sectionAway_projModelZero_eq_zChart]
  exact (projModelZChart W).2.preimage_of_isIso e.hom

/-- Every residue fibre of the family obtained by removing the marked section is affine. -/
theorem FibrewiseElliptic.sectionAway_comp_fiber_isAffine
    {E S : Scheme.{u}} {π : E ⟶ S} [IsSeparated π]
    {z : S ⟶ E} {hz : z ≫ π = 𝟙 S}
    (h : FibrewiseElliptic π z hz) (s : S) :
    IsAffine (((sectionAway z hz).ι ≫ π).fiber s) := by
  letI : IsSeparated (π.fiberToSpecResidueField s) :=
    isSeparated_fiberToSpecResidueField π s
  let V := @sectionAway (π.fiber s) (Spec (S.residueField s))
    (π.fiberToSpecResidueField s) (isSeparated_fiberToSpecResidueField π s)
    (sectionFiberPoint π z hz s) (pullback.lift_snd _ _ _)
  have hV : IsAffineOpen V := h.sectionAway_fiber_isAffineOpen s
  let j : pullback (sectionAway z hz).ι (pullback.fst π (S.fromSpecResidueField s)) ⟶
      pullback π (S.fromSpecResidueField s) :=
    pullback.snd (sectionAway z hz).ι (pullback.fst π (S.fromSpecResidueField s))
  have hj : j.opensRange = V := by
    dsimp only [j, V]
    rw [Scheme.Hom.opensRange_pullbackSnd, Scheme.Opens.opensRange_ι]
    exact fiberι_preimage_sectionAway z hz s
  have hj_set : Set.range ⇑j = Set.range ⇑V.ι := by
    rw [← Scheme.Hom.coe_opensRange, hj, Scheme.Opens.range_ι]
    rfl
  have hVι : IsOpenImmersion V.ι :=
    @Scheme.Opens.instIsOpenImmersionι _ V
  have hjι : IsOpenImmersion j := by
    dsimp only [j]
    infer_instance
  let e : pullback (sectionAway z hz).ι (pullback.fst π (S.fromSpecResidueField s)) ≅
      V.toScheme := @IsOpenImmersion.isoOfRangeEq _ _ _ j V.ι hjι hVι hj_set
  haveI : IsAffine V.toScheme := hV
  haveI : IsAffine
      (pullback (sectionAway z hz).ι (pullback.fst π (S.fromSpecResidueField s))) :=
    @IsAffine.of_isIso _ _ e.hom (by infer_instance) inferInstance
  change IsAffine (pullback ((sectionAway z hz).ι ≫ π) (S.fromSpecResidueField s))
  let e' :=
    pullbackRightPullbackFstIso π (S.fromSpecResidueField s) (sectionAway z hz).ι
  exact @IsAffine.of_isIso _ _ e'.inv (by infer_instance) inferInstance

end

end ModularCurves
