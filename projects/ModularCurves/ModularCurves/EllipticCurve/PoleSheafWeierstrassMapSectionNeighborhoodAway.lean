import ModularCurves.EllipticCurve.PoleSheafWeierstrassMapGlobalFinite
import ModularCurves.ForMathlib.AwayMapBasicOpen
import ModularCurves.ForMathlib.ResLEIsIso

/-!
# The punctured comparison on the affine section neighborhood

The punctured Weierstrass comparison identifies the away localizations of
the coordinate rings on the canonical affine section neighborhood.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace ModularCurves

noncomputable section

/-- A finite comparison that is an isomorphism over the `Z`-chart induces a
bijective away map on the canonical affine section-neighborhood rings. -/
theorem projModelMap_sectionNeighborhood_awayMap_bijective
    {R : Type u} [CommRing R] {C : Scheme.{u}}
    (W : WeierstrassCurve R) (F : C ⟶ projModel W)
    [IsFinite F]
    (V : C.Opens)
    (hpre : F ⁻¹ᵁ (projModelZChart W : (projModel W).Opens) = V)
    [IsIso
      (F.resLE (projModelZChart W : (projModel W).Opens)
        V (le_of_eq hpre.symm))] :
    Function.Bijective
      (Localization.awayMap
        (F.appLE (projModelSectionNeighborhood W)
          (F ⁻¹ᵁ (projModelSectionNeighborhood W :
            (projModel W).Opens)) le_rfl).hom
        (projModelSectionRoot W)) := by
  let N : (projModel W).Opens := projModelSectionNeighborhood W
  let P : C.Opens := F ⁻¹ᵁ N
  let r : Γ(projModel W, N) := projModelSectionRoot W
  let D : (projModel W).Opens := (projModel W).basicOpen r
  let Q : C.Opens :=
    C.basicOpen (F.appLE N P le_rfl r)
  have hN : IsAffineOpen N := (projModelSectionNeighborhood W).2
  have hP : IsAffineOpen P := hN.preimage F
  have hDN : D ≤ N := by
    dsimp only [D, N, r]
    rw [← projModelPoleOverlap_eq_basicOpen_sectionRoot W]
    exact projModelPoleOverlap_le_sectionNeighborhood W
  have hDZ :
      D ≤ (projModelZChart W : (projModel W).Opens) := by
    dsimp only [D, r]
    rw [← projModelPoleOverlap_eq_basicOpen_sectionRoot W]
    exact projModelPoleOverlap_le_ZChart W
  have hQ :
      Q = V ⊓ F ⁻¹ᵁ D := by
    calc
      Q = P ⊓ F ⁻¹ᵁ D := by
        dsimp only [Q, P, D]
        exact Scheme.basicOpen_appLE F
          (F ⁻¹ᵁ N) N le_rfl r
      _ = F ⁻¹ᵁ D :=
        inf_eq_right.mpr (F.preimage_mono hDN)
      _ = V ⊓ F ⁻¹ᵁ D := by
        symm
        apply inf_eq_right.mpr
        rw [← hpre]
        exact F.preimage_mono hDZ
  haveI hSmall :
      IsIso
        (F.resLE D Q
          (by rw [hQ]; exact inf_le_right)) :=
    F.resLE_isIso_of_le_of_resLE_isIso
      (le_of_eq hpre.symm) hDZ hQ
  exact
    F.awayMap_appLE_bijective_of_resLE_basicOpen_isIso
      hN hP le_rfl r

end

end ModularCurves
