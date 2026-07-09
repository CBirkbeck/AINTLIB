import ModularCurves.EllipticCurve.GroupLawConstruction

/-!
# Field-points of the two-law multiplication (T-W7.0c·c6, [C6-SPECPOINTS])

The evaluation layer for `mulModelHom_specPoints`: a field-valued point of `E ×_R E` factors
through one of the two regularity opens (`blOpen_cover` + the unique point of `Spec K`), where
the multiplication restricts to the corresponding Bosma–Lenstra law.
-/

open MvPolynomial ModularCurves AlgebraicGeometry CategoryTheory Limits WeierstrassCurve

universe u

namespace ModularCurves

variable {R : Type u} [CommRing R]

/-- [C6-a] A field-valued point of `E ×_R E` factors through `blOpenZ` or `blOpenY`. -/
theorem specPoint_factors_blOpenZ_or_blOpenY (W : WeierstrassCurve R) [W.IsElliptic]
    (K : Type u) [Field K] [Algebra R K]
    (g : Spec (CommRingCat.of K) ⟶ pullback (projModelπ W) (projModelπ W)) :
    (∃ h, h ≫ (blOpenZ W).ι = g) ∨ (∃ h, h ≫ (blOpenY W).ι = g) := by
  have hmem : g.base default ∈ blOpenZ W ⊔ blOpenY W := by
    rw [blOpen_cover]
    trivial
  have hrange : Set.range g.base = {g.base default} := Set.range_unique
  rcases (TopologicalSpace.Opens.mem_sup).mp hmem with hx | hx
  · refine Or.inl ⟨IsOpenImmersion.lift (blOpenZ W).ι g ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rw [Scheme.Opens.range_ι, hrange]
    exact Set.singleton_subset_iff.mpr hx
  · refine Or.inr ⟨IsOpenImmersion.lift (blOpenY W).ι g ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rw [Scheme.Opens.range_ι, hrange]
    exact Set.singleton_subset_iff.mpr hx

/-- [C6-b, Z] Through a blOpenZ factorisation, `mulModelHom` evaluates as `addOnZ`. -/
theorem specPoint_mulModelHom_of_blOpenZ (W : WeierstrassCurve R) [W.IsElliptic]
    {K : Type u} [CommRing K]
    {g : Spec (CommRingCat.of K) ⟶ pullback (projModelπ W) (projModelπ W)}
    {h : Spec (CommRingCat.of K) ⟶ (blOpenZ W).toScheme} (hh : h ≫ (blOpenZ W).ι = g) :
    g ≫ mulModelHom W = h ≫ addOnZ W := by
  rw [← hh, Category.assoc, blOpenZ_ι_mulModelHom]

/-- [C6-b, Y] Mirror. -/
theorem specPoint_mulModelHom_of_blOpenY (W : WeierstrassCurve R) [W.IsElliptic]
    {K : Type u} [CommRing K]
    {g : Spec (CommRingCat.of K) ⟶ pullback (projModelπ W) (projModelπ W)}
    {h : Spec (CommRingCat.of K) ⟶ (blOpenY W).toScheme} (hh : h ≫ (blOpenY W).ι = g) :
    g ≫ mulModelHom W = h ≫ addOnY W := by
  rw [← hh, Category.assoc, blOpenY_ι_mulModelHom]
/-- **[C6-U] THE ATLAS BRIDGE** — over the ULift universal atlas, GLC's base-change
multiplication IS the glued two-law multiplication. -/
theorem mulModelHom_universalWeierstrassLocU :
    mulModelHom universalWeierstrassLocU.{u} =
      WeierstrassCurve.Projective.mulModelHom universalWeierstrassLocU.{u}
        universalWeierstrassLocU.isUnit_Δ := by
  rw [mulModelHom]
  rw [mulModelHomBC_congr (classifyRingHomU universalWeierstrassLocU.{u})
    (RingHom.id _) classifyRingHomU_universalWeierstrassLocU
    universalWeierstrassLocU universalWeierstrassLocU.isUnit_Δ
    universalWeierstrassLocU (universalWeierstrassLocU_map_classifyRingHomU _) rfl]
  exact mulModelHomBC_id universalWeierstrassLocU universalWeierstrassLocU.isUnit_Δ
end ModularCurves
