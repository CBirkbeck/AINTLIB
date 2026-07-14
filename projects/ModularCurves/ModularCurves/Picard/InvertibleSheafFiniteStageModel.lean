import ModularCurves.ForMathlib.ProperAffineIntersectionModel
import ModularCurves.ForMathlib.FinitePresentationFunctorCover
import ModularCurves.Picard.InvertibleSheafCocycle
import ModularCurves.Picard.InvertibleSheafFiniteAffineCover

/-!
# Finite-stage models adapted to invertible sheaves

An invertible sheaf on a proper family admits a finite affine trivializing cover. The same
cover can be used to spread the family's complete affine-intersection diagram to a finite
stage of a filtered presentation of the affine base.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

private theorem topIso_hom_naturality
    {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) :
    (X.homOfLE hVU).appTop ≫ V.topIso.hom =
      U.topIso.hom ≫ X.presheaf.map (homOfLE hVU).op := by
  exact (Scheme.restrictFunctorΓ (X := X)).hom.naturality (homOfLE hVU).op

private theorem topIso_inv_naturality
    {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) :
    U.topIso.inv ≫ (X.homOfLE hVU).appTop =
      X.presheaf.map (homOfLE hVU).op ≫ V.topIso.inv := by
  calc
    U.topIso.inv ≫ (X.homOfLE hVU).appTop =
        (U.topIso.inv ≫ (X.homOfLE hVU).appTop) ≫
          (V.topIso.hom ≫ V.topIso.inv) := by
            rw [V.topIso.hom_inv_id, Category.comp_id]
    _ = U.topIso.inv ≫
        ((X.homOfLE hVU).appTop ≫ V.topIso.hom) ≫ V.topIso.inv := by
          simp only [Category.assoc]
    _ = U.topIso.inv ≫
        (U.topIso.hom ≫ X.presheaf.map (homOfLE hVU).op) ≫
          V.topIso.inv := by
            rw [topIso_hom_naturality hVU]
    _ = X.presheaf.map (homOfLE hVU).op ≫ V.topIso.inv := by
      simpa only [Category.assoc] using U.topIso.inv_hom_id_assoc
        (X.presheaf.map (homOfLE hVU).op ≫ V.topIso.inv)

private theorem finiteIntersectionOpen_le
    {X : Scheme.{u}} {J : Type u} (U : J → X.Opens)
    (s : Finset J) {i : J} (hi : i ∈ s) :
    X.finiteIntersectionOpen U s ≤ U i := by
  rw [← X.finiteIntersectionOpen_singleton U i]
  exact X.finiteIntersectionOpen_antitone U
    (Finset.singleton_subset_iff.mpr hi)

/-- The transition unit between two chosen trivializations, transported to a nonempty
object of the affine-intersection coordinate-ring functor. -/
noncomputable def affineIntersectionTransitionUnit
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (s : Finset J) (hs : s.Nonempty) (i j : J) (hi : i ∈ s) (hj : j ∈ s) :
    ((π.affineIntersectionFunctor U).obj s)ˣ :=
  let V := X.finiteIntersectionOpen U s
  Units.map (π.finiteIntersectionRingIso U s hs).hom.hom.toMonoidHom
    (Units.map V.topIso.inv.hom.toMonoidHom
      (trivializingCoverTransitionUnitOn U e V i j
        (finiteIntersectionOpen_le U s hi) (finiteIntersectionOpen_le U s hj)))

/-- The transition unit in the canonical pair object of the affine-intersection functor. -/
noncomputable def affineIntersectionPairTransitionUnit
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (i j : J) :
    ((π.affineIntersectionFunctor U).obj
      (Scheme.GlueData.affineIntersectionPairIndex i j))ˣ :=
  affineIntersectionTransitionUnit π U e
    (Scheme.GlueData.affineIntersectionPairIndex i j) (by
      classical
      simp [Scheme.GlueData.affineIntersectionPairIndex])
    i j (by
      classical
      simp [Scheme.GlueData.affineIntersectionPairIndex]) (by
      classical
      simp [Scheme.GlueData.affineIntersectionPairIndex])

/-- Multiplicative descent data on the pair and triple objects of an affine-intersection
algebra functor. -/
structure AffineIntersectionUnitCocycle
    {A J : Type u} [CommRing A] (F : Finset J ⥤ CommAlgCat.{u} A) where
  transition : ∀ i j,
    (F.obj (Scheme.GlueData.affineIntersectionPairIndex i j))ˣ
  cocycle : ∀ i j k,
    Units.map (F.map
          (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).hom.toMonoidHom
        (transition i j) *
      Units.map (F.map
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).hom.toMonoidHom
        (transition j k) =
    Units.map (F.map
        (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).hom.toMonoidHom
      (transition i k)

/-- Affine-intersection transition units are compatible with every restriction map in
the coordinate-ring functor. -/
theorem affineIntersectionTransitionUnit_map
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    {s q : Finset J} (f : s ⟶ q) (hs : s.Nonempty) (hq : q.Nonempty)
    (i j : J) (hi : i ∈ s) (hj : j ∈ s) :
    Units.map ((π.affineIntersectionFunctor U).map f).hom.toMonoidHom
        (affineIntersectionTransitionUnit π U e s hs i j hi hj) =
      affineIntersectionTransitionUnit π U e q hq i j
        (leOfHom f hi) (leOfHom f hj) := by
  let V := X.finiteIntersectionOpen U s
  let W := X.finiteIntersectionOpen U q
  let hWV : W ≤ V := X.finiteIntersectionOpen_antitone U (leOfHom f)
  let hVi : V ≤ U i := finiteIntersectionOpen_le U s hi
  let hVj : V ≤ U j := finiteIntersectionOpen_le U s hj
  let gV := trivializingCoverTransitionUnitOn U e V i j hVi hVj
  let gW := trivializingCoverTransitionUnitOn U e W i j
    (hWV.trans hVi) (hWV.trans hVj)
  have hg : Units.map
      (X.presheaf.map (homOfLE hWV).op).hom.toMonoidHom gV = gW := by
    exact trivializingCoverTransitionUnitOn_restrict U e hWV i j hVi hVj
  have htop := ConcreteCategory.congr_hom (topIso_inv_naturality hWV) (gV : Γ(X, V))
  have hrestrict :
      (π.finiteIntersectionRestriction U (leOfHom f)).hom
          (V.topIso.inv.hom (gV : Γ(X, V))) =
        W.topIso.inv.hom (gW : Γ(X, W)) := by
    calc
      (π.finiteIntersectionRestriction U (leOfHom f)).hom
          (V.topIso.inv.hom (gV : Γ(X, V))) =
        (X.homOfLE hWV).appTop.hom (V.topIso.inv.hom (gV : Γ(X, V))) :=
          ConcreteCategory.congr_hom
            (π.finiteIntersectionRestriction_forget U f)
              (V.topIso.inv.hom (gV : Γ(X, V)))
      _ = W.topIso.inv.hom
          ((X.presheaf.map (homOfLE hWV).op).hom (gV : Γ(X, V))) := htop
      _ = W.topIso.inv.hom (gW : Γ(X, W)) := by
        exact congrArg W.topIso.inv.hom (congrArg Units.val hg)
  apply Units.ext
  change ((π.affineIntersectionFunctor U).map f).hom
      ((π.finiteIntersectionRingIso U s hs).hom.hom
        (V.topIso.inv.hom (gV : Γ(X, V)))) =
    (π.finiteIntersectionRingIso U q hq).hom.hom
      (W.topIso.inv.hom (gW : Γ(X, W)))
  exact (ConcreteCategory.congr_hom
    (π.finiteIntersectionRestriction_ringIso U f hs hq)
      (V.topIso.inv.hom (gV : Γ(X, V)))).symm.trans
        (congrArg (π.finiteIntersectionRingIso U q hq).hom.hom hrestrict)

/-- Affine-intersection transition units satisfy the multiplicative transition law in
every nonempty functor object. -/
theorem affineIntersectionTransitionUnit_trans
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (s : Finset J) (hs : s.Nonempty) (i j k : J)
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) :
    affineIntersectionTransitionUnit π U e s hs i j hi hj *
        affineIntersectionTransitionUnit π U e s hs j k hj hk =
      affineIntersectionTransitionUnit π U e s hs i k hi hk := by
  let V := X.finiteIntersectionOpen U s
  let hVi : V ≤ U i := finiteIntersectionOpen_le U s hi
  let hVj : V ≤ U j := finiteIntersectionOpen_le U s hj
  let hVk : V ≤ U k := finiteIntersectionOpen_le U s hk
  let g (a b : J) (ha : V ≤ U a) (hb : V ≤ U b) :=
    trivializingCoverTransitionUnitOn U e V a b ha hb
  apply Units.ext
  change (π.finiteIntersectionRingIso U s hs).hom.hom
        (V.topIso.inv.hom (g i j hVi hVj : Γ(X, V))) *
      (π.finiteIntersectionRingIso U s hs).hom.hom
        (V.topIso.inv.hom (g j k hVj hVk : Γ(X, V))) =
    (π.finiteIntersectionRingIso U s hs).hom.hom
      (V.topIso.inv.hom (g i k hVi hVk : Γ(X, V)))
  calc
    _ = (π.finiteIntersectionRingIso U s hs).hom.hom
        (V.topIso.inv.hom (g i j hVi hVj : Γ(X, V)) *
          V.topIso.inv.hom (g j k hVj hVk : Γ(X, V))) :=
      ((π.finiteIntersectionRingIso U s hs).hom.hom.map_mul _ _).symm
    _ = (π.finiteIntersectionRingIso U s hs).hom.hom
        (V.topIso.inv.hom
          ((g i j hVi hVj : Γ(X, V)) * (g j k hVj hVk : Γ(X, V)))) :=
      congrArg (π.finiteIntersectionRingIso U s hs).hom.hom
        (V.topIso.inv.hom.map_mul _ _).symm
    _ = _ := congrArg
      (fun z => (π.finiteIntersectionRingIso U s hs).hom.hom (V.topIso.inv.hom z))
      (congrArg Units.val
        (trivializingCoverTransitionUnitOn_trans U e V i j k hVi hVj hVk))

/-- The pair-object transition units satisfy the Cech equation after applying the three
canonical restriction maps to a triple object. -/
theorem affineIntersectionTransitionUnit_cocycle
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme)
    (i j k : J) :
    Units.map ((π.affineIntersectionFunctor U).map
          (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).hom.toMonoidHom
        (affineIntersectionPairTransitionUnit π U e i j) *
      Units.map ((π.affineIntersectionFunctor U).map
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).hom.toMonoidHom
        (affineIntersectionPairTransitionUnit π U e j k) =
    Units.map ((π.affineIntersectionFunctor U).map
        (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).hom.toMonoidHom
      (affineIntersectionPairTransitionUnit π U e i k) := by
  classical
  unfold affineIntersectionPairTransitionUnit
  rw [affineIntersectionTransitionUnit_map π U e
      (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k),
    affineIntersectionTransitionUnit_map π U e
      (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k),
    affineIntersectionTransitionUnit_map π U e
      (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)]
  exact affineIntersectionTransitionUnit_trans π U e
    (Scheme.GlueData.affineIntersectionTripleIndex i j k) (by
      simp [Scheme.GlueData.affineIntersectionTripleIndex])
    i j k (by
      simp [Scheme.GlueData.affineIntersectionTripleIndex]) (by
      simp [Scheme.GlueData.affineIntersectionTripleIndex]) (by
      simp [Scheme.GlueData.affineIntersectionTripleIndex])

/-- The pair transition units of an invertible sheaf form multiplicative descent data on
the affine-intersection algebra functor. -/
noncomputable def affineIntersectionUnitCocycle
    {X S : Scheme.{u}} (π : X ⟶ S) {N : X.Modules} {J : Type u}
    (U : J → X.Opens)
    (e : ∀ i, N.restrict (U i).ι ≅ unitObj (U i).toScheme) :
    AffineIntersectionUnitCocycle (π.affineIntersectionFunctor U) where
  transition := affineIntersectionPairTransitionUnit π U e
  cocycle := affineIntersectionTransitionUnit_cocycle π U e

/-- An invertible sheaf on a proper, locally finitely presented family admits a finite affine
trivializing cover whose affine-intersection model recovers the family after base change. -/
theorem IsInvertible.exists_affineIntersectionModelBaseChangeIso_of_isProper
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    {X S : Scheme.{u}} {π : X ⟶ S} [IsProper π] [IsAffine S]
    [LocallyOfFinitePresentation π] [Algebra R Γ(S, (⊤ : S.Opens))]
    {uS : ∀ i, 𝒮 i →ₐ[R] Γ(S, (⊤ : S.Opens))}
    {N : X.Modules} (hN : IsInvertible N)
    (H : Algebra.IsFilteredAlgColimit R 𝒮 t Γ(S, (⊤ : S.Opens)) uS) :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens)
      (_ : IsOpenCover U) (_ : ∀ i, IsAffineOpen (U i))
      (_ : ∀ i, Nonempty (N.restrict (U i).ι ≅ unitObj (U i).toScheme))
      (_ : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
      (M : Algebra.SpreadData.FunctorModel (π.affineIntersectionFunctor U) H)
      (hopenM : Scheme.GlueData.IsOpenAffineIntersectionFunctor M.toFunctor)
      (hpushM : Scheme.GlueData.IsPushoutAffineIntersectionFunctor M.toFunctor),
      Nonempty
        (letI : Algebra (𝒮 M.stage) Γ(S, (⊤ : S.Opens)) :=
            (uS M.stage).toRingHom.toAlgebra;
          CategoryTheory.Limits.pullback
              (Scheme.GlueData.affineIntersectionToSpec M.toFunctor hopenM hpushM)
              (Spec.map (CommRingCat.ofHom
                (algebraMap (𝒮 M.stage) Γ(S, (⊤ : S.Opens))))) ≅ X) := by
  letI : CompactSpace X := (quasiCompact_iff_compactSpace π).mp inferInstance
  obtain ⟨J, hJ, U, hcover, hUaff, htriv⟩ :=
    hN.exists_finite_affine_trivializingCover
  letI : Finite J := hJ
  obtain ⟨hU, M, hopenM, hpushM, e⟩ :=
    π.exists_affineIntersectionModelBaseChangeIso_of_isProper_of_cover
      H U hcover hUaff
  exact ⟨J, hJ, U, hcover, hUaff, htriv, hU, M, hopenM, hpushM, e⟩

end

end AlgebraicGeometry.Scheme.Modules
