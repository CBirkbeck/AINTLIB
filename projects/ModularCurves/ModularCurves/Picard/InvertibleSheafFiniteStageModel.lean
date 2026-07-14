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

private theorem functorMapUnits_injective_of_retraction
    {A J : Type u} [CommRing A] (F : Finset J ⥤ CommAlgCat.{u} A)
    {s q : Finset J} (f : s ⟶ q) (g : q ⟶ s) :
    Function.Injective (Units.map (F.map f).hom.toMonoidHom) := by
  apply Units.map_injective
  intro x y hxy
  calc
    x = (F.map g).hom ((F.map f).hom x) := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp]
      have hfg : f ≫ g = 𝟙 s := Subsingleton.elim _ _
      rw [hfg, F.map_id]
      rfl
    _ = (F.map g).hom ((F.map f).hom y) := congrArg (F.map g).hom hxy
    _ = y := by
      rw [← ConcreteCategory.comp_apply, ← F.map_comp]
      have hfg : f ≫ g = 𝟙 s := Subsingleton.elim _ _
      rw [hfg, F.map_id]
      rfl

/-- The transition unit from a chart to itself is trivial. -/
@[simp]
theorem AffineIntersectionUnitCocycle.transition_self
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F) (i : J) :
    c.transition i i = 1 := by
  classical
  let f := Scheme.GlueData.affineIntersectionPairToTripleLeft i i i
  let g : Scheme.GlueData.affineIntersectionTripleIndex i i i ⟶
      Scheme.GlueData.affineIntersectionPairIndex i i := homOfLE (by
        simp [Scheme.GlueData.affineIntersectionPairIndex,
          Scheme.GlueData.affineIntersectionTripleIndex])
  apply functorMapUnits_injective_of_retraction F f g
  have hc := c.cocycle i i i
  have hmiddle :
      Scheme.GlueData.affineIntersectionPairToTripleMiddle i i i = f :=
    Subsingleton.elim _ _
  have hright :
      Scheme.GlueData.affineIntersectionPairToTripleRight i i i = f :=
    Subsingleton.elim _ _
  rw [hmiddle, hright] at hc
  rw [map_one]
  apply mul_left_cancel (a := Units.map (F.map f).hom.toMonoidHom (c.transition i i))
  simpa only [mul_one] using hc

/-- Reversing an ordered pair inverts its transition unit after transport along the
canonical pair-swap map. -/
theorem AffineIntersectionUnitCocycle.transition_mul_swap
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F) (i j : J) :
    c.transition i j *
        Units.map (F.map
          (Scheme.GlueData.affineIntersectionPairSwap i j)).hom.toMonoidHom
          (c.transition j i) = 1 := by
  classical
  let f := Scheme.GlueData.affineIntersectionPairToTripleLeft i j i
  let g : Scheme.GlueData.affineIntersectionTripleIndex i j i ⟶
      Scheme.GlueData.affineIntersectionPairIndex i j := homOfLE (by
        intro x hx
        simpa [Scheme.GlueData.affineIntersectionPairIndex,
          Scheme.GlueData.affineIntersectionTripleIndex, or_comm] using hx)
  apply functorMapUnits_injective_of_retraction F f g
  rw [map_mul, map_one]
  have hc := c.cocycle i j i
  have hmiddle :
      Scheme.GlueData.affineIntersectionPairSwap i j ≫ f =
        Scheme.GlueData.affineIntersectionPairToTripleMiddle i j i :=
    Subsingleton.elim _ _
  have hswap :
      Units.map (F.map f).hom.toMonoidHom
          (Units.map (F.map
            (Scheme.GlueData.affineIntersectionPairSwap i j)).hom.toMonoidHom
              (c.transition j i)) =
        Units.map (F.map
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j i)).hom.toMonoidHom
            (c.transition j i) := by
    apply Units.ext
    change (F.map f).hom
        ((F.map (Scheme.GlueData.affineIntersectionPairSwap i j)).hom
          (c.transition j i : F.obj
            (Scheme.GlueData.affineIntersectionPairIndex j i))) =
      (F.map (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j i)).hom
        (c.transition j i : F.obj
          (Scheme.GlueData.affineIntersectionPairIndex j i))
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, hmiddle]
  rw [hswap]
  rw [c.transition_self i, map_one] at hc
  exact hc

/-- The transition unit on the reversed overlap is the inverse transition unit after
transport to the original ordered overlap. -/
theorem AffineIntersectionUnitCocycle.transition_swap
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F) (i j : J) :
    Units.map (F.map
        (Scheme.GlueData.affineIntersectionPairSwap i j)).hom.toMonoidHom
        (c.transition j i) = (c.transition i j)⁻¹ :=
  eq_inv_of_mul_eq_one_right (c.transition_mul_swap i j)

private theorem ΓSpecUnit_naturality
    {R S : CommRingCat.{u}} (f : R ⟶ S) (r : Rˣ) :
    Units.map (Spec.map f).appTop.hom.toMonoidHom
        (Units.map (Scheme.ΓSpecIso R).inv.hom.toMonoidHom r) =
      Units.map (Scheme.ΓSpecIso S).inv.hom.toMonoidHom
        (Units.map f.hom.toMonoidHom r) := by
  apply Units.ext
  exact (ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality f) (r : R)).symm

/-- A transition unit regarded as an invertible global function on its affine overlap
scheme. -/
noncomputable def AffineIntersectionUnitCocycle.overlapTransitionSection
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F) (i j : J) :
    Γ(Scheme.GlueData.affineIntersectionOverlap F i j, ⊤)ˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of
    (F.obj (Scheme.GlueData.affineIntersectionPairIndex i j)))).inv.hom.toMonoidHom
      (c.transition i j)

/-- The overlap transition section from a chart to itself is one. -/
@[simp]
theorem AffineIntersectionUnitCocycle.overlapTransitionSection_self
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F) (i : J) :
    c.overlapTransitionSection i i = 1 := by
  rw [overlapTransitionSection, c.transition_self, map_one]

/-- Pulling a reversed overlap transition section across the canonical pair-swap gives
the inverse transition section. -/
theorem AffineIntersectionUnitCocycle.overlapTransitionSection_swap
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F) (i j : J) :
    Units.map (Spec.map (CommRingCat.ofHom ((F.map
        (Scheme.GlueData.affineIntersectionPairSwap i j)).hom.toRingHom))).appTop.hom.toMonoidHom
        (c.overlapTransitionSection j i) =
      (c.overlapTransitionSection i j)⁻¹ := by
  rw [overlapTransitionSection, ΓSpecUnit_naturality]
  change Units.map (Scheme.ΓSpecIso (CommRingCat.of
      (F.obj (Scheme.GlueData.affineIntersectionPairIndex i j)))).inv.hom.toMonoidHom
      (Units.map (F.map
        (Scheme.GlueData.affineIntersectionPairSwap i j)).hom.toMonoidHom
          (c.transition j i)) =
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of
      (F.obj (Scheme.GlueData.affineIntersectionPairIndex i j)))).inv.hom.toMonoidHom
      (c.transition i j))⁻¹
  rw [c.transition_swap, map_inv]

/-- The overlap transition sections satisfy the multiplicative Cech equation on the
canonical affine triple intersection. -/
theorem AffineIntersectionUnitCocycle.overlapTransitionSection_cocycle
    {A J : Type u} [CommRing A] {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F) (i j k : J) :
    Units.map (Spec.map (CommRingCat.ofHom ((F.map
          (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).hom.toRingHom))).appTop.hom.toMonoidHom
        (c.overlapTransitionSection i j) *
      Units.map (Spec.map (CommRingCat.ofHom ((F.map
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).hom.toRingHom))).appTop.hom.toMonoidHom
        (c.overlapTransitionSection j k) =
    Units.map (Spec.map (CommRingCat.ofHom ((F.map
        (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).hom.toRingHom))).appTop.hom.toMonoidHom
      (c.overlapTransitionSection i k) := by
  rw [overlapTransitionSection, overlapTransitionSection,
    overlapTransitionSection, ΓSpecUnit_naturality, ΓSpecUnit_naturality,
    ΓSpecUnit_naturality]
  change Units.map (Scheme.ΓSpecIso (CommRingCat.of
      (F.obj (Scheme.GlueData.affineIntersectionTripleIndex i j k)))).inv.hom.toMonoidHom
      (Units.map (F.map
        (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).hom.toMonoidHom
          (c.transition i j)) *
      Units.map (Scheme.ΓSpecIso (CommRingCat.of
        (F.obj (Scheme.GlueData.affineIntersectionTripleIndex i j k)))).inv.hom.toMonoidHom
        (Units.map (F.map
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).hom.toMonoidHom
            (c.transition j k)) =
    Units.map (Scheme.ΓSpecIso (CommRingCat.of
      (F.obj (Scheme.GlueData.affineIntersectionTripleIndex i j k)))).inv.hom.toMonoidHom
      (Units.map (F.map
        (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).hom.toMonoidHom
          (c.transition i k))
  rw [← map_mul, c.cocycle]

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

/-- A finite affine-intersection unit cocycle over a filtered colimit descends to a common
finite stage, retaining both its transition units and all triple equations. -/
theorem AffineIntersectionUnitCocycle.exists_modelAtLaterStage
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    {A : Type u} [CommRing A] [Algebra R A]
    {uA : ∀ i, 𝒮 i →ₐ[R] A} {J : Type u} [Finite J]
    {F : Finset J ⥤ CommAlgCat.{u} A}
    (c : AffineIntersectionUnitCocycle F)
    (H : Algebra.IsFilteredAlgColimit R 𝒮 t A uA)
    (M : Algebra.SpreadData.FunctorModel F H) :
    ∃ (q : ι) (hiq : M.stage ≤ q) (r : ι) (hqr : q ≤ r)
        (c_r : AffineIntersectionUnitCocycle
          (((M.mapToStage hiq).mapToStage hqr).toFunctor)),
      ∀ i j, Units.map (((M.mapToStage hiq).object
          (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit H
            ⟨r, ((M.mapToStage hiq).le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr⟩).toMonoidHom
          (c_r.transition i j) = c.transition i j := by
  classical
  let pairObj : J × J → Finset J := fun p =>
    Scheme.GlueData.affineIntersectionPairIndex p.1 p.2
  let pairUnit : ∀ p, (F.obj (pairObj p))ˣ := fun p =>
    c.transition p.1 p.2
  obtain ⟨q, hiq, gq, hgq⟩ :=
    M.exists_common_unit_liftAtLaterStage pairObj pairUnit
  let Mq := M.mapToStage hiq
  let g (i j : J) :
      ((Mq.object
        (Scheme.GlueData.affineIntersectionPairIndex i j)).spreadStage (t := t)
          (Mq.le_stage (Scheme.GlueData.affineIntersectionPairIndex i j)))ˣ :=
    gq (i, j)
  have hg (i j : J) :
      Units.map ((Mq.object
          (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit H
            ⟨Mq.stage, Mq.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i j)⟩).toMonoidHom
          (g i j) = c.transition i j := by
    apply Units.ext
    change (M.object
        (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit H
          ⟨q, (M.le_stage
            (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hiq⟩
          (gq (i, j) : (M.object
            (Scheme.GlueData.affineIntersectionPairIndex i j)).spreadStage (t := t)
              ((M.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hiq)) =
      (c.transition i j : F.obj
        (Scheme.GlueData.affineIntersectionPairIndex i j))
    exact congrArg Units.val (hgq (i, j))
  let tripleObj : J × (J × J) → Finset J := fun p =>
    Scheme.GlueData.affineIntersectionTripleIndex p.1 p.2.1 p.2.2
  let x : ∀ p : J × (J × J),
      ((Mq.object (tripleObj p)).spreadStage (t := t)
        (Mq.le_stage (tripleObj p)))ˣ := fun p =>
    Units.map (Mq.map
          (Scheme.GlueData.affineIntersectionPairToTripleLeft
            p.1 p.2.1 p.2.2)).toMonoidHom (g p.1 p.2.1) *
      Units.map (Mq.map
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle
            p.1 p.2.1 p.2.2)).toMonoidHom (g p.2.1 p.2.2)
  let y : ∀ p : J × (J × J),
      ((Mq.object (tripleObj p)).spreadStage (t := t)
        (Mq.le_stage (tripleObj p)))ˣ := fun p =>
    Units.map (Mq.map
        (Scheme.GlueData.affineIntersectionPairToTripleRight
          p.1 p.2.1 p.2.2)).toMonoidHom (g p.1 p.2.2)
  have hxy : ∀ p, Units.map ((Mq.object (tripleObj p)).stageToColimit H
        ⟨Mq.stage, Mq.le_stage (tripleObj p)⟩).toMonoidHom (x p) =
      Units.map ((Mq.object (tripleObj p)).stageToColimit H
        ⟨Mq.stage, Mq.le_stage (tripleObj p)⟩).toMonoidHom (y p) := by
    rintro ⟨i, ⟨j, k⟩⟩
    dsimp only [x, y, tripleObj]
    rw [map_mul, Mq.map_unit_colimit, Mq.map_unit_colimit,
      Mq.map_unit_colimit, hg i j, hg j k, hg i k]
    exact c.cocycle i j k
  obtain ⟨r, hqr, hcocycle⟩ :=
    Mq.exists_common_unit_eq_atLaterStage tripleObj x y hxy
  have hcocycle_r (i j k : J) :
      Units.map ((Mq.object
          (Scheme.GlueData.affineIntersectionTripleIndex i j k)).stageTransition H
            (P := ⟨Mq.stage, Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)⟩)
            (Q := ⟨r, (Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)).trans hqr⟩)
            hqr).toMonoidHom
          (Units.map (Mq.map
            (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).toMonoidHom
              (g i j)) *
        Units.map ((Mq.object
          (Scheme.GlueData.affineIntersectionTripleIndex i j k)).stageTransition H
            (P := ⟨Mq.stage, Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)⟩)
            (Q := ⟨r, (Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)).trans hqr⟩)
            hqr).toMonoidHom
          (Units.map (Mq.map
            (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).toMonoidHom
              (g j k)) =
        Units.map ((Mq.object
          (Scheme.GlueData.affineIntersectionTripleIndex i j k)).stageTransition H
            (P := ⟨Mq.stage, Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)⟩)
            (Q := ⟨r, (Mq.le_stage
              (Scheme.GlueData.affineIntersectionTripleIndex i j k)).trans hqr⟩)
            hqr).toMonoidHom
          (Units.map (Mq.map
            (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).toMonoidHom
              (g i k)) := by
    rw [← map_mul]
    simpa only [x, y, tripleObj] using hcocycle (i, (j, k))
  let gr (i j : J) :
      ((Mq.object
        (Scheme.GlueData.affineIntersectionPairIndex i j)).spreadStage (t := t)
          ((Mq.le_stage
            (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr))ˣ :=
    Units.map ((Mq.object
      (Scheme.GlueData.affineIntersectionPairIndex i j)).stageTransition H
        (P := ⟨Mq.stage, Mq.le_stage
          (Scheme.GlueData.affineIntersectionPairIndex i j)⟩)
        (Q := ⟨r, (Mq.le_stage
          (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr⟩)
        hqr).toMonoidHom (g i j)
  let c_r : AffineIntersectionUnitCocycle (Mq.mapToStage hqr).toFunctor := {
    transition := gr
    cocycle := by
      intro i j k
      dsimp only [gr]
      change Units.map ((Mq.mapToStage hqr).map
            (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k)).toMonoidHom
          (Units.map ((Mq.object
            (Scheme.GlueData.affineIntersectionPairIndex i j)).stageTransition H
              (P := ⟨Mq.stage, Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex i j)⟩)
              (Q := ⟨r, (Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr⟩)
              hqr).toMonoidHom (g i j)) *
        Units.map ((Mq.mapToStage hqr).map
            (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k)).toMonoidHom
          (Units.map ((Mq.object
            (Scheme.GlueData.affineIntersectionPairIndex j k)).stageTransition H
              (P := ⟨Mq.stage, Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex j k)⟩)
              (Q := ⟨r, (Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex j k)).trans hqr⟩)
              hqr).toMonoidHom (g j k)) =
        Units.map ((Mq.mapToStage hqr).map
            (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)).toMonoidHom
          (Units.map ((Mq.object
            (Scheme.GlueData.affineIntersectionPairIndex i k)).stageTransition H
              (P := ⟨Mq.stage, Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex i k)⟩)
              (Q := ⟨r, (Mq.le_stage
                (Scheme.GlueData.affineIntersectionPairIndex i k)).trans hqr⟩)
              hqr).toMonoidHom (g i k))
      rw [Mq.mapToStage_map_unitTransition hqr
          (Scheme.GlueData.affineIntersectionPairToTripleLeft i j k),
        Mq.mapToStage_map_unitTransition hqr
          (Scheme.GlueData.affineIntersectionPairToTripleMiddle i j k),
        Mq.mapToStage_map_unitTransition hqr
          (Scheme.GlueData.affineIntersectionPairToTripleRight i j k)]
      exact hcocycle_r i j k }
  refine ⟨q, hiq, r, hqr, c_r, fun i j => ?_⟩
  apply Units.ext
  change (Mq.object
      (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit H
        ⟨r, (Mq.le_stage
          (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr⟩
        ((Mq.object
          (Scheme.GlueData.affineIntersectionPairIndex i j)).stageTransition H
            (P := ⟨Mq.stage, Mq.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i j)⟩)
            (Q := ⟨r, (Mq.le_stage
              (Scheme.GlueData.affineIntersectionPairIndex i j)).trans hqr⟩)
            hqr (g i j : (Mq.object
              (Scheme.GlueData.affineIntersectionPairIndex i j)).spreadStage (t := t)
                (Mq.le_stage
                  (Scheme.GlueData.affineIntersectionPairIndex i j)))) =
    (c.transition i j : F.obj
      (Scheme.GlueData.affineIntersectionPairIndex i j))
  exact ((Mq.object
    (Scheme.GlueData.affineIntersectionPairIndex i j)).stageToColimit_stageTransition H
      (Mq.le_stage (Scheme.GlueData.affineIntersectionPairIndex i j)) hqr
      (g i j : (Mq.object
        (Scheme.GlueData.affineIntersectionPairIndex i j)).spreadStage (t := t)
          (Mq.le_stage (Scheme.GlueData.affineIntersectionPairIndex i j)))).trans
          (congrArg Units.val (hg i j))

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
