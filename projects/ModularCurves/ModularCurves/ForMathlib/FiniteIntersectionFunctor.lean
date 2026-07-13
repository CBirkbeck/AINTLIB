import ModularCurves.ForMathlib.FinitePresentationSchemeGlueData

/-!
# Algebra diagrams of finite affine intersections

A finite family of opens in a scheme determines a covariant diagram of coordinate
algebras: inclusions of finite index sets give restriction maps on the corresponding
intersections. The empty intersection is augmented by the coordinate ring of the base,
so finite presentation of global functions on the total space is not required.
-/

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} {J : Type u}

/-- The intersection of the opens whose indices belong to `s`. -/
def Scheme.finiteIntersectionOpen (U : J → X.Opens) (s : Finset J) : X.Opens :=
  ⨅ j ∈ (s : Set J), U j

@[simp]
theorem Scheme.finiteIntersectionOpen_empty (U : J → X.Opens) :
    X.finiteIntersectionOpen U ∅ = ⊤ := by
  simp [Scheme.finiteIntersectionOpen]

@[simp]
theorem Scheme.finiteIntersectionOpen_singleton (U : J → X.Opens) (i : J) :
    X.finiteIntersectionOpen U {i} = U i := by
  simp [Scheme.finiteIntersectionOpen]

theorem Scheme.finiteIntersectionOpen_antitone (U : J → X.Opens)
    {s t : Finset J} (hst : s ⊆ t) :
    X.finiteIntersectionOpen U t ≤ X.finiteIntersectionOpen U s := by
  rw [Scheme.finiteIntersectionOpen, Scheme.finiteIntersectionOpen]
  refine le_iInf fun i => le_iInf fun hi => ?_
  exact iInf_le_of_le i (iInf_le_of_le (hst hi) le_rfl)

private abbrev finiteIntersectionSections (U : J → X.Opens) (s : Finset J) :=
  Γ((X.finiteIntersectionOpen U s).toScheme,
    (⊤ : (X.finiteIntersectionOpen U s).toScheme.Opens))

@[reducible]
private noncomputable def Scheme.Hom.finiteIntersectionAlgebra
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) :
    Algebra Γ(S, (⊤ : S.Opens)) (finiteIntersectionSections U s) :=
  ((X.finiteIntersectionOpen U s).ι ≫ π).appTop.hom.toAlgebra

/-- The coordinate ring of a finite intersection, regarded as an algebra over the
base through the structure morphism. -/
noncomputable def Scheme.Hom.finiteIntersectionRing
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) :
    CommAlgCat.{u} Γ(S, (⊤ : S.Opens)) := by
  letI := π.finiteIntersectionAlgebra U s
  exact CommAlgCat.of Γ(S, (⊤ : S.Opens)) (finiteIntersectionSections U s)

/-- Restriction of functions along the inclusion between two finite intersections. -/
noncomputable def Scheme.Hom.finiteIntersectionRestriction
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (hst : s ⊆ t) :
    π.finiteIntersectionRing U s ⟶ π.finiteIntersectionRing U t := by
  letI := π.finiteIntersectionAlgebra U s
  letI := π.finiteIntersectionAlgebra U t
  apply CommAlgCat.ofHom
  exact
    { __ := (X.homOfLE (X.finiteIntersectionOpen_antitone U hst)).appTop.hom
      commutes' r := by
        change (((X.finiteIntersectionOpen U s).ι ≫ π).appTop ≫
          (X.homOfLE (X.finiteIntersectionOpen_antitone U hst)).appTop).hom r =
            (((X.finiteIntersectionOpen U t).ι ≫ π).appTop).hom r
        rw [← Scheme.Hom.comp_appTop]
        change ((((X.homOfLE (X.finiteIntersectionOpen_antitone U hst)) ≫
          (X.finiteIntersectionOpen U s).ι) ≫ π).appTop).hom r = _
        rw [Scheme.homOfLE_ι] }

/-- The algebra structure map from the base ring to a finite-intersection ring. -/
noncomputable def Scheme.Hom.finiteIntersectionStructureMap
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) :
    CommAlgCat.of Γ(S, (⊤ : S.Opens)) Γ(S, (⊤ : S.Opens)) ⟶
      π.finiteIntersectionRing U s := by
  letI := π.finiteIntersectionAlgebra U s
  exact CommAlgCat.ofHom
    (Algebra.ofId Γ(S, (⊤ : S.Opens)) (finiteIntersectionSections U s))

private theorem Scheme.Hom.finiteIntersectionRestriction_id
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) :
    π.finiteIntersectionRestriction U (show s ⊆ s from fun _ hi => hi) = 𝟙 _ := by
  letI := π.finiteIntersectionAlgebra U s
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change ((X.homOfLE _).appTop).hom x = x
  rw [Scheme.homOfLE_rfl, Scheme.Hom.id_appTop]
  rfl

private theorem Scheme.Hom.finiteIntersectionRestriction_comp
    (π : X ⟶ S) (U : J → X.Opens) {s t v : Finset J}
    (hst : s ⊆ t) (htv : t ⊆ v) :
    π.finiteIntersectionRestriction U (hst.trans htv) =
      π.finiteIntersectionRestriction U hst ≫
        π.finiteIntersectionRestriction U htv := by
  letI := π.finiteIntersectionAlgebra U s
  letI := π.finiteIntersectionAlgebra U t
  letI := π.finiteIntersectionAlgebra U v
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change ((X.homOfLE (X.finiteIntersectionOpen_antitone U (hst.trans htv))).appTop).hom x =
    ((X.homOfLE (X.finiteIntersectionOpen_antitone U hst)).appTop ≫
      (X.homOfLE (X.finiteIntersectionOpen_antitone U htv)).appTop).hom x
  rw [← Scheme.Hom.comp_appTop, Scheme.homOfLE_homOfLE]

private theorem Scheme.Hom.finiteIntersectionStructureMap_naturality
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (hst : s ⊆ t) :
    π.finiteIntersectionStructureMap U s ≫
        π.finiteIntersectionRestriction U hst =
      π.finiteIntersectionStructureMap U t := by
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  change (π.finiteIntersectionRestriction U hst).hom
      (algebraMap Γ(S, (⊤ : S.Opens)) (π.finiteIntersectionRing U s) x) =
    algebraMap Γ(S, (⊤ : S.Opens)) (π.finiteIntersectionRing U t) x
  exact (π.finiteIntersectionRestriction U hst).hom.commutes x

@[reducible]
private noncomputable def Scheme.Hom.affineIntersectionObj
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) :
    CommAlgCat.{u} Γ(S, (⊤ : S.Opens)) :=
  if s.Nonempty then π.finiteIntersectionRing U s
  else CommAlgCat.of Γ(S, (⊤ : S.Opens)) Γ(S, (⊤ : S.Opens))

private theorem Scheme.Hom.affineIntersectionObj_nonempty
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) (hs : s.Nonempty) :
    π.affineIntersectionObj U s = π.finiteIntersectionRing U s := by
  exact if_pos hs

private theorem Scheme.Hom.affineIntersectionObj_empty
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) (hs : ¬s.Nonempty) :
    π.affineIntersectionObj U s =
      CommAlgCat.of Γ(S, (⊤ : S.Opens)) Γ(S, (⊤ : S.Opens)) := by
  exact if_neg hs

private noncomputable def Scheme.Hom.affineIntersectionMap
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (f : s ⟶ t) :
    π.affineIntersectionObj U s ⟶ π.affineIntersectionObj U t := by
  classical
  by_cases hs : s.Nonempty
  · have ht : t.Nonempty := hs.mono (leOfHom f)
    exact eqToHom (π.affineIntersectionObj_nonempty U s hs) ≫
      π.finiteIntersectionRestriction U (leOfHom f) ≫
      eqToHom (π.affineIntersectionObj_nonempty U t ht).symm
  · by_cases ht : t.Nonempty
    · exact eqToHom (π.affineIntersectionObj_empty U s hs) ≫
        π.finiteIntersectionStructureMap U t ≫
        eqToHom (π.affineIntersectionObj_nonempty U t ht).symm
    · exact eqToHom (π.affineIntersectionObj_empty U s hs) ≫
        𝟙 (CommAlgCat.of Γ(S, (⊤ : S.Opens)) Γ(S, (⊤ : S.Opens))) ≫
        eqToHom (π.affineIntersectionObj_empty U t ht).symm

private theorem Scheme.Hom.affineIntersectionMap_id
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) :
    π.affineIntersectionMap U (𝟙 s) = 𝟙 _ := by
  classical
  by_cases hs : s.Nonempty
  · simp only [Scheme.Hom.affineIntersectionMap, dif_pos hs]
    rw [π.finiteIntersectionRestriction_id U]
    simp
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hs
    simp only [Scheme.Hom.affineIntersectionMap, dif_neg Finset.not_nonempty_empty]
    simp

private theorem Scheme.Hom.affineIntersectionMap_comp
    (π : X ⟶ S) (U : J → X.Opens) {s t v : Finset J}
    (f : s ⟶ t) (g : t ⟶ v) :
    π.affineIntersectionMap U (f ≫ g) =
      π.affineIntersectionMap U f ≫ π.affineIntersectionMap U g := by
  classical
  by_cases hs : s.Nonempty
  · have ht : t.Nonempty := hs.mono (leOfHom f)
    have hv : v.Nonempty := ht.mono (leOfHom g)
    simp only [Scheme.Hom.affineIntersectionMap, dif_pos hs, dif_pos ht]
    rw [π.finiteIntersectionRestriction_comp U (leOfHom f) (leOfHom g)]
    simp
  · by_cases ht : t.Nonempty
    · have hv : v.Nonempty := ht.mono (leOfHom g)
      obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hs
      simp only [Scheme.Hom.affineIntersectionMap,
        dif_neg Finset.not_nonempty_empty, dif_pos hv, dif_pos ht]
      simp only [Category.assoc]
      simp
      simpa only [Category.assoc] using congrArg
        (fun k => eqToHom (π.affineIntersectionObj_empty U ∅ Finset.not_nonempty_empty) ≫
          k ≫ eqToHom (π.affineIntersectionObj_nonempty U v hv).symm)
        (π.finiteIntersectionStructureMap_naturality U (leOfHom g)).symm
    · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hs
      obtain rfl := Finset.not_nonempty_iff_eq_empty.mp ht
      by_cases hv : v.Nonempty
      · simp only [Scheme.Hom.affineIntersectionMap,
          dif_neg Finset.not_nonempty_empty, dif_pos hv]
        simp
      · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp hv
        simp only [Scheme.Hom.affineIntersectionMap,
          dif_neg Finset.not_nonempty_empty]
        simp

/-- The augmented coordinate-algebra diagram of a finite family of opens. The empty
index is sent to the base ring, while a nonempty index is sent to global sections of
the corresponding open subscheme. -/
@[reducible]
noncomputable def Scheme.Hom.affineIntersectionFunctor
    (π : X ⟶ S) (U : J → X.Opens) :
    CategoryTheory.Functor (Finset J) (CommAlgCat.{u} Γ(S, (⊤ : S.Opens))) where
  obj := π.affineIntersectionObj U
  map := π.affineIntersectionMap U
  map_id := π.affineIntersectionMap_id U
  map_comp := π.affineIntersectionMap_comp U

/-- A nonempty object of the affine-intersection functor is the coordinate ring of the
corresponding open subscheme. -/
theorem Scheme.Hom.affineIntersectionFunctor_obj_nonempty
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) (hs : s.Nonempty) :
    (π.affineIntersectionFunctor U).obj s = π.finiteIntersectionRing U s := by
  exact π.affineIntersectionObj_nonempty U s hs

/-- On nonempty indices, the affine-intersection functor map is restriction along the
inclusion of the corresponding open subschemes. -/
theorem Scheme.Hom.affineIntersectionFunctor_map_nonempty
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (f : s ⟶ t)
    (hs : s.Nonempty) (ht : t.Nonempty) :
    eqToHom (π.affineIntersectionFunctor_obj_nonempty U s hs).symm ≫
        (π.affineIntersectionFunctor U).map f ≫
        eqToHom (π.affineIntersectionFunctor_obj_nonempty U t ht) =
      π.finiteIntersectionRestriction U (leOfHom f) := by
  change eqToHom _ ≫ π.affineIntersectionMap U f ≫ eqToHom _ = _
  rw [Scheme.Hom.affineIntersectionMap, dif_pos hs]
  simp

/-- The empty object of the affine-intersection functor is the base ring. -/
theorem Scheme.Hom.affineIntersectionFunctor_obj_empty
    (π : X ⟶ S) (U : J → X.Opens) :
    (π.affineIntersectionFunctor U).obj ∅ =
      CommAlgCat.of Γ(S, (⊤ : S.Opens)) Γ(S, (⊤ : S.Opens)) := by
  exact π.affineIntersectionObj_empty U ∅ Finset.not_nonempty_empty

/-- The map from the empty index to a nonempty intersection is its base-algebra
structure map. -/
theorem Scheme.Hom.affineIntersectionFunctor_map_empty
    (π : X ⟶ S) (U : J → X.Opens) {t : Finset J} (f : ∅ ⟶ t)
    (ht : t.Nonempty) :
    eqToHom (π.affineIntersectionFunctor_obj_empty U).symm ≫
        (π.affineIntersectionFunctor U).map f ≫
        eqToHom (π.affineIntersectionFunctor_obj_nonempty U t ht) =
      π.finiteIntersectionStructureMap U t := by
  change eqToHom _ ≫ π.affineIntersectionMap U f ≫ eqToHom _ = _
  rw [Scheme.Hom.affineIntersectionMap, dif_neg Finset.not_nonempty_empty, dif_pos ht]
  simp

end

end AlgebraicGeometry
