import Mathlib.AlgebraicGeometry.Morphisms.Affine
import ModularCurves.ForMathlib.FiniteIntersectionFunctor

/-!
# Geometry of finite affine-intersection diagrams

The coordinate-algebra functor of a family of affine open intersections has open
singleton-to-pair spectrum maps, and its singleton/pair/triple squares are pushouts.
-/

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} {J : Type u}

private noncomputable abbrev geometrySingletonIndex (i : J) : Finset J := by
  classical
  exact {i}

private noncomputable abbrev geometryPairIndex (i j : J) : Finset J := by
  classical
  exact {i, j}

private noncomputable abbrev geometryTripleIndex (i j k : J) : Finset J := by
  classical
  exact {i, j, k}

private noncomputable def geometrySingletonToPair (i j : J) :
    geometrySingletonIndex i ⟶ geometryPairIndex i j :=
  homOfLE (by
    classical
    simp [geometrySingletonIndex, geometryPairIndex])

private noncomputable def geometryPairToTripleLeft (i j k : J) :
    geometryPairIndex i j ⟶ geometryTripleIndex i j k :=
  homOfLE (by
    classical
    simp [geometryPairIndex, geometryTripleIndex])

private noncomputable def geometryPairToTripleRight (i j k : J) :
    geometryPairIndex i k ⟶ geometryTripleIndex i j k :=
  homOfLE (by
    classical
    simp [geometryPairIndex, geometryTripleIndex])

/-- The underlying ring of a nonempty object of the affine-intersection functor is
canonically the ring of functions on the corresponding geometric intersection. -/
noncomputable def Scheme.Hom.finiteIntersectionRingIso
    (π : X ⟶ S) (U : J → X.Opens) (s : Finset J) (hs : s.Nonempty) :
    (forget₂ (CommAlgCat Γ(S, (⊤ : S.Opens))) CommRingCat).obj
        (π.finiteIntersectionRing U s) ≅
      (forget₂ (CommAlgCat Γ(S, (⊤ : S.Opens))) CommRingCat).obj
        ((π.affineIntersectionFunctor U).obj s) :=
  (forget₂ (CommAlgCat Γ(S, (⊤ : S.Opens))) CommRingCat).mapIso
    (eqToIso (π.affineIntersectionFunctor_obj_nonempty U s hs).symm)

/-- The canonical ring isomorphisms for nonempty finite intersections intertwine
the functor map with geometric restriction of functions. -/
theorem Scheme.Hom.finiteIntersectionRestriction_ringIso
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (f : s ⟶ t)
    (hs : s.Nonempty) (ht : t.Nonempty) :
    CommRingCat.ofHom (π.finiteIntersectionRestriction U (leOfHom f)).hom.toRingHom ≫
        (π.finiteIntersectionRingIso U t ht).hom =
      (π.finiteIntersectionRingIso U s hs).hom ≫
        CommRingCat.ofHom ((π.affineIntersectionFunctor U).map f).hom.toRingHom := by
  have hAlg :
      π.finiteIntersectionRestriction U (leOfHom f) ≫
          eqToHom (π.affineIntersectionFunctor_obj_nonempty U t ht).symm =
        eqToHom (π.affineIntersectionFunctor_obj_nonempty U s hs).symm ≫
          (π.affineIntersectionFunctor U).map f := by
    rw [← π.affineIntersectionFunctor_map_nonempty U f hs ht]
    simp
  ext x
  exact ConcreteCategory.congr_hom hAlg x

/-- Forgetting the algebra structure, finite-intersection restriction is the map on
global sections induced by the corresponding inclusion of open subschemes. -/
theorem Scheme.Hom.finiteIntersectionRestriction_forget
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (f : s ⟶ t) :
    CommRingCat.ofHom (π.finiteIntersectionRestriction U (leOfHom f)).hom.toRingHom =
      (X.homOfLE (X.finiteIntersectionOpen_antitone U (leOfHom f))).appTop := by
  rfl

private theorem Scheme.Hom.isOpenImmersion_specMap_affineIntersectionFunctor_map_nonempty
    (π : X ⟶ S) (U : J → X.Opens) {s t : Finset J} (f : s ⟶ t)
    (hs : s.Nonempty) (ht : t.Nonempty)
    (hUs : IsAffineOpen (X.finiteIntersectionOpen U s))
    (hUt : IsAffineOpen (X.finiteIntersectionOpen U t)) :
    IsOpenImmersion
      (Spec.map (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map f).hom.toRingHom)) := by
  let g := X.homOfLE (X.finiteIntersectionOpen_antitone U (leOfHom f))
  letI : IsAffine (X.finiteIntersectionOpen U s).toScheme := hUs
  letI : IsAffine (X.finiteIntersectionOpen U t).toScheme := hUt
  have hg : IsOpenImmersion (Spec.map g.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @IsOpenImmersion
      (arrowIsoSpecΓOfIsAffine g)).mp inferInstance
  have hg' : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom
        (π.finiteIntersectionRestriction U (leOfHom f)).hom.toRingHom)) := by
    rw [π.finiteIntersectionRestriction_forget U f]
    exact hg
  have hRing := π.finiteIntersectionRestriction_ringIso U f hs ht
  have hSpec := congrArg (fun q => Spec.map q) hRing
  rw [Spec.map_comp, Spec.map_comp] at hSpec
  have hcomp : IsOpenImmersion
      (Spec.map (π.finiteIntersectionRingIso U t ht).hom ≫
        Spec.map (CommRingCat.ofHom
          (π.finiteIntersectionRestriction U (leOfHom f)).hom.toRingHom)) :=
    (MorphismProperty.cancel_left_of_respectsIso (P := @IsOpenImmersion) _ _).mpr
      hg'
  rw [hSpec] at hcomp
  exact (MorphismProperty.cancel_right_of_respectsIso (P := @IsOpenImmersion) _ _).mp hcomp

/-- If every nonempty finite intersection is affine, the singleton-to-pair maps of
the affine-intersection functor induce open immersions on spectra. -/
theorem Scheme.Hom.isOpenAffineIntersectionFunctor_affineIntersectionFunctor
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    Scheme.GlueData.IsOpenAffineIntersectionFunctor (π.affineIntersectionFunctor U) := by
  classical
  intro i j
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom
      ((π.affineIntersectionFunctor U).map (geometrySingletonToPair i j)).hom.toRingHom))
  have hs : (geometrySingletonIndex i).Nonempty := by
    simp [geometrySingletonIndex]
  have ht : (geometryPairIndex i j).Nonempty := hs.mono (leOfHom (geometrySingletonToPair i j))
  exact π.isOpenImmersion_specMap_affineIntersectionFunctor_map_nonempty U
    (geometrySingletonToPair i j) hs ht (hU _ hs) (hU _ ht)

private theorem Scheme.finiteIntersectionOpen_triple_eq_pair_inf_pair
    (U : J → X.Opens) (i j k : J) :
    X.finiteIntersectionOpen U (geometryTripleIndex i j k) =
      X.finiteIntersectionOpen U (geometryPairIndex i j) ⊓
        X.finiteIntersectionOpen U (geometryPairIndex i k) := by
  classical
  have hij_i : X.finiteIntersectionOpen U (geometryPairIndex i j) ≤ U i := by
    rw [Scheme.finiteIntersectionOpen]
    exact iInf_le_of_le i (iInf_le_of_le (by simp [geometryPairIndex]) le_rfl)
  have hij_j : X.finiteIntersectionOpen U (geometryPairIndex i j) ≤ U j := by
    rw [Scheme.finiteIntersectionOpen]
    exact iInf_le_of_le j (iInf_le_of_le (by simp [geometryPairIndex]) le_rfl)
  have hik_k : X.finiteIntersectionOpen U (geometryPairIndex i k) ≤ U k := by
    rw [Scheme.finiteIntersectionOpen]
    exact iInf_le_of_le k (iInf_le_of_le (by simp [geometryPairIndex]) le_rfl)
  apply le_antisymm
  · exact le_inf
      (X.finiteIntersectionOpen_antitone U (leOfHom (geometryPairToTripleLeft i j k)))
      (X.finiteIntersectionOpen_antitone U (leOfHom (geometryPairToTripleRight i j k)))
  · rw [Scheme.finiteIntersectionOpen]
    refine le_iInf fun x => le_iInf fun hx => ?_
    have hx' : x = i ∨ x = j ∨ x = k := by
      simpa [geometryTripleIndex] using hx
    rcases hx' with rfl | rfl | rfl
    · exact inf_le_left.trans hij_i
    · exact inf_le_left.trans hij_j
    · exact inf_le_right.trans hik_k

private theorem Scheme.finiteIntersectionOpen_isPullback
    (U : J → X.Opens) (i j k : J) :
    IsPullback
      (X.homOfLE (X.finiteIntersectionOpen_antitone U
        (leOfHom (geometryPairToTripleLeft i j k))))
      (X.homOfLE (X.finiteIntersectionOpen_antitone U
        (leOfHom (geometryPairToTripleRight i j k))))
      (X.homOfLE (X.finiteIntersectionOpen_antitone U
        (leOfHom (geometrySingletonToPair i j))))
      (X.homOfLE (X.finiteIntersectionOpen_antitone U
        (leOfHom (geometrySingletonToPair i k)))) := by
  classical
  let h := isPullback_opens_inf_le
    (X.finiteIntersectionOpen_antitone U (leOfHom (geometrySingletonToPair i j)))
    (X.finiteIntersectionOpen_antitone U (leOfHom (geometrySingletonToPair i k)))
  let e := X.isoOfEq (X.finiteIntersectionOpen_triple_eq_pair_inf_pair U i j k).symm
  refine h.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  all_goals simp [e, ← cancel_mono (Scheme.Opens.ι _)]

private theorem Scheme.Hom.isPushout_affineIntersectionFunctor
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s))
    (i j k : J) :
    IsPushout
      (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map
        (geometrySingletonToPair i j)).hom.toRingHom)
      (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map
        (geometrySingletonToPair i k)).hom.toRingHom)
      (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map
        (geometryPairToTripleLeft i j k)).hom.toRingHom)
      (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map
        (geometryPairToTripleRight i j k)).hom.toRingHom) := by
  classical
  have hs : (geometrySingletonIndex i).Nonempty := by simp [geometrySingletonIndex]
  have hij : (geometryPairIndex i j).Nonempty := hs.mono (leOfHom (geometrySingletonToPair i j))
  have hik : (geometryPairIndex i k).Nonempty := hs.mono (leOfHom (geometrySingletonToPair i k))
  have hijk : (geometryTripleIndex i j k).Nonempty :=
    hij.mono (leOfHom (geometryPairToTripleLeft i j k))
  letI : IsAffine (X.finiteIntersectionOpen U (geometrySingletonIndex i)).toScheme :=
    hU (geometrySingletonIndex i) hs
  letI : IsAffine (X.finiteIntersectionOpen U (geometryPairIndex i j)).toScheme :=
    hU (geometryPairIndex i j) hij
  letI : IsAffine (X.finiteIntersectionOpen U (geometryPairIndex i k)).toScheme :=
    hU (geometryPairIndex i k) hik
  letI : IsAffine (X.finiteIntersectionOpen U (geometryTripleIndex i j k)).toScheme :=
    hU (geometryTripleIndex i j k) hijk
  have h := isPushout_appTop_of_isPullback
    (X.finiteIntersectionOpen_isPullback U i j k)
  exact h.of_iso
    (π.finiteIntersectionRingIso U _ hs)
    (π.finiteIntersectionRingIso U _ hij)
    (π.finiteIntersectionRingIso U _ hik)
    (π.finiteIntersectionRingIso U _ hijk)
    (π.finiteIntersectionRestriction_ringIso U _ hs hij)
    (π.finiteIntersectionRestriction_ringIso U _ hs hik)
    (π.finiteIntersectionRestriction_ringIso U _ hij hijk)
    (π.finiteIntersectionRestriction_ringIso U _ hik hijk)

/-- If every nonempty finite intersection is affine, the singleton/pair/triple
squares of the affine-intersection functor are pushouts. -/
theorem Scheme.Hom.isPushoutAffineIntersectionFunctor_affineIntersectionFunctor
    (π : X ⟶ S) (U : J → X.Opens)
    (hU : ∀ s : Finset J, s.Nonempty → IsAffineOpen (X.finiteIntersectionOpen U s)) :
    Scheme.GlueData.IsPushoutAffineIntersectionFunctor (π.affineIntersectionFunctor U) := by
  classical
  intro i j k
  change IsPushout
    (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map
      (geometrySingletonToPair i j)).hom.toRingHom)
    (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map
      (geometrySingletonToPair i k)).hom.toRingHom)
    (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map
      (geometryPairToTripleLeft i j k)).hom.toRingHom)
    (CommRingCat.ofHom ((π.affineIntersectionFunctor U).map
      (geometryPairToTripleRight i j k)).hom.toRingHom)
  exact π.isPushout_affineIntersectionFunctor U hU i j k

end

end AlgebraicGeometry
