import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Sites.GlobalSections
import ModularCurves.ForMathlib.FlasqueCohomology

/-!
# Sheaf cohomology as derived global sections

This file identifies `Ext` from a representing object with the right-derived functors of
the represented additive functor. It then specializes this comparison to identify genuine
sheaf cohomology with right-derived global sections.
-/

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Abelian.Ext

noncomputable section

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {G : C ⥤ AddCommGrpCat.{v}} [G.Additive]
variable {Z F : C}

private def cochainToSectionsEquiv
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ) :
    CochainComplex.HomComplex.Cochain
        ((CochainComplex.singleFunctor C 0).obj Z) K n ≃+
      ↑(G.obj (K.X n)) :=
  (CochainComplex.HomComplex.Cochain.fromSingleEquiv (zero_add n)).trans (e (K.X n))

private def cochainToSectionsIso
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ) :
    (((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).X n ≅
      ((G.mapHomologicalComplex (.up ℤ)).obj K).X n :=
  (cochainToSectionsEquiv e K n).toAddCommGrpIso

omit [G.Additive] in
private lemma cochainToSectionsEquiv_fromSingleMk
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ) (f : Z ⟶ K.X n) :
    cochainToSectionsEquiv e K n
        (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add n)) = e (K.X n) f := by
  exact congrArg (e (K.X n))
    (CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk f (zero_add n))

private lemma cochainToSectionsIso_hom_apply
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (K : CochainComplex C ℤ) (n : ℤ)
    (α : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj Z) K n) :
    (cochainToSectionsIso e K n).hom.hom α = cochainToSectionsEquiv e K n α :=
  rfl

private lemma homComplex_d_apply
    (K : CochainComplex C ℤ) (i j : ℤ)
    (α : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj Z) K i) :
    ((((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).d i j).hom α =
      CochainComplex.HomComplex.δ i j α :=
  rfl

private def homComplexIsoSections
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (f : Z ⟶ X) (g : X ⟶ Y),
      e Y (f ≫ g) = G.map g (e X f))
    (K : CochainComplex C ℤ) :
    ((CochainComplex.singleFunctor C 0).obj Z).HomComplex K ≅
      (G.mapHomologicalComplex (.up ℤ)).obj K :=
  HomologicalComplex.Hom.isoOfComponents (cochainToSectionsIso e K) fun i j hij ↦ by
    ext α
    obtain ⟨f, rfl⟩ :=
      CochainComplex.HomComplex.Cochain.fromSingleMk_surjective α i (zero_add i)
    rw [AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply,
      cochainToSectionsIso_hom_apply, Functor.mapHomologicalComplex_obj_d,
      homComplex_d_apply, cochainToSectionsIso_hom_apply]
    rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (zero_add i) j j
      (zero_add j), cochainToSectionsEquiv_fromSingleMk,
      cochainToSectionsEquiv_fromSingleMk]
    exact (he f (K.d i j)).symm

private lemma homComplexIsoSections_hom_f_apply
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (a : Z ⟶ X) (b : X ⟶ Y),
      e Y (a ≫ b) = G.map b (e X a))
    (K : CochainComplex C ℤ) (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj Z) K n) :
    ((homComplexIsoSections e he K).hom.f n).hom z =
      cochainToSectionsEquiv e K n z :=
  rfl

private def homComplexPostcomp {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    ((CochainComplex.singleFunctor C 0).obj Z).HomComplex K ⟶
      ((CochainComplex.singleFunctor C 0).obj Z).HomComplex L where
  f n := AddCommGrpCat.ofHom
    { toFun := fun z ↦ z.comp (.ofHom f) (add_zero n)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  comm' i j _ := by
    ext z
    exact CochainComplex.HomComplex.δ_comp_ofHom z f j

private lemma homComplexPostcomp_f_apply {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n : ℤ)
    (z : CochainComplex.HomComplex.Cochain
      ((CochainComplex.singleFunctor C 0).obj Z) K n) :
    ((homComplexPostcomp f).f n).hom z =
      z.comp (.ofHom f) (add_zero n) :=
  rfl

private lemma homComplexIsoSections_naturality
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (a : Z ⟶ X) (b : X ⟶ Y),
      e Y (a ≫ b) = G.map b (e X a))
    {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    homComplexPostcomp f ≫ (homComplexIsoSections e he L).hom =
      (homComplexIsoSections e he K).hom ≫
        (G.mapHomologicalComplex (.up ℤ)).map f := by
  ext n z
  obtain ⟨a, rfl⟩ :=
    CochainComplex.HomComplex.Cochain.fromSingleMk_surjective z n (zero_add n)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    AddCommGrpCat.comp_apply, AddCommGrpCat.comp_apply, homComplexPostcomp_f_apply,
    homComplexIsoSections_hom_f_apply, homComplexIsoSections_hom_f_apply,
    Functor.mapHomologicalComplex_map_f]
  rw [← CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp]
  rw [cochainToSectionsEquiv_fromSingleMk, cochainToSectionsEquiv_fromSingleMk]
  exact he a (f.f n)

private def cocyclePostcomp {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.Cocycle ((CochainComplex.singleFunctor C 0).obj Z) K n →+
      CochainComplex.HomComplex.Cocycle ((CochainComplex.singleFunctor C 0).obj Z) L n where
  toFun z := z.postcomp f
  map_zero' := by ext; simp [CochainComplex.HomComplex.Cocycle.postcomp]
  map_add' x y := by ext; simp [CochainComplex.HomComplex.Cocycle.postcomp]

private def cohomologyClassPostcomp {K L : CochainComplex C ℤ} (f : K ⟶ L) (n : ℤ) :
    CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor C 0).obj Z) K n →+
      CochainComplex.HomComplex.CohomologyClass
        ((CochainComplex.singleFunctor C 0).obj Z) L n :=
  CochainComplex.HomComplex.CohomologyClass.descAddMonoidHom
    ((CochainComplex.HomComplex.CohomologyClass.mkAddMonoidHom
      ((CochainComplex.singleFunctor C 0).obj Z) L n).comp (cocyclePostcomp f n)) (by
        rintro z ⟨m, hm, β, hβ⟩
        rw [AddMonoidHom.mem_ker]
        change CochainComplex.HomComplex.CohomologyClass.mk (z.postcomp f) = 0
        rw [CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff]
        refine ⟨m, hm, β.comp (.ofHom f) (add_zero m), ?_⟩
        rw [CochainComplex.HomComplex.Cocycle.postcomp_coe, ← hβ]
        exact CochainComplex.HomComplex.δ_comp_ofHom β f n)

private lemma cohomologyClassPostcomp_mk {K L : CochainComplex C ℤ} (f : K ⟶ L)
    (n : ℤ)
    (z : CochainComplex.HomComplex.Cocycle
      ((CochainComplex.singleFunctor C 0).obj Z) K n) :
    cohomologyClassPostcomp f n (CochainComplex.HomComplex.CohomologyClass.mk z) =
      CochainComplex.HomComplex.CohomologyClass.mk (z.postcomp f) :=
  rfl

private def homComplexPostcompLeftHomologyMapData {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v} (.up ℤ) n).map
        (homComplexPostcomp f))
      (CochainComplex.HomComplex.leftHomologyData
        ((CochainComplex.singleFunctor C 0).obj Z) K n)
      (CochainComplex.HomComplex.leftHomologyData
        ((CochainComplex.singleFunctor C 0).obj Z) L n) where
  φK := AddCommGrpCat.ofHom (cocyclePostcomp f n)
  φH := AddCommGrpCat.ofHom (cohomologyClassPostcomp f n)
  commi := by ext; rfl
  commf' := by
    let hK := CochainComplex.HomComplex.leftHomologyData
      ((CochainComplex.singleFunctor C 0).obj Z) K n
    let hL := CochainComplex.HomComplex.leftHomologyData
      ((CochainComplex.singleFunctor C 0).obj Z) L n
    let φ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v} (.up ℤ) n).map
      (homComplexPostcomp (Z := Z) f)
    let φK : hK.K ⟶ hL.K := AddCommGrpCat.ofHom (cocyclePostcomp f n)
    change hK.f' ≫ φK = φ.τ₁ ≫ hL.f'
    have hcommi : φK ≫ hL.i = hK.i ≫ φ.τ₂ := by
      ext
      rfl
    apply (cancel_mono hL.i).1
    calc
      (hK.f' ≫ φK) ≫ hL.i = hK.f' ≫ hK.i ≫ φ.τ₂ := by
        rw [Category.assoc, hcommi]
      _ = ((((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).sc n).f ≫
          φ.τ₂ := by rw [← Category.assoc, hK.f'_i]
      _ = φ.τ₁ ≫ ((((CochainComplex.singleFunctor C 0).obj Z).HomComplex L).sc n).f :=
        φ.comm₁₂.symm
      _ = (φ.τ₁ ≫ hL.f') ≫ hL.i := by rw [Category.assoc, hL.f'_i]
  commπ := by ext; rfl

private lemma homologyAddEquiv_homComplexPostcomp {K L : CochainComplex C ℤ}
    (f : K ⟶ L) (n : ℤ)
    (x : ↑((((CochainComplex.singleFunctor C 0).obj Z).HomComplex K).homology n)) :
    CochainComplex.HomComplex.homologyAddEquiv
        ((CochainComplex.singleFunctor C 0).obj Z) L n
        (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map
          (homComplexPostcomp f)).hom x) =
      cohomologyClassPostcomp f n
        (CochainComplex.HomComplex.homologyAddEquiv
          ((CochainComplex.singleFunctor C 0).obj Z) K n x) := by
  rw [HomologicalComplex.homologyFunctor_map]
  let hK := CochainComplex.HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor C 0).obj Z) K n
  let hL := CochainComplex.HomComplex.leftHomologyData
    ((CochainComplex.singleFunctor C 0).obj Z) L n
  let φ := (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{v} (.up ℤ) n).map
    (homComplexPostcomp (Z := Z) f)
  let γ := homComplexPostcompLeftHomologyMapData (Z := Z) f n
  change (hL.homologyIso.hom).hom ((ShortComplex.homologyMap φ).hom x) =
    (AddCommGrpCat.ofHom (cohomologyClassPostcomp f n)).hom ((hK.homologyIso.hom).hom x)
  exact ConcreteCategory.congr_hom γ.homologyMap_comm x

private def mapXIso (K : CochainComplex C ℕ) (n : ℕ) :
    G.obj (K.X n) ≅ ((G.mapHomologicalComplex (.up ℕ)).obj K).X n :=
  Iso.refl _

private lemma mapXIso_naturality (K : CochainComplex C ℕ) (i j : ℕ) :
    (mapXIso K i).hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d i j =
      G.map (K.d i j) ≫ (mapXIso K j).hom :=
  rfl

private def mapExtendXIso
    (K : CochainComplex C ℕ) (n : ℤ) :
    G.obj ((K.extend ComplexShape.embeddingUpNat).X n) ≅
      (((G.mapHomologicalComplex (.up ℕ)).obj K).extend
        ComplexShape.embeddingUpNat).X n := by
  classical
  exact if h : 0 ≤ n then
      G.mapIso (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
        (Int.toNat_of_nonneg h)) ≪≫
        mapXIso K n.toNat ≪≫
        (HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat (Int.toNat_of_nonneg h)).symm
    else
      IsZero.iso
        (G.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat n
          (fun k hk ↦ h (hk ▸ Int.natCast_nonneg k))))
        (((G.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingUpNat n (fun k hk ↦ h (hk ▸ Int.natCast_nonneg k)))

private lemma mapExtendXIso_natCast (K : CochainComplex C ℕ) (k : ℕ) :
    mapExtendXIso (G := G) K (k : ℤ) =
      G.mapIso (HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f k)) ≪≫
        mapXIso (G := G) K k ≪≫
          (HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)).symm := by
  classical
  simp [mapExtendXIso]

private def mapExtendIso (K : CochainComplex C ℕ) :
    (G.mapHomologicalComplex (.up ℤ)).obj (K.extend ComplexShape.embeddingUpNat) ≅
      ((G.mapHomologicalComplex (.up ℕ)).obj K).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.Hom.isoOfComponents (mapExtendXIso K) fun i j hij ↦ by
    clear hij
    by_cases hi : ∃ k, ComplexShape.embeddingUpNat.f k = i
    · obtain ⟨a, ha⟩ := hi
      have ha' : (a : ℤ) = i := (ComplexShape.embeddingUpNat_f a).symm.trans ha
      clear ha
      subst i
      by_cases hj : ∃ k, ComplexShape.embeddingUpNat.f k = j
      · obtain ⟨b, hb⟩ := hj
        have hb' : (b : ℤ) = j := (ComplexShape.embeddingUpNat_f b).symm.trans hb
        clear hb
        subst j
        rw [mapExtendXIso_natCast (G := G) K a, mapExtendXIso_natCast (G := G) K b]
        rw [Functor.mapHomologicalComplex_obj_d,
          HomologicalComplex.extend_d_eq ((G.mapHomologicalComplex (.up ℕ)).obj K)
            ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)
              (ComplexShape.embeddingUpNat_f b),
          HomologicalComplex.extend_d_eq K ComplexShape.embeddingUpNat
            (ComplexShape.embeddingUpNat_f a) (ComplexShape.embeddingUpNat_f b)]
        let eᵢ := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f a)
        let eⱼ := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
          (ComplexShape.embeddingUpNat_f b)
        let fᵢ := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f a)
        let fⱼ := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
          ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f b)
        let mᵢ := mapXIso (G := G) K a
        let mⱼ := mapXIso (G := G) K b
        change (G.map eᵢ.hom ≫ mᵢ.hom ≫ fᵢ.inv) ≫
            (fᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
              a b ≫ fⱼ.inv) =
          G.map (eᵢ.hom ≫ K.d a b ≫ eⱼ.inv) ≫
            (G.map eⱼ.hom ≫ mⱼ.hom ≫ fⱼ.inv)
        calc
          _ = G.map eᵢ.hom ≫
              (mᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
                a b) ≫ fⱼ.inv := by
            simp [Category.assoc]
          _ = G.map eᵢ.hom ≫
              (G.map (K.d a b) ≫ mⱼ.hom) ≫ fⱼ.inv := by
            rw [show mᵢ.hom ≫ ((G.mapHomologicalComplex (.up ℕ)).obj K).d
                a b = G.map (K.d a b) ≫ mⱼ.hom by
              exact mapXIso_naturality K a b]
          _ = _ := by simp [Functor.map_comp, Category.assoc]
      · exact (((G.mapHomologicalComplex (.up ℕ)).obj K).isZero_extend_X
          ComplexShape.embeddingUpNat j (fun k hk ↦ hj ⟨k, hk⟩) |>.eq_of_tgt _ _)
    · exact (G.map_isZero (K.isZero_extend_X ComplexShape.embeddingUpNat i
        (fun k hk ↦ hi ⟨k, hk⟩)) |>.eq_of_src _ _)

private lemma mapExtendIso_hom_f (K : CochainComplex C ℕ) (n : ℤ) :
    (mapExtendIso (G := G) K).hom.f n = (mapExtendXIso (G := G) K n).hom :=
  rfl

private lemma mapExtendIso_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) :
    (G.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap f ComplexShape.embeddingUpNat) ≫
          (mapExtendIso L).hom =
      (mapExtendIso K).hom ≫
        HomologicalComplex.extendMap
          ((G.mapHomologicalComplex (.up ℕ)).map f) ComplexShape.embeddingUpNat := by
  classical
  apply HomologicalComplex.Hom.ext
  funext n
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    mapExtendIso_hom_f (G := G), mapExtendIso_hom_f (G := G),
    Functor.mapHomologicalComplex_map_f]
  by_cases h : ∃ k, ComplexShape.embeddingUpNat.f k = n
  · obtain ⟨k, hk⟩ := h
    have hk' : (k : ℤ) = n := (ComplexShape.embeddingUpNat_f k).symm.trans hk
    clear hk
    subst n
    rw [HomologicalComplex.extendMap_f f ComplexShape.embeddingUpNat
        (ComplexShape.embeddingUpNat_f k),
      HomologicalComplex.extendMap_f
        ((G.mapHomologicalComplex (.up ℕ)).map f)
        ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)]
    rw [mapExtendXIso_natCast (G := G) K k, mapExtendXIso_natCast (G := G) L k]
    rw [Functor.mapHomologicalComplex_map_f]
    simp only [G.map_comp, Iso.trans_hom, Iso.symm_hom, mapXIso, Iso.refl_hom]
    let eK := HomologicalComplex.extendXIso K ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f k)
    let eL := HomologicalComplex.extendXIso L ComplexShape.embeddingUpNat
      (ComplexShape.embeddingUpNat_f k)
    let gK := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj K)
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)
    let gL := HomologicalComplex.extendXIso ((G.mapHomologicalComplex (.up ℕ)).obj L)
      ComplexShape.embeddingUpNat (ComplexShape.embeddingUpNat_f k)
    change (G.map eK.hom ≫ G.map (f.f k) ≫ G.map eL.inv) ≫
        (G.map eL.hom ≫ 𝟙 _ ≫ gL.inv) =
      (G.map eK.hom ≫ 𝟙 _ ≫ gK.inv) ≫
        (gK.hom ≫ G.map (f.f k) ≫ gL.inv)
    have heL : G.map eL.inv ≫ G.map eL.hom = 𝟙 _ :=
      (G.mapIso eL).inv_hom_id
    have heLgL : G.map eL.inv ≫ G.map eL.hom ≫ gL.inv = gL.inv := by
      rw [← Category.assoc, heL, Category.id_comp]
    have hgK : gK.inv ≫ gK.hom ≫ G.map (f.f k) ≫ gL.inv =
        G.map (f.f k) ≫ gL.inv := by
      exact gK.inv_hom_id_assoc (G.map (f.f k) ≫ gL.inv)
    calc
      _ = G.map eK.hom ≫ G.map (f.f k) ≫ gL.inv := by
        simp only [Category.id_comp, Category.assoc, heLgL]
      _ = _ := by
        simp only [Category.id_comp, Category.assoc]
        apply (cancel_epi (G.mapIso eK).hom).2
        exact hgK.symm
  · exact (((G.mapHomologicalComplex (.up ℕ)).obj L).isZero_extend_X
      ComplexShape.embeddingUpNat n (fun k hk ↦ h ⟨k, hk⟩) |>.eq_of_tgt _ _)

private def extAddEquivHomComplexHomology
    [HasExt.{v} C] (R : InjectiveResolution F) (n : ℕ) :
    Ext.{v} Z F n ≃+
      ↑((((CochainComplex.singleFunctor C 0).obj Z).HomComplex R.cochainComplex).homology n) :=
  (R.extAddEquivCohomologyClass (X := Z)).trans
    (CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor C 0).obj Z) R.cochainComplex n).symm

private lemma extAddEquivHomComplexHomology_naturality
    [HasExt.{v} C] {F' : C} (R : InjectiveResolution F) (R' : InjectiveResolution F')
    (g : F ⟶ F') (φ : InjectiveResolution.Hom R R' g) (n : ℕ) (x : Ext.{v} Z F n) :
    extAddEquivHomComplexHomology R' n (x.comp (Ext.mk₀ g) (add_zero n)) =
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map
        (homComplexPostcomp φ.hom')).hom (extAddEquivHomComplexHomology R n x) := by
  obtain ⟨a, ha, rfl⟩ := R.extMk_surjective x (n + 1) rfl
  rw [R.extMk_comp_mk₀ a (n + 1) rfl ha φ]
  apply (CochainComplex.HomComplex.homologyAddEquiv
    ((CochainComplex.singleFunctor C 0).obj Z) R'.cochainComplex n).injective
  rw [homologyAddEquiv_homComplexPostcomp]
  simp only [extAddEquivHomComplexHomology, AddEquiv.trans_apply,
    AddEquiv.apply_symm_apply, InjectiveResolution.extAddEquivCohomologyClass_apply,
    InjectiveResolution.extEquivCohomologyClass_extMk, cohomologyClassPostcomp_mk]
  congr 1
  have hcomp : (a ≫ φ.hom.f n) ≫ (R'.cochainComplexXIso n n (by lia)).inv =
      (a ≫ (R.cochainComplexXIso n n (by lia)).inv) ≫ φ.hom'.f n := by
    simp [φ.hom'_f n n rfl]
  rw [← CochainComplex.HomComplex.Cocycle.fromSingleMk_postcomp
    (a ≫ (R.cochainComplexXIso n n rfl).inv) (zero_add (n : ℤ))
      ((n + 1 : ℕ) : ℤ) (by lia) (by
        rw [R.cochainComplex_d (n : ℤ) ((n + 1 : ℕ) : ℤ) n (n + 1) rfl rfl]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [← Category.assoc, ha]
        simp
        rfl) φ.hom']
  ext : 1
  simp only [CochainComplex.HomComplex.Cocycle.fromSingleMk_coe]
  exact congrArg
    (fun t ↦ CochainComplex.HomComplex.Cochain.fromSingleMk t (zero_add (n : ℤ))) hcomp

private def homComplexHomologyAddEquivSections
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (f : Z ⟶ X) (g : X ⟶ Y),
      e Y (f ≫ g) = G.map g (e X f))
    (R : InjectiveResolution F) (n : ℕ) :
    ↑((((CochainComplex.singleFunctor C 0).obj Z).HomComplex R.cochainComplex).homology n) ≃+
      ↑(((G.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology n) :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).mapIso
    (homComplexIsoSections e he R.cochainComplex)).addCommGroupIsoToAddEquiv

private lemma homComplexHomologyAddEquivSections_naturality
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (a : Z ⟶ X) (b : X ⟶ Y),
      e Y (a ≫ b) = G.map b (e X a))
    {F' : C} (R : InjectiveResolution F) (R' : InjectiveResolution F')
    (g : F ⟶ F') (φ : InjectiveResolution.Hom R R' g) (n : ℕ)
    (x : ↑((((CochainComplex.singleFunctor C 0).obj Z).HomComplex
      R.cochainComplex).homology n)) :
    homComplexHomologyAddEquivSections e he R' n
        (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map
          (homComplexPostcomp φ.hom')).hom x) =
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map
        ((G.mapHomologicalComplex (.up ℤ)).map φ.hom')).hom
          (homComplexHomologyAddEquivSections e he R n x) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n
  have h := congrArg H.map (homComplexIsoSections_naturality e he φ.hom')
  rw [Functor.map_comp, Functor.map_comp] at h
  have hx := ConcreteCategory.congr_hom h x
  change (H.map (homComplexIsoSections e he R'.cochainComplex).hom).hom
      ((H.map (homComplexPostcomp φ.hom')).hom x) =
    (H.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom')).hom
      ((H.map (homComplexIsoSections e he R.cochainComplex).hom).hom x)
  exact hx

private def sectionsCochainHomologyAddEquivCocomplex
    (R : InjectiveResolution F) (n : ℕ) :
    ↑(((G.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology n) ≃+
      ↑(((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology n) :=
  ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).mapIso
      (mapExtendIso R.cocomplex)).addCommGroupIsoToAddEquiv.trans
    (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat
      (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)).addCommGroupIsoToAddEquiv

private lemma sectionsCochainHomologyAddEquivCocomplex_naturality
    {F' : C} (R : InjectiveResolution F) (R' : InjectiveResolution F')
    (g : F ⟶ F') (φ : InjectiveResolution.Hom R R' g) (n : ℕ)
    (x : ↑(((G.mapHomologicalComplex (.up ℤ)).obj R.cochainComplex).homology n)) :
    sectionsCochainHomologyAddEquivCocomplex R' n
        (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n).map
          ((G.mapHomologicalComplex (.up ℤ)).map φ.hom')).hom x) =
      ((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℕ) n).map
        ((G.mapHomologicalComplex (.up ℕ)).map φ.hom)).hom
          (sectionsCochainHomologyAddEquivCocomplex R n x) := by
  let HZ := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℤ) n
  let HN := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℕ) n
  let fN := (G.mapHomologicalComplex (.up ℕ)).map φ.hom
  let fE := HomologicalComplex.extendMap fN ComplexShape.embeddingUpNat
  have hmap :
      (G.mapHomologicalComplex (.up ℤ)).map φ.hom' ≫ (mapExtendIso R'.cocomplex).hom =
        (mapExtendIso R.cocomplex).hom ≫ fE := by
    simpa [InjectiveResolution.cochainComplex, InjectiveResolution.Hom.hom', fN, fE] using
      mapExtendIso_naturality (G := G) φ.hom
  have hmapH :
      HZ.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
          HZ.map (mapExtendIso R'.cocomplex).hom =
        HZ.map (mapExtendIso R.cocomplex).hom ≫ HZ.map fE := by
    rw [← Functor.map_comp, ← Functor.map_comp, hmap]
    rfl
  have hext : HZ.map fE ≫
        (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat rfl).hom =
      (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat rfl).hom ≫ HN.map fN := by
    change HomologicalComplex.homologyMap fE (n : ℤ) ≫
        (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat rfl).hom =
      (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
          ComplexShape.embeddingUpNat rfl).hom ≫ HomologicalComplex.homologyMap fN n
    exact HomologicalComplex.extendHomologyIso_hom_naturality fN
      ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f n = (n : ℤ) from rfl)
  have htotal :
      (HZ.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom') ≫
          HZ.map (mapExtendIso R'.cocomplex).hom) ≫
            (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
              ComplexShape.embeddingUpNat rfl).hom =
        (HZ.map (mapExtendIso R.cocomplex).hom ≫
          (((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat rfl).hom) ≫ HN.map fN := by
    calc
      _ = (HZ.map (mapExtendIso R.cocomplex).hom ≫ HZ.map fE) ≫
          (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat rfl).hom :=
        congrArg (fun q ↦ q ≫
          (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat rfl).hom) hmapH
      _ = HZ.map (mapExtendIso R.cocomplex).hom ≫
          (HZ.map fE ≫
            (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
              ComplexShape.embeddingUpNat rfl).hom) := Category.assoc _ _ _
      _ = HZ.map (mapExtendIso R.cocomplex).hom ≫
          ((((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
            ComplexShape.embeddingUpNat rfl).hom ≫ HN.map fN) :=
        congrArg (fun q ↦ HZ.map (mapExtendIso R.cocomplex).hom ≫ q) hext
      _ = _ := (Category.assoc _ _ _).symm
  have hx := ConcreteCategory.congr_hom htotal x
  change (((G.mapHomologicalComplex (.up ℕ)).obj R'.cocomplex).extendHomologyIso
      ComplexShape.embeddingUpNat rfl).hom.hom
        ((HZ.map (mapExtendIso R'.cocomplex).hom).hom
          ((HZ.map ((G.mapHomologicalComplex (.up ℤ)).map φ.hom')).hom x)) =
    (HN.map fN).hom
      ((((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).extendHomologyIso
        ComplexShape.embeddingUpNat rfl).hom.hom
          ((HZ.map (mapExtendIso R.cocomplex).hom).hom x))
  exact hx

private def sectionsCocomplexHomologyAddEquivRightDerived
    [HasInjectiveResolutions C] (R : InjectiveResolution F) (n : ℕ) :
    ↑(((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology n) ≃+
      ↑((G.rightDerived n).obj F) :=
  (R.isoRightDerivedObj G n).symm.addCommGroupIsoToAddEquiv

private lemma sectionsCocomplexHomologyAddEquivRightDerived_naturality
    [HasInjectiveResolutions C]
    {F' : C} (R : InjectiveResolution F) (R' : InjectiveResolution F')
    (g : F ⟶ F') (φ : InjectiveResolution.Hom R R' g) (n : ℕ)
    (x : ↑(((G.mapHomologicalComplex (.up ℕ)).obj R.cocomplex).homology n)) :
    sectionsCocomplexHomologyAddEquivRightDerived R' n
        (((HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℕ) n).map
          ((G.mapHomologicalComplex (.up ℕ)).map φ.hom)).hom x) =
      ((G.rightDerived n).map g).hom
        (sectionsCocomplexHomologyAddEquivRightDerived R n x) := by
  let HN := HomologicalComplex.homologyFunctor AddCommGrpCat.{v} (.up ℕ) n
  let fN := (G.mapHomologicalComplex (.up ℕ)).map φ.hom
  have h := InjectiveResolution.isoRightDerivedObj_inv_naturality g R R' φ.hom
    (by simpa using φ.ι_f_zero_comp_hom_f_zero) G n
  have hx := ConcreteCategory.congr_hom h x
  change (R'.isoRightDerivedObj G n).inv.hom ((HN.map fN).hom x) =
    ((G.rightDerived n).map g).hom ((R.isoRightDerivedObj G n).inv.hom x)
  exact hx.symm

/-- If an additive functor is represented by `Z`, then `Extⁿ(Z, -)` agrees with its
right-derived functor in degree `n`. -/
noncomputable def addEquivRightDerived
    [HasExt.{v} C] [HasInjectiveResolutions C]
    (G : C ⥤ AddCommGrpCat.{v}) [G.Additive] (Z F : C)
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (f : Z ⟶ X) (g : X ⟶ Y),
      e Y (f ≫ g) = G.map g (e X f)) (n : ℕ) :
    Ext.{v} Z F n ≃+ ↑((G.rightDerived n).obj F) :=
  let R := injectiveResolution F
  (extAddEquivHomComplexHomology R n).trans
    ((homComplexHomologyAddEquivSections e he R n).trans
      ((sectionsCochainHomologyAddEquivCocomplex R n).trans
        (sectionsCocomplexHomologyAddEquivRightDerived R n)))

/-- The comparison between represented `Ext` and the right-derived functor is natural
in the derived variable. -/
theorem addEquivRightDerived_naturality
    [HasExt.{v} C] [HasInjectiveResolutions C]
    (G : C ⥤ AddCommGrpCat.{v}) [G.Additive] (Z : C)
    (e : ∀ X : C, (Z ⟶ X) ≃+ ↑(G.obj X))
    (he : ∀ {X Y : C} (a : Z ⟶ X) (b : X ⟶ Y),
      e Y (a ≫ b) = G.map b (e X a))
    {F F' : C} (f : F ⟶ F') (n : ℕ) (x : Ext.{v} Z F n) :
    addEquivRightDerived G Z F' e he n (((Ext.mk₀ f).postcomp Z (add_zero n)) x) =
      ((G.rightDerived n).map f).hom (addEquivRightDerived G Z F e he n x) := by
  let R := injectiveResolution F
  let R' := injectiveResolution F'
  let φ : InjectiveResolution.Hom R R' f :=
    { hom := InjectiveResolution.desc f R' R
      ι_f_zero_comp_hom_f_zero := by
        simpa using InjectiveResolution.desc_commutes_zero f R' R }
  change sectionsCocomplexHomologyAddEquivRightDerived R' n
      (sectionsCochainHomologyAddEquivCocomplex R' n
        (homComplexHomologyAddEquivSections e he R' n
          (extAddEquivHomComplexHomology R' n (x.comp (Ext.mk₀ f) (add_zero n))))) =
    ((G.rightDerived n).map f).hom
      (sectionsCocomplexHomologyAddEquivRightDerived R n
        (sectionsCochainHomologyAddEquivCocomplex R n
          (homComplexHomologyAddEquivSections e he R n
            (extAddEquivHomComplexHomology R n x))))
  rw [extAddEquivHomComplexHomology_naturality R R' f φ n x]
  rw [homComplexHomologyAddEquivSections_naturality e he R R' f φ n]
  rw [sectionsCochainHomologyAddEquivCocomplex_naturality R R' f φ n]
  exact sectionsCocomplexHomologyAddEquivRightDerived_naturality R R' f φ n _

end

end CategoryTheory.Abelian.Ext

open TopologicalSpace

namespace TopCat.Sheaf

noncomputable section

variable {X : TopCat.{u}}

private abbrev J (X : TopCat.{u}) := Opens.grothendieckTopology X

private abbrev globalSections (X : TopCat.{u}) :
    CategoryTheory.Sheaf (J X) AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ (J X) AddCommGrpCat.{u}

private abbrev constantZ (X : TopCat.{u}) :
    CategoryTheory.Sheaf (J X) AddCommGrpCat.{u} :=
  (CategoryTheory.constantSheaf (J X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

noncomputable local instance : (globalSections X).Additive :=
  (CategoryTheory.constantSheafΓAdj (J X) AddCommGrpCat.{u}).right_adjoint_additive

private def homToGlobalSectionsEquiv
    (F : CategoryTheory.Sheaf (J X) AddCommGrpCat.{u}) :
    (constantZ X ⟶ F) ≃+ ↑((globalSections X).obj F) :=
  ((CategoryTheory.constantSheafΓAdj (J X) AddCommGrpCat.{u}).homAddEquiv
      (AddCommGrpCat.of (ULift.{u} ℤ)) F).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv ((globalSections X).obj F))

private lemma homToGlobalSectionsEquiv_naturality
    {F G : CategoryTheory.Sheaf (J X) AddCommGrpCat.{u}}
    (f : constantZ X ⟶ F) (g : F ⟶ G) :
    homToGlobalSectionsEquiv G (f ≫ g) =
      (globalSections X).map g (homToGlobalSectionsEquiv F f) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((CategoryTheory.constantSheafΓAdj (J X) AddCommGrpCat.{u}).homEquiv _ _ (f ≫ g)) = _
  rw [(CategoryTheory.constantSheafΓAdj
    (J X) AddCommGrpCat.{u}).homEquiv_naturality_right]
  rfl

/-- Sheaf cohomology agrees with the right-derived functors of global sections. -/
noncomputable def H.addEquivRightDerivedGlobalSections
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H F n ≃+ ↑(((globalSections X).rightDerived n).obj (toSiteSheaf F)) := by
  exact CategoryTheory.Abelian.Ext.addEquivRightDerived
    (globalSections X) (constantZ X) (toSiteSheaf F)
    homToGlobalSectionsEquiv
    (fun f g ↦ homToGlobalSectionsEquiv_naturality f g) n

/-- The identification of sheaf cohomology with derived global sections commutes with
morphisms of sheaves. -/
theorem H.addEquivRightDerivedGlobalSections_naturality
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (n : ℕ) (x : H F n) :
    H.addEquivRightDerivedGlobalSections G n (H.map f n x) =
      (((globalSections X).rightDerived n).map f).hom
        (H.addEquivRightDerivedGlobalSections F n x) := by
  exact CategoryTheory.Abelian.Ext.addEquivRightDerived_naturality
    (globalSections X) (constantZ X) homToGlobalSectionsEquiv
      (fun a b ↦ homToGlobalSectionsEquiv_naturality a b) f n x

end

end TopCat.Sheaf
