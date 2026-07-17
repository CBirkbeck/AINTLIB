import Mathlib.AlgebraicGeometry.Morphisms.Affine
import ModularCurves.ForMathlib.KempfInduction
import ModularCurves.ForMathlib.SchemeModuleQuasicoherent
import ModularCurves.ForMathlib.SchemeModuleSheaf

/-!
# Affine vanishing for quasicoherent modules

This file proves that positive-degree sheaf cohomology vanishes for a quasicoherent module on an
affine scheme. The proof is Kempf's induction: kill a class on a finite affine-open cover, embed
the module into the product of the restriction-pushforwards, and dimension-shift through its
cokernel.
-/

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open TopCat TopCat.Sheaf

variable {X : Scheme.{u}} (F : X.Modules)

private noncomputable def topCatFunctorH (X : TopCat.{u}) (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} where
  obj G := AddCommGrpCat.of (H G n)
  map f := AddCommGrpCat.ofHom (H.map f n)
  map_id G := by
    ext c
    exact CategoryTheory.Sheaf.H.map_id_apply c
  map_comp f g := by
    ext c
    exact CategoryTheory.Sheaf.H.map_comp_apply f g c

private instance (X : TopCat.{u}) (n : ℕ) : (topCatFunctorH X n).Additive where
  map_add := by
    intro G K f g
    ext c
    exact CategoryTheory.Sheaf.H.map_add_apply f g c

private lemma topCatFunctorH_map_comp_eq {G K L : TopCat.Sheaf AddCommGrpCat.{u} X}
    {f : G ⟶ K} {g : K ⟶ L} {h : G ⟶ L} (e : f ≫ g = h)
    (n : ℕ) (c : H G n) :
    (topCatFunctorH X n).map g ((topCatFunctorH X n).map f c) =
      (topCatFunctorH X n).map h c := by
  subst h
  exact (CategoryTheory.Sheaf.H.map_comp_apply f g c).symm

private lemma H_equiv₀_naturality {G K : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : G ⟶ K) (x : H G 0) :
    f.hom.app (op ⊤) (H.equiv₀ G x) = H.equiv₀ K (H.map f 0 x) := by
  exact CategoryTheory.Sheaf.H.equiv₀_naturality
    (T := (⊤ : Opens X)) isTerminalTop f x

section RestrictionAdjunction

variable {U : Scheme.{u}} (f : U ⟶ X) [hf : IsOpenImmersion f]

/-- Forgetting module structure identifies the module restriction unit with the additive-sheaf
restriction unit. -/
lemma restrictAdjunction_sheafHom : ((restrictAdjunction f).unit.app F).sheafHom =
    (TopCat.Sheaf.restrictPushforwardAdjunction _ hf.base_open).unit.app F.sheaf := by
  rfl

lemma restrictAdjunction_toRestrict (U : X.Opens) :
    ((restrictAdjunction U.ι).unit.app F).sheafHom =
      (TopCat.Sheaf.toRestrict _ U).app F.sheaf := by
  apply restrictAdjunction_sheafHom

end RestrictionAdjunction

section CoverSheaf

variable {I : Type u} (U : I → X.Opens)

/-- The map from a module to the product of the pushforwards of its restrictions to an open
family. -/
noncomputable def toCoverSheaf :
    F ⟶ ∏ᶜ fun i ↦ (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F :=
  Pi.lift fun i ↦ (restrictAdjunction (U i).ι).unit.app F

theorem coverSheaf_isQuasicoherent [IsAffine X] [F.IsQuasicoherent] [Finite I]
    [∀ i, IsAffine (U i)] :
    (∏ᶜ fun i ↦ (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F).IsQuasicoherent := by
  refine (isQuasicoherent X).prop_limit (Discrete.functor _) fun _ ↦ ?_
  simp only [Functor.comp_obj, Discrete.functor_obj_eq_as, isQuasicoherent_def]
  infer_instance

@[simp]
lemma toCoverSheaf_comp_pi (i : I) :
    F.toCoverSheaf U ≫
      Pi.π (fun i ↦ (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i =
        (restrictAdjunction (U i).ι).unit.app F := by
  simp [toCoverSheaf]

private lemma toCoverSheaf_sheafHom_comp_pi (i : I) :
    (F.toCoverSheaf U).sheafHom ≫
      (Pi.π (fun i ↦
        (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i).sheafHom =
      ((restrictAdjunction (U i).ι).unit.app F).sheafHom := by
  change (toSheaf X).map (F.toCoverSheaf U) ≫
      (toSheaf X).map
        (Pi.π (fun i ↦
          (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i) =
    (toSheaf X).map ((restrictAdjunction (U i).ι).unit.app F)
  rw [← Functor.map_comp, toCoverSheaf_comp_pi]

private lemma toCoverSheaf_sheafHom_comp_pi_toRestrict (i : I) :
    (F.toCoverSheaf U).sheafHom ≫
      (Pi.π (fun i ↦
        (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i).sheafHom =
      (toRestrict _ (U i)).app F.sheaf :=
  (toCoverSheaf_sheafHom_comp_pi F U i).trans
    (restrictAdjunction_toRestrict F (U i))

private lemma toCoverSheaf_comp_pi_apply {V : X.Opens}
    (s : F.sheaf.obj.obj (op V)) (i : I) :
    (Pi.π (fun i ↦ (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i).sheafHom.hom.app
        (op V) ((F.toCoverSheaf U).sheafHom.hom.app (op V) s) =
      ((restrictAdjunction (U i).ι).unit.app F).sheafHom.hom.app (op V) s := by
  exact TopCat.Sheaf.comp_app_apply (toCoverSheaf_sheafHom_comp_pi F U i) (op V) s

private lemma toCoverSheaf_sheafHom_injective (hU : IsOpenCover U)
    (W : (Opens X)ᵒᵖ) : Function.Injective ((F.toCoverSheaf U).sheafHom.hom.app W) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  refine TopCat.Presheaf.IsSheaf.section_ext F.sheaf.property fun x hx ↦ ?_
  obtain ⟨i, hi⟩ := hU.exists_mem x
  refine ⟨(unop W) ⊓ U i, inf_le_left, ⟨by simpa using ⟨hx, hi⟩, ?_⟩⟩
  rw [map_zero]
  have hzero :
      ((restrictAdjunction (U i).ι).unit.app F).sheafHom.hom.app W s = 0 := by
    have h := congr(
      (Pi.π (fun i ↦ (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i).sheafHom.hom.app
        W $(hs))
    rw [map_zero] at h
    exact (toCoverSheaf_comp_pi_apply F U s i).symm.trans h
  rw [restrictAdjunction_sheafHom] at hzero
  simp only [Functor.id_obj] at hzero
  have hle : (unop W) ⊓ U i ≤
      (U i).isOpenEmbedding.functor.obj ((Opens.map (U i).inclusion').obj (unop W)) := by
    aesop
  let q := (U i).isOpenEmbedding.isOpenMap.adjunction.counit.app (unop W)
  change F.sheaf.obj.map q.op s = 0 at hzero
  have harrow : q.op ≫ (homOfLE hle).op = (homOfLE inf_le_left).op :=
    Subsingleton.elim _ _
  calc
    F.sheaf.obj.map (homOfLE inf_le_left).op s =
        F.sheaf.obj.map (q.op ≫ (homOfLE hle).op) s := by
      rw [harrow]
    _ = F.sheaf.obj.map (homOfLE hle).op (F.sheaf.obj.map q.op s) := by
      rw [Functor.map_comp]
      rfl
    _ = F.sheaf.obj.map (homOfLE hle).op 0 := by
      rw [hzero]
    _ = 0 := by
      rw [map_zero]

/-- If the opens cover, the map to the product of restriction-pushforwards is monic. -/
theorem toCoverSheaf_mono (hU : IsOpenCover U) : Mono (F.toCoverSheaf U) := by
  have hs : Mono (F.toCoverSheaf U).sheafHom := by
    refine CategoryTheory.Sheaf.mono_of_injective _ ?_
    exact F.toCoverSheaf_sheafHom_injective U hU
  exact Functor.mono_of_mono_map (SheafOfModules.toSheaf X.ringCatSheaf) hs

/-- If a cohomology class restricts to zero on every member of a finite family, its image under
the map to the product of restriction-pushforwards is zero. -/
theorem toCoverSheaf_H_map_zero (n : ℕ) (c : H F.sheaf n) [Finite I]
    (h : ∀ i, H.map ((toRestrict _ (U i)).app F.sheaf) n c = 0) :
    H.map (F.toCoverSheaf U).sheafHom n c = 0 := by
  haveI : (toSheaf X ⋙ topCatFunctorH X n).Additive := inferInstance
  change (toSheaf X ⋙ topCatFunctorH X n).map (F.toCoverSheaf U) c = 0
  apply Limits.Concrete.Pi.map_ext
  intro i
  rw [map_zero]
  change (topCatFunctorH X n).map (Pi.π (fun i ↦
      (restrictFunctor (U i).ι ⋙ pushforward (U i).ι).obj F) i).sheafHom
      ((topCatFunctorH X n).map (F.toCoverSheaf U).sheafHom c) = 0
  have hcomp := topCatFunctorH_map_comp_eq
    (toCoverSheaf_sheafHom_comp_pi_toRestrict F U i) n c
  exact hcomp.trans (h i)

end CoverSheaf

private lemma affineOpens_inf [IsAffine X] (U V : X.Opens)
    (hU : U ∈ X.affineOpens) (hV : V ∈ X.affineOpens) : U ⊓ V ∈ X.affineOpens :=
  ((diagonal_isAffine_iff_forall_isAffineOpen_inf (𝟙 X)).mp
    (fun _ _ _ _ ↦ inferInstance)) U V hU hV

private lemma H_zero_surjective_of_quasicoherent_epi [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] : Function.Surjective (H.map f.sheafHom 0) := by
  intro y
  obtain ⟨x, hx⟩ := isQuasicoherent_surjective_of_epi f
    (H.equiv₀ N.sheaf y)
  refine ⟨(H.equiv₀ M.sheaf).symm x, ?_⟩
  have hnat := H_equiv₀_naturality f.sheafHom ((H.equiv₀ M.sheaf).symm x)
  have hsource : f.sheafHom.hom.app (op ⊤)
      (H.equiv₀ M.sheaf ((H.equiv₀ M.sheaf).symm x)) =
      f.sheafHom.hom.app (op ⊤) x :=
    congrArg (f.sheafHom.hom.app (op ⊤)) ((H.equiv₀ M.sheaf).apply_symm_apply x)
  have hnat' : f.sheafHom.hom.app (op ⊤) x =
      H.equiv₀ N.sheaf (H.map f.sheafHom 0 ((H.equiv₀ M.sheaf).symm x)) :=
    hsource.symm.trans hnat
  apply (H.equiv₀ N.sheaf).injective
  exact hnat'.symm.trans hx

private lemma H_map_injective_of_subsingleton_cokernel
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)}
    (hS : S.ShortExact) (n : ℕ) [Subsingleton (H S.X₃ n)] :
    Function.Injective (H.map S.f (n + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨x, hx⟩ := CategoryTheory.Sheaf.H.longSequence_exact₁
    hS n (n + 1) rfl c hc
  rw [← hx, Subsingleton.elim x 0, map_zero]

private theorem affine_H_one_subsingleton [IsAffine X] [F.IsQuasicoherent] :
    Subsingleton (H F.sheaf 1) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨I, U', hU', vanish⟩ := TopCat.Sheaf.kempfProp1 F.sheaf 0
    X.isBasis_affineOpens affineOpens_inf
    (by
      intro r U hr₁ hr₂ hU
      omega) c
  obtain ⟨s, hU⟩ := hU'.exists_finite_of_compactSpace
  let U : s → X.Opens := fun i ↦ U' i.1
  have hAffine : ∀ i, IsAffine (U i) := fun i ↦ (vanish i.1).1
  letI (i : s) : IsAffine (U i) := hAffine i
  haveI : Mono (F.toCoverSheaf U) := F.toCoverSheaf_mono U hU
  let S := ShortComplex.mk (F.toCoverSheaf U)
    (cokernel.π (F.toCoverSheaf U)) (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel (F.toCoverSheaf U))
  let Ssheaf := S.map (toSheaf X)
  have hSsheaf : Ssheaf.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS (toSheaf X)
  letI : S.X₂.IsQuasicoherent := F.coverSheaf_isQuasicoherent U
  letI : S.X₃.IsQuasicoherent :=
    (isQuasicoherent X).prop_colimit (parallelPair _ 0) (by
      intro j
      cases j with
      | zero =>
          change F.IsQuasicoherent
          infer_instance
      | one =>
          change S.X₂.IsQuasicoherent
          infer_instance)
  have hsurj : Function.Surjective (H.map Ssheaf.g 0) := by
    change Function.Surjective (H.map S.g.sheafHom 0)
    exact H_zero_surjective_of_quasicoherent_epi S.g
  obtain ⟨x₃, hx₃⟩ := CategoryTheory.Sheaf.H.longSequence_exact₁
    hSsheaf 0 1 rfl c (by
      change H.map (F.toCoverSheaf U).sheafHom 1 c = 0
      exact F.toCoverSheaf_H_map_zero U 1 c fun i ↦ (vanish i.1).2)
  obtain ⟨x₂, hx₂⟩ := hsurj x₃
  rw [← hx₃, ← hx₂]
  exact CategoryTheory.Sheaf.H.longSequence_comp_zero₃ hSsheaf 0 1 rfl x₂

private theorem affine_H_succ_subsingleton [IsAffine X] [F.IsQuasicoherent]
    (n : ℕ)
    (hi : ∀ m ≤ n, ∀ {Y : Scheme.{u}} (G : Y.Modules)
      [IsAffine Y] [G.IsQuasicoherent], Subsingleton (H G.sheaf (m + 1))) :
    Subsingleton (H F.sheaf (n + 1 + 1)) := by
  refine subsingleton_of_forall_eq 0 fun c ↦ ?_
  obtain ⟨I, U', hU', vanish⟩ := TopCat.Sheaf.kempfProp1 F.sheaf (n + 1)
    X.isBasis_affineOpens affineOpens_inf
    (by
      intro r U hr₁ hr₂ hU
      letI : IsAffine U := hU
      have hsub := hi (r - 1) (by omega) (F.restrict (Scheme.Opens.ι U))
      rw [Nat.sub_add_cancel hr₁] at hsub
      exact hsub) c
  obtain ⟨s, hU⟩ := hU'.exists_finite_of_compactSpace
  let U : s → X.Opens := fun i ↦ U' i.1
  have hAffine : ∀ i, IsAffine (U i) := fun i ↦ (vanish i.1).1
  letI (i : s) : IsAffine (U i) := hAffine i
  haveI : Mono (F.toCoverSheaf U) := F.toCoverSheaf_mono U hU
  let S := ShortComplex.mk (F.toCoverSheaf U)
    (cokernel.π (F.toCoverSheaf U)) (cokernel.condition _)
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel (F.toCoverSheaf U))
  let Ssheaf := S.map (toSheaf X)
  have hSsheaf : Ssheaf.ShortExact :=
    ShortComplex.ShortExact.map_of_exact hS (toSheaf X)
  letI : S.X₂.IsQuasicoherent := F.coverSheaf_isQuasicoherent U
  letI : S.X₃.IsQuasicoherent :=
    (isQuasicoherent X).prop_colimit (parallelPair _ 0) (by
      intro j
      cases j with
      | zero =>
          change F.IsQuasicoherent
          infer_instance
      | one =>
          change S.X₂.IsQuasicoherent
          infer_instance)
  have hcoker : Subsingleton (H S.X₃.sheaf (n + 1)) := hi n (le_refl n) S.X₃
  letI : Subsingleton (H Ssheaf.X₃ (n + 1)) := hcoker
  have hinj : Function.Injective (H.map Ssheaf.f (n + 1 + 1)) :=
    H_map_injective_of_subsingleton_cokernel hSsheaf (n + 1)
  apply (injective_iff_map_eq_zero _).mp hinj
  change H.map (F.toCoverSheaf U).sheafHom (n + 1 + 1) c = 0
  exact F.toCoverSheaf_H_map_zero U (n + 1 + 1) c fun i ↦ (vanish i.1).2

/-- Positive-degree sheaf cohomology vanishes for a quasicoherent module on an affine scheme. -/
theorem affine_subsingleton_H [IsAffine X] [F.IsQuasicoherent] (n : ℕ) :
    Subsingleton (H F.sheaf (n + 1)) := by
  revert F X
  refine Nat.case_strong_induction_on
    (p := fun n ↦ ∀ {X : Scheme.{u}} (F : X.Modules)
      [IsAffine X] [F.IsQuasicoherent], Subsingleton (H F.sheaf (n + 1)))
    n ?_ ?_
  · intro X F _ _
    exact affine_H_one_subsingleton F
  · intro n hi X F _ _
    exact affine_H_succ_subsingleton F n hi

instance [IsAffine X] [F.IsQuasicoherent] (n : ℕ) :
    Subsingleton (H F.sheaf (n + 1)) :=
  affine_subsingleton_H F n

end AlgebraicGeometry.Scheme.Modules
