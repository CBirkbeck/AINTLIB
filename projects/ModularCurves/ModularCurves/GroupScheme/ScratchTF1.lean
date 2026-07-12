import ModularCurves.GroupScheme.TorsionEtaleTriv
open AlgebraicGeometry CategoryTheory Limits
open scoped TensorProduct
universe u
namespace ModularCurves.EllipticCurve

theorem torsion_etaleLocal_triv_affine {R : CommRingCat.{u}} (E : EllipticCurve (Spec R))
    (N : ℕ) [NeZero N] (hinv : NIsInvertible (Spec R) N) :
    ∃ (T : Scheme.{u}) (p : T ⟶ Spec R), Etale p ∧ Surjective p ∧
      Nonempty (Over.mk (pullback.snd (E.torsionπ N) p) ≅
        Over.mk (constSchemeπ T (Fin 2 → ZMod N))) := by
  haveI hfinite : IsFinite (E.torsionπ N) := E.torsionπ_isFinite N
  haveI hetale : Etale (E.torsionπ N) := E.torsionπ_etale N hinv
  haveI : IsAffine (E.torsion N) := isAffine_of_isAffineHom (E.torsionπ N)
  set φ : R ⟶ Γ(E.torsion N, ⊤) :=
    Spec.preimage ((E.torsion N).isoSpec.inv ≫ E.torsionπ N) with hφ
  have hspecmap : Spec.map φ = (E.torsion N).isoSpec.inv ≫ E.torsionπ N := by
    rw [hφ, Spec.map_preimage]
  haveI hspecE : Etale (Spec.map φ) := by
    rw [hspecmap]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @Etale)
      (E.torsion N).isoSpec.inv (E.torsionπ N)).mpr hetale
  haveI hspecF : IsFinite (Spec.map φ) := by
    rw [hspecmap]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := @IsFinite)
      (E.torsion N).isoSpec.inv (E.torsionπ N)).mpr hfinite
  letI : Algebra R (Γ(E.torsion N, ⊤)) := φ.hom.toAlgebra
  haveI : Algebra.Etale R (Γ(E.torsion N, ⊤)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mp hspecE
  haveI : Module.Finite R (Γ(E.torsion N, ⊤)) := (IsFinite.SpecMap_iff φ).mp hspecF
  haveI hflatMod : Module.Flat R (Γ(E.torsion N, ⊤)) := inferInstance
  have hAlg : Spec.map (CommRingCat.ofHom (algebraMap R (Γ(E.torsion N, ⊤)))) = Spec.map φ := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom]
  have hrank : Module.rankAtStalk (R := R) (Γ(E.torsion N, ⊤)) = (N ^ 2 : ℕ) := by
    funext x
    rw [← Scheme.Hom.finrank_SpecMap_algebraMap R (Γ(E.torsion N, ⊤)) x, hAlg, hspecmap,
      Scheme.Hom.finrank_comp_left_of_isIso, E.torsion_rank N x]
    simp
  obtain ⟨Tr, _, _, hff, hfinT, hetT, hsplit⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale
      (R := R) (S := Γ(E.torsion N, ⊤)) hrank
  have hrankTr : Module.rankAtStalk (R := Tr) (Tr ⊗[R] (Γ(E.torsion N, ⊤))) = (N ^ 2 : ℕ) := by
    funext p
    rw [Module.rankAtStalk_baseChange]
    exact congrFun hrank _
  have hcard : Fintype.card (Fin 2 → ZMod N) = N ^ 2 := by
    simp [ZMod.card, pow_two]
  let eCard : Fin (N ^ 2) ≃ (Fin 2 → ZMod N) := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨eSplit⟩ := isFiniteSplit_algEquiv_fin_of_rankAtStalk hrankTr
  let algChain : (Tr ⊗[R] (Γ(E.torsion N, ⊤))) ≃ₐ[Tr] ((Fin 2 → ZMod N) → Tr) :=
    eSplit.trans (AlgEquiv.piCongrLeft' Tr (fun _ : Fin (N ^ 2) => Tr) eCard)
  -- the split cover and its structure map
  set fA : R ⟶ Γ(E.torsion N, ⊤) := CommRingCat.ofHom (algebraMap R (Γ(E.torsion N, ⊤))) with hfA
  set pmap : Spec (CommRingCat.of Tr) ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R Tr)) with hpmap
  -- transport pullback(torsionπ) ≅ pullback(Spec.map fA)
  have htp : (E.torsion N).isoSpec.hom ≫ Spec.map fA = E.torsionπ N := by
    rw [hAlg, hspecmap, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let t1 : pullback (E.torsionπ N) pmap ≅ pullback (Spec.map fA) pmap :=
    asIso (pullback.map (E.torsionπ N) pmap (Spec.map fA) pmap (E.torsion N).isoSpec.hom
      (𝟙 _) (𝟙 _) (by rw [Category.comp_id, htp]) (by rw [Category.comp_id, Category.id_comp]))
  let t2 : pullback (Spec.map fA) pmap ≅ pullback pmap (Spec.map fA) := pullbackSymmetry _ _
  let t3 : pullback pmap (Spec.map fA) ≅ Spec (CommRingCat.of (Tr ⊗[R] (Γ(E.torsion N, ⊤)))) :=
    pullbackSpecIso R Tr (Γ(E.torsion N, ⊤))
  let t4 : Spec (CommRingCat.of (Tr ⊗[R] (Γ(E.torsion N, ⊤)))) ≅
      Spec (CommRingCat.of ((Fin 2 → ZMod N) → Tr)) :=
    Scheme.Spec.mapIso (algChain.toRingEquiv.toCommRingCatIso).symm.op
  let t5 : Spec (CommRingCat.of ((Fin 2 → ZMod N) → Tr)) ≅
      constScheme (Spec (CommRingCat.of Tr)) (Fin 2 → ZMod N) :=
    (constSchemeSpecIso (CommRingCat.of Tr) (Fin 2 → ZMod N)).symm
  let e : pullback (E.torsionπ N) pmap ≅ constScheme (Spec (CommRingCat.of Tr)) (Fin 2 → ZMod N) :=
    t1 ≪≫ t2 ≪≫ t3 ≪≫ t4 ≪≫ t5
  refine ⟨Spec (CommRingCat.of Tr), pmap, ?_, ?_, ⟨Over.isoMk e ?_⟩⟩
  · rw [hpmap]
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hetT)
  · rw [hpmap]
    exact ((flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap R Tr))).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr hff)).2
  · show e.hom ≫ constSchemeπ (Spec (CommRingCat.of Tr)) (Fin 2 → ZMod N)
        = pullback.snd (E.torsionπ N) pmap
    have ht5 : t5.hom ≫ constSchemeπ (Spec (CommRingCat.of Tr)) (Fin 2 → ZMod N)
        = Spec.map (CommRingCat.ofHom (Pi.constRingHom (Fin 2 → ZMod N) Tr)) := by
      have h := constSchemeSpecIso_hom_π (CommRingCat.of Tr) (Fin 2 → ZMod N)
      rw [show t5.hom = (constSchemeSpecIso (CommRingCat.of Tr) (Fin 2 → ZMod N)).inv from rfl,
        ← h, Iso.inv_hom_id_assoc]
    simp only [e, Iso.trans_hom, Category.assoc, ht5]
    have ht4 : t4.hom ≫ Spec.map (CommRingCat.ofHom (Pi.constRingHom (Fin 2 → ZMod N) Tr))
        = Spec.map (CommRingCat.ofHom (algebraMap Tr (Tr ⊗[R] (Γ(E.torsion N, ⊤))))) := by
      have hh : t4.hom = Spec.map algChain.toRingEquiv.toCommRingCatIso.inv := by
        rw [show t4.hom
          = Scheme.Spec.map algChain.toRingEquiv.toCommRingCatIso.symm.op.hom from rfl,
          Scheme.Spec_map]
      rw [hh, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      ext t
      exact algChain.symm.commutes t
    rw [ht4, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]
    simp [t1]

end ModularCurves.EllipticCurve
