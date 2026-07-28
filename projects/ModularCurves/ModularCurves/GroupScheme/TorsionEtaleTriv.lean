import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.GroupScheme.MuN
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Flat.Rank
import ModularCurves.ForMathlib.BaseChangeAlongCompat

/-!
# T-F1-general — the étale-local trivialisation of `E[N]` (KM 2.3.1)

**Interface pin (CHARTER-C5B-2, owned by c5β; consumed by NEW-Y1's CLOPEN-β descent geometry).**

KM 2.3.1: for `N` invertible on `S`, the group scheme `E[N]` is *finite étale over `S`, locally
for the étale topology on `S` isomorphic to `ℤ/NZ × ℤ/NZ`*. This file states that étale-local
structure as `torsion_etaleLocal_triv`: `E[N]` is trivialised by a surjective étale cover
`p : T ⟶ S`, over which `E[N] ×_S T` is isomorphic (as a `T`-scheme) to the constant scheme
`(ℤ/N)²_T = constScheme T (Fin 2 → ZMod N)`.

The proof (c5β's L2b) goes via the fibrewise-iso ⟹ iso criterion
(`isIso_of_isPullback_of_fppf`) on the finite-étale `torsionπ_etale`; NEW-Y1 codes CLOPEN-β to
this pin meanwhile (v10.154 adjudication).

BOUNDARY: does NOT build the Weil pairing (p2's `[T-C1-KM28]`).
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory Limits

universe u

namespace ModularCurves

/-- **T-F1 infra (universe-bridged)** — the constant scheme on `Spec T` indexed by a finite
`Type 0` `ι` is `Spec` of the product ring `ι → T`. (Mathlib's `sigmaSpec` iso is pinned to a
`Type u` index; `constScheme`'s index is `Type 0`, so we bridge through `ULift.{u} ι`.) -/
noncomputable def constSchemeSpecIso (T : CommRingCat.{u}) (ι : Type) [Finite ι] :
    constScheme (Spec T) ι ≅ Spec (CommRingCat.of (ι → (T : Type u))) :=
  (Sigma.whiskerEquiv (Equiv.ulift.{u,0}) (fun _ => Iso.refl (Spec T))).symm ≪≫
    asIso (sigmaSpec (fun _ : ULift.{u} ι => T)) ≪≫
    Scheme.Spec.mapIso ((RingEquiv.piCongrLeft' (fun _ : ULift.{u} ι => (T : Type u))
      (Equiv.ulift.{u,0})).toCommRingCatIso).symm.op

/-- The summand components of `constSchemeSpecIso`: the `v`-th inclusion corresponds to
evaluation at `v`. -/
@[reassoc]
lemma constSchemeSpecIso_ι_hom (T : CommRingCat.{u}) (ι : Type) [Finite ι] (v : ι) :
    Sigma.ι (fun _ : ι => Spec T) v ≫ (constSchemeSpecIso T ι).hom
      = Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : ι => (T : Type u)) v)) := by
  simp only [constSchemeSpecIso, Iso.trans_hom, Iso.symm_hom, Sigma.whiskerEquiv_inv,
    Functor.mapIso_hom, Iso.op_hom, asIso_hom]
  rw [Sigma.ι_comp_map'_assoc, ι_sigmaSpec_assoc]
  simp only [eqToHom_refl, Iso.refl_hom, Category.id_comp, Scheme.Spec_map,
    Quiver.Hom.unop_op]
  rw [← Spec.map_comp]
  congr 1

/-- `constSchemeSpecIso` is a morphism over the base: it intertwines the constant-scheme
projection `constSchemeπ` with the diagonal ring map `T → (ι → T)`. -/
@[reassoc]
lemma constSchemeSpecIso_hom_π (T : CommRingCat.{u}) (ι : Type) [Finite ι] :
    (constSchemeSpecIso T ι).hom ≫ Spec.map (CommRingCat.ofHom (Pi.constRingHom ι T))
      = constSchemeπ (Spec T) ι := by
  refine Sigma.hom_ext _ _ fun a => ?_
  simp only [constSchemeSpecIso, Iso.trans_hom, Iso.symm_hom, Sigma.whiskerEquiv_inv,
    Functor.mapIso_hom, Iso.op_hom, asIso_hom, Category.assoc, constSchemeπ]
  rw [Sigma.ι_comp_map'_assoc, ι_sigmaSpec_assoc]
  simp only [Sigma.ι_desc, Category.id_comp, eqToHom_refl, Iso.refl_hom,
    Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
  congr 1

/-- **T-F1 infra (rank-match)** — a finite-split `T`-algebra of constant rank `n` is
`T`-algebra-isomorphic to `Fin n → T`. The existential rank in `IsFiniteSplit` is pinned to `n`
by the rank hypothesis; the trivial base case `Subsingleton T` is handled directly (both sides
subsingleton). -/
lemma isFiniteSplit_algEquiv_fin_of_rankAtStalk {T A : Type u} [CommRing T] [CommRing A]
    [Algebra T A] [Algebra.IsFiniteSplit T A] {n : ℕ}
    (hn : Module.rankAtStalk (R := T) A = n) :
    Nonempty (A ≃ₐ[T] (Fin n → T)) := by
  obtain ⟨m, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T A
  rcases subsingleton_or_nontrivial T with hT | hT
  · haveI : Subsingleton (Fin m → T) := inferInstance
    haveI : Subsingleton A := e.injective.subsingleton
    haveI : Subsingleton (Fin n → T) := inferInstance
    exact ⟨AlgEquiv.ofLinearEquiv default (Subsingleton.elim _ _)
      (fun _ _ => Subsingleton.elim _ _)⟩
  · have hmn : m = n := by
      obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum T))
      have h1 : Module.rankAtStalk (R := T) A p = Module.rankAtStalk (R := T) (Fin m → T) p :=
        congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) p
      rw [hn] at h1
      have h2 : Module.rankAtStalk (R := T) (Fin m → T) p = m := by
        rw [Module.rankAtStalk_pi]; simp [finsum_eq_sum_of_fintype]
      rw [h2] at h1
      exact h1.symm
    subst hmn
    exact ⟨e⟩

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- **T-F1 (affine base)** — the étale-local trivialization of `E[N]` over an affine base:
the split cover from `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale` (Lenstra 5.10),
with the trivialization assembled through the `pullbackSpecIso`/`constSchemeSpecIso` chain. -/
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
      have hh : t4.hom = Spec.map algChain.toRingEquiv.toCommRingCatIso.inv := rfl
      rw [hh, ← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      ext t
      exact algChain.symm.commutes t
    rw [ht4, pullbackSpecIso_hom_fst', pullbackSymmetry_hom_comp_fst]
    simp only [t1, asIso_hom]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/-- **Torsion commutes with base change** — packaged from `torsion_baseChange_isPullback`
(`TorsionFibre.lean`), which provides the cartesian square. -/
noncomputable def torsionBaseChangeIso {T : Scheme.{u}} (g : T ⟶ S) (N : ℕ) :
    (E.baseChange g).torsion N ≅ pullback (E.torsionπ N) g :=
  (E.torsion_baseChange_isPullback N g).isoPullback

@[reassoc]
theorem torsionBaseChangeIso_hom_snd {T : Scheme.{u}} (g : T ⟶ S) (N : ℕ) :
    (E.torsionBaseChangeIso g N).hom ≫ pullback.snd (E.torsionπ N) g
      = (E.baseChange g).torsionπ N :=
  (E.torsion_baseChange_isPullback N g).isoPullback_hom_snd

section SigmaPullback

variable {σ : Type u} {Y : σ → Scheme.{u}} {X S : Scheme.{u}}

/-- The chart component of the pullback–coproduct comparison: the pullback along one
summand, included into the pullback along the coproduct. -/
noncomputable def sigmaPullbackComponent (f : X ⟶ S) (q : ∀ i, Y i ⟶ S) (i : σ) :
    pullback f (q i) ⟶ pullback f (Sigma.desc q) :=
  (pullback.congrHom rfl (Sigma.ι_desc q i).symm).hom ≫
    (pullbackLeftPullbackSndIso f (Sigma.desc q) (Sigma.ι Y i)).inv ≫
    pullback.fst (pullback.snd f (Sigma.desc q)) (Sigma.ι Y i)

instance (f : X ⟶ S) (q : ∀ i, Y i ⟶ S) (i : σ) :
    IsOpenImmersion (sigmaPullbackComponent f q i) := by
  haveI hι : IsOpenImmersion (Sigma.ι Y i) := (sigmaOpenCover Y).map_prop i
  haveI h1 : IsOpenImmersion
      (pullback.fst (pullback.snd f (Sigma.desc q)) (Sigma.ι Y i)) := inferInstance
  rw [sigmaPullbackComponent]
  infer_instance

@[reassoc]
theorem sigmaPullbackComponent_snd (f : X ⟶ S) (q : ∀ i, Y i ⟶ S) (i : σ) :
    sigmaPullbackComponent f q i ≫ pullback.snd f (Sigma.desc q)
      = pullback.snd f (q i) ≫ Sigma.ι Y i := by
  rw [sigmaPullbackComponent, Category.assoc, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst_snd, ← Category.assoc,
    pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]

@[reassoc]
theorem sigmaPullbackComponent_fst (f : X ⟶ S) (q : ∀ i, Y i ⟶ S) (i : σ) :
    sigmaPullbackComponent f q i ≫ pullback.fst f (Sigma.desc q)
      = pullback.fst f (q i) := by
  rw [sigmaPullbackComponent, Category.assoc, Category.assoc,
    pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, pullback.lift_fst,
    Category.comp_id]

/-- The range of a chart component is the preimage of the summand. -/
theorem range_sigmaPullbackComponent (f : X ⟶ S) (q : ∀ i, Y i ⟶ S) (i : σ) :
    Set.range (sigmaPullbackComponent f q i).base
      = (pullback.snd f (Sigma.desc q)).base ⁻¹' Set.range (Sigma.ι Y i).base := by
  have hsplit : sigmaPullbackComponent f q i
      = ((pullback.congrHom rfl (Sigma.ι_desc q i).symm).hom ≫
          (pullbackLeftPullbackSndIso f (Sigma.desc q) (Sigma.ι Y i)).inv) ≫
        pullback.fst (pullback.snd f (Sigma.desc q)) (Sigma.ι Y i) := by
    rw [sigmaPullbackComponent, Category.assoc]
  haveI : AlgebraicGeometry.Surjective
      ((pullback.congrHom rfl (Sigma.ι_desc q i).symm).hom ≫
        (pullbackLeftPullbackSndIso f (Sigma.desc q) (Sigma.ι Y i)).inv) :=
    inferInstance
  rw [hsplit]
  calc Set.range (((pullback.congrHom rfl (Sigma.ι_desc q i).symm).hom ≫
        (pullbackLeftPullbackSndIso f (Sigma.desc q) (Sigma.ι Y i)).inv) ≫
        pullback.fst (pullback.snd f (Sigma.desc q)) (Sigma.ι Y i)).base
      = Set.range (⇑(pullback.fst (pullback.snd f (Sigma.desc q)) (Sigma.ι Y i)).base ∘
          ⇑((pullback.congrHom rfl (Sigma.ι_desc q i).symm).hom ≫
            (pullbackLeftPullbackSndIso f (Sigma.desc q) (Sigma.ι Y i)).inv).base) := rfl
    _ = ⇑(pullback.fst (pullback.snd f (Sigma.desc q)) (Sigma.ι Y i)).base ''
          Set.range ((pullback.congrHom rfl (Sigma.ι_desc q i).symm).hom ≫
            (pullbackLeftPullbackSndIso f (Sigma.desc q) (Sigma.ι Y i)).inv).base :=
        Set.range_comp _ _
    _ = ⇑(pullback.fst (pullback.snd f (Sigma.desc q)) (Sigma.ι Y i)).base ''
          Set.univ := by
        rw [((pullback.congrHom rfl (Sigma.ι_desc q i).symm).hom ≫
          (pullbackLeftPullbackSndIso f (Sigma.desc q) (Sigma.ι Y i)).inv).surjective.range_eq]
    _ = Set.range (pullback.fst (pullback.snd f (Sigma.desc q)) (Sigma.ι Y i)).base := by
        rw [Set.image_univ]
    _ = (pullback.snd f (Sigma.desc q)).base ⁻¹' Set.range (Sigma.ι Y i).base :=
        Scheme.Pullback.range_fst _ _

/-- **Pullback distributes over coproducts of schemes**: the chart components assemble to
an isomorphism (a surjective open immersion, ranges being the disjoint covering
preimages of the summands). -/
noncomputable def sigmaPullbackIso (f : X ⟶ S) (q : ∀ i, Y i ⟶ S) :
    (∐ fun i => pullback f (q i)) ≅ pullback f (Sigma.desc q) := by
  haveI hOI : IsOpenImmersion (Sigma.desc (sigmaPullbackComponent f q)) := by
    refine isOpenImmersion_sigmaDesc _ _ (fun i j hij => ?_)
    show Disjoint (Set.range (sigmaPullbackComponent f q i).base)
      (Set.range (sigmaPullbackComponent f q j).base)
    rw [range_sigmaPullbackComponent, range_sigmaPullbackComponent]
    refine Disjoint.preimage _ ?_
    rw [Set.disjoint_left]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have ha' : sigmaMk Y ⟨i, a⟩ = sigmaMk Y ⟨j, b⟩ := by
      rw [sigmaMk_mk, sigmaMk_mk]
      exact hb.symm
    exact hij (congrArg Sigma.fst ((sigmaMk Y).injective ha'))
  haveI hSurj : AlgebraicGeometry.Surjective
      (Sigma.desc (sigmaPullbackComponent f q)) := by
    refine ⟨fun z => ?_⟩
    obtain ⟨⟨i, t⟩, ht⟩ := (sigmaMk Y).surjective
      ((pullback.snd f (Sigma.desc q)).base z)
    have hz : z ∈ Set.range (sigmaPullbackComponent f q i).base := by
      rw [range_sigmaPullbackComponent]
      refine ⟨t, ?_⟩
      rw [← sigmaMk_mk]
      exact ht
    obtain ⟨w, hw⟩ := hz
    refine ⟨(Sigma.ι (fun i => pullback f (q i)) i).base w, ?_⟩
    exact ((Scheme.Hom.comp_apply _ _ _).symm.trans (congrArg
      (fun m : pullback f (q i) ⟶ pullback f (Sigma.desc q) => m.base w)
      (Sigma.ι_desc _ i))).trans hw
  haveI : IsIso (Sigma.desc (sigmaPullbackComponent f q)) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    refine TopologicalSpace.Opens.ext ?_
    exact (Sigma.desc (sigmaPullbackComponent f q)).surjective.range_eq
  exact asIso (Sigma.desc (sigmaPullbackComponent f q))

@[reassoc]
theorem ι_sigmaPullbackIso_hom (f : X ⟶ S) (q : ∀ i, Y i ⟶ S) (i : σ) :
    Sigma.ι (fun i => pullback f (q i)) i ≫ (sigmaPullbackIso f q).hom
      = sigmaPullbackComponent f q i := by
  rw [sigmaPullbackIso]
  exact Sigma.ι_desc _ i

end SigmaPullback

/-- **T-F1-general (interface — sorried pin)** — the étale-local structure of `E[N]` (KM 2.3.1):
for `N` invertible on `S` there is a surjective étale cover `p : T ⟶ S` over which the base
change `E[N] ×_S T` is `T`-isomorphic to the constant scheme `(ℤ/N)²_T`. NEW-Y1's CLOPEN-β
consumes this as a pin. -/
theorem torsion_etaleLocal_triv (N : ℕ) [NeZero N] (hinv : NIsInvertible S N) :
    ∃ (T : Scheme.{u}) (p : T ⟶ S), Etale p ∧ Surjective p ∧
      Nonempty (Over.mk (pullback.snd (E.torsionπ N) p) ≅
        Over.mk (constSchemeπ T (Fin 2 → ZMod N))) := by
  classical
  set 𝒰 := S.affineCover with h𝒰
  have haff : ∀ i : 𝒰.I₀, ∃ (Ti : Scheme.{u}) (pi : Ti ⟶ 𝒰.X i),
      Etale pi ∧ Surjective pi ∧
      Nonempty (Over.mk (pullback.snd ((E.baseChange (𝒰.f i)).torsionπ N) pi) ≅
        Over.mk (constSchemeπ Ti (Fin 2 → ZMod N))) := fun i =>
    torsion_etaleLocal_triv_affine (E.baseChange (𝒰.f i)) N
      (NIsInvertible.of_hom (𝒰.f i) hinv)
  choose Ti pi heti hsuri htrivi using haff
  set q : ∀ i, Ti i ⟶ S := fun i => pi i ≫ 𝒰.f i with hq
  have hqet : ∀ i, Etale (q i) := fun i => by
    haveI := heti i
    haveI : Etale (𝒰.f i) := inferInstance
    infer_instance
  refine ⟨∐ Ti, Sigma.desc q, IsZariskiLocalAtSource.sigmaDesc fun i => hqet i, ?_, ?_⟩
  · refine Surjective.sigmaDesc_of_union_range_eq_univ ?_
    refine Set.eq_univ_of_forall fun s => Set.mem_iUnion.mpr ?_
    have hs : s ∈ ⋃ i, Set.range (𝒰.f i).base := by
      rw [𝒰.iUnion_range]
      trivial
    obtain ⟨i, t, ht⟩ := by simpa only [Set.mem_iUnion, Set.mem_range] using hs
    obtain ⟨u, hu⟩ := (hsuri i).1 t
    refine ⟨i, u, ?_⟩
    show (pi i ≫ 𝒰.f i).base u = s
    rw [Scheme.Hom.comp_apply, hu, ht]
  · -- per-chart comparison, with its structure triangle
    have hΘ : ∀ i, ∃ Θ : pullback (E.torsionπ N) (q i) ≅
        constScheme (Ti i) (Fin 2 → ZMod N),
        Θ.hom ≫ constSchemeπ (Ti i) (Fin 2 → ZMod N)
          = pullback.snd (E.torsionπ N) (q i) := by
      intro i
      let Θ1 : pullback (E.torsionπ N) (q i) ≅
          pullback (pullback.snd (E.torsionπ N) (𝒰.f i)) (pi i) :=
        (pullbackLeftPullbackSndIso (E.torsionπ N) (𝒰.f i) (pi i)).symm
      have hw1 : pullback.snd (E.torsionπ N) (𝒰.f i) ≫ 𝟙 (𝒰.X i)
          = (E.torsionBaseChangeIso (𝒰.f i) N).inv ≫
            (E.baseChange (𝒰.f i)).torsionπ N := by
        rw [Category.comp_id, ← E.torsionBaseChangeIso_hom_snd (𝒰.f i) N,
          ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
      have hw2 : pi i ≫ 𝟙 (𝒰.X i) = 𝟙 (Ti i) ≫ pi i := by
        rw [Category.comp_id, Category.id_comp]
      set m2 := pullback.map (pullback.snd (E.torsionπ N) (𝒰.f i)) (pi i)
        ((E.baseChange (𝒰.f i)).torsionπ N) (pi i)
        (E.torsionBaseChangeIso (𝒰.f i) N).inv (𝟙 _) (𝟙 _) hw1 hw2 with hm2
      let Θ2 : pullback (pullback.snd (E.torsionπ N) (𝒰.f i)) (pi i) ≅
          pullback ((E.baseChange (𝒰.f i)).torsionπ N) (pi i) := asIso m2
      let Θ3 : pullback ((E.baseChange (𝒰.f i)).torsionπ N) (pi i) ≅
          constScheme (Ti i) (Fin 2 → ZMod N) :=
        (Over.forget _).mapIso (htrivi i).some
      refine ⟨Θ1 ≪≫ Θ2 ≪≫ Θ3, ?_⟩
      have h3 : Θ3.hom ≫ constSchemeπ (Ti i) (Fin 2 → ZMod N)
          = pullback.snd ((E.baseChange (𝒰.f i)).torsionπ N) (pi i) :=
        Over.w (htrivi i).some.hom
      have h2 : Θ2.hom ≫ pullback.snd ((E.baseChange (𝒰.f i)).torsionπ N) (pi i)
          = pullback.snd (pullback.snd (E.torsionπ N) (𝒰.f i)) (pi i) := by
        rw [show Θ2.hom = m2 from rfl, hm2, pullback.lift_snd, Category.comp_id]
      have h1 : Θ1.hom ≫ pullback.snd (pullback.snd (E.torsionπ N) (𝒰.f i)) (pi i)
          = pullback.snd (E.torsionπ N) (q i) :=
        pullbackLeftPullbackSndIso_inv_snd_snd _ _ _
      simp only [Iso.trans_hom, Category.assoc]
      rw [h3, h2, h1]
    choose Θ hΘπ using hΘ
    -- the label swap of the constant-scheme coproduct
    set κ : (∐ fun i => constScheme (Ti i) (Fin 2 → ZMod N)) ⟶
        constScheme (∐ Ti) (Fin 2 → ZMod N) :=
      Sigma.desc (fun i => Sigma.desc fun l =>
        Sigma.ι Ti i ≫ Sigma.ι (fun _ : Fin 2 → ZMod N => ∐ Ti) l) with hκ
    set κinv : constScheme (∐ Ti) (Fin 2 → ZMod N) ⟶
        (∐ fun i => constScheme (Ti i) (Fin 2 → ZMod N)) :=
      Sigma.desc (fun l => Sigma.desc fun i =>
        Sigma.ι (fun _ : Fin 2 → ZMod N => Ti i) l ≫
          Sigma.ι (fun i => constScheme (Ti i) (Fin 2 → ZMod N)) i) with hκinv
    have hκκ : κ ≫ κinv = 𝟙 _ := by
      refine Sigma.hom_ext _ _ fun i => ?_
      refine Sigma.hom_ext _ _ fun l => ?_
      simp [hκ, hκinv, Sigma.ι_desc_assoc, Sigma.ι_desc]
    have hκκ' : κinv ≫ κ = 𝟙 _ := by
      refine Sigma.hom_ext _ _ fun l => ?_
      refine Sigma.hom_ext _ _ fun i => ?_
      simp [hκ, hκinv, Sigma.ι_desc_assoc, Sigma.ι_desc]
    have hκπ : ∀ i, Sigma.ι (fun i => constScheme (Ti i) (Fin 2 → ZMod N)) i ≫
        (κ ≫ constSchemeπ (∐ Ti) (Fin 2 → ZMod N))
        = constSchemeπ (Ti i) (Fin 2 → ZMod N) ≫ Sigma.ι Ti i := by
      intro i
      rw [← Category.assoc, hκ, Sigma.ι_desc]
      refine Sigma.hom_ext _ _ fun l => ?_
      simp [constSchemeπ, Sigma.ι_desc, Sigma.ι_desc_assoc]
    set e : pullback (E.torsionπ N) (Sigma.desc q) ≅
        constScheme (∐ Ti) (Fin 2 → ZMod N) :=
      (sigmaPullbackIso (E.torsionπ N) q).symm ≪≫ Sigma.mapIso Θ ≪≫
        ⟨κ, κinv, hκκ, hκκ'⟩ with he
    refine ⟨Over.isoMk e ?_⟩
    show e.hom ≫ constSchemeπ (∐ Ti) (Fin 2 → ZMod N)
      = pullback.snd (E.torsionπ N) (Sigma.desc q)
    rw [← cancel_epi (sigmaPullbackIso (E.torsionπ N) q).hom]
    refine Sigma.hom_ext _ _ fun i => ?_
    have hcomp : (sigmaPullbackIso (E.torsionπ N) q).hom ≫
        e.hom ≫ constSchemeπ (∐ Ti) (Fin 2 → ZMod N)
        = (Sigma.mapIso Θ).hom ≫ κ ≫ constSchemeπ (∐ Ti) (Fin 2 → ZMod N) := by
      rw [he]
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
    rw [hcomp, ← Category.assoc, Sigma.ι_mapIso_hom, Category.assoc, hκπ i,
      ← Category.assoc, hΘπ i]
    rw [← Category.assoc, ι_sigmaPullbackIso_hom]
    exact (sigmaPullbackComponent_snd _ _ i).symm

end EllipticCurve

end ModularCurves
