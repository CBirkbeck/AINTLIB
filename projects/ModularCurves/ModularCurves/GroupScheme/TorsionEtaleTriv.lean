import ModularCurves.EllipticCurve.Torsion
import ModularCurves.GroupScheme.MuN
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.Flat.Rank

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

/-- **T-F1-general (interface — sorried pin)** — the étale-local structure of `E[N]` (KM 2.3.1):
for `N` invertible on `S` there is a surjective étale cover `p : T ⟶ S` over which the base
change `E[N] ×_S T` is `T`-isomorphic to the constant scheme `(ℤ/N)²_T`. NEW-Y1's CLOPEN-β
consumes this as a pin. -/
theorem torsion_etaleLocal_triv (N : ℕ) [NeZero N] (hinv : NIsInvertible S N) :
    ∃ (T : Scheme.{u}) (p : T ⟶ S), Etale p ∧ Surjective p ∧
      Nonempty (Over.mk (pullback.snd (E.torsionπ N) p) ≅
        Over.mk (constSchemeπ T (Fin 2 → ZMod N))) := sorry

end EllipticCurve

end ModularCurves
