/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# H¹-cotangent base change along standard étale algebras

**[T-YR-6 (c1-C)]** If `T` is a standard étale `S`-algebra, then
`T ⊗[S] H1Cotangent R S ≃ H1Cotangent R T` for any base `R → S`.

Strategy (mirroring `Algebra.tensorH1CotangentOfIsLocalization`): present `S`
by `P := (Generators.self R S).toExtension`, lift the standard étale pair
`(f, g)` of `T/S` to a pair `(f̂, ĝ·f̂')` over `P.Ring` — whose invertibility
condition holds by construction with witnesses `(ĝ, 0, 1)` — and apply
`Algebra.Extension.tensorH1CotangentOfFormallyEtale` to the resulting
formally étale extension hom; the kernel base-change hypothesis follows from
flatness of the standard étale cover.

This is the étale-local input for descending smoothness along the finite
étale `Y(ρ̄)`-covers (`T-YR-6 (c1)`).
-/

open Polynomial TensorProduct

namespace StandardEtalePair

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable (P : StandardEtalePair R)

/-- The pair `(f, g·f')`. Its invertibility condition holds by construction;
its algebra is the same as that of `(f, g)` (see `mulDerivativeEquiv`). -/
@[simps] noncomputable def mulDerivative : StandardEtalePair R where
  f := P.f
  monic_f := P.monic_f
  g := P.g * derivative P.f
  cond := ⟨P.g, 0, 1, by ring⟩

lemma hasMap_mulDerivative_iff {x : S} :
    P.mulDerivative.HasMap x ↔ P.HasMap x := by
  unfold HasMap
  simp only [mulDerivative_f, mulDerivative_g, map_mul]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, isUnit_of_mul_isUnit_left h2⟩
  · rintro ⟨h1, h2⟩
    have hpm : P.HasMap x := ⟨h1, h2⟩
    exact ⟨h1, h2.mul hpm.isUnit_derivative_f⟩

/-- `(f, g·f')` and `(f, g)` present the same algebra. -/
noncomputable def mulDerivativeEquiv : P.mulDerivative.Ring ≃ₐ[R] P.Ring :=
  AlgEquiv.ofAlgHom
    (P.mulDerivative.lift P.X ((P.hasMap_mulDerivative_iff).mpr P.hasMap_X))
    (P.lift P.mulDerivative.X ((P.hasMap_mulDerivative_iff).mp
      P.mulDerivative.hasMap_X))
    (hom_ext (by simp))
    (hom_ext (by simp))

@[simp] lemma mulDerivativeEquiv_X :
    P.mulDerivativeEquiv P.mulDerivative.X = P.X := by
  simp [mulDerivativeEquiv]

end StandardEtalePair

namespace StandardEtalePair

/-- The tautological presentation of a standard étale pair's algebra. -/
noncomputable def selfPresentation {R : Type*} [CommRing R]
    (P : StandardEtalePair R) : StandardEtalePresentation R P.Ring :=
  ⟨P, P.X, P.hasMap_X,
    by simpa [StandardEtalePair.lift_X_left] using Function.bijective_id⟩

end StandardEtalePair

namespace Algebra

open TensorProduct Polynomial

/-- (Implementation) An extension hom into `Extension.ofSurjective`, from a ring
map on presentation rings commuting with the structure maps. Top-level so the
structure literal is checked against the instantiated extension. -/
noncomputable def Extension.homToOfSurjective
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T]
    (P : Extension R S) {B : Type*} [CommRing B] [Algebra R B]
    (g : P.Ring →+* B)
    (hg : ∀ x, g (algebraMap R P.Ring x) = algebraMap R B x)
    (fQ : B →ₐ[R] T) (hsurj : Function.Surjective fQ)
    (hcomm : ∀ x, fQ (g x) = algebraMap S T (algebraMap P.Ring S x)) :
    P.Hom (Extension.ofSurjective fQ hsurj) where
  toRingHom := g
  toRingHom_algebraMap := fun x => hg x
  algebraMap_toRingHom := hcomm

section LiftedPair

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable (P : Extension R S) (pres : StandardEtalePresentation S T)
variable (F G : Polynomial P.Ring)

/-- (Implementation) The lifted standard étale pair `(F, G·F′)` over a
presentation ring: its invertibility condition holds by construction. -/
noncomputable def liftedPair (hFm : F.Monic) : StandardEtalePair P.Ring :=
  ⟨F, hFm, G * derivative F, ⟨G, 0, 1, by ring⟩⟩

variable (hFm : F.Monic)

/-- (Implementation) The `R`-algebra structure on the lifted pair ring, through
the quotient presentation. -/
@[reducible] noncomputable def liftedPairRingAlgebra :
    Algebra R (liftedPair P F G hFm).Ring :=
  inferInstanceAs (Algebra R (Polynomial (Polynomial P.Ring) ⧸
    Ideal.span {C (liftedPair P F G hFm).f,
      Polynomial.X * C (liftedPair P F G hFm).g - 1}))

attribute [local instance] liftedPairRingAlgebra

lemma liftedPairRing_isScalarTower :
    IsScalarTower R P.Ring (liftedPair P F G hFm).Ring :=
  inferInstanceAs (IsScalarTower R P.Ring (Polynomial (Polynomial P.Ring) ⧸
    Ideal.span {C (liftedPair P F G hFm).f,
      Polynomial.X * C (liftedPair P F G hFm).g - 1}))

attribute [local instance] liftedPairRing_isScalarTower

lemma tensor_isScalarTower :
    IsScalarTower R P.Ring (S ⊗[P.Ring] (liftedPair P F G hFm).Ring) :=
  .of_algebraMap_eq fun r => by
    rw [IsScalarTower.algebraMap_apply P.Ring S
        (S ⊗[P.Ring] (liftedPair P F G hFm).Ring),
      ← IsScalarTower.algebraMap_apply R P.Ring S,
      ← IsScalarTower.algebraMap_apply R S
        (S ⊗[P.Ring] (liftedPair P F G hFm).Ring)]

attribute [local instance] tensor_isScalarTower

variable (hF : F.map (algebraMap P.Ring S) = pres.P.f)
  (hG : G.map (algebraMap P.Ring S) = pres.P.g)

include hF hG

lemma liftedPair_map_f :
    ((liftedPair P F G hFm).map (algebraMap P.Ring S)).f = pres.P.f := by
  simpa [liftedPair] using hF

lemma liftedPair_map_g :
    ((liftedPair P F G hFm).map (algebraMap P.Ring S)).g =
      pres.P.g * derivative pres.P.f := by
  show (G * derivative F).map (algebraMap P.Ring S) = _
  rw [Polynomial.map_mul, hG, ← Polynomial.derivative_map, hF]

lemma liftedPair_hasMap_x :
    ((liftedPair P F G hFm).map (algebraMap P.Ring S)).HasMap pres.x := by
  refine ⟨?_, ?_⟩
  · rw [liftedPair_map_f P pres F G hFm hF hG]
    exact pres.hasMap.1
  · rw [liftedPair_map_g P pres F G hFm hF hG, map_mul]
    exact pres.hasMap.2.mul pres.hasMap.isUnit_derivative_f

lemma liftedPair_hasMap_X :
    pres.P.HasMap (((liftedPair P F G hFm).map (algebraMap P.Ring S)).X) := by
  have hX := ((liftedPair P F G hFm).map (algebraMap P.Ring S)).hasMap_X
  refine ⟨?_, ?_⟩
  · rw [← liftedPair_map_f P pres F G hFm hF hG]
    exact hX.1
  · have h2 := hX.2
    rw [liftedPair_map_g P pres F G hFm hF hG, map_mul] at h2
    exact isUnit_of_mul_isUnit_left h2

/-- (Implementation) The base change of the lifted pair presents `T`. -/
noncomputable def liftedPairEquivT :
    ((liftedPair P F G hFm).map (algebraMap P.Ring S)).Ring ≃ₐ[S] T := by
  refine AlgEquiv.ofAlgHom
    (((liftedPair P F G hFm).map (algebraMap P.Ring S)).lift pres.x
      (liftedPair_hasMap_x P pres F G hFm hF hG))
    ((pres.P.lift _ (liftedPair_hasMap_X P pres F G hFm hF hG)).comp
      pres.equivRing.toAlgHom) ?_ ?_
  · have key : (((liftedPair P F G hFm).map (algebraMap P.Ring S)).lift pres.x
        (liftedPair_hasMap_x P pres F G hFm hF hG)).comp
          (pres.P.lift _ (liftedPair_hasMap_X P pres F G hFm hF hG)) =
        pres.equivRing.symm.toAlgHom :=
      StandardEtalePair.hom_ext (by simp)
    rw [← AlgHom.comp_assoc, key]
    exact AlgEquiv.symm_comp pres.equivRing
  · refine StandardEtalePair.hom_ext ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, StandardEtalePair.lift_X,
      StandardEtalePresentation.equivRing_x, AlgHom.id_apply]

/-- (Implementation) `S ⊗ (lifted pair ring) ≃ T`. -/
noncomputable def liftedTensorEquivT :
    (S ⊗[P.Ring] (liftedPair P F G hFm).Ring) ≃ₐ[S] T :=
  ((liftedPair P F G hFm).selfPresentation.baseChange.equivRing).trans
    (liftedPairEquivT P pres F G hFm hF hG)

/-- (Implementation) The cover map onto `T`. -/
noncomputable def liftedCoverHom : (liftedPair P F G hFm).Ring →ₐ[R] T :=
  ((liftedTensorEquivT P pres F G hFm hF hG).toAlgHom.restrictScalars R).comp
    ((Algebra.TensorProduct.includeRight (R := P.Ring) (A := S)
      (B := (liftedPair P F G hFm).Ring)).restrictScalars R)

lemma liftedCoverHom_surjective (hπ : Function.Surjective (algebraMap P.Ring S)) :
    Function.Surjective (liftedCoverHom P pres F G hFm hF hG) :=
  (liftedTensorEquivT P pres F G hFm hF hG).surjective.comp
    (Algebra.TensorProduct.includeRight_surjective (liftedPair P F G hFm).Ring hπ)

lemma liftedCoverHom_algebraMap (x : P.Ring) :
    liftedCoverHom P pres F G hFm hF hG
      (algebraMap P.Ring (liftedPair P F G hFm).Ring x) =
    algebraMap S T (algebraMap P.Ring S x) := by
  show (liftedTensorEquivT P pres F G hFm hF hG)
      ((Algebra.TensorProduct.includeRight (R := P.Ring))
        (algebraMap P.Ring (liftedPair P F G hFm).Ring x)) = _
  rw [(Algebra.TensorProduct.includeRight (R := P.Ring)
      (A := S) (B := (liftedPair P F G hFm).Ring)).commutes,
    IsScalarTower.algebraMap_apply P.Ring S
      (S ⊗[P.Ring] (liftedPair P F G hFm).Ring)]
  exact (liftedTensorEquivT P pres F G hFm hF hG).commutes _

/-- (Implementation) The lifted extension of `T`. -/
noncomputable def liftedExtension
    (hπ : Function.Surjective (algebraMap P.Ring S)) : Extension R T :=
  .ofSurjective (liftedCoverHom P pres F G hFm hF hG)
    (liftedCoverHom_surjective P pres F G hFm hF hG hπ)

/-- (Implementation) The presentation-ring algebra structure on the lifted
extension's ring. -/
@[reducible] noncomputable def liftedExtensionRingAlgebra
    (hπ : Function.Surjective (algebraMap P.Ring S)) :
    Algebra P.Ring (liftedExtension P pres F G hFm hF hG hπ).Ring :=
  inferInstanceAs (Algebra P.Ring (liftedPair P F G hFm).Ring)

attribute [local instance] liftedExtensionRingAlgebra

/-- (Implementation) The extension hom into the lifted extension. -/
noncomputable def liftedExtensionHom
    (hπ : Function.Surjective (algebraMap P.Ring S)) :
    P.Hom (liftedExtension P pres F G hFm hF hG hπ) :=
  Extension.homToOfSurjective P
    (algebraMap P.Ring (liftedPair P F G hFm).Ring)
    (fun x => (IsScalarTower.algebraMap_apply R P.Ring
      (liftedPair P F G hFm).Ring x).symm)
    (liftedCoverHom P pres F G hFm hF hG)
    (liftedCoverHom_surjective P pres F G hFm hF hG hπ)
    (liftedCoverHom_algebraMap P pres F G hFm hF hG)

lemma liftedExtensionHom_mapKer_bijective
    (hπ : Function.Surjective (algebraMap P.Ring S)) :
    Function.Bijective
      (((liftedExtensionHom P pres F G hFm hF hG hπ).mapKer
        (show algebraMap P.Ring (liftedExtension P pres F G hFm hF hG hπ).Ring =
          (liftedExtensionHom P pres F G hFm hF hG hπ).toRingHom from rfl)
        ).liftBaseChange (liftedExtension P pres F G hFm hF hG hπ).Ring) := by
  sorry

end LiftedPair

open TensorProduct in
/-- **[T-YR-6 (c1-C)]** H¹-cotangent commutes with standard étale extension of
scalars: if `T` is standard étale over `S`, then
`T ⊗[S] H¹(L_{S/R}) ≃ H¹(L_{T/R})`.

Mirrors `Algebra.tensorH1CotangentOfIsLocalization`: lift the standard étale
pair `(f, g)` presenting `T/S` along `P.Ring ↠ S` to the pair `(f̂, ĝ·f̂′)`
(whose invertibility condition holds by construction), and apply
`Extension.tensorH1CotangentOfFormallyEtale`; the kernel hypothesis follows
from flatness of the standard étale cover. -/
noncomputable
def tensorH1CotangentOfIsStandardEtale (R S T : Type*) [CommRing R] [CommRing S]
    [CommRing T] [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsStandardEtale S T] :
    T ⊗[S] H1Cotangent R S ≃ₗ[T] H1Cotangent R T := by
  letI pres : StandardEtalePresentation S T := Nonempty.some inferInstance
  letI P : Extension R S := (Generators.self R S).toExtension
  have hπ : Function.Surjective (algebraMap P.Ring S) := P.algebraMap_surjective
  have hlift := Polynomial.lifts_and_natDegree_eq_and_monic
    (f := (algebraMap P.Ring S)) (p := pres.P.f)
    (by obtain ⟨q, hq⟩ := Polynomial.map_surjective _ hπ pres.P.f
        exact ⟨q, by simpa using hq⟩)
    pres.P.monic_f
  letI F : Polynomial P.Ring := hlift.choose
  have hF : F.map (algebraMap P.Ring S) = pres.P.f := hlift.choose_spec.1
  have hFm : F.Monic := hlift.choose_spec.2.2
  letI G : Polynomial P.Ring :=
    (Polynomial.map_surjective (algebraMap P.Ring S) hπ pres.P.g).choose
  have hG : G.map (algebraMap P.Ring S) = pres.P.g :=
    (Polynomial.map_surjective (algebraMap P.Ring S) hπ pres.P.g).choose_spec
  letI := liftedPairRingAlgebra (R := R) P F G hFm
  haveI : IsScalarTower R P.Ring (liftedPair P F G hFm).Ring :=
    liftedPairRing_isScalarTower (R := R) P F G hFm
  haveI : FormallySmooth R P.Ring :=
    inferInstanceAs (FormallySmooth R (MvPolynomial S R))
  haveI : FormallySmooth P.Ring (liftedPair P F G hFm).Ring := inferInstance
  haveI : FormallySmooth R (liftedExtension P pres F G hFm hF hG hπ).Ring :=
    .comp R P.Ring (liftedPair P F G hFm).Ring
  haveI : Module.Flat S T := by
    haveI : Module.Free S (AdjoinRoot pres.P.f) :=
      Module.Free.of_basis (AdjoinRoot.powerBasis' pres.P.monic_f).basis
    haveI : Module.Flat (AdjoinRoot pres.P.f)
        (Localization.Away (AdjoinRoot.mk pres.P.f pres.P.g)) :=
      IsLocalization.flat _ (Submonoid.powers (AdjoinRoot.mk pres.P.f pres.P.g))
    haveI : Module.Flat S (Localization.Away (AdjoinRoot.mk pres.P.f pres.P.g)) :=
      Module.Flat.trans S (AdjoinRoot pres.P.f) _
    exact Module.Flat.of_linearEquiv
      ((pres.equivRing.trans pres.P.equivAwayAdjoinRoot).toLinearEquiv)
  letI : Algebra P.Ring (liftedExtension P pres F G hFm hF hG hπ).Ring :=
    inferInstanceAs (Algebra P.Ring (liftedPair P F G hFm).Ring)
  refine Extension.tensorH1CotangentOfFormallyEtale
    (liftedExtensionHom P pres F G hFm hF hG hπ)
    rfl ?_ (liftedExtensionHom_mapKer_bijective P pres F G hFm hF hG hπ) ≪≫ₗ
    Extension.equivH1CotangentOfFormallySmooth _
  · exact RingHom.formallyEtale_algebraMap.mpr
      (inferInstanceAs (FormallyEtale P.Ring (liftedPair P F G hFm).Ring))

end Algebra
