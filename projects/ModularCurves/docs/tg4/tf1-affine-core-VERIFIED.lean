import ModularCurves.EllipticCurve.Torsion
import Mathlib.RingTheory.TotallySplit
open AlgebraicGeometry CategoryTheory
universe u
namespace ModularCurves.EllipticCurve
example {R : CommRingCat.{u}} (E : EllipticCurve (Spec R)) (N : ℕ) [NeZero N]
    (hinv : NIsInvertible (Spec R) N) : True := by
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
  have hrank : Module.rankAtStalk (R := R) (Γ(E.torsion N, ⊤)) = (N ^ 2 : ℕ) := sorry
  obtain ⟨T, _, _, _, _, _, hsplit⟩ :=
    Algebra.IsFiniteSplit.exists_tensorProduct_of_etale
      (R := R) (S := Γ(E.torsion N, ⊤)) hrank
  trivial
end ModularCurves.EllipticCurve
