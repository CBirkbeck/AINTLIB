import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.RingHom.QuasiFinite
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Quasi-finiteness descends along faithfully flat maps (mathlib gap, BB-QF seam-i)

`Algebra.QuasiFinite R T` descends along a faithfully flat `R → S`: the fibre of `T` at a
prime `p` of `R` base-changes to the fibre of `S ⊗[R] T` at any prime `Q` of `S` over `p`
(the `cancelBaseChange` iso from `Algebra.QuasiFinite.baseChange`, read backwards), and
`Module.Finite` descends along the faithfully flat residue extension
(`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`). Packaged as
`RingHom.QuasiFinite.codescendsAlong_faithfullyFlat` and the scheme-level
`DescendsAlong @LocallyQuasiFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact)` instance, in the
exact shape of `Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`.
-/

open TensorProduct

namespace Algebra.QuasiFinite

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- Quasi-finiteness of algebras descends along a faithfully flat base change. -/
theorem of_quasiFinite_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat R S] [Algebra.QuasiFinite S (S ⊗[R] T)] :
    Algebra.QuasiFinite R T := by
  refine ⟨fun p hp ↦ ?_⟩
  -- choose a prime of `S` over `p` (faithful flatness is surjective on spectra)
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (B := S)
    ⟨p, hp⟩
  haveI hlo : Q.asIdeal.LiesOver p := ⟨congrArg PrimeSpectrum.asIdeal hQ.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver p Q.asIdeal
  let e : Q.asIdeal.Fiber (S ⊗[R] T) ≃ₐ[Q.asIdeal.ResidueField]
      Q.asIdeal.ResidueField ⊗[p.ResidueField] (p.Fiber T) :=
    (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).trans
      (Algebra.TensorProduct.cancelBaseChange _ _ _ _ _).symm
  haveI : Module.Finite Q.asIdeal.ResidueField
      (Q.asIdeal.ResidueField ⊗[p.ResidueField] (p.Fiber T)) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  haveI : Module.Free p.ResidueField Q.asIdeal.ResidueField :=
    Module.Free.of_divisionRing _ _
  haveI : Module.FaithfullyFlat p.ResidueField Q.asIdeal.ResidueField := inferInstance
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat Q.asIdeal.ResidueField

end Algebra.QuasiFinite

namespace RingHom.QuasiFinite

/-- Quasi-finiteness of ring maps codescends along faithfully flat maps (the shape
`HasRingHomProperty.descendsAlong_flat` consumes). -/
theorem codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.QuasiFinite RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.QuasiFinite.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.quasiFinite_algebraMap] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact Algebra.QuasiFinite.of_quasiFinite_tensorProduct_of_faithfullyFlat (S := S)

end RingHom.QuasiFinite

namespace AlgebraicGeometry

open CategoryTheory MorphismProperty

/-- **Local quasi-finiteness descends along fppf morphisms** (the missing companion of
`Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent`'s instances). -/
instance : DescendsAlong @LocallyQuasiFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat
    RingHom.QuasiFinite.codescendsAlong_faithfullyFlat

end AlgebraicGeometry
