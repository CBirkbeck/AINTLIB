import ModularCurves.ForMathlib.CochainComplexBoundedFlat
import ModularCurves.ForMathlib.SchemeModuleProperLowDegreeCechFinite
import ModularCurves.Picard.InvertibleSheafBaseCechFlat

/-!
# Spreading residue-fibre Cech exactness

Finite homology and termwise flatness spread exactness of the ordered
base-Cech complex of an invertible sheaf from one residue fibre to a
principal neighborhood.
-/

open CategoryTheory ModularCurves TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

/-- Exactness of an ordered base-Cech complex on one residue fibre spreads to a
principal neighborhood for an invertible sheaf on a proper Noetherian family. -/
theorem IsInvertible.exists_away_orderedBaseCech_exact_of_residueField_exact
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {X : Scheme.{u}} [IsNoetherian X] [X.IsSeparated]
    {π : X ⟶ Spec (.of R)}
    [LocallyOfFinitePresentation π] [IsProper π] [Flat π]
    {M : X.Modules} (hM : IsInvertible M)
    {ι : Type u} [Fintype ι] [LinearOrder ι]
    (U : ι → X.Opens) (hU : IsOpenCover U)
    (hUaff : ∀ i, IsAffineOpen (U i))
    (p : Ideal Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)))
    [p.IsPrime]
    (hresidue : ∀ q, q < Fintype.card ι →
      let C := orderedBaseCechComplex π M U
      Function.Exact
        ((C.d q (q + 1)).hom.baseChange p.ResidueField)
        ((C.d (q + 1) (q + 2)).hom.baseChange p.ResidueField)) :
    ∃ r : Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens)),
      r ∉ p ∧
        let C := orderedBaseCechComplex π M U
        ∀ q, q < Fintype.card ι →
          Function.Exact
            ((C.d q (q + 1)).hom.baseChange
              (Localization.Away r))
            ((C.d (q + 1) (q + 2)).hom.baseChange
              (Localization.Away r)) := by
  let C := orderedBaseCechComplex π M U
  let B := Γ(Spec (.of R), (⊤ : (Spec (.of R)).Opens))
  letI : M.IsQuasicoherent := hM.isQuasicoherent
  letI : M.IsFinitePresentation := hM.isFinitePresentation
  letI : M.IsFiniteType :=
    SheafOfModules.instIsFiniteTypeOfIsFinitePresentation M
  letI (q : ℕ) : Module.Flat B (C.X q) :=
    orderedBaseCechObject_flat_of_isInvertible
      π M hM U hUaff q
  have hfinite :=
    orderedBaseCechHomologyFinite_of_isProper
      (xπ := π) U hU hUaff M
  letI (q : ℕ) : Module.Finite B (C.homology q) :=
    hfinite q
  let N := Fintype.card ι
  letI : Subsingleton (C.X (N + 1)) :=
    orderedBaseCechObject_subsingleton_of_card_le
      π M U (N + 1) (Nat.le_succ N)
  exact
    HomologicalComplex.exists_away_functionExact_of_residueField_exact_of_finite_homology
      C N p hresidue

end

end AlgebraicGeometry.Scheme.Modules
