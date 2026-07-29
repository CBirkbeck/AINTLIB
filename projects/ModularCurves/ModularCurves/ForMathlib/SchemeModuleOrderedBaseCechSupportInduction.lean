/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

Adapted from the Apache-licensed
`WellFoundedSheafCohomologyCodesvissage.lean` in Vilin97/Clawristotle.
-/
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechFinite
import ModularCurves.ForMathlib.SchemeModuleSupport

/-!
# Ordered base-Cech finiteness by closed-support induction

A comparison from a quasicoherent module to a good model reduces ordered
base-Cech homology finiteness to the two residuals in the
kernel-image-cokernel factorization. Strict decrease of a well-founded rank,
specialized to closed stalk support on a Noetherian space, closes the induction.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace OrderedBaseCechHomologyFinite

/-- Well-founded ordered base-Cech finiteness codévissage for comparisons
`M ⟶ E`. -/
theorem of_wellFounded_comodels
    {α : Type*} (r : α → α → Prop) [IsWellFounded α r]
    {X S : Scheme.{u}} (π : X ⟶ S) [X.IsSeparated]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    [IsNoetherianRing Γ(S, (⊤ : S.Opens))]
    (rank : X.Modules → α)
    (P Good : X.Modules → Prop)
    (hPqc : ∀ M, P M → M.IsQuasicoherent)
    (hGoodqc : ∀ E, Good E → E.IsQuasicoherent)
    (hcomodel :
      ∀ (M : X.Modules), P M →
        ∃ (E : X.Modules) (f : M ⟶ E),
          Good E ∧
          P (kernel (Abelian.factorThruImage f)) ∧
          P (cokernel (Abelian.image.ι f)) ∧
          (IsZero (kernel (Abelian.factorThruImage f)) ∨
            r (rank (kernel (Abelian.factorThruImage f))) (rank M)) ∧
          (IsZero (cokernel (Abelian.image.ι f)) ∨
            r (rank (cokernel (Abelian.image.ι f))) (rank M)))
    (hgood :
      ∀ E, Good E → OrderedBaseCechHomologyFinite π U E) :
    ∀ M, P M → OrderedBaseCechHomologyFinite π U M := by
  let rel : X.Modules → X.Modules → Prop :=
    fun A B ↦ r (rank A) (rank B)
  haveI : IsWellFounded X.Modules rel :=
    inferInstanceAs
      (IsWellFounded X.Modules (InvImage r rank))
  intro M hM
  induction M using IsWellFounded.induction rel with
  | ind M ih =>
      letI : M.IsQuasicoherent := hPqc M hM
      obtain ⟨E, f, hE, hPK, hPQ, hKsmaller, hQsmaller⟩ :=
        hcomodel M hM
      let K := kernel (Abelian.factorThruImage f)
      let I := Abelian.image f
      let Q := cokernel (Abelian.image.ι f)
      have hK : OrderedBaseCechHomologyFinite π U K := by
        rcases hKsmaller with hKzero | hKlt
        · exact of_isZero π U hKzero
        · exact ih K hKlt hPK
      have hQ : OrderedBaseCechHomologyFinite π U Q := by
        rcases hQsmaller with hQzero | hQlt
        · exact of_isZero π U hQzero
        · exact ih Q hQlt hPQ
      have hEfinite : OrderedBaseCechHomologyFinite π U E :=
        hgood E hE
      letI : E.IsQuasicoherent := hGoodqc E hE
      letI : K.IsQuasicoherent := hPqc K hPK
      letI : Q.IsQuasicoherent := hPqc Q hPQ
      letI : I.IsQuasicoherent := by
        dsimp only [I]
        exact isQuasicoherent_image f
      let S₂ :=
        ShortComplex.cokernelSequence (Abelian.image.ι f)
      haveI : Mono S₂.f := by
        dsimp [S₂, ShortComplex.cokernelSequence]
        infer_instance
      have hS₂ : S₂.ShortExact :=
        { exact :=
            ShortComplex.cokernelSequence_exact
              (Abelian.image.ι f) }
      letI : S₂.X₁.IsQuasicoherent := by
        change I.IsQuasicoherent
        infer_instance
      letI : S₂.X₂.IsQuasicoherent := by
        change E.IsQuasicoherent
        infer_instance
      letI : S₂.X₃.IsQuasicoherent := by
        change Q.IsQuasicoherent
        infer_instance
      have hI : OrderedBaseCechHomologyFinite π U I := by
        change OrderedBaseCechHomologyFinite π U S₂.X₁
        apply left π U hU hS₂
        · change OrderedBaseCechHomologyFinite π U E
          exact hEfinite
        · change OrderedBaseCechHomologyFinite π U Q
          exact hQ
      let S₁ :=
        ShortComplex.kernelSequence
          (Abelian.factorThruImage f)
      haveI : Epi S₁.g := by
        dsimp [S₁, ShortComplex.kernelSequence]
        infer_instance
      have hS₁ : S₁.ShortExact :=
        { exact :=
            ShortComplex.kernelSequence_exact
              (Abelian.factorThruImage f) }
      letI : S₁.X₁.IsQuasicoherent := by
        change K.IsQuasicoherent
        infer_instance
      letI : S₁.X₂.IsQuasicoherent := by
        change M.IsQuasicoherent
        infer_instance
      letI : S₁.X₃.IsQuasicoherent := by
        change I.IsQuasicoherent
        infer_instance
      change OrderedBaseCechHomologyFinite π U S₁.X₂
      apply middle π U hU hS₁
      · change OrderedBaseCechHomologyFinite π U K
        exact hK
      · change OrderedBaseCechHomologyFinite π U I
        exact hI

/-- Closed-stalk-support induction for ordered base-Cech homology finiteness. -/
theorem of_closedStalkSupport_comodels
    {X S : Scheme.{u}} (π : X ⟶ S)
    [X.IsSeparated] [NoetherianSpace X]
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i))
    [IsNoetherianRing Γ(S, (⊤ : S.Opens))]
    (P Good : X.Modules → Prop)
    (hPqc : ∀ M, P M → M.IsQuasicoherent)
    (hGoodqc : ∀ E, Good E → E.IsQuasicoherent)
    (hcomodel :
      ∀ (M : X.Modules), P M →
        ∃ (E : X.Modules) (f : M ⟶ E),
          Good E ∧
          P (kernel (Abelian.factorThruImage f)) ∧
          P (cokernel (Abelian.image.ι f)) ∧
          (IsZero (kernel (Abelian.factorThruImage f)) ∨
            closedStalkSupport
                (kernel (Abelian.factorThruImage f)) <
              closedStalkSupport M) ∧
          (IsZero (cokernel (Abelian.image.ι f)) ∨
            closedStalkSupport
                (cokernel (Abelian.image.ι f)) <
              closedStalkSupport M))
    (hgood :
      ∀ E, Good E → OrderedBaseCechHomologyFinite π U E) :
    ∀ M, P M → OrderedBaseCechHomologyFinite π U M :=
  of_wellFounded_comodels
    (fun Z W : Closeds X ↦ Z < W) π U hU
    closedStalkSupport P Good hPqc hGoodqc hcomodel hgood

end OrderedBaseCechHomologyFinite
end AlgebraicGeometry.Scheme.Modules
