/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
-/
import ModularCurves.ForMathlib.FiniteHomologySequence
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechExact

/-!
# Finiteness of ordered base-linear Cech homology

Over a Noetherian coefficient ring, finiteness of every ordered base-Cech homology
module is stable under short exact sequences of quasicoherent scheme modules.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Every ordered base-Cech homology module of `M` is finite over the base
ring of global sections. -/
def OrderedBaseCechHomologyFinite
    {X S : Scheme.{u}} (π : X ⟶ S)
    {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)
    (M : X.Modules) : Prop :=
  ∀ n : ℕ,
    Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π M U).homology n)

namespace OrderedBaseCechHomologyFinite

variable {X S : Scheme.{u}} (π : X ⟶ S)
variable {ι : Type u} [LinearOrder ι] (U : ι → X.Opens)

/-- A zero scheme module has finite ordered base-Cech homology. -/
theorem of_isZero {M : X.Modules} (hM : IsZero M) :
    OrderedBaseCechHomologyFinite π U M := by
  intro n
  let C := orderedBaseCechComplex π M U
  have hC : IsZero C :=
    (orderedBaseCechComplexFunctor π U).map_isZero hM
  have hX : IsZero (C.X n) :=
    (HomologicalComplex.eval _ _ n).map_isZero hC
  have hH : IsZero (C.homology n) :=
    ShortComplex.isZero_homology_of_isZero_X₂ (C.sc n) hX
  letI : Subsingleton (C.homology n) :=
    ModuleCat.subsingleton_of_isZero hH
  change Module.Finite Γ(S, (⊤ : S.Opens)) (C.homology n)
  infer_instance

variable [IsNoetherianRing Γ(S, (⊤ : S.Opens))] [X.IsSeparated]
variable (hU : ∀ i, IsAffineOpen (U i))

include hU

/-- Finiteness of ordered base-Cech homology is closed under extensions. -/
theorem middle
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent]
    [T.X₃.IsQuasicoherent]
    (h₁ : OrderedBaseCechHomologyFinite π U T.X₁)
    (h₃ : OrderedBaseCechHomologyFinite π U T.X₃) :
    OrderedBaseCechHomologyFinite π U T.X₂ := by
  intro n
  let F := orderedBaseCechComplexFunctor π U
  have hTF : (T.map F).ShortExact :=
    hT.map_orderedBaseCechComplexFunctor_of_affine_openCover π U hU
  letI : Module.Finite Γ(S, (⊤ : S.Opens))
      ((T.map F).X₁.homology n) := by
    change Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π T.X₁ U).homology n)
    exact h₁ n
  letI : Module.Finite Γ(S, (⊤ : S.Opens))
      ((T.map F).X₃.homology n) := by
    change Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π T.X₃ U).homology n)
    exact h₃ n
  change Module.Finite Γ(S, (⊤ : S.Opens))
    ((T.map F).X₂.homology n)
  exact
    ModularCurves.CategoryTheory.ShortComplex.ShortExact.finite_homology_X2
      hTF n

/-- Finiteness for the middle and quotient terms implies finiteness for the
subobject term. -/
theorem left
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent]
    [T.X₃.IsQuasicoherent]
    (h₂ : OrderedBaseCechHomologyFinite π U T.X₂)
    (h₃ : OrderedBaseCechHomologyFinite π U T.X₃) :
    OrderedBaseCechHomologyFinite π U T.X₁ := by
  intro n
  let F := orderedBaseCechComplexFunctor π U
  have hTF : (T.map F).ShortExact :=
    hT.map_orderedBaseCechComplexFunctor_of_affine_openCover π U hU
  letI (q : ℕ) : Module.Finite Γ(S, (⊤ : S.Opens))
      ((T.map F).X₂.homology q) := by
    change Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π T.X₂ U).homology q)
    exact h₂ q
  letI (q : ℕ) : Module.Finite Γ(S, (⊤ : S.Opens))
      ((T.map F).X₃.homology q) := by
    change Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π T.X₃ U).homology q)
    exact h₃ q
  change Module.Finite Γ(S, (⊤ : S.Opens))
    ((T.map F).X₁.homology n)
  exact
    ModularCurves.CategoryTheory.ShortComplex.ShortExact.finite_homology_X1_up_nat
      hTF n

/-- Finiteness for the subobject and middle terms implies finiteness for the
quotient term. -/
theorem right
    {T : ShortComplex X.Modules} (hT : T.ShortExact)
    [T.X₁.IsQuasicoherent] [T.X₂.IsQuasicoherent]
    [T.X₃.IsQuasicoherent]
    (h₁ : OrderedBaseCechHomologyFinite π U T.X₁)
    (h₂ : OrderedBaseCechHomologyFinite π U T.X₂) :
    OrderedBaseCechHomologyFinite π U T.X₃ := by
  intro n
  let F := orderedBaseCechComplexFunctor π U
  have hTF : (T.map F).ShortExact :=
    hT.map_orderedBaseCechComplexFunctor_of_affine_openCover π U hU
  letI : Module.Finite Γ(S, (⊤ : S.Opens))
      ((T.map F).X₂.homology n) := by
    change Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π T.X₂ U).homology n)
    exact h₂ n
  letI : Module.Finite Γ(S, (⊤ : S.Opens))
      ((T.map F).X₁.homology (n + 1)) := by
    change Module.Finite Γ(S, (⊤ : S.Opens))
      ((orderedBaseCechComplex π T.X₁ U).homology (n + 1))
    exact h₁ (n + 1)
  change Module.Finite Γ(S, (⊤ : S.Opens))
    ((T.map F).X₃.homology n)
  exact
    ModularCurves.CategoryTheory.ShortComplex.ShortExact.finite_homology_X3
      hTF n (n + 1) (by simp [ComplexShape.up_Rel])

end OrderedBaseCechHomologyFinite

end AlgebraicGeometry.Scheme.Modules
