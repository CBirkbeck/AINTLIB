/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project

ForMathlib (OURS, not vendored): upstream candidate.
-/
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechFinite
import ModularCurves.ForMathlib.SchemeModuleOrderedBaseCechPushforward

/-!
# Finiteness of ordered Cech homology under pushforward

The ordered base-Cech complex of a pushforward on a cover is isomorphic
to the ordered base-Cech complex upstairs on the inverse-image cover.
Consequently finiteness of every homology module is equivalent.
-/

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules
namespace OrderedBaseCechHomologyFinite

/-- Finite ordered base-Cech homology is invariant under the canonical
pushforward comparison with the inverse-image cover. -/
theorem pushforward_iff
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (π : Y ⟶ S)
    (M : X.Modules) {ι : Type u} [LinearOrder ι]
    (U : ι → Y.Opens) :
    OrderedBaseCechHomologyFinite (f ≫ π)
        (fun i => f ⁻¹ᵁ U i) M ↔
      OrderedBaseCechHomologyFinite π U
        ((pushforward f).obj M) := by
  constructor
  · intro h n
    letI : Module.Finite Γ(S, (⊤ : S.Opens))
        ((orderedBaseCechComplex (f ≫ π) M
          (fun i => f ⁻¹ᵁ U i)).homology n) :=
      h n
    let e := HomologicalComplex.homologyMapIso
      (orderedBaseCechComplexPushforwardIso f π M U) n
    exact Module.Finite.equiv e.toLinearEquiv
  · intro h n
    letI : Module.Finite Γ(S, (⊤ : S.Opens))
        ((orderedBaseCechComplex π
          ((pushforward f).obj M) U).homology n) :=
      h n
    let e := HomologicalComplex.homologyMapIso
      (orderedBaseCechComplexPushforwardIso f π M U) n
    exact Module.Finite.equiv e.symm.toLinearEquiv

end OrderedBaseCechHomologyFinite
end AlgebraicGeometry.Scheme.Modules
