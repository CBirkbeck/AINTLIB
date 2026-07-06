import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.KrullTopology
import ModularCurves.ForMathlib.FiniteEtaleFiberFunctor

/-!
# The absolute Galois group is the fundamental group of `FiniteEtale k`

We show `Gal(k^sep/k) = (SeparableClosure k ≃ₐ[k] SeparableClosure k)` with its Krull
topology is a fundamental group (in the sense of
`CategoryTheory.PreGaloisCategory.IsFundamentalGroup`) for the fiber functor of
`(FiniteEtale k)ᵒᵖ` at the separable closure:

* the natural action is post-composition on points;
* connected objects are fields (`isField_of_isConnected`), so transitivity on Galois
  objects is conjugacy of embeddings (`AlgEquiv.liftNormal`);
* stabilisers of points are fixing subgroups of finite-dimensional intermediate
  fields, which are open in the Krull topology;
* an automorphism acting trivially on all fibers fixes every element of the
  separable closure.
-/

universe u

open CategoryTheory Limits CommAlgCat

open scoped TensorProduct

namespace ModularCurves

namespace FiniteEtaleGalois

variable (k : Type u) [Field k]

/-! The natural action of the Galois group on the fibers (leaf AG-GG-3a). -/

section Action

variable {k}

noncomputable instance fiberMulAction (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    MulAction (SeparableClosure k ≃ₐ[k] SeparableClosure k)
      ((CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X) where
  smul σ x := FintypeCat.homMk (σ.toAlgHom.comp ·)
    ((CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X) x
  one_smul x := AlgHom.ext fun a => rfl
  mul_smul σ τ x := AlgHom.ext fun a => rfl

lemma fiber_smul_def (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (x : (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k)).obj X) :
    σ • x = σ.toAlgHom.comp x :=
  rfl

instance : PreGaloisCategory.IsNaturalSMul
    (CommAlgCat.FiniteEtale.fiber k (SeparableClosure k))
    (SeparableClosure k ≃ₐ[k] SeparableClosure k) where
  naturality σ {X Y} f x := AlgHom.ext fun a => rfl

end Action

end FiniteEtaleGalois

end ModularCurves
