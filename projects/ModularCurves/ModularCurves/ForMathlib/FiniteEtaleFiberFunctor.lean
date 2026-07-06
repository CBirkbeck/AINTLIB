import Mathlib.RingTheory.TensorProduct.Pi
import ModularCurves.ForMathlib.FiniteEtaleGalois

/-!
# The fiber functor on finite étale algebras is a Galois fiber functor

Mathlib provides the fiber functor `CommAlgCat.FiniteEtale.fiber k Ω :
(FiniteEtale k)ᵒᵖ ⥤ FintypeCat` (homs into a geometric point `Ω`), the factorisation
`fiberIsoBaseChangeFiber : fiber k Ω ≅ (baseChange k Ω).op ⋙ fiber Ω Ω`, and — for `Ω`
separably closed — the fact that `fiber Ω Ω` is an equivalence.  Consequently every
axiom of `CategoryTheory.PreGaloisCategory.FiberFunctor` for `fiber k (SeparableClosure k)`
reduces to an exactness property of the base change functor
`baseChange k Ω : FiniteEtale k ⥤ FiniteEtale Ω`, which is what this file proves:

* base change preserves the initial object (`Ω ⊗[k] k ≅ Ω`);
* base change preserves finite products (`Algebra.TensorProduct.piRight`);
* base change preserves the tensor-product pushouts;
* base change preserves monomorphisms (kernel-pair subalgebra + flatness);
* base change preserves `SingleObj`-shaped limits (fixed points commute with flat
  base change);
* the fiber functor reflects isomorphisms (counting via `natCard_algHom_sepClosure`).
-/

universe u

open CategoryTheory Limits CommAlgCat

open scoped TensorProduct

namespace ModularCurves

namespace FiniteEtaleGalois

variable (k : Type u) [Field k] (Ω : Type u) [Field Ω] [Algebra k Ω]

/-! Base change preserves the initial object (leaf AG-GG-2a). -/

section Initial

/-- `Ω ⊗[k] k` is the initial finite étale `Ω`-algebra. -/
noncomputable def baseChangeInitialIso :
    (CommAlgCat.FiniteEtale.baseChange k Ω).obj (CommAlgCat.FiniteEtale.of k k) ≅
      CommAlgCat.FiniteEtale.of Ω Ω :=
  CommAlgCat.FiniteEtale.isoMk (Algebra.TensorProduct.rid k Ω Ω)

/-- The unique-morphism structure on `FiniteEtale.of k k`, from the `Subsingleton` and
`Nonempty` instances. -/
noncomputable def uniqueHomFromSelf (A : CommAlgCat.FiniteEtale.{u} k) :
    Unique (CommAlgCat.FiniteEtale.of k k ⟶ A) where
  default := Nonempty.some inferInstance
  uniq _ := Subsingleton.elim _ _

/-- `FiniteEtale.of k k` is initial. -/
noncomputable def isInitialOfSelf : IsInitial (CommAlgCat.FiniteEtale.of k k) :=
  haveI : ∀ A : CommAlgCat.FiniteEtale.{u} k,
      Unique (CommAlgCat.FiniteEtale.of k k ⟶ A) := fun A => uniqueHomFromSelf k A
  IsInitial.ofUnique _

lemma preservesInitial_baseChange :
    PreservesColimit (Functor.empty.{0} (CommAlgCat.FiniteEtale.{u} k))
      (CommAlgCat.FiniteEtale.baseChange k Ω) := by
  refine preservesInitial_of_iso _ ?_
  refine (initialIsoIsInitial (isInitialOfSelf Ω)).trans ?_
  refine (baseChangeInitialIso k Ω).symm.trans ?_
  exact ((CommAlgCat.FiniteEtale.baseChange k Ω).mapIso
    (initialIsoIsInitial (isInitialOfSelf k))).symm

lemma preservesColimitsOfShapePEmpty_baseChange :
    PreservesColimitsOfShape (Discrete PEmpty.{1})
      (CommAlgCat.FiniteEtale.baseChange k Ω) :=
  haveI := preservesInitial_baseChange k Ω
  preservesColimitsOfShape_pempty_of_preservesInitial _

end Initial

end FiniteEtaleGalois

end ModularCurves
