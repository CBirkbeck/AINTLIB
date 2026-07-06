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
  smul σ x := σ.toAlgHom.comp x
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

/-! Connected finite étale algebras are fields (leaf AG-GG-3d). -/

section Connected

variable {k}

/-- The `k`-algebra map into a subsingleton algebra. -/
private noncomputable def algHomToSubsingleton {A B : Type u} [CommRing A] [Algebra k A]
    [CommRing B] [Algebra k B] [Subsingleton B] : A →ₐ[k] B where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _

/-- A finite étale algebra with subsingleton carrier is terminal. -/
private noncomputable def isTerminalOfSubsingleton (T : CommAlgCat.FiniteEtale.{u} k)
    [Subsingleton (T : Type u)] : IsTerminal T :=
  haveI : ∀ B : CommAlgCat.FiniteEtale.{u} k, Unique (B ⟶ T) := fun B =>
    { default := ObjectProperty.homMk (CommAlgCat.ofHom algHomToSubsingleton)
      uniq := fun f => by ext b; exact Subsingleton.elim _ _ }
  IsTerminal.ofUnique _

/-- The carrier of a connected object of `(FiniteEtale k)ᵒᵖ` is nontrivial. -/
theorem nontrivial_of_isConnected (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    [PreGaloisCategory.IsConnected X] : Nontrivial (X.unop : Type u) := by
  rcases subsingleton_or_nontrivial (X.unop : Type u) with hsub | h
  · exfalso
    apply PreGaloisCategory.IsConnected.notInitial (X := X)
    exact initialOpOfTerminal (isTerminalOfSubsingleton X.unop)
  · exact h

/-- Connected finite étale algebras over a field are fields. -/
theorem isField_of_isConnected (X : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    [PreGaloisCategory.IsConnected X] : IsField (X.unop : Type u) := by
  haveI hnt : Nontrivial (X.unop : Type u) := nontrivial_of_isConnected X
  obtain ⟨m₀, hm₀⟩ := Ideal.exists_maximal (X.unop : Type u)
  haveI := hm₀
  haveI : Algebra.Etale k ((X.unop : Type u) ⧸ m₀) := etale_quotient m₀
  haveI : Module.Finite k ((X.unop : Type u) ⧸ m₀) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ k m₀).toLinearMap
      Ideal.Quotient.mk_surjective
  letI : Field ((X.unop : Type u) ⧸ m₀) := Ideal.Quotient.field m₀
  set q : X.unop ⟶ CommAlgCat.FiniteEtale.of k ((X.unop : Type u) ⧸ m₀) :=
    ObjectProperty.homMk (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k m₀)) with hq
  haveI : Epi ((ObjectProperty.ι (CommAlgCat.finiteEtale k)).map q) :=
    CategoryTheory.ConcreteCategory.epi_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Epi q := (ObjectProperty.ι (CommAlgCat.finiteEtale k)).epi_of_epi_map
    inferInstance
  haveI hmono : Mono q.op := inferInstance
  have hiso : IsIso q.op := by
    refine PreGaloisCategory.IsConnected.noTrivialComponent _ q.op ?_
    intro hini
    have hterm : IsTerminal (CommAlgCat.FiniteEtale.of k ((X.unop : Type u) ⧸ m₀)) :=
      terminalUnopOfInitial hini
    haveI : Algebra.FinitePresentation k (Fin 0 → k) :=
      Algebra.FinitePresentation.of_finiteType.mp inferInstance
    haveI : Algebra.Etale k (Fin 0 → k) := ⟨inferInstance, inferInstance⟩
    have hiso2 := hterm.uniqueUpToIso
      (isTerminalOfSubsingleton (CommAlgCat.FiniteEtale.of k (Fin 0 → k)))
    have hcarrier : ((X.unop : Type u) ⧸ m₀) ≃ (Fin 0 → k) :=
      ⟨hiso2.hom.hom.hom, hiso2.inv.hom.hom,
        fun a => congrArg (fun (t : CommAlgCat.FiniteEtale.of k
          ((X.unop : Type u) ⧸ m₀) ⟶ CommAlgCat.FiniteEtale.of k
          ((X.unop : Type u) ⧸ m₀)) => t.hom.hom a) hiso2.hom_inv_id,
        fun a => congrArg (fun (t : CommAlgCat.FiniteEtale.of k (Fin 0 → k) ⟶
          CommAlgCat.FiniteEtale.of k (Fin 0 → k)) => t.hom.hom a)
          hiso2.inv_hom_id⟩
    haveI : Subsingleton ((X.unop : Type u) ⧸ m₀) := hcarrier.subsingleton
    exact false_of_nontrivial_of_subsingleton ((X.unop : Type u) ⧸ m₀)
  haveI : IsIso q := (isIso_op_iff q).mp hiso
  haveI : IsIso ((ObjectProperty.ι (CommAlgCat.finiteEtale k)).map q) :=
    Functor.map_isIso _ q
  have hbij : Function.Bijective (Ideal.Quotient.mkₐ k m₀) :=
    CategoryTheory.ConcreteCategory.bijective_of_isIso
      ((ObjectProperty.ι (CommAlgCat.finiteEtale k)).map q)
  refine ⟨exists_pair_ne _, mul_comm, ?_⟩
  intro a ha
  have hea : Ideal.Quotient.mkₐ k m₀ a ≠ 0 := by
    intro h0
    exact ha (hbij.1 (h0.trans (map_zero _).symm))
  obtain ⟨b', hb'⟩ := IsUnit.exists_right_inv (Ne.isUnit hea)
  obtain ⟨b, rfl⟩ := hbij.2 b'
  refine ⟨b, hbij.1 ?_⟩
  rw [map_mul, map_one]
  exact hb'

end Connected

end FiniteEtaleGalois

end ModularCurves
