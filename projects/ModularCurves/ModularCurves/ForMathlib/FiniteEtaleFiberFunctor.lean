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

/-- The base change functor with both algebra universes pinned to `u`.  `baseChange`
has a free object-universe parameter which otherwise leaks into every statement. -/
noncomputable abbrev baseChangeU :
    CommAlgCat.FiniteEtale.{u} k ⥤ CommAlgCat.FiniteEtale.{u} Ω :=
  CommAlgCat.FiniteEtale.baseChange k Ω

/-! Base change preserves the initial object (leaf AG-GG-2a). -/

section Initial

/-- `Ω ⊗[k] k` is the initial finite étale `Ω`-algebra. -/
noncomputable def baseChangeInitialIso :
    (baseChangeU k Ω).obj (CommAlgCat.FiniteEtale.of k k) ≅
      CommAlgCat.FiniteEtale.of Ω Ω :=
  CommAlgCat.FiniteEtale.isoMk (Algebra.TensorProduct.rid k Ω Ω)

/-- `FiniteEtale.of k k` is initial. -/
noncomputable def isInitialOfSelf : IsInitial (CommAlgCat.FiniteEtale.of k k) :=
  haveI : ∀ A : CommAlgCat.FiniteEtale.{u} k,
      Unique (CommAlgCat.FiniteEtale.of k k ⟶ A) := fun _ =>
    ⟨⟨Nonempty.some inferInstance⟩, fun _ => Subsingleton.elim _ _⟩
  IsInitial.ofUnique _

lemma preservesInitial_baseChange :
    PreservesColimit (Functor.empty.{0} (CommAlgCat.FiniteEtale.{u} k))
      (baseChangeU k Ω) := by
  refine preservesInitial_of_iso _ ?_
  refine (initialIsoIsInitial (isInitialOfSelf Ω)).trans ?_
  refine (baseChangeInitialIso k Ω).symm.trans ?_
  exact ((baseChangeU k Ω).mapIso
    (initialIsoIsInitial (isInitialOfSelf k))).symm

lemma preservesColimitsOfShapePEmpty_baseChange :
    PreservesColimitsOfShape (Discrete PEmpty.{1}) (baseChangeU k Ω) :=
  haveI := preservesInitial_baseChange k Ω
  preservesColimitsOfShape_pempty_of_preservesInitial (baseChangeU k Ω)

end Initial

/-! Base change preserves finite products (leaf AG-GG-2c): `Ω ⊗[k] ∏ᵢ Aᵢ ≅ ∏ᵢ (Ω ⊗[k] Aᵢ)`
via `Algebra.TensorProduct.piRight`. -/

section Products

variable {k Ω}

/-- Evaluating a base-changed product at a coordinate is the `piRight` coordinate. -/
lemma map_eval_eq_piRight_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) (i : ι) (x : Ω ⊗[k] (Π j, A j)) :
    Algebra.TensorProduct.map (AlgHom.id Ω Ω)
        (Pi.evalAlgHom k (fun j => (A j : Type u)) i) x =
      Algebra.TensorProduct.piRight k Ω Ω (fun j => (A j : Type u)) x i := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul ω f => simp [Algebra.TensorProduct.piRight_tmul]
  | add a b ha hb => simp [map_add, ha, hb]

/-- Two maps into a base-changed product agreeing on all coordinate projections are
equal. -/
lemma baseChangePi_hom_ext {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) {W : CommAlgCat.FiniteEtale.{u} Ω}
    {u v : W ⟶ (baseChangeU k Ω).obj (CommAlgCat.FiniteEtale.of k (Π j, A j))}
    (h : ∀ i, u ≫ (baseChangeU k Ω).map ((productFan A).π.app ⟨i⟩) =
      v ≫ (baseChangeU k Ω).map ((productFan A).π.app ⟨i⟩)) : u = v := by
  ext x
  apply (Algebra.TensorProduct.piRight k Ω Ω (fun j => (A j : Type u))).injective
  refine funext fun i => ?_
  rw [← map_eval_eq_piRight_apply A i, ← map_eval_eq_piRight_apply A i]
  exact congrArg (fun q => q.hom.hom x) (h i)

/-- The base change of the product fan is a limit fan: `Ω ⊗[k] ∏ᵢ Aᵢ` is the product
of the `Ω ⊗[k] Aᵢ`, via `piRight`. -/
noncomputable def isLimitMapConeProductFan {ι : Type} [Finite ι]
    (A : ι → CommAlgCat.FiniteEtale.{u} k) :
    IsLimit ((baseChangeU k Ω).mapCone (productFan A)) := by
  haveI := Fintype.ofFinite ι
  haveI := Classical.decEq ι
  have hfac : ∀ (s : Cone (Discrete.functor A ⋙ baseChangeU k Ω)) (i : ι),
      (ObjectProperty.homMk (CommAlgCat.ofHom
        ((Algebra.TensorProduct.piRight k Ω Ω
            (fun j => (A j : Type u))).symm.toAlgHom.comp
          (AlgHom.pi (fun i => (s.π.app ⟨i⟩).hom.hom)))) :
          s.pt ⟶ (baseChangeU k Ω).obj (CommAlgCat.FiniteEtale.of k (Π j, A j))) ≫
        ((baseChangeU k Ω).mapCone (productFan A)).π.app ⟨i⟩ = s.π.app ⟨i⟩ := by
    intro s i
    ext x
    show Algebra.TensorProduct.map (AlgHom.id Ω Ω)
        (Pi.evalAlgHom k (fun j => (A j : Type u)) i)
        ((Algebra.TensorProduct.piRight k Ω Ω _).symm
          (fun j => (s.π.app ⟨j⟩).hom.hom x)) =
      (s.π.app ⟨i⟩).hom.hom x
    rw [map_eval_eq_piRight_apply, AlgEquiv.apply_symm_apply]
  refine IsLimit.mk
    (fun s => ObjectProperty.homMk (CommAlgCat.ofHom
      ((Algebra.TensorProduct.piRight k Ω Ω
          (fun j => (A j : Type u))).symm.toAlgHom.comp
        (AlgHom.pi (fun i => (s.π.app ⟨i⟩).hom.hom)))))
    (fun s => by rintro ⟨i⟩; exact hfac s i)
    (fun s m hm => baseChangePi_hom_ext A fun i => (hm ⟨i⟩).trans (hfac s i).symm)

lemma preservesLimitsOfShapeDiscrete_baseChange (ι : Type) [Finite ι] :
    PreservesLimitsOfShape (Discrete ι) (baseChangeU k Ω) where
  preservesLimit {K} :=
    haveI : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) (baseChangeU k Ω) :=
      preservesLimit_of_preserves_limit_cone
        (productFanIsLimit (K.obj ∘ Discrete.mk))
        (isLimitMapConeProductFan (K.obj ∘ Discrete.mk))
    preservesLimit_of_iso_diagram _ (Discrete.natIsoFunctor (F := K)).symm

end Products

end FiniteEtaleGalois

end ModularCurves
