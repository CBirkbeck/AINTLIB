import ModularCurves.ForMathlib.FinitePresentationOpenImmersionFamily
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Spreading affine pushout squares

The canonical comparison from a tensor-product pushout to the fourth corner
of a commutative algebra square is used to reflect the pushout condition from
a filtered colimit to one finite stage.
-/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Algebra

variable {S C₀ C₁ C₂ C₃ : Type u}
  [CommRing S] [CommRing C₀] [CommRing C₁] [CommRing C₂] [CommRing C₃]
  [Algebra S C₀] [Algebra S C₁] [Algebra S C₂] [Algebra S C₃]

/-- The canonical map from the tensor-product pushout of the top and left
maps to the fourth corner of a commutative square of algebra maps. -/
noncomputable def pushoutMap
    (f : C₀ →ₐ[S] C₁) (g : C₀ →ₐ[S] C₂)
    (inl : C₁ →ₐ[S] C₃) (inr : C₂ →ₐ[S] C₃)
    (h : inl.comp f = inr.comp g) :
    letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
    letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
    TensorProduct C₀ C₁ C₂ →ₐ[S] C₃ := by
  letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
  letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
  letI : Algebra C₀ C₃ := (inl.comp f).toRingHom.toAlgebra
  let inl₀ : C₁ →ₐ[C₀] C₃ :=
    { inl.toRingHom with commutes' := fun _ => rfl }
  let inr₀ : C₂ →ₐ[C₀] C₃ :=
    { inr.toRingHom with
      commutes' := fun x => by
        exact congrArg (fun q : C₀ →ₐ[S] C₃ => q x) h.symm }
  haveI : IsScalarTower S C₀ C₁ :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  haveI : IsScalarTower S C₀ C₂ :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  haveI : IsScalarTower S C₀ C₃ :=
    IsScalarTower.of_algebraMap_eq' (inl.comp f).comp_algebraMap.symm
  exact (Algebra.TensorProduct.productMap inl₀ inr₀).restrictScalars S

@[simp]
theorem pushoutMap_includeLeft
    (f : C₀ →ₐ[S] C₁) (g : C₀ →ₐ[S] C₂)
    (inl : C₁ →ₐ[S] C₃) (inr : C₂ →ₐ[S] C₃)
    (h : inl.comp f = inr.comp g) :
    letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
    letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
    letI : IsScalarTower S C₀ C₁ :=
      IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    letI : IsScalarTower S C₀ C₂ :=
      IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
    (pushoutMap f g inl inr h).comp
        (Algebra.TensorProduct.includeLeft (R := C₀) (S := S) (A := C₁) (B := C₂)) =
      inl := by
  letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
  letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
  letI : Algebra C₀ C₃ := (inl.comp f).toRingHom.toAlgebra
  ext x
  exact Algebra.TensorProduct.productMap_left_apply
    (f := ({ inl.toRingHom with commutes' := fun _ => rfl } : C₁ →ₐ[C₀] C₃))
    (g := ({ inr.toRingHom with
      commutes' := fun y =>
        congrArg (fun q : C₀ →ₐ[S] C₃ => q y) h.symm } : C₂ →ₐ[C₀] C₃)) x

@[simp]
theorem pushoutMap_includeRight
    (f : C₀ →ₐ[S] C₁) (g : C₀ →ₐ[S] C₂)
    (inl : C₁ →ₐ[S] C₃) (inr : C₂ →ₐ[S] C₃)
    (h : inl.comp f = inr.comp g) :
    letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
    letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
    letI : IsScalarTower S C₀ C₁ :=
      IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
    letI : IsScalarTower S C₀ C₂ :=
      IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
    (pushoutMap f g inl inr h).comp
        ((Algebra.TensorProduct.includeRight (R := C₀) (A := C₁) (B := C₂)).restrictScalars S) =
      inr := by
  letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
  letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
  letI : Algebra C₀ C₃ := (inl.comp f).toRingHom.toAlgebra
  ext x
  exact Algebra.TensorProduct.productMap_right_apply
    (f := ({ inl.toRingHom with commutes' := fun _ => rfl } : C₁ →ₐ[C₀] C₃))
    (g := ({ inr.toRingHom with
      commutes' := fun y =>
        congrArg (fun q : C₀ →ₐ[S] C₃ => q y) h.symm } : C₂ →ₐ[C₀] C₃)) x

/-- A commutative algebra square is a pushout when its canonical map from the
tensor-product pushout is bijective. -/
theorem isPushout_of_pushoutMap_bijective
    (f : C₀ →ₐ[S] C₁) (g : C₀ →ₐ[S] C₂)
    (inl : C₁ →ₐ[S] C₃) (inr : C₂ →ₐ[S] C₃)
    (h : inl.comp f = inr.comp g)
    (hbij :
      letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
      letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
      Function.Bijective (pushoutMap f g inl inr h)) :
    CategoryTheory.IsPushout (CommRingCat.ofHom f.toRingHom)
      (CommRingCat.ofHom g.toRingHom) (CommRingCat.ofHom inl.toRingHom)
      (CommRingCat.ofHom inr.toRingHom) := by
  letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
  letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
  letI : IsScalarTower S C₀ C₁ :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : IsScalarTower S C₀ C₂ :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let q := pushoutMap f g inl inr h
  let e := (AlgEquiv.ofBijective q hbij).toRingEquiv.toCommRingCatIso
  apply (CommRingCat.isPushout_tensorProduct C₀ C₁ C₂).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  · ext x
    rfl
  · ext x
    rfl
  · ext x
    exact congrArg (fun φ : C₁ →ₐ[S] C₃ => φ x)
      (pushoutMap_includeLeft f g inl inr h)
  · ext x
    exact congrArg (fun φ : C₂ →ₐ[S] C₃ => φ x)
      (pushoutMap_includeRight f g inl inr h)

private theorem isPushout_toUnder
    (f : C₀ →ₐ[S] C₁) (g : C₀ →ₐ[S] C₂)
    (inl : C₁ →ₐ[S] C₃) (inr : C₂ →ₐ[S] C₃)
    (h : CategoryTheory.IsPushout (CommRingCat.ofHom f.toRingHom)
      (CommRingCat.ofHom g.toRingHom) (CommRingCat.ofHom inl.toRingHom)
      (CommRingCat.ofHom inr.toRingHom)) :
    CategoryTheory.IsPushout
      (f.toUnder : CommRingCat.mkUnder (CommRingCat.of S) C₀ ⟶
        CommRingCat.mkUnder (CommRingCat.of S) C₁)
      (g.toUnder : CommRingCat.mkUnder (CommRingCat.of S) C₀ ⟶
        CommRingCat.mkUnder (CommRingCat.of S) C₂)
      (inl.toUnder : CommRingCat.mkUnder (CommRingCat.of S) C₁ ⟶
        CommRingCat.mkUnder (CommRingCat.of S) C₃)
      (inr.toUnder : CommRingCat.mkUnder (CommRingCat.of S) C₂ ⟶
        CommRingCat.mkUnder (CommRingCat.of S) C₃) := by
  have hw : CommSq
      (f.toUnder : CommRingCat.mkUnder (CommRingCat.of S) C₀ ⟶
        CommRingCat.mkUnder (CommRingCat.of S) C₁)
      (g.toUnder : CommRingCat.mkUnder (CommRingCat.of S) C₀ ⟶
        CommRingCat.mkUnder (CommRingCat.of S) C₂)
      (inl.toUnder : CommRingCat.mkUnder (CommRingCat.of S) C₁ ⟶
        CommRingCat.mkUnder (CommRingCat.of S) C₃)
      (inr.toUnder : CommRingCat.mkUnder (CommRingCat.of S) C₂ ⟶
        CommRingCat.mkUnder (CommRingCat.of S) C₃) := by
    constructor
    ext x
    exact congrArg (fun q : CommRingCat.of C₀ ⟶ CommRingCat.of C₃ => q x) h.w
  refine CategoryTheory.IsPushout.of_isColimit' hw ?_
  apply PushoutCocone.isColimitAux'
  intro s
  let hs := congrArg Under.Hom.right s.condition
  let d₀ := h.desc s.inl.right s.inr.right hs
  letI : Algebra S s.pt.right := s.pt.hom.hom.toAlgebra
  let dAlg : C₃ →ₐ[S] s.pt.right :=
    { d₀.hom with
      commutes' := fun x => by
        rw [← inl.commutes x]
        change d₀ (inl (algebraMap S C₁ x)) = _
        calc
          _ = s.inl.right (algebraMap S C₁ x) :=
            congrArg (fun q : CommRingCat.of C₁ ⟶ s.pt.right =>
              q (algebraMap S C₁ x))
              (h.inl_desc s.inl.right s.inr.right hs)
          _ = s.pt.hom x :=
            congrArg (fun q : CommRingCat.of S ⟶ s.pt.right => q x) s.inl.w }
  refine ⟨dAlg.toUnder, ?_, ?_, ?_⟩
  · ext x
    change d₀ (inl x) = s.inl.right x
    exact congrArg (fun q : CommRingCat.of C₁ ⟶ s.pt.right => q x)
      (h.inl_desc s.inl.right s.inr.right hs)
  · ext x
    change d₀ (inr x) = s.inr.right x
    exact congrArg (fun q : CommRingCat.of C₂ ⟶ s.pt.right => q x)
      (h.inr_desc s.inl.right s.inr.right hs)
  · intro m hm₁ hm₂
    ext x
    exact congrArg (fun q : CommRingCat.of C₃ ⟶ s.pt.right => q x)
      (h.hom_ext
        ((congrArg Under.Hom.right hm₁).trans
          (h.inl_desc s.inl.right s.inr.right hs).symm)
        ((congrArg Under.Hom.right hm₂).trans
          (h.inr_desc s.inl.right s.inr.right hs).symm))

private noncomputable def tensorProd_mkUnder_iso
    {A C : Type u} [CommRing A] [CommRing C] [Algebra S A] [Algebra S C] :
    (CommRingCat.tensorProd (CommRingCat.of S) (CommRingCat.of A)).obj
        (CommRingCat.mkUnder (CommRingCat.of S) C) ≅
      CommRingCat.mkUnder (CommRingCat.of A) (TensorProduct S A C) := by
  let U := CommRingCat.mkUnder (CommRingCat.of S) C
  letI : Algebra S (U : Type u) := RingHom.toAlgebra U.hom.hom
  let eC : U ≃ₐ[S] C :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_mul' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  let e := Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) eC
  exact Under.isoMk e.toRingEquiv.toCommRingCatIso (by
    ext x
    exact e.commutes x)

private theorem tensorProd_mkUnder_iso_naturality
    {A C D : Type u} [CommRing A] [CommRing C] [CommRing D]
    [Algebra S A] [Algebra S C] [Algebra S D] (f : C →ₐ[S] D) :
    (CommRingCat.tensorProd (CommRingCat.of S) (CommRingCat.of A)).map f.toUnder ≫
        (tensorProd_mkUnder_iso (S := S) (A := A) (C := D)).hom =
      (tensorProd_mkUnder_iso (S := S) (A := A) (C := C)).hom ≫
        (Algebra.TensorProduct.map (AlgHom.id A A) f).toUnder := by
  let U := CommRingCat.mkUnder (CommRingCat.of S) C
  letI : Algebra S (U : Type u) := RingHom.toAlgebra U.hom.hom
  apply StructuredArrow.hom_ext
  apply CommRingCat.Hom.ext
  apply Algebra.TensorProduct.ringHom_ext
  · ext a
    rfl
  · ext c
    rfl

private theorem isPushout_tensorProduct_map_toUnder
    {T : Type u} [CommRing T] [Algebra S T]
    (f : C₀ →ₐ[S] C₁) (g : C₀ →ₐ[S] C₂)
    (inl : C₁ →ₐ[S] C₃) (inr : C₂ →ₐ[S] C₃)
    (h : CategoryTheory.IsPushout (CommRingCat.ofHom f.toRingHom)
      (CommRingCat.ofHom g.toRingHom) (CommRingCat.ofHom inl.toRingHom)
      (CommRingCat.ofHom inr.toRingHom)) :
    let fT := Algebra.TensorProduct.map (AlgHom.id T T) f
    let gT := Algebra.TensorProduct.map (AlgHom.id T T) g
    let inlT := Algebra.TensorProduct.map (AlgHom.id T T) inl
    let inrT := Algebra.TensorProduct.map (AlgHom.id T T) inr
    CategoryTheory.IsPushout
      (fT.toUnder : CommRingCat.mkUnder (CommRingCat.of T) (TensorProduct S T C₀) ⟶
        CommRingCat.mkUnder (CommRingCat.of T) (TensorProduct S T C₁))
      (gT.toUnder : CommRingCat.mkUnder (CommRingCat.of T) (TensorProduct S T C₀) ⟶
        CommRingCat.mkUnder (CommRingCat.of T) (TensorProduct S T C₂))
      (inlT.toUnder : CommRingCat.mkUnder (CommRingCat.of T) (TensorProduct S T C₁) ⟶
        CommRingCat.mkUnder (CommRingCat.of T) (TensorProduct S T C₃))
      (inrT.toUnder : CommRingCat.mkUnder (CommRingCat.of T) (TensorProduct S T C₂) ⟶
        CommRingCat.mkUnder (CommRingCat.of T) (TensorProduct S T C₃)) := by
  let hU := isPushout_toUnder f g inl inr h
  let BC := CommRingCat.tensorProd (CommRingCat.of S) (CommRingCat.of T)
  haveI : (Under.pushout (CommRingCat.ofHom (algebraMap S T))).IsLeftAdjoint :=
    inferInstance
  haveI : BC.IsLeftAdjoint := Functor.isLeftAdjoint_of_iso
    (CommRingCat.tensorProdIsoPushout (CommRingCat.of S) (CommRingCat.of T)).symm
  let hT := BC.map_isPushout hU
  apply hT.of_iso tensorProd_mkUnder_iso tensorProd_mkUnder_iso
    tensorProd_mkUnder_iso tensorProd_mkUnder_iso
  · exact tensorProd_mkUnder_iso_naturality f
  · exact tensorProd_mkUnder_iso_naturality g
  · exact tensorProd_mkUnder_iso_naturality inl
  · exact tensorProd_mkUnder_iso_naturality inr

private theorem isPushout_tensorProduct_map
    {T : Type u} [CommRing T] [Algebra S T]
    (f : C₀ →ₐ[S] C₁) (g : C₀ →ₐ[S] C₂)
    (inl : C₁ →ₐ[S] C₃) (inr : C₂ →ₐ[S] C₃)
    (h : CategoryTheory.IsPushout (CommRingCat.ofHom f.toRingHom)
      (CommRingCat.ofHom g.toRingHom) (CommRingCat.ofHom inl.toRingHom)
      (CommRingCat.ofHom inr.toRingHom)) :
    let fT := Algebra.TensorProduct.map (AlgHom.id T T) f
    let gT := Algebra.TensorProduct.map (AlgHom.id T T) g
    let inlT := Algebra.TensorProduct.map (AlgHom.id T T) inl
    let inrT := Algebra.TensorProduct.map (AlgHom.id T T) inr
    CategoryTheory.IsPushout (CommRingCat.ofHom fT.toRingHom)
      (CommRingCat.ofHom gT.toRingHom) (CommRingCat.ofHom inlT.toRingHom)
      (CommRingCat.ofHom inrT.toRingHom) := by
  let hU := isPushout_tensorProduct_map_toUnder (S := S) (T := T)
    (C₀ := C₀) (C₁ := C₁) (C₂ := C₂) (C₃ := C₃) f g inl inr h
  let hR := (Under.forget (CommRingCat.of T)).map_isPushout hU
  exact hR

private theorem isPushout_tensorProduct_map_of_pushoutMap_bijective
    {T : Type u} [CommRing T] [Algebra S T]
    (f : C₀ →ₐ[S] C₁) (g : C₀ →ₐ[S] C₂)
    (inl : C₁ →ₐ[S] C₃) (inr : C₂ →ₐ[S] C₃)
    (h : inl.comp f = inr.comp g)
    (hbij :
      letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
      letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
      Function.Bijective
        (Algebra.TensorProduct.map (AlgHom.id S T) (pushoutMap f g inl inr h))) :
    let fT := Algebra.TensorProduct.map (AlgHom.id T T) f
    let gT := Algebra.TensorProduct.map (AlgHom.id T T) g
    let inlT := Algebra.TensorProduct.map (AlgHom.id T T) inl
    let inrT := Algebra.TensorProduct.map (AlgHom.id T T) inr
    CategoryTheory.IsPushout (CommRingCat.ofHom fT.toRingHom)
      (CommRingCat.ofHom gT.toRingHom) (CommRingCat.ofHom inlT.toRingHom)
      (CommRingCat.ofHom inrT.toRingHom) := by
  letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
  letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
  letI : IsScalarTower S C₀ C₁ :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : IsScalarTower S C₀ C₂ :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let P := TensorProduct C₀ C₁ C₂
  let left : C₁ →ₐ[S] P :=
    Algebra.TensorProduct.includeLeft (R := C₀) (S := S) (A := C₁) (B := C₂)
  let right : C₂ →ₐ[S] P :=
    (Algebra.TensorProduct.includeRight (R := C₀) (A := C₁) (B := C₂)).restrictScalars S
  have hP : CategoryTheory.IsPushout (CommRingCat.ofHom f.toRingHom)
      (CommRingCat.ofHom g.toRingHom) (CommRingCat.ofHom left.toRingHom)
      (CommRingCat.ofHom right.toRingHom) := by
    dsimp [P, left, right]
    convert CommRingCat.isPushout_tensorProduct C₀ C₁ C₂ using 1 <;> ext <;> rfl
  let fT := Algebra.TensorProduct.map (AlgHom.id T T) f
  let gT := Algebra.TensorProduct.map (AlgHom.id T T) g
  let inlT := Algebra.TensorProduct.map (AlgHom.id T T) inl
  let inrT := Algebra.TensorProduct.map (AlgHom.id T T) inr
  let leftT := Algebra.TensorProduct.map (AlgHom.id T T) left
  let rightT := Algebra.TensorProduct.map (AlgHom.id T T) right
  let qT := Algebra.TensorProduct.map (AlgHom.id T T) (pushoutMap f g inl inr h)
  have hbijT : Function.Bijective qT := by
    rw [show (qT : TensorProduct S T P → TensorProduct S T C₃) =
      Algebra.TensorProduct.map (AlgHom.id S T) (pushoutMap f g inl inr h) by rfl]
    exact hbij
  let e := (AlgEquiv.ofBijective qT hbijT).toRingEquiv.toCommRingCatIso
  have hleft : qT.comp leftT = inlT := by
    rw [← Algebra.TensorProduct.map_id_comp]
    exact congrArg (Algebra.TensorProduct.map (AlgHom.id T T))
      (pushoutMap_includeLeft f g inl inr h)
  have hright : qT.comp rightT = inrT := by
    rw [← Algebra.TensorProduct.map_id_comp]
    exact congrArg (Algebra.TensorProduct.map (AlgHom.id T T))
      (pushoutMap_includeRight f g inl inr h)
  apply (isPushout_tensorProduct_map f g left right hP).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e
  · simp
  · simp
  · apply CommRingCat.Hom.ext
    exact congrArg AlgHom.toRingHom hleft
  · apply CommRingCat.Hom.ext
    exact congrArg AlgHom.toRingHom hright

private theorem tensorProduct_map_pushoutMap_bijective
    {A B₀ B₁ B₂ B₃ : Type u}
    [CommRing A] [Algebra S A]
    [CommRing B₀] [CommRing B₁] [CommRing B₂] [CommRing B₃]
    [Algebra A B₀] [Algebra A B₁] [Algebra A B₂] [Algebra A B₃]
    (f : C₀ →ₐ[S] C₁) (g : C₀ →ₐ[S] C₂)
    (inl : C₁ →ₐ[S] C₃) (inr : C₂ →ₐ[S] C₃)
    (h : inl.comp f = inr.comp g)
    (F : B₀ →ₐ[A] B₁) (G : B₀ →ₐ[A] B₂)
    (Inl : B₁ →ₐ[A] B₃) (Inr : B₂ →ₐ[A] B₃)
    (Hpush : CategoryTheory.IsPushout (CommRingCat.ofHom F.toRingHom)
      (CommRingCat.ofHom G.toRingHom) (CommRingCat.ofHom Inl.toRingHom)
      (CommRingCat.ofHom Inr.toRingHom))
    (e₀ : TensorProduct S A C₀ ≃ₐ[A] B₀)
    (e₁ : TensorProduct S A C₁ ≃ₐ[A] B₁)
    (e₂ : TensorProduct S A C₂ ≃ₐ[A] B₂)
    (e₃ : TensorProduct S A C₃ ≃ₐ[A] B₃)
    (hf : e₁.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id A A) f) =
      F.comp e₀.toAlgHom)
    (hg : e₂.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id A A) g) =
      G.comp e₀.toAlgHom)
    (hinl : e₃.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id A A) inl) =
      Inl.comp e₁.toAlgHom)
    (hinr : e₃.toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id A A) inr) =
      Inr.comp e₂.toAlgHom) :
    letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
    letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
    Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id S A) (pushoutMap f g inl inr h)) := by
  letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
  letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
  letI : IsScalarTower S C₀ C₁ :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : IsScalarTower S C₀ C₂ :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  let P := TensorProduct C₀ C₁ C₂
  let left : C₁ →ₐ[S] P :=
    Algebra.TensorProduct.includeLeft (R := C₀) (S := S) (A := C₁) (B := C₂)
  let right : C₂ →ₐ[S] P :=
    (Algebra.TensorProduct.includeRight (R := C₀) (A := C₁) (B := C₂)).restrictScalars S
  have hP : CategoryTheory.IsPushout (CommRingCat.ofHom f.toRingHom)
      (CommRingCat.ofHom g.toRingHom) (CommRingCat.ofHom left.toRingHom)
      (CommRingCat.ofHom right.toRingHom) := by
    dsimp [P, left, right]
    convert CommRingCat.isPushout_tensorProduct C₀ C₁ C₂ using 1 <;> ext <;> rfl
  let hBU := isPushout_toUnder F G Inl Inr Hpush
  let fA := Algebra.TensorProduct.map (AlgHom.id A A) f
  let gA := Algebra.TensorProduct.map (AlgHom.id A A) g
  let inlA := Algebra.TensorProduct.map (AlgHom.id A A) inl
  let inrA := Algebra.TensorProduct.map (AlgHom.id A A) inr
  have hCA : CategoryTheory.IsPushout fA.toUnder gA.toUnder inlA.toUnder inrA.toUnder :=
    hBU.of_iso' e₀.toUnder e₁.toUnder e₂.toUnder e₃.toUnder
      (by ext x; exact congrArg (fun φ : TensorProduct S A C₀ →ₐ[A] B₁ => φ x) hf.symm)
      (by ext x; exact congrArg (fun φ : TensorProduct S A C₀ →ₐ[A] B₂ => φ x) hg.symm)
      (by ext x; exact congrArg (fun φ : TensorProduct S A C₁ →ₐ[A] B₃ => φ x) hinl.symm)
      (by ext x; exact congrArg (fun φ : TensorProduct S A C₂ →ₐ[A] B₃ => φ x) hinr.symm)
  let q := pushoutMap f g inl inr h
  let qA := Algebra.TensorProduct.map (AlgHom.id A A) q
  let leftA := Algebra.TensorProduct.map (AlgHom.id A A) left
  let rightA := Algebra.TensorProduct.map (AlgHom.id A A) right
  have hleft : qA.comp leftA = inlA := by
    rw [← Algebra.TensorProduct.map_id_comp]
    exact congrArg (Algebra.TensorProduct.map (AlgHom.id A A))
      (pushoutMap_includeLeft f g inl inr h)
  have hright : qA.comp rightA = inrA := by
    rw [← Algebra.TensorProduct.map_id_comp]
    exact congrArg (Algebra.TensorProduct.map (AlgHom.id A A))
      (pushoutMap_includeRight f g inl inr h)
  have hPA' : CategoryTheory.IsPushout
      (fA.toUnder : CommRingCat.mkUnder (CommRingCat.of A) (TensorProduct S A C₀) ⟶
        CommRingCat.mkUnder (CommRingCat.of A) (TensorProduct S A C₁))
      (gA.toUnder : CommRingCat.mkUnder (CommRingCat.of A) (TensorProduct S A C₀) ⟶
        CommRingCat.mkUnder (CommRingCat.of A) (TensorProduct S A C₂))
      (leftA.toUnder : CommRingCat.mkUnder (CommRingCat.of A) (TensorProduct S A C₁) ⟶
        CommRingCat.mkUnder (CommRingCat.of A) (TensorProduct S A P))
      (rightA.toUnder : CommRingCat.mkUnder (CommRingCat.of A) (TensorProduct S A C₂) ⟶
        CommRingCat.mkUnder (CommRingCat.of A) (TensorProduct S A P)) :=
    isPushout_tensorProduct_map_toUnder f g left right hP
  let eP := hPA'.isoIsPushout _ _ hCA
  have hq : qA.toUnder = eP.hom := by
    apply hPA'.hom_ext
    · rw [hPA'.inl_isoIsPushout_hom _ _ hCA]
      exact congrArg
        (fun φ : TensorProduct S A C₁ →ₐ[A] TensorProduct S A C₃ =>
          AlgHom.toUnder (R := CommRingCat.of A) φ) hleft
    · rw [hPA'.inr_isoIsPushout_hom _ _ hCA]
      exact congrArg
        (fun φ : TensorProduct S A C₂ →ₐ[A] TensorProduct S A C₃ =>
          AlgHom.toUnder (R := CommRingCat.of A) φ) hright
  let ePRing := (Under.forget (CommRingCat.of A)).mapIso eP
  have heP : Function.Bijective
      ePRing.hom :=
    ConcreteCategory.bijective_of_isIso _
  have hqA : Function.Bijective qA := by
    rw [show (qA : TensorProduct S A P → TensorProduct S A C₃) =
      ePRing.hom by
        funext x
        exact congrArg (fun φ => φ.right x) hq]
    exact heP
  constructor
  · intro x y hxy
    exact hqA.1 hxy
  · intro y
    obtain ⟨x, hx⟩ := hqA.2 y
    exact ⟨x, hx⟩

private theorem SpreadData.baseChangeColimEquiv_map
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (F : B₁ →ₐ[A] B₂)
    (hf : ∀ x, D₂.stageToColimit H ⟨i, h₂⟩ (f x) =
      F (D₁.stageToColimit H ⟨i, h₁⟩ x)) :
    letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
    (D₂.baseChangeColimEquiv h₂ H).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id A A) f) =
      F.comp (D₁.baseChangeColimEquiv h₁ H).toAlgHom := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  apply AlgHom.ext
  intro z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) hx hy
  | tmul a x =>
      rw [TensorProduct.tmul_eq_smul_one_tmul]
      simp only [AlgHom.comp_apply, map_smul]
      rw [Algebra.TensorProduct.map_tmul]
      simp only [AlgHom.id_apply]
      apply congrArg (a • ·)
      calc
        D₂.baseChangeColimEquiv h₂ H (1 ⊗ₜ[𝒮 i] f x) =
            D₂.stageToColimit H ⟨i, h₂⟩ (f x) :=
          D₂.baseChangeColimEquiv_tmul h₂ H (f x)
        _ = F (D₁.stageToColimit H ⟨i, h₁⟩ x) := hf x
        _ = F (D₁.baseChangeColimEquiv h₁ H (1 ⊗ₜ[𝒮 i] x)) :=
          congrArg F (D₁.baseChangeColimEquiv_tmul h₁ H x).symm

private theorem SpreadData.spreadStageBaseChangeEquiv_mapAtLaterStage
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
    {B₁ B₂ : Type u} [CommRing B₁] [CommRing B₂]
    [Algebra A B₁] [Algebra A B₂]
    (D₁ : SpreadData 𝒮 uA B₁) (D₂ : SpreadData 𝒮 uA B₂)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₁ : D₁.i₀ ≤ i) (h₂ : D₂.i₀ ≤ i) (hij : i ≤ j)
    (f : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂) :
    letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
    (D₂.spreadStageBaseChangeEquiv hij h₂ H).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id (𝒮 j) (𝒮 j)) f) =
      (D₁.mapAtLaterStage D₂ H h₁ h₂ hij f).comp
        (D₁.spreadStageBaseChangeEquiv hij h₁ H).toAlgHom := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  apply AlgHom.ext
  intro x
  rw [AlgHom.comp_apply, AlgHom.comp_apply, D₁.mapAtLaterStage_apply]
  simp

private theorem SpreadData.isPushout_mapAtLaterStage_of_tensorProduct
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
    {B₀ B₁ B₂ B₃ : Type u}
    [CommRing B₀] [CommRing B₁] [CommRing B₂] [CommRing B₃]
    [Algebra A B₀] [Algebra A B₁] [Algebra A B₂] [Algebra A B₃]
    (D₀ : SpreadData 𝒮 uA B₀) (D₁ : SpreadData 𝒮 uA B₁)
    (D₂ : SpreadData 𝒮 uA B₂) (D₃ : SpreadData 𝒮 uA B₃)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j : ι} (h₀ : D₀.i₀ ≤ i) (h₁ : D₁.i₀ ≤ i)
    (h₂ : D₂.i₀ ≤ i) (h₃ : D₃.i₀ ≤ i) (hij : i ≤ j)
    (f : D₀.spreadStage (t := t) h₀ →ₐ[𝒮 i]
      D₁.spreadStage (t := t) h₁)
    (g : D₀.spreadStage (t := t) h₀ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (inl : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₃.spreadStage (t := t) h₃)
    (inr : D₂.spreadStage (t := t) h₂ →ₐ[𝒮 i]
      D₃.spreadStage (t := t) h₃)
    (hpush :
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      letI : CommRing (TensorProduct (𝒮 i) (𝒮 j)
          (D₀.spreadStage (t := t) h₀)) := Algebra.TensorProduct.instCommRing
      letI : CommRing (TensorProduct (𝒮 i) (𝒮 j)
          (D₁.spreadStage (t := t) h₁)) := Algebra.TensorProduct.instCommRing
      letI : CommRing (TensorProduct (𝒮 i) (𝒮 j)
          (D₂.spreadStage (t := t) h₂)) := Algebra.TensorProduct.instCommRing
      letI : CommRing (TensorProduct (𝒮 i) (𝒮 j)
          (D₃.spreadStage (t := t) h₃)) := Algebra.TensorProduct.instCommRing
      let fT := Algebra.TensorProduct.map (AlgHom.id (𝒮 j) (𝒮 j)) f
      let gT := Algebra.TensorProduct.map (AlgHom.id (𝒮 j) (𝒮 j)) g
      let inlT := Algebra.TensorProduct.map (AlgHom.id (𝒮 j) (𝒮 j)) inl
      let inrT := Algebra.TensorProduct.map (AlgHom.id (𝒮 j) (𝒮 j)) inr
      CategoryTheory.IsPushout
        (CommRingCat.ofHom fT.toRingHom) (CommRingCat.ofHom gT.toRingHom)
        (CommRingCat.ofHom inlT.toRingHom) (CommRingCat.ofHom inrT.toRingHom)) :
    CategoryTheory.IsPushout
      (CommRingCat.ofHom
        (D₀.mapAtLaterStage D₁ H h₀ h₁ hij f).toRingHom)
      (CommRingCat.ofHom
        (D₀.mapAtLaterStage D₂ H h₀ h₂ hij g).toRingHom)
      (CommRingCat.ofHom
        (D₁.mapAtLaterStage D₃ H h₁ h₃ hij inl).toRingHom)
      (CommRingCat.ofHom
        (D₂.mapAtLaterStage D₃ H h₂ h₃ hij inr).toRingHom) := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  letI : CommRing (TensorProduct (𝒮 i) (𝒮 j)
      (D₀.spreadStage (t := t) h₀)) := Algebra.TensorProduct.instCommRing
  letI : CommRing (TensorProduct (𝒮 i) (𝒮 j)
      (D₁.spreadStage (t := t) h₁)) := Algebra.TensorProduct.instCommRing
  letI : CommRing (TensorProduct (𝒮 i) (𝒮 j)
      (D₂.spreadStage (t := t) h₂)) := Algebra.TensorProduct.instCommRing
  letI : CommRing (TensorProduct (𝒮 i) (𝒮 j)
      (D₃.spreadStage (t := t) h₃)) := Algebra.TensorProduct.instCommRing
  let e₀ := (D₀.spreadStageBaseChangeEquiv hij h₀ H).toRingEquiv.toCommRingCatIso
  let e₁ := (D₁.spreadStageBaseChangeEquiv hij h₁ H).toRingEquiv.toCommRingCatIso
  let e₂ := (D₂.spreadStageBaseChangeEquiv hij h₂ H).toRingEquiv.toCommRingCatIso
  let e₃ := (D₃.spreadStageBaseChangeEquiv hij h₃ H).toRingEquiv.toCommRingCatIso
  apply hpush.of_iso e₀ e₁ e₂ e₃
  · apply CommRingCat.Hom.ext
    exact congrArg AlgHom.toRingHom
      (D₀.spreadStageBaseChangeEquiv_mapAtLaterStage D₁ H h₀ h₁ hij f)
  · apply CommRingCat.Hom.ext
    exact congrArg AlgHom.toRingHom
      (D₀.spreadStageBaseChangeEquiv_mapAtLaterStage D₂ H h₀ h₂ hij g)
  · apply CommRingCat.Hom.ext
    exact congrArg AlgHom.toRingHom
      (D₁.spreadStageBaseChangeEquiv_mapAtLaterStage D₃ H h₁ h₃ hij inl)
  · apply CommRingCat.Hom.ext
    exact congrArg AlgHom.toRingHom
      (D₂.spreadStageBaseChangeEquiv_mapAtLaterStage D₃ H h₂ h₃ hij inr)

/-- A commutative square between four common-stage spread models which is a
pushout after base change to the filtered colimit is a pushout at one common
later stage. -/
theorem SpreadData.exists_isPushout_mapAtLaterStage
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
    {B₀ B₁ B₂ B₃ : Type u}
    [CommRing B₀] [CommRing B₁] [CommRing B₂] [CommRing B₃]
    [Algebra A B₀] [Algebra A B₁] [Algebra A B₂] [Algebra A B₃]
    (D₀ : SpreadData 𝒮 uA B₀) (D₁ : SpreadData 𝒮 uA B₁)
    (D₂ : SpreadData 𝒮 uA B₂) (D₃ : SpreadData 𝒮 uA B₃)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i : ι} (h₀ : D₀.i₀ ≤ i) (h₁ : D₁.i₀ ≤ i)
    (h₂ : D₂.i₀ ≤ i) (h₃ : D₃.i₀ ≤ i)
    (f : D₀.spreadStage (t := t) h₀ →ₐ[𝒮 i]
      D₁.spreadStage (t := t) h₁)
    (g : D₀.spreadStage (t := t) h₀ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (inl : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₃.spreadStage (t := t) h₃)
    (inr : D₂.spreadStage (t := t) h₂ →ₐ[𝒮 i]
      D₃.spreadStage (t := t) h₃)
    (h : inl.comp f = inr.comp g)
    (F : B₀ →ₐ[A] B₁) (G : B₀ →ₐ[A] B₂)
    (Inl : B₁ →ₐ[A] B₃) (Inr : B₂ →ₐ[A] B₃)
    (hf : ∀ x, D₁.stageToColimit H ⟨i, h₁⟩ (f x) =
      F (D₀.stageToColimit H ⟨i, h₀⟩ x))
    (hg : ∀ x, D₂.stageToColimit H ⟨i, h₂⟩ (g x) =
      G (D₀.stageToColimit H ⟨i, h₀⟩ x))
    (hinl : ∀ x, D₃.stageToColimit H ⟨i, h₃⟩ (inl x) =
      Inl (D₁.stageToColimit H ⟨i, h₁⟩ x))
    (hinr : ∀ x, D₃.stageToColimit H ⟨i, h₃⟩ (inr x) =
      Inr (D₂.stageToColimit H ⟨i, h₂⟩ x))
    (Hpush : CategoryTheory.IsPushout (CommRingCat.ofHom F.toRingHom)
      (CommRingCat.ofHom G.toRingHom) (CommRingCat.ofHom Inl.toRingHom)
      (CommRingCat.ofHom Inr.toRingHom)) :
    ∃ (j : ι) (hij : i ≤ j),
      CategoryTheory.IsPushout
        (CommRingCat.ofHom
          (D₀.mapAtLaterStage D₁ H h₀ h₁ hij f).toRingHom)
        (CommRingCat.ofHom
          (D₀.mapAtLaterStage D₂ H h₀ h₂ hij g).toRingHom)
        (CommRingCat.ofHom
          (D₁.mapAtLaterStage D₃ H h₁ h₃ hij inl).toRingHom)
        (CommRingCat.ofHom
          (D₂.mapAtLaterStage D₃ H h₂ h₃ hij inr).toRingHom) := by
  letI : Algebra (𝒮 i) A := (uA i).toRingHom.toAlgebra
  let C₀ := D₀.spreadStage (t := t) h₀
  let C₁ := D₁.spreadStage (t := t) h₁
  let C₂ := D₂.spreadStage (t := t) h₂
  let C₃ := D₃.spreadStage (t := t) h₃
  letI : Algebra C₀ C₁ := f.toRingHom.toAlgebra
  letI : Algebra C₀ C₂ := g.toRingHom.toAlgebra
  letI : IsScalarTower (𝒮 i) C₀ C₁ :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  letI : IsScalarTower (𝒮 i) C₀ C₂ :=
    IsScalarTower.of_algebraMap_eq' g.comp_algebraMap.symm
  have hcolim : Function.Bijective
      (Algebra.TensorProduct.map (AlgHom.id (𝒮 i) A)
        (pushoutMap f g inl inr h)) :=
    tensorProduct_map_pushoutMap_bijective f g inl inr h F G Inl Inr Hpush
      (D₀.baseChangeColimEquiv h₀ H) (D₁.baseChangeColimEquiv h₁ H)
      (D₂.baseChangeColimEquiv h₂ H) (D₃.baseChangeColimEquiv h₃ H)
      (D₀.baseChangeColimEquiv_map D₁ H h₀ h₁ f F hf)
      (D₀.baseChangeColimEquiv_map D₂ H h₀ h₂ g G hg)
      (D₁.baseChangeColimEquiv_map D₃ H h₁ h₃ inl Inl hinl)
      (D₂.baseChangeColimEquiv_map D₃ H h₂ h₃ inr Inr hinr)
  haveI : FinitePresentation (𝒮 i) C₀ := D₀.spreadStage_finitePresentation h₀
  haveI : FinitePresentation (𝒮 i) C₁ := D₁.spreadStage_finitePresentation h₁
  haveI : FinitePresentation (𝒮 i) C₂ := D₂.spreadStage_finitePresentation h₂
  haveI : FinitePresentation (𝒮 i) C₃ := D₃.spreadStage_finitePresentation h₃
  letI : FinitePresentation C₀ C₂ :=
    FinitePresentation.of_restrict_scalars_finitePresentation (𝒮 i) C₀ C₂
  let P := TensorProduct C₀ C₁ C₂
  letI : FinitePresentation C₁ P := inferInstance
  letI : FinitePresentation (𝒮 i) P := FinitePresentation.trans (𝒮 i) C₁ P
  obtain ⟨j, hij, hbij⟩ :=
    H.exists_tensorProductMap_bijective (pushoutMap f g inl inr h) hcolim
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  have hpushT := isPushout_tensorProduct_map_of_pushoutMap_bijective
    f g inl inr h hbij
  exact ⟨j, hij, D₀.isPushout_mapAtLaterStage_of_tensorProduct
    D₁ D₂ D₃ H h₀ h₁ h₂ h₃ hij f g inl inr hpushT⟩

/-- A pushout square of transported spread-stage maps remains a pushout after
every further transition in the filtered system. -/
theorem SpreadData.isPushout_mapAtLaterStage_trans
    {R : Type u} [CommRing R] {ι : Type u} [Preorder ι]
    {𝒮 : ι → Type u} [∀ i, CommRing (𝒮 i)] [∀ i, Algebra R (𝒮 i)]
    {t : ∀ ⦃i j : ι⦄, i ≤ j → (𝒮 i →ₐ[R] 𝒮 j)}
    {A : Type u} [CommRing A] [Algebra R A] {uA : ∀ i, 𝒮 i →ₐ[R] A}
    {B₀ B₁ B₂ B₃ : Type u}
    [CommRing B₀] [CommRing B₁] [CommRing B₂] [CommRing B₃]
    [Algebra A B₀] [Algebra A B₁] [Algebra A B₂] [Algebra A B₃]
    (D₀ : SpreadData 𝒮 uA B₀) (D₁ : SpreadData 𝒮 uA B₁)
    (D₂ : SpreadData 𝒮 uA B₂) (D₃ : SpreadData 𝒮 uA B₃)
    (H : IsFilteredAlgColimit R 𝒮 t A uA)
    {i j k : ι} (h₀ : D₀.i₀ ≤ i) (h₁ : D₁.i₀ ≤ i)
    (h₂ : D₂.i₀ ≤ i) (h₃ : D₃.i₀ ≤ i) (hij : i ≤ j) (hjk : j ≤ k)
    (f : D₀.spreadStage (t := t) h₀ →ₐ[𝒮 i]
      D₁.spreadStage (t := t) h₁)
    (g : D₀.spreadStage (t := t) h₀ →ₐ[𝒮 i]
      D₂.spreadStage (t := t) h₂)
    (inl : D₁.spreadStage (t := t) h₁ →ₐ[𝒮 i]
      D₃.spreadStage (t := t) h₃)
    (inr : D₂.spreadStage (t := t) h₂ →ₐ[𝒮 i]
      D₃.spreadStage (t := t) h₃)
    (hpush :
      letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
      CategoryTheory.IsPushout
        (CommRingCat.ofHom
          (D₀.mapAtLaterStage D₁ H h₀ h₁ hij f).toRingHom)
        (CommRingCat.ofHom
          (D₀.mapAtLaterStage D₂ H h₀ h₂ hij g).toRingHom)
        (CommRingCat.ofHom
          (D₁.mapAtLaterStage D₃ H h₁ h₃ hij inl).toRingHom)
        (CommRingCat.ofHom
          (D₂.mapAtLaterStage D₃ H h₂ h₃ hij inr).toRingHom)) :
    letI : Algebra (𝒮 i) (𝒮 k) := (t (hij.trans hjk)).toRingHom.toAlgebra
    CategoryTheory.IsPushout
      (CommRingCat.ofHom
        (D₀.mapAtLaterStage D₁ H h₀ h₁ (hij.trans hjk) f).toRingHom)
      (CommRingCat.ofHom
        (D₀.mapAtLaterStage D₂ H h₀ h₂ (hij.trans hjk) g).toRingHom)
      (CommRingCat.ofHom
        (D₁.mapAtLaterStage D₃ H h₁ h₃ (hij.trans hjk) inl).toRingHom)
      (CommRingCat.ofHom
        (D₂.mapAtLaterStage D₃ H h₂ h₃ (hij.trans hjk) inr).toRingHom) := by
  letI : Algebra (𝒮 i) (𝒮 j) := (t hij).toRingHom.toAlgebra
  letI : Algebra (𝒮 j) (𝒮 k) := (t hjk).toRingHom.toAlgebra
  letI : Algebra (𝒮 i) (𝒮 k) := (t (hij.trans hjk)).toRingHom.toAlgebra
  let f_j := D₀.mapAtLaterStage D₁ H h₀ h₁ hij f
  let g_j := D₀.mapAtLaterStage D₂ H h₀ h₂ hij g
  let inl_j := D₁.mapAtLaterStage D₃ H h₁ h₃ hij inl
  let inr_j := D₂.mapAtLaterStage D₃ H h₂ h₃ hij inr
  have hpushT := isPushout_tensorProduct_map
    (S := 𝒮 j) (T := 𝒮 k)
    (C₀ := D₀.spreadStage (t := t) (h₀.trans hij))
    (C₁ := D₁.spreadStage (t := t) (h₁.trans hij))
    (C₂ := D₂.spreadStage (t := t) (h₂.trans hij))
    (C₃ := D₃.spreadStage (t := t) (h₃.trans hij))
    f_j g_j inl_j inr_j hpush
  have hpushK := D₀.isPushout_mapAtLaterStage_of_tensorProduct D₁ D₂ D₃ H
    (h₀.trans hij) (h₁.trans hij) (h₂.trans hij) (h₃.trans hij) hjk
      f_j g_j inl_j inr_j hpushT
  simpa only [f_j, g_j, inl_j, inr_j,
    D₀.mapAtLaterStage_trans D₁ H h₀ h₁ hij hjk f,
    D₀.mapAtLaterStage_trans D₂ H h₀ h₂ hij hjk g,
    D₁.mapAtLaterStage_trans D₃ H h₁ h₃ hij hjk inl,
    D₂.mapAtLaterStage_trans D₃ H h₂ h₃ hij hjk inr] using hpushK

end Algebra
