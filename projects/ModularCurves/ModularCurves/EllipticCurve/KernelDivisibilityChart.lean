/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.TorsionUnramifiedFibre
import ModularCurves.EllipticCurve.MulByHomFlat

/-!
# Kernel divisibility, chart-locally (BB-FLAT route (G), the core)

The square-zero point-kernel calculus over an **arbitrary affine base**: the
`TorsionUnramifiedFibre` co-multiplication layer transplanted off the field base (its
private algebra/box layer is base-generic; the field entered only the stalk/units dance,
replaced here by the `y₀`-separation and `pairLift_key`). Deliverables:

* `pointSharp_add_of_kernel` — additivity of chart comorphisms on square-zero kernel
  points (the (ADD) step of board v10.147);
* `exists_div_of_kernel` / `smul_kernel_injective` — `N`-divisibility and
  `N`-injectivity of the kernel, chart-locally (CHART-DIV).

The gluing to arbitrary tests and the consumption into `Flat [N]` live downstream
(`MulByHomFlat.lean` chain).
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
  MonObj TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

noncomputable section

namespace ModularCurves

namespace EllipticCurve

section AugmentationAlgebra

variable {k' C R : Type u} [CommRing k'] [CommRing C] [CommRing R]
  [Algebra k' C] [Algebra k' R]

/-- The left axis restriction `C ⊗ C → C`, `c ⊗ c' ↦ ε(c)·c'`. -/
private noncomputable def axisL (ε : C →ₐ[k'] k') : C ⊗[k'] C →ₐ[k'] C :=
  Algebra.TensorProduct.lift ((Algebra.ofId k' C).comp ε) (AlgHom.id k' C)
    fun _ _ => Commute.all _ _

/-- The right axis restriction `C ⊗ C → C`, `c ⊗ c' ↦ c·ε(c')`. -/
private noncomputable def axisR (ε : C →ₐ[k'] k') : C ⊗[k'] C →ₐ[k'] C :=
  Algebra.TensorProduct.lift (AlgHom.id k' C) ((Algebra.ofId k' C).comp ε)
    fun _ _ => Commute.all _ _

/-- The double augmentation `C ⊗ C → k'`. -/
private noncomputable def foldε (ε : C →ₐ[k'] k') : C ⊗[k'] C →ₐ[k'] k' :=
  Algebra.TensorProduct.lift ε ε fun _ _ => Commute.all _ _

@[simp] private lemma axisL_tmul (ε : C →ₐ[k'] k') (c c' : C) :
    axisL ε (c ⊗ₜ c') = algebraMap k' C (ε c) * c' := by
  simp [axisL, Algebra.ofId_apply]

@[simp] private lemma axisR_tmul (ε : C →ₐ[k'] k') (c c' : C) :
    axisR ε (c ⊗ₜ c') = c * algebraMap k' C (ε c') := by
  simp [axisR, Algebra.ofId_apply]

@[simp] private lemma foldε_tmul (ε : C →ₐ[k'] k') (c c' : C) :
    foldε ε (c ⊗ₜ c') = ε c * ε c' := by
  simp [foldε]

/-- **The key identity**: modulo `I·I = 0`, a tensor-lift of two `I`-close-to-augmentation
maps is determined by the two axis restrictions and the double augmentation. -/
private theorem pairLift_key (ε : C →ₐ[k'] k') (p₁ p₂ : C →ₐ[k'] R) {I : Ideal R}
    (h₁ : ∀ c, p₁ c - algebraMap k' R (ε c) ∈ I)
    (h₂ : ∀ c, p₂ c - algebraMap k' R (ε c) ∈ I)
    (hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0)
    (x : C ⊗[k'] C) :
    Algebra.TensorProduct.lift p₁ p₂ (fun _ _ => Commute.all _ _) x =
      p₂ (axisL ε x) + p₁ (axisR ε x) - algebraMap k' R (foldε ε x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c c' =>
      have hz : (p₁ c - algebraMap k' R (ε c)) * (p₂ c' - algebraMap k' R (ε c')) = 0 :=
        hII _ (h₁ c) _ (h₂ c')
      simp only [Algebra.TensorProduct.lift_tmul, axisL_tmul, axisR_tmul, foldε_tmul,
        map_mul, AlgHom.commutes]
      ring_nf
      ring_nf at hz
      linear_combination hz
  | add x y hx hy => simp only [map_add, hx, hy]; ring

/-- The double augmentation factors through the left axis. -/
private theorem foldε_eq_axisL (ε : C →ₐ[k'] k') (x : C ⊗[k'] C) :
    foldε ε x = ε (axisL ε x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c c' => simp [mul_comm]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Ring maps out of a tensor product agree if they agree on both inclusions. -/
private theorem tensor_ringHom_ext {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    [Algebra k' A] [Algebra k' B] {u v : A ⊗[k'] B →+* T}
    (hL : ∀ a, u (a ⊗ₜ 1) = v (a ⊗ₜ 1)) (hR : ∀ b, u (1 ⊗ₜ b) = v (1 ⊗ₜ b)) : u = v := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
      have h : (a ⊗ₜ[k'] b : A ⊗[k'] B) = (a ⊗ₜ 1) * (1 ⊗ₜ b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
      rw [h, map_mul, map_mul, hL, hR]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The double augmentation factors through the right axis. -/
private theorem foldε_eq_axisR (ε : C →ₐ[k'] k') (x : C ⊗[k'] C) :
    foldε ε x = ε (axisR ε x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c c' => simp
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The final kill: if both axis restrictions of `x` vanish, so does the pair-lift. -/
private theorem pairLift_eq_zero_of_axes (ε : C →ₐ[k'] k') (p₁ p₂ : C →ₐ[k'] R) {I : Ideal R}
    (h₁ : ∀ c, p₁ c - algebraMap k' R (ε c) ∈ I)
    (h₂ : ∀ c, p₂ c - algebraMap k' R (ε c) ∈ I)
    (hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0)
    {x : C ⊗[k'] C} (hx₁ : axisL ε x = 0) (hx₂ : axisR ε x = 0) :
    Algebra.TensorProduct.lift p₁ p₂ (fun _ _ => Commute.all _ _) x = 0 := by
  have hfold : foldε ε x = 0 := by rw [foldε_eq_axisL, hx₁, map_zero]
  rw [pairLift_key ε p₁ p₂ h₁ h₂ hII, hx₁, hx₂, hfold, map_zero, map_zero, map_zero]
  ring

end AugmentationAlgebra

section AugmentationScheme

variable {B : CommRingCat.{u}} {F : EllipticCurve (Spec B)}
  {R S' : CommRingCat.{u}} {φ : R ⟶ S'}

/-- `Spec` of a surjection with nilpotent kernel is surjective on points. -/
private theorem specMap_base_surjective (hφ : Function.Surjective φ.hom)
    (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥) :
    Function.Surjective (Spec.map φ).base := by
  intro p
  have hker : RingHom.ker φ.hom ≤ p.asIdeal := by
    intro x hx
    have hx2 : x ^ 2 = 0 := by
      have : x ^ 2 ∈ RingHom.ker φ.hom ^ 2 := by
        rw [sq, sq]
        exact Ideal.mul_mem_mul hx hx
      simpa [hφ2] using this
    exact p.isPrime.mem_of_pow_mem 2 (hx2 ▸ p.asIdeal.zero_mem)
  have hp : p ∈ Set.range (PrimeSpectrum.comap φ.hom) := by
    rw [range_comap_of_surjective _ _ hφ]
    exact hker
  obtain ⟨q, hq⟩ := hp
  exact ⟨q, hq⟩

/-- Every kernel-of-reduction point lands topologically in the zero point's chart. -/
private theorem range_base_subset_of_reduction {U : (F.E).Opens}
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec B} {w : Spec R ⟶ F.E}
    (hred : Spec.map φ ≫ w = Spec.map φ ≫ (t ≫ F.zero)) :
    ∀ x : ↑(Spec R), w.base x ∈ U := by
  intro x
  obtain ⟨y, rfl⟩ := specMap_base_surjective hφ hφ2 x
  have h1 : w.base ((Spec.map φ).base y) = (Spec.map φ ≫ w).base y := rfl
  rw [h1, hred]
  exact heU _

/-- The chart comorphism of a morphism `Spec R ⟶ E` landing in `U`, as a map into `R`. -/
private noncomputable def pointSharp {U : (F.E).Opens} (w : Spec R ⟶ F.E)
    (hw : ∀ x : ↑(Spec R), w.base x ∈ U) : Γ(F.E, U) ⟶ R :=
  w.appLE U ⊤ (fun x _ => hw x) ≫ (Scheme.ΓSpecIso R).hom

/-- Morphisms into `E` landing in the affine chart are determined by their chart
comorphism (`IsAffineOpen.SpecMap_appLE_fromSpec` recovery). -/
private theorem eq_of_pointSharp_eq {U : (F.E).Opens} (hU : IsAffineOpen U)
    {w w' : Spec R ⟶ F.E} (hw : ∀ x : ↑(Spec R), w.base x ∈ U)
    (hw' : ∀ x : ↑(Spec R), w'.base x ∈ U)
    (h : pointSharp w hw = pointSharp w' hw') : w = w' := by
  have happ : w.appLE U ⊤ (fun x _ => hw x) = w'.appLE U ⊤ (fun x _ => hw' x) := by
    have := congrArg (· ≫ (Scheme.ΓSpecIso R).inv) h
    simpa [pointSharp] using this
  have h1 := hU.SpecMap_appLE_fromSpec w (isAffineOpen_top (Spec R)) (fun x _ => hw x)
  have h2 := hU.SpecMap_appLE_fromSpec w' (isAffineOpen_top (Spec R)) (fun x _ => hw' x)
  rw [happ] at h1
  rw [IsAffineOpen.fromSpec_top] at h1 h2
  have h3 := h1.symm.trans h2
  exact (cancel_epi (Spec R).isoSpec.inv).mp h3



/-! #### The chunk-(i) scheme identities for `pointSharp_add`

`pointSharp_add`'s proof (the stalk design): the pairing of `P₁ P₂` factors through the
affine Künneth box `κ : pullback (π.resLE) (π.resLE) ≅ Spec (C ⊗ C)` as
`Spec.map pairTensor`; the sum's comorphism is then computed at the stalk of `C ⊗ C` at the
double augmentation prime, where the two axis laws — the `Γ`-shadows of `0 + X = X` and
`X + 0 = X` for the tautological chart point — force the `μ`-comorphism of an augmentation
element into the kernels of both axis stalk maps; the `(1 ⊗ u)(v ⊗ 1)`-cleared numerator then
dies under `pairTensor` by `pairLift_eq_zero_of_axes`, and units transport the vanishing to
`R`. -/

/-- The `Spec`-shadow of the zero section through the chart. -/
private theorem specMap_zero_appLE_fromSpec {U : (F.E).Opens} (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U) :
    Spec.map (F.zero.appLE U ⊤ (fun x _ => heU x)) ≫ hU.fromSpec =
      (isAffineOpen_top (Spec B)).fromSpec ≫ F.zero :=
  hU.SpecMap_appLE_fromSpec F.zero (isAffineOpen_top _) _

/-- The `Spec`-shadow of the structure morphism through the chart. -/
private theorem specMap_π_appLE_fromSpec {U : (F.E).Opens} (hU : IsAffineOpen U) :
    Spec.map (F.π.appLE ⊤ U (fun _ _ => trivial)) ≫
      (isAffineOpen_top (Spec B)).fromSpec = hU.fromSpec ≫ F.π :=
  (isAffineOpen_top _).SpecMap_appLE_fromSpec F.π hU _

/-- The tautological point of the chart: `fromSpec` as a point of `E` over its own
`π`-composite. -/
private noncomputable def tautPoint {U : (F.E).Opens} (hU : IsAffineOpen U) :
    F.Point (hU.fromSpec ≫ F.π) :=
  ⟨hU.fromSpec, rfl⟩

/-- **The left axis law** (the value shadow of `0 + X = X`): pairing the zero point with the
tautological point and multiplying is `fromSpec`. -/
private theorem zero_pairing_mul {U : (F.E).Opens} (hU : IsAffineOpen U) :
    (lift (F.pointEquivOverHom _ (0 : F.Point (hU.fromSpec ≫ F.π)))
        (F.pointEquivOverHom _ (tautPoint hU))).left ≫ (μ[F.asOver]).left =
      hU.fromSpec := by
  have h := point_add_val_mu F ((0 : F.Point (hU.fromSpec ≫ F.π))) (tautPoint hU)
  rw [zero_add] at h
  exact h.symm

/-- **The right axis law** (the value shadow of `X + 0 = X`). -/
private theorem pairing_zero_mul {U : (F.E).Opens} (hU : IsAffineOpen U) :
    (lift (F.pointEquivOverHom _ (tautPoint hU))
        (F.pointEquivOverHom _ (0 : F.Point (hU.fromSpec ≫ F.π)))).left ≫
      (μ[F.asOver]).left = hU.fromSpec := by
  have h := point_add_val_mu F (tautPoint hU) ((0 : F.Point (hU.fromSpec ≫ F.π)))
  rw [add_zero] at h
  exact h.symm

/-- `pointSharp` only depends on the morphism. -/
private theorem pointSharp_congr {U : (F.E).Opens} {w w' : Spec R ⟶ F.E} (h : w = w')
    (hw : ∀ x : ↑(Spec R), w.base x ∈ U) (hw' : ∀ x : ↑(Spec R), w'.base x ∈ U) :
    pointSharp w hw = pointSharp w' hw' := by
  subst h; rfl

/-- Evaluation of the zero point: the chart comorphism of `t ≫ zero` is the augmentation
followed by the structure map of `R`. -/
private theorem pointSharp_zero_point {U : (F.E).Opens}
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U) (t : Spec R ⟶ Spec B)
    (hz : ∀ x : ↑(Spec R), ((0 : F.Point t) : Spec R ⟶ F.E).base x ∈ U)
    (f : Γ(F.E, U)) :
    pointSharp ((0 : F.Point t) : Spec R ⟶ F.E) hz f =
      (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)
        (F.zero.appLE U ⊤ (fun x _ => heU x) f) := by
  have hz' : ∀ x : ↑(Spec R), (t ≫ F.zero).base x ∈ U := by
    intro x
    simpa using heU (t.base x)
  rw [pointSharp_congr (F.point_zero_val t) hz hz']
  show ((t ≫ F.zero).appLE U ⊤ _ ≫ (Scheme.ΓSpecIso R).hom) f = _
  rw [← Scheme.Hom.appLE_comp_appLE t F.zero U ⊤ ⊤ (fun x _ => heU x) le_top]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The chart comorphism of a point over `t` restricts along `π` to the `t`-comorphism. -/
private theorem pointSharp_comp_π {U : (F.E).Opens} {t : Spec R ⟶ Spec B} (P : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (c : Γ(Spec B, ⊤)) :
    pointSharp P.1 hp (F.π.appLE ⊤ U (fun _ _ => trivial) c) =
      (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom) c := by
  show ((F.π.appLE ⊤ U _ ≫ P.1.appLE U ⊤ _) ≫ (Scheme.ΓSpecIso R).hom) c = _
  rw [Scheme.Hom.appLE_comp_appLE P.1 F.π ⊤ U ⊤ _ _,
    appLE_congr_hom P.2 ⊤ ⊤]

set_option backward.isDefEq.respectTransparency.types false in
/-- The augmentation retracts the structure map: `ζ ∘ π♯ = id` (`Γ`-dual of `zero ≫ π = 𝟙`). -/
private theorem zero_appLE_π_appLE {U : (F.E).Opens}
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U) (c : Γ(Spec B, ⊤)) :
    F.zero.appLE U ⊤ (fun x _ => heU x) (F.π.appLE ⊤ U (fun _ _ => trivial) c) = c := by
  show (F.π.appLE ⊤ U _ ≫ F.zero.appLE U ⊤ _) c = c
  rw [Scheme.Hom.appLE_comp_appLE F.zero F.π ⊤ U ⊤ _ _,
    appLE_congr_hom F.zero_π ⊤ ⊤,
    appLE_id]
  rfl


section Box

variable {U : (F.E).Opens}

/-- The chart's `k'`-algebra structure via the structure morphism. -/
private noncomputable local instance chartAlgebra :
    Algebra ↑Γ(Spec B, ⊤) ↑Γ(F.E, U) :=
  (F.π.appLE ⊤ U (fun _ _ => trivial)).hom.toAlgebra

private theorem chartAlgebra_ofHom :
    CommRingCat.ofHom (algebraMap ↑Γ(Spec B, ⊤) ↑Γ(F.E, U)) =
      F.π.appLE ⊤ U (fun _ _ => trivial) := rfl

/-- The affine Künneth box of the chart (`patchKunneth`, consumed from NEW-HOPF's
`PatchKunneth.lean`). -/
private noncomputable def boxIso (hU : IsAffineOpen U) :
    pullback (F.π.resLE ⊤ U (fun _ _ => trivial)) (F.π.resLE ⊤ U (fun _ _ => trivial)) ≅
      Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U))) :=
  patchKunneth F.π F.π (isAffineOpen_top _) hU hU chartAlgebra_ofHom chartAlgebra_ofHom

/-- The box sits inside the fibre square of `E`. -/
private noncomputable def boxι :
    (pullback (F.π.resLE ⊤ U (fun _ _ => trivial))
      (F.π.resLE ⊤ U (fun _ _ => trivial)) : Scheme) ⟶ pullback F.π F.π :=
  pullback.map _ _ _ _ U.ι U.ι (⊤ : (Spec B).Opens).ι
    (Scheme.Hom.resLE_comp_ι _ _) (Scheme.Hom.resLE_comp_ι _ _)

/-- Factorisation of a chart-supported morphism through the open. -/
private noncomputable def liftU {w : Spec R ⟶ F.E} (hw : ∀ x : ↑(Spec R), w.base x ∈ U) :
    Spec R ⟶ ↑U :=
  IsOpenImmersion.lift U.ι w (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hw x)

private theorem liftU_ι {w : Spec R ⟶ F.E} (hw : ∀ x : ↑(Spec R), w.base x ∈ U) :
    liftU hw ≫ U.ι = w :=
  IsOpenImmersion.lift_fac _ _ _

/-- **The chart correspondence**: the open factorisation composed with the affine
identification is `Spec` of the chart comorphism. -/
private theorem liftU_toSpecΓ (hU : IsAffineOpen U) {w : Spec R ⟶ F.E}
    (hw : ∀ x : ↑(Spec R), w.base x ∈ U) :
    liftU hw ≫ U.toSpecΓ = Spec.map (pointSharp w hw) := by
  have h0 := hU.SpecMap_appLE_fromSpec w (isAffineOpen_top (Spec R)) (fun x _ => hw x)
  rw [IsAffineOpen.fromSpec_top] at h0
  have hfromSpec : hU.fromSpec = hU.isoSpec.inv ≫ U.ι := rfl
  have hw' : (Spec R).isoSpec.hom ≫ Spec.map (w.appLE U ⊤ (fun x _ => hw x)) ≫
      hU.fromSpec = w := by
    rw [h0, Iso.hom_inv_id_assoc]
  have hlift : liftU hw = (Spec R).isoSpec.hom ≫
      Spec.map (w.appLE U ⊤ (fun x _ => hw x)) ≫ hU.isoSpec.inv := by
    rw [← cancel_mono U.ι, liftU_ι hw]
    rw [show ((Spec R).isoSpec.hom ≫ Spec.map (w.appLE U ⊤ (fun x _ => hw x)) ≫
        hU.isoSpec.inv) ≫ U.ι = (Spec R).isoSpec.hom ≫
        Spec.map (w.appLE U ⊤ (fun x _ => hw x)) ≫ hU.fromSpec from by
      rw [hfromSpec]; simp only [Category.assoc]]
    exact hw'.symm
  rw [hlift, ← hU.isoSpec_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The pairing of two points through the box. -/
private noncomputable def pairBox {t : Spec R ⟶ Spec B} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    Spec R ⟶ pullback (F.π.resLE ⊤ U (fun _ _ => trivial))
      (F.π.resLE ⊤ U (fun _ _ => trivial)) :=
  pullback.lift (liftU hp) (liftU hq) (by
    rw [← cancel_mono (⊤ : (Spec B).Opens).ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc, ← Category.assoc, liftU_ι, liftU_ι, P.2, Q.2])

private theorem pairBox_fst {t : Spec R ⟶ Spec B} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    pairBox P Q hp hq ≫ pullback.fst _ _ = liftU hp :=
  pullback.lift_fst _ _ _

private theorem pairBox_snd {t : Spec R ⟶ Spec B} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    pairBox P Q hp hq ≫ pullback.snd _ _ = liftU hq :=
  pullback.lift_snd _ _ _

/-- The pairing of `Hom.commGroup` is the box pairing followed by the box inclusion. -/
private theorem pairing_eq_pairBox {t : Spec R ⟶ Spec B} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    (lift (F.pointEquivOverHom t P) (F.pointEquivOverHom t Q)).left =
      pairBox P Q hp hq ≫ boxι := by
  refine pullback.hom_ext (f := F.π) (g := F.π) ?_ ?_
  · have hR : (pairBox P Q hp hq ≫ boxι) ≫ pullback.fst F.π F.π = P.1 := by
      rw [Category.assoc,
        show boxι (U := U) ≫ pullback.fst F.π F.π = pullback.fst _ _ ≫ U.ι from
          pullback.lift_fst _ _ _,
        ← Category.assoc, pairBox_fst, liftU_ι]
    exact (point_pair_left_fst F P Q).trans hR.symm
  · have hR : (pairBox P Q hp hq ≫ boxι) ≫ pullback.snd F.π F.π = Q.1 := by
      rw [Category.assoc,
        show boxι (U := U) ≫ pullback.snd F.π F.π = pullback.snd _ _ ≫ U.ι from
          pullback.lift_snd _ _ _,
        ← Category.assoc, pairBox_snd, liftU_ι]
    exact (point_pair_left_snd F P Q).trans hR.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- The left leg of the Künneth identification of the pairing. -/
private theorem pairBox_boxIso_includeLeft (hU : IsAffineOpen U)
    {t : Spec R ⟶ Spec B} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    pairBox P Q hp hq ≫ (boxIso hU).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := ↑Γ(Spec B, ⊤)) (A := ↑Γ(F.E, U)) (B := ↑Γ(F.E, U)))) =
      Spec.map (pointSharp P.1 hp) := by
  rw [boxIso, patchKunneth_hom_comp_includeLeft, ← Category.assoc, pairBox_fst,
    liftU_toSpecΓ hU]

set_option backward.isDefEq.respectTransparency.types false in
/-- The right leg of the Künneth identification of the pairing. -/
private theorem pairBox_boxIso_includeRight (hU : IsAffineOpen U)
    {t : Spec R ⟶ Spec B} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    pairBox P Q hp hq ≫ (boxIso hU).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := ↑Γ(Spec B, ⊤)) (A := ↑Γ(F.E, U))
          (B := ↑Γ(F.E, U))).toRingHom) =
      Spec.map (pointSharp Q.1 hq) := by
  rw [boxIso, patchKunneth_hom_comp_includeRight, ← Category.assoc, pairBox_snd,
    liftU_toSpecΓ hU]

set_option backward.isDefEq.respectTransparency.types false in
/-- **(TAUT-SHARP)** The chart comorphism of `fromSpec` is the identity. -/
private theorem pointSharp_fromSpec (hU : IsAffineOpen U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U) :
    pointSharp (R := Γ(F.E, U)) hU.fromSpec htaut = 𝟙 Γ(F.E, U) := by
  show hU.fromSpec.appLE U ⊤ _ ≫ (Scheme.ΓSpecIso Γ(F.E, U)).hom = 𝟙 _
  have hdef : hU.fromSpec = hU.isoSpec.inv ≫ U.ι := rfl
  rw [appLE_congr_hom hdef U ⊤,
    ← Scheme.Hom.appLE_comp_appLE hU.isoSpec.inv U.ι U ⊤ ⊤
      U.ι_preimage_self.ge le_top,
    ι_appLE_top,
    appLE_top_top]
  have h1 : hU.isoSpec.inv.appTop ≫ hU.isoSpec.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  have h2 : hU.isoSpec.hom.appTop =
      (Scheme.ΓSpecIso Γ(F.E, U)).hom ≫ U.topIso.inv := by
    rw [hU.isoSpec_hom, Scheme.Opens.toSpecΓ_appTop]
  rw [h2] at h1
  have h3 : hU.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(F.E, U)).hom = U.topIso.hom := by
    have h4 := congrArg (· ≫ U.topIso.hom) h1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp] at h4
    exact h4
  rw [Category.assoc, h3, Iso.inv_hom_id]

/-- **(TAUT-ZERO)** The chart comorphism of the zero point over the tautological base is the
structure map composed with the augmentation. -/
private theorem pointSharp_zero_taut (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    (hz : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U) :
    pointSharp (R := Γ(F.E, U)) ((0 : F.Point (hU.fromSpec ≫ F.π)) : _ ⟶ F.E) hz =
      F.zero.appLE U ⊤ (fun x _ => heU x) ≫ F.π.appLE ⊤ U (fun _ _ => trivial) := by
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  have h0 := pointSharp_zero_point (R := Γ(F.E, U)) heU (hU.fromSpec ≫ F.π) hz c
  rw [h0]
  show ((hU.fromSpec ≫ F.π).appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso Γ(F.E, U)).hom)
      (F.zero.appLE U ⊤ (fun x _ => heU x) c) = _
  rw [← Scheme.Hom.appLE_comp_appLE hU.fromSpec F.π ⊤ U ⊤ (fun _ _ => trivial)
    (fun x _ => htaut x)]
  show (pointSharp (R := Γ(F.E, U)) hU.fromSpec htaut)
      ((F.π.appLE ⊤ U (fun _ _ => trivial)) (F.zero.appLE U ⊤ (fun x _ => heU x) c)) = _
  rw [pointSharp_fromSpec hU htaut]
  rfl

/-- The Künneth identification of the pairing, map form (instance-free statement: the
target ring map is characterised by its two inclusion legs). -/
private theorem pairBox_boxIso_eq_specMap (hU : IsAffineOpen U)
    {t : Spec R ⟶ Spec B} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U)
    {pT : CommRingCat.of (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) ⟶ R}
    (hL : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ↑Γ(Spec B, ⊤))) ≫ pT = pointSharp P.1 hp)
    (hR : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := ↑Γ(Spec B, ⊤)) (A := ↑Γ(F.E, U))).toRingHom ≫ pT =
      pointSharp Q.1 hq) :
    pairBox P Q hp hq ≫ (boxIso hU).hom = Spec.map pT := by
  have hu : pairBox P Q hp hq ≫ (boxIso hU).hom =
      Spec.map (Spec.preimage (pairBox P Q hp hq ≫ (boxIso hU).hom)) :=
    (Spec.map_preimage _).symm
  rw [hu]
  refine congrArg Spec.map ?_
  have hLu : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := ↑Γ(Spec B, ⊤))) ≫
        Spec.preimage (pairBox P Q hp hq ≫ (boxIso hU).hom) = pointSharp P.1 hp := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, Spec.map_preimage, ← pairBox_boxIso_includeLeft hU P Q hp hq,
      Category.assoc]
  have hRu : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
      (R := ↑Γ(Spec B, ⊤)) (A := ↑Γ(F.E, U))).toRingHom ≫
        Spec.preimage (pairBox P Q hp hq ≫ (boxIso hU).hom) = pointSharp Q.1 hq := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, Spec.map_preimage, ← pairBox_boxIso_includeRight hU P Q hp hq,
      Category.assoc]
  refine CommRingCat.hom_ext (tensor_ringHom_ext (fun a => ?_) (fun b => ?_))
  · have h1 := congrArg (fun (m : _ ⟶ R) => m.hom a) (hLu.trans hL.symm)
    exact h1
  · have h1 := congrArg (fun (m : _ ⟶ R) => m.hom b) (hRu.trans hR.symm)
    exact h1

/-- The augmentation of the chart, as an algebra map over the base sections. -/
private noncomputable def chartAug
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U) :
    ↑Γ(F.E, U) →ₐ[↑Γ(Spec B, ⊤)] ↑Γ(Spec B, ⊤) :=
  { toRingHom := (F.zero.appLE U ⊤ (fun x _ => heU x)).hom
    commutes' := fun c => zero_appLE_π_appLE heU c }

set_option backward.isDefEq.respectTransparency.types false in
/-- **The left axis law, `Spec` form**: `Spec` of the left axis restriction, through the
Künneth box and the multiplication, is the tautological chart inclusion (the geometric
content of `0 + X = X`). -/
private theorem axisL_spec_law (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    (hz : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U) :
    Spec.map (CommRingCat.ofHom (axisL (chartAug heU)).toRingHom) ≫ (boxIso hU).inv ≫
        boxι ≫ (μ[F.asOver]).left = hU.fromSpec := by
  have hident : pairBox (0 : F.Point (hU.fromSpec ≫ F.π)) (tautPoint hU) hz htaut ≫
      (boxIso hU).hom = Spec.map (CommRingCat.ofHom (axisL (chartAug heU)).toRingHom) := by
    refine pairBox_boxIso_eq_specMap hU _ _ hz htaut ?_ ?_
    · rw [pointSharp_zero_taut hU heU htaut hz]
      refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      show axisL (chartAug heU) (c ⊗ₜ 1) = _
      rw [axisL_tmul, _root_.mul_one]
      rfl
    · rw [pointSharp_congr (show ((tautPoint hU : F.Point (hU.fromSpec ≫ F.π)) :
          Spec Γ(F.E, U) ⟶ F.E) = hU.fromSpec from rfl) htaut htaut,
        pointSharp_fromSpec hU htaut]
      refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      show axisL (chartAug heU) (1 ⊗ₜ c) = c
      rw [axisL_tmul, map_one, map_one, _root_.one_mul]
  rw [← hident]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← pairing_eq_pairBox]
  exact zero_pairing_mul hU

set_option backward.isDefEq.respectTransparency.types false in
/-- **The right axis law, `Spec` form** (the geometric content of `X + 0 = X`). -/
private theorem axisR_spec_law (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    (hz : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U) :
    Spec.map (CommRingCat.ofHom (axisR (chartAug heU)).toRingHom) ≫ (boxIso hU).inv ≫
        boxι ≫ (μ[F.asOver]).left = hU.fromSpec := by
  have hident : pairBox (tautPoint hU) (0 : F.Point (hU.fromSpec ≫ F.π)) htaut hz ≫
      (boxIso hU).hom = Spec.map (CommRingCat.ofHom (axisR (chartAug heU)).toRingHom) := by
    refine pairBox_boxIso_eq_specMap hU _ _ htaut hz ?_ ?_
    · rw [pointSharp_congr (show ((tautPoint hU : F.Point (hU.fromSpec ≫ F.π)) :
          Spec Γ(F.E, U) ⟶ F.E) = hU.fromSpec from rfl) htaut htaut,
        pointSharp_fromSpec hU htaut]
      refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      show axisR (chartAug heU) (c ⊗ₜ 1) = c
      rw [axisR_tmul, map_one, map_one, _root_.mul_one]
    · rw [pointSharp_zero_taut hU heU htaut hz]
      refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      show axisR (chartAug heU) (1 ⊗ₜ c) = _
      rw [axisR_tmul, _root_.one_mul]
      rfl
  rw [← hident]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← pairing_eq_pairBox]
  exact pairing_zero_mul hU

set_option backward.isDefEq.respectTransparency.types false in
/-- Chart evaluation of a `Spec`-precomposition: `(Spec.map g ≫ v)♯ = v♯ ≫ g`. -/
private theorem pointSharp_specMap_comp {R' R'' : CommRingCat.{u}} (g : R'' ⟶ R')
    {v : Spec R'' ⟶ F.E} (hv : ∀ x : ↑(Spec R''), v.base x ∈ U)
    (hcomp : ∀ x : ↑(Spec R'), (Spec.map g ≫ v).base x ∈ U) :
    pointSharp (Spec.map g ≫ v) hcomp = pointSharp v hv ≫ g := by
  have hnat : pointSharp v hv ≫ g = (Spec.map g ≫ v).appLE U ⊤
      (fun x _ => hcomp x) ≫ (Scheme.ΓSpecIso R').hom := by
    rw [pointSharp, Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← appLE_top_top (Spec.map g),
      Scheme.Hom.appLE_comp_appLE]
  rw [hnat]
  rfl


/-! ### The separating section `y₀` and the localized evaluation -/

/-- The chart-valued composite of the box: `Spec (C ⊗ C) → E`. -/
private noncomputable def boxMul (hU : IsAffineOpen U) :
    Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U))) ⟶ F.E :=
  (boxIso hU).inv ≫ boxι ≫ (μ[F.asOver]).left

set_option backward.isDefEq.respectTransparency.types false in
/-- **The separating section**: a tensor `y₀` with both axis values `1` whose basic open
maps into the chart under the box multiplication. Comaximality of the vanishing ideal of
the non-chart locus with the two axis kernels (the axis laws land the axis primes inside
the chart). -/
private theorem exists_sep (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    (hz : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U) :
    ∃ y₀ : ↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U),
      axisL (chartAug heU) y₀ = 1 ∧ axisR (chartAug heU) y₀ = 1 ∧
      ∀ x : ↑(Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)))),
        y₀ ∉ x.asIdeal → (boxMul hU).base x ∈ U := by
  classical
  -- the non-chart locus is closed; take a vanishing ideal
  have hopen : IsOpen ((boxMul hU).base ⁻¹' (U : Set F.E)) :=
    U.2.preimage (boxMul hU).continuous
  obtain ⟨I₀, hI₀⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp
    hopen.isClosed_compl
  -- the two axis kernels
  set JL := RingHom.ker (axisL (chartAug heU)).toRingHom with hJL
  set JR := RingHom.ker (axisR (chartAug heU)).toRingHom with hJR
  -- axis primes are chart primes
  have haxL : ∀ p, JL ≤ p.asIdeal → (boxMul hU).base p ∈ U := by
    intro p hp
    have hsurj : Function.Surjective (axisL (chartAug heU)).toRingHom := fun c =>
      ⟨1 ⊗ₜ c, by simp⟩
    have hrange : p ∈ Set.range (PrimeSpectrum.comap (axisL (chartAug heU)).toRingHom) := by
      rw [range_comap_of_surjective _ _ hsurj]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr hp
    obtain ⟨p', hp'⟩ := hrange
    have h1 : (Spec.map (CommRingCat.ofHom (axisL (chartAug heU)).toRingHom) ≫
        boxMul hU).base p' = (hU.fromSpec).base p' :=
      congrArg (fun m : Spec Γ(F.E, U) ⟶ F.E => m.base p')
        (show Spec.map (CommRingCat.ofHom (axisL (chartAug heU)).toRingHom) ≫
          boxMul hU = hU.fromSpec from axisL_spec_law hU heU htaut hz)
    rw [Scheme.Hom.comp_apply] at h1
    have hbase : (Spec.map (CommRingCat.ofHom (axisL (chartAug heU)).toRingHom)).base p' =
        p := hp'
    rw [hbase] at h1
    rw [h1]
    have hr := IsAffineOpen.range_fromSpec hU
    have : (hU.fromSpec).base p' ∈ Set.range (hU.fromSpec).base := Set.mem_range_self p'
    rwa [hr] at this
  have haxR : ∀ p, JR ≤ p.asIdeal → (boxMul hU).base p ∈ U := by
    intro p hp
    have hsurj : Function.Surjective (axisR (chartAug heU)).toRingHom := fun c =>
      ⟨c ⊗ₜ 1, by simp⟩
    have hrange : p ∈ Set.range (PrimeSpectrum.comap (axisR (chartAug heU)).toRingHom) := by
      rw [range_comap_of_surjective _ _ hsurj]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr hp
    obtain ⟨p', hp'⟩ := hrange
    have h1 : (Spec.map (CommRingCat.ofHom (axisR (chartAug heU)).toRingHom) ≫
        boxMul hU).base p' = (hU.fromSpec).base p' :=
      congrArg (fun m : Spec Γ(F.E, U) ⟶ F.E => m.base p')
        (show Spec.map (CommRingCat.ofHom (axisR (chartAug heU)).toRingHom) ≫
          boxMul hU = hU.fromSpec from axisR_spec_law hU heU htaut hz)
    rw [Scheme.Hom.comp_apply] at h1
    have hbase : (Spec.map (CommRingCat.ofHom (axisR (chartAug heU)).toRingHom)).base p' =
        p := hp'
    rw [hbase] at h1
    rw [h1]
    have hr := IsAffineOpen.range_fromSpec hU
    have : (hU.fromSpec).base p' ∈ Set.range (hU.fromSpec).base := Set.mem_range_self p'
    rwa [hr] at this
  -- comaximality
  have htop : I₀ ⊔ JL ⊓ JR = ⊤ := by
    rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top]
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    have hle : I₀ ⊔ JL ⊓ JR ≤ p.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp hp
    have hp₀ : I₀ ≤ p.asIdeal := le_trans le_sup_left hle
    have hpLR : JL ⊓ JR ≤ p.asIdeal := le_trans le_sup_right hle
    have hpZ : p ∈ ((boxMul hU).base ⁻¹' (U : Set F.E))ᶜ := by
      rw [hI₀]
      exact (PrimeSpectrum.mem_zeroLocus _ _).mpr hp₀
    rcases (p.isPrime.inf_le).mp hpLR with hL | hR
    · exact hpZ (haxL p hL)
    · exact hpZ (haxR p hR)
  -- extract the separating element
  have hmem : (1 : ↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) ∈ I₀ ⊔ JL ⊓ JR := by
    rw [htop]; trivial
  obtain ⟨z, hz', j, hj, hzj⟩ := Submodule.mem_sup.mp hmem
  have h1 : z = 1 - j := by rw [← hzj]; ring
  refine ⟨z, ?_, ?_, ?_⟩
  · have hjL : (axisL (chartAug heU)) j = 0 := RingHom.mem_ker.mp hj.1
    rw [h1, map_sub, map_one, hjL, sub_zero]
  · have hjR : (axisR (chartAug heU)) j = 0 := RingHom.mem_ker.mp hj.2
    rw [h1, map_sub, map_one, hjR, sub_zero]
  · intro x hx
    by_contra hnot
    have hxZ : x ∈ PrimeSpectrum.zeroLocus (I₀ : Set _) := by
      rw [← hI₀]
      exact hnot
    exact hx ((PrimeSpectrum.mem_zeroLocus _ _).mp hxZ hz')

section Loc

variable (y₀ : ↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U))

/-- The box ring localized away from the separating tensor — a registered `def`
(v10.129 registry: inline localizations churn `isDefEq`). -/
private def BoxLoc : Type u := Localization.Away y₀

private noncomputable instance : CommRing (BoxLoc y₀) :=
  inferInstanceAs (CommRing (Localization.Away y₀))

private noncomputable instance : Algebra (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U))
    (BoxLoc y₀) :=
  inferInstanceAs (Algebra _ (Localization.Away y₀))

private instance : IsLocalization.Away y₀ (BoxLoc y₀) :=
  inferInstanceAs (IsLocalization.Away y₀ (Localization.Away y₀))

/-- The universal lift out of the box localization. -/
private noncomputable def locLift {T : Type u} [CommRing T]
    (g : ↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U) →+* T) (hg : IsUnit (g y₀)) :
    BoxLoc y₀ →+* T :=
  IsLocalization.Away.lift y₀ hg

private theorem locLift_eq {T : Type u} [CommRing T]
    (g : ↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U) →+* T) (hg : IsUnit (g y₀))
    (x : ↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) :
    locLift y₀ g hg (algebraMap _ (BoxLoc y₀) x) = g x :=
  IsLocalization.Away.lift_eq y₀ hg x

private theorem algebraMap_boxLoc_isUnit :
    IsUnit (algebraMap (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) (BoxLoc y₀) y₀) :=
  IsLocalization.Away.algebraMap_isUnit y₀

end Loc

/-- Kernel points have chart comorphisms `I`-close to the augmentation (the `(H-φ)`
computation). Raw form, no algebra instances. -/
private theorem pointSharp_sub_mem_ker
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (_hφ : Function.Surjective φ.hom) (_hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec B} (P : F.Point t)
    (hP : Point.restrict F (Spec.map φ) P = 0)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (c : Γ(F.E, U)) :
    (pointSharp P.1 hp).hom c -
      ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom
        ((F.zero.appLE U ⊤ (fun x _ => heU x)) c) ∈ RingHom.ker φ.hom := by
  -- the reduction of `P` is the zero point over the reduced base
  have hval : Spec.map φ ≫ P.1 = ((0 : F.Point (Spec.map φ ≫ t)) : Spec S' ⟶ F.E) :=
    congrArg Subtype.val hP
  have hcomp : ∀ x : ↑(Spec S'), (Spec.map φ ≫ P.1).base x ∈ U := by
    intro x
    rw [Scheme.Hom.comp_apply]
    exact hp _
  have hz' : ∀ x : ↑(Spec S'),
      ((0 : F.Point (Spec.map φ ≫ t)) : Spec S' ⟶ F.E).base x ∈ U := by
    intro x
    rw [← hval, Scheme.Hom.comp_apply]
    exact hp _
  -- φ of the sharp is the sharp of the reduction, which is the augmentation composite
  have h1 : φ.hom ((pointSharp P.1 hp).hom c) =
      (pointSharp ((0 : F.Point (Spec.map φ ≫ t)) : Spec S' ⟶ F.E) hz').hom c := by
    have h2 := pointSharp_specMap_comp φ hp hcomp
    have h3 := congrArg (fun (m : Γ(F.E, U) ⟶ S') => m.hom c)
      (h2.symm.trans (pointSharp_congr hval hcomp hz'))
    exact h3
  have h4 := pointSharp_zero_point heU (Spec.map φ ≫ t) hz' c
  -- both sides are the augmentation through the composite base map
  have h6 : (Spec.map φ).appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso S').hom =
      (Scheme.ΓSpecIso R).hom ≫ φ := by
    rw [show (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop from rfl]
    exact Scheme.ΓSpecIso_naturality φ
  have h5 : ((Spec.map φ ≫ t).appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso S').hom) =
      (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom) ≫ φ := by
    rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) t ⊤ ⊤ ⊤ le_top le_top]
    rw [Category.assoc, h6, Category.assoc]
  have h4' : (pointSharp ((0 : F.Point (Spec.map φ ≫ t)) : Spec S' ⟶ F.E) hz').hom c =
      φ.hom (((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom
        ((F.zero.appLE U ⊤ (fun x _ => heU x)) c)) := by
    refine h4.trans ?_
    exact congrArg (fun (m : _ ⟶ S') => m.hom ((F.zero.appLE U ⊤ (fun x _ => heU x)) c)) h5
  rw [RingHom.mem_ker, map_sub, h1, h4', sub_self]

/-- In a commutative ring, an ideal that squares to zero annihilates products of its
members: if `I ^ 2 = ⊥` then `a * b = 0` for all `a b ∈ I`. -/
private theorem mul_eq_zero_of_mem_of_sq_eq_bot {A : Type*} [CommRing A] {I : Ideal A}
    (hI : I ^ 2 = ⊥) {a b : A} (ha : a ∈ I) (hb : b ∈ I) : a * b = 0 := by
  have h1 : a * b ∈ I ^ 2 := by rw [sq]; exact Ideal.mul_mem_mul ha hb
  simpa [hI] using h1

/-- If a ring map `g : D ⟶ Γ(E, U)` factors the tautological chart cover through a morphism
`w₀`, i.e. `hU.fromSpec = Spec.map g ≫ w₀`, then `g` recovers every section from the chart
comorphism of `w₀`: `g (pointSharp w₀ f) = f`. This is the localized axis-law step, shared
between the two axes of `pointSharp_add_of_kernel`. -/
private theorem hom_pointSharp_eq_of_fromSpec_factor {D : CommRingCat.{u}}
    (hU : IsAffineOpen U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    {w₀ : Spec D ⟶ F.E} (hw₀ : ∀ x : ↑(Spec D), w₀.base x ∈ U)
    (g : D ⟶ Γ(F.E, U)) (hfromSpec : hU.fromSpec = Spec.map g ≫ w₀) (f : Γ(F.E, U)) :
    g.hom ((pointSharp w₀ hw₀).hom f) = f := by
  have hcomp : ∀ x : ↑(Spec Γ(F.E, U)), (Spec.map g ≫ w₀).base x ∈ U := by
    intro x
    rw [← hfromSpec]
    exact htaut x
  have h3 := (pointSharp_congr hfromSpec htaut hcomp).trans
    (pointSharp_specMap_comp g hw₀ hcomp)
  have h4 := congrArg (fun (m : Γ(F.E, U) ⟶ Γ(F.E, U)) => m.hom f)
    ((pointSharp_fromSpec hU htaut).symm.trans h3)
  exact h4.symm

/-- **(ADD — the co-multiplication additivity on kernel points, arbitrary base)** For two
points restricting to zero modulo a square-zero kernel, the chart comorphism of the sum is
additive on augmentation-ideal elements. The `y₀`-localized evaluation replaces the
field-only stalk argument of `TorsionUnramifiedFibre.pointSharp_add`. -/
private theorem pointSharp_add_of_kernel (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    (hz : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U)
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec B} (P Q : F.Point t)
    (hP : Point.restrict F (Spec.map φ) P = 0) (hQ : Point.restrict F (Spec.map φ) Q = 0)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U)
    (hpq : ∀ x : ↑(Spec R), ((P + Q : F.Point t) : Spec R ⟶ F.E).base x ∈ U)
    (f : Γ(F.E, U)) (hf : F.zero.appLE U ⊤ (fun x _ => heU x) f = 0) :
    (pointSharp ((P + Q : F.Point t) : Spec R ⟶ F.E) hpq).hom f =
      (pointSharp P.1 hp).hom f + (pointSharp Q.1 hq).hom f := by
  classical
  -- the algebra structures
  letI : Algebra ↑Γ(Spec B, ⊤) ↑R :=
    ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom.toAlgebra
  set ε : ↑Γ(F.E, U) →ₐ[↑Γ(Spec B, ⊤)] ↑Γ(Spec B, ⊤) := chartAug heU with hε
  set p₁ : ↑Γ(F.E, U) →ₐ[↑Γ(Spec B, ⊤)] ↑R :=
    { toRingHom := (pointSharp P.1 hp).hom
      commutes' := fun c => pointSharp_comp_π P hp c } with hp₁
  set p₂ : ↑Γ(F.E, U) →ₐ[↑Γ(Spec B, ⊤)] ↑R :=
    { toRingHom := (pointSharp Q.1 hq).hom
      commutes' := fun c => pointSharp_comp_π Q hq c } with hp₂
  have hclose₁ : ∀ c, p₁ c - algebraMap ↑Γ(Spec B, ⊤) ↑R (ε c) ∈ RingHom.ker φ.hom :=
    fun c => pointSharp_sub_mem_ker heU hφ hφ2 P hP hp c
  have hclose₂ : ∀ c, p₂ c - algebraMap ↑Γ(Spec B, ⊤) ↑R (ε c) ∈ RingHom.ker φ.hom :=
    fun c => pointSharp_sub_mem_ker heU hφ hφ2 Q hQ hq c
  -- the separating tensor and the pair lift
  obtain ⟨y₀, hyL, hyR, hyU⟩ := exists_sep hU heU htaut hz
  set pT : ↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U) →ₐ[↑Γ(Spec B, ⊤)] ↑R :=
    Algebra.TensorProduct.lift p₁ p₂ (fun _ _ => Commute.all _ _) with hpT
  have hkey : ∀ x, pT x = p₂ (axisL ε x) + p₁ (axisR ε x) -
      algebraMap ↑Γ(Spec B, ⊤) ↑R (foldε ε x) :=
    fun x => pairLift_key ε p₁ p₂ hclose₁ hclose₂
      (fun _ ha _ hb => mul_eq_zero_of_mem_of_sq_eq_bot hφ2 ha hb) x
  have hpTy₀ : pT y₀ = 1 := by
    rw [hkey, hyL, hyR, foldε_eq_axisL, hyL, map_one, map_one, map_one, map_one]
    ring
  -- the Künneth identification of the pairing
  have hid : pairBox P Q hp hq ≫ (boxIso hU).hom =
      Spec.map (CommRingCat.ofHom pT.toRingHom) := by
    refine pairBox_boxIso_eq_specMap hU P Q hp hq ?_ ?_
    · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      show pT (c ⊗ₜ 1) = (pointSharp P.1 hp).hom c
      rw [hpT, Algebra.TensorProduct.lift_tmul, map_one, _root_.mul_one]
      rfl
    · refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      show pT (1 ⊗ₜ c) = (pointSharp Q.1 hq).hom c
      rw [hpT, Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
      rfl
  -- the sum through the box multiplication
  have hsum : ((P + Q : F.Point t) : Spec R ⟶ F.E) =
      Spec.map (CommRingCat.ofHom pT.toRingHom) ≫ boxMul hU := by
    rw [← hid, boxMul]
    have h1 := point_add_val_mu F P Q
    rw [h1, pairing_eq_pairBox P Q hp hq]
    refine (Category.assoc _ _ _).trans ?_
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  -- units of the separating tensor under the three maps
  have hyLunit : IsUnit ((axisL ε).toRingHom y₀) := by
    show IsUnit (axisL ε y₀)
    rw [hyL]; exact isUnit_one
  have hyRunit : IsUnit ((axisR ε).toRingHom y₀) := by
    show IsUnit (axisR ε y₀)
    rw [hyR]; exact isUnit_one
  have hpTyunit : IsUnit (pT.toRingHom y₀) := by
    show IsUnit (pT y₀)
    rw [hpTy₀]; exact isUnit_one
  -- the lifts to the localization away from `y₀`
  set pTL : BoxLoc y₀ →+* ↑R := locLift y₀ pT.toRingHom hpTyunit with hpTLdef
  set aLL : BoxLoc y₀ →+* ↑Γ(F.E, U) :=
    locLift y₀ (axisL ε).toRingHom hyLunit with haLLdef
  set aRL : BoxLoc y₀ →+* ↑Γ(F.E, U) :=
    locLift y₀ (axisR ε).toRingHom hyRunit with haRLdef
  have hpTL_eq : ∀ x, pTL (algebraMap _ (BoxLoc y₀) x) = pT x := fun x =>
    locLift_eq y₀ pT.toRingHom hpTyunit x
  have haLL_eq : ∀ x, aLL (algebraMap _ (BoxLoc y₀) x) = axisL ε x := fun x =>
    locLift_eq y₀ (axisL ε).toRingHom hyLunit x
  have haRL_eq : ∀ x, aRL (algebraMap _ (BoxLoc y₀) x) = axisR ε x := fun x =>
    locLift_eq y₀ (axisR ε).toRingHom hyRunit x
  -- the localized box morphism lands in the chart
  have hqLland : ∀ x : ↑(Spec (CommRingCat.of (BoxLoc y₀))),
      (Spec.map (CommRingCat.ofHom
        (algebraMap (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) (BoxLoc y₀))) ≫
        boxMul hU).base x ∈ U := by
    intro x
    rw [Scheme.Hom.comp_apply]
    refine hyU _ ?_
    intro hy
    have hunit : IsUnit (algebraMap
        (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) (BoxLoc y₀) y₀) :=
      algebraMap_boxLoc_isUnit y₀
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy hunit)
  -- factor the pairing and the axes through the localization
  have hfacT : Spec.map (CommRingCat.ofHom pT.toRingHom) =
      Spec.map (CommRingCat.ofHom pTL) ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) (BoxLoc y₀))) := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
    show pT x = pTL (algebraMap _ _ x)
    exact (hpTL_eq x).symm
  have hfacL : Spec.map (CommRingCat.ofHom (axisL ε).toRingHom) =
      Spec.map (CommRingCat.ofHom aLL) ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) (BoxLoc y₀))) := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
    show axisL ε x = aLL (algebraMap _ _ x)
    exact (haLL_eq x).symm
  have hfacR : Spec.map (CommRingCat.ofHom (axisR ε).toRingHom) =
      Spec.map (CommRingCat.ofHom aRL) ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) (BoxLoc y₀))) := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => ?_))
    show axisR ε x = aRL (algebraMap _ _ x)
    exact (haRL_eq x).symm
  -- the sharp of the sum evaluates through the localized pairing
  have hcompsum : ∀ x : ↑(Spec R), (Spec.map (CommRingCat.ofHom pTL) ≫
      (Spec.map (CommRingCat.ofHom
        (algebraMap (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) (BoxLoc y₀))) ≫
        boxMul hU)).base x ∈ U := by
    intro x
    have h2 : Spec.map (CommRingCat.ofHom pTL) ≫
        (Spec.map (CommRingCat.ofHom
          (algebraMap (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) (BoxLoc y₀))) ≫
          boxMul hU) = ((P + Q : F.Point t) : Spec R ⟶ F.E) := by
      rw [hsum, hfacT, Category.assoc]
    rw [h2]
    exact hpq x
  have hsharp_sum : (pointSharp ((P + Q : F.Point t) : Spec R ⟶ F.E) hpq).hom f =
      pTL ((pointSharp _ hqLland).hom f) := by
    have h2 : ((P + Q : F.Point t) : Spec R ⟶ F.E) =
        Spec.map (CommRingCat.ofHom pTL) ≫
          (Spec.map (CommRingCat.ofHom
            (algebraMap (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U)) (BoxLoc y₀))) ≫
            boxMul hU) := by
      rw [hsum, hfacT, Category.assoc]
    have h3 := (pointSharp_congr h2 hpq hcompsum).trans
      (pointSharp_specMap_comp (CommRingCat.ofHom pTL) hqLland hcompsum)
    exact congrArg (fun (m : Γ(F.E, U) ⟶ R) => m.hom f) h3
  -- the axis laws evaluate through the localization
  have haxLf : aLL ((pointSharp _ hqLland).hom f) = f := by
    refine hom_pointSharp_eq_of_fromSpec_factor hU htaut hqLland (CommRingCat.ofHom aLL) ?_ f
    rw [← Category.assoc, ← hfacL]
    exact (show Spec.map (CommRingCat.ofHom (axisL ε).toRingHom) ≫ boxMul hU =
      hU.fromSpec from axisL_spec_law hU heU htaut hz).symm
  have haxRf : aRL ((pointSharp _ hqLland).hom f) = f := by
    refine hom_pointSharp_eq_of_fromSpec_factor hU htaut hqLland (CommRingCat.ofHom aRL) ?_ f
    rw [← Category.assoc, ← hfacR]
    exact (show Spec.map (CommRingCat.ofHom (axisR ε).toRingHom) ≫ boxMul hU =
      hU.fromSpec from axisR_spec_law hU heU htaut hz).symm
  -- clear the denominator
  obtain ⟨⟨num, den⟩, hnd⟩ := IsLocalization.surj (M := Submonoid.powers y₀)
    ((pointSharp _ hqLland).hom f)
  obtain ⟨n, hn⟩ := den.2
  have hpT_den : pT den.1 = 1 := by
    rw [← hn]
    show pT (y₀ ^ n) = 1
    rw [map_pow, hpTy₀, one_pow]
  have haxL_den : (axisL ε) den.1 = 1 := by
    rw [← hn]
    show axisL ε (y₀ ^ n) = 1
    rw [map_pow, hyL, one_pow]
  have haxR_den : (axisR ε) den.1 = 1 := by
    rw [← hn]
    show axisR ε (y₀ ^ n) = 1
    rw [map_pow, hyR, one_pow]
  -- the numerator's axis values (defeq-absorbing the localization instance paths)
  have hnumL : axisL ε num = f := by
    have h6 : aLL ((pointSharp _ hqLland).hom f) *
        aLL (algebraMap _ (BoxLoc y₀) den.1) = aLL (algebraMap _ (BoxLoc y₀) num) := by
      have h2 := congrArg aLL hnd
      rw [map_mul] at h2
      exact h2
    rw [haLL_eq, haLL_eq, haxLf, haxL_den, _root_.mul_one] at h6
    exact h6.symm
  have hnumR : axisR ε num = f := by
    have h6 : aRL ((pointSharp _ hqLland).hom f) *
        aRL (algebraMap _ (BoxLoc y₀) den.1) = aRL (algebraMap _ (BoxLoc y₀) num) := by
      have h2 := congrArg aRL hnd
      rw [map_mul] at h2
      exact h2
    rw [haRL_eq, haRL_eq, haxRf, haxR_den, _root_.mul_one] at h6
    exact h6.symm
  have hnumF : foldε ε num = 0 := by
    rw [foldε_eq_axisL, hnumL]
    show F.zero.appLE U ⊤ (fun x _ => heU x) f = 0
    exact hf
  -- assemble
  have hfin : pTL ((pointSharp _ hqLland).hom f) = pT num := by
    have h6 : pTL ((pointSharp _ hqLland).hom f) *
        pTL (algebraMap _ (BoxLoc y₀) den.1) = pTL (algebraMap _ (BoxLoc y₀) num) := by
      have h2 := congrArg pTL hnd
      rw [map_mul] at h2
      exact h2
    rw [hpTL_eq, hpTL_eq, hpT_den, _root_.mul_one] at h6
    exact h6
  rw [hsharp_sum, hfin, hkey, hnumL, hnumR, hnumF, map_zero, sub_zero]
  show (pointSharp Q.1 hq).hom f + (pointSharp P.1 hp).hom f = _
  ring

/-- Kernel points land in the zero chart. -/
private theorem kernel_mem (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec B} (P : F.Point t)
    (hP : Point.restrict F (Spec.map φ) P = 0) :
    ∀ x : ↑(Spec R), (P.1).base x ∈ U := by
  refine range_base_subset_of_reduction (t := t) heU hφ hφ2 ?_
  have hval : Spec.map φ ≫ P.1 = ((0 : F.Point (Spec.map φ ≫ t)) : Spec S' ⟶ F.E) :=
    congrArg Subtype.val hP
  rw [hval, F.point_zero_val, Category.assoc]

/-- Kernels are closed under `ℕ`-scalars. -/
private theorem kernel_nsmul {t : Spec R ⟶ Spec B} (P : F.Point t)
    (hP : Point.restrict F (Spec.map φ) P = 0) (n : ℕ) :
    Point.restrict F (Spec.map φ) ((n • P : F.Point t)) = 0 := by
  induction n with
  | zero => simpa using restrict_zero F (Spec.map φ)
  | succ k ih =>
      rw [succ_nsmul, restrict_add, ih, hP, add_zero]

/-- Chart comorphisms are `ℕ`-linear on kernel points over augmentation elements. -/
private theorem pointSharp_nsmul_of_kernel (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    (hz : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U)
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec B} (P : F.Point t)
    (hP : Point.restrict F (Spec.map φ) P = 0)
    (f : Γ(F.E, U)) (hf : F.zero.appLE U ⊤ (fun x _ => heU x) f = 0) (n : ℕ) :
    (pointSharp ((n • P : F.Point t) : Spec R ⟶ F.E)
      (kernel_mem heU hφ hφ2 _ (kernel_nsmul P hP n))).hom f =
      n • (pointSharp P.1 (kernel_mem heU hφ hφ2 P hP)).hom f := by
  induction n with
  | zero =>
      have h0 : ((0 • P : F.Point t) : Spec R ⟶ F.E) =
          ((0 : F.Point t) : Spec R ⟶ F.E) := by
        rw [zero_nsmul]
      rw [pointSharp_congr h0 _ (kernel_mem heU hφ hφ2 _ (by
        simpa using restrict_zero F (Spec.map φ)))]
      have h1 := pointSharp_zero_point heU t (kernel_mem heU hφ hφ2 _ (by
        simpa using restrict_zero F (Spec.map φ))) f
      rw [h1, hf, map_zero, zero_smul]
  | succ k ih =>
      have hsucc : (((k + 1) • P : F.Point t) : Spec R ⟶ F.E) =
          (((k • P : F.Point t) + P : F.Point t) : Spec R ⟶ F.E) := by
        rw [succ_nsmul]
      rw [pointSharp_congr hsucc _ (kernel_mem heU hφ hφ2 _ (by
        rw [restrict_add, kernel_nsmul P hP k, hP, add_zero]))]
      rw [pointSharp_add_of_kernel hU heU htaut hz hφ hφ2 (k • P) P
        (kernel_nsmul P hP k) hP
        (kernel_mem heU hφ hφ2 _ (kernel_nsmul P hP k))
        (kernel_mem heU hφ hφ2 P hP) _ f hf]
      rw [ih, succ_nsmul]

/-! The divided comorphism, hoisted (small context) per the 200k discipline. -/

private noncomputable def divSharpHom (sh βr : ↑Γ(F.E, U) →+* ↑R) (u : ↑R)
    (hII : ∀ c c', (sh c - βr c) * (sh c' - βr c') = 0) : ↑Γ(F.E, U) →+* ↑R where
  toFun := fun c => βr c + u * (sh c - βr c)
  map_one' := by rw [map_one, map_one, sub_self, mul_zero, add_zero]
  map_mul' := by
    intro c c'
    have h2 := hII c c'
    show βr (c * c') + u * (sh (c * c') - βr (c * c')) =
      (βr c + u * (sh c - βr c)) * (βr c' + u * (sh c' - βr c'))
    rw [map_mul sh, map_mul βr]
    linear_combination (u - u * u) * h2
  map_zero' := by rw [map_zero, map_zero, sub_self, mul_zero, add_zero]
  map_add' := by
    intro c c'
    show βr (c + c') + u * (sh (c + c') - βr (c + c')) = _
    rw [map_add sh, map_add βr]
    ring

/-- Points of the chart from base-compatible comorphisms. -/
private theorem exists_point_of_sharp (hU : IsAffineOpen U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    {t : Spec R ⟶ Spec B} (g : ↑Γ(F.E, U) →+* ↑R)
    (hgπ : ∀ c₀, g (F.π.appLE ⊤ U (fun _ _ => trivial) c₀) =
      ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom c₀) :
    ∃ (δ : F.Point t) (hmem : ∀ x : ↑(Spec R), (δ.1).base x ∈ U),
      pointSharp δ.1 hmem = CommRingCat.ofHom g := by
  set w : Spec R ⟶ F.E := Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec with hw
  have hwU : ∀ x : ↑(Spec R), w.base x ∈ U := by
    intro x
    rw [hw, Scheme.Hom.comp_apply]
    have hr := IsAffineOpen.range_fromSpec hU
    have h2 : (hU.fromSpec).base ((Spec.map (CommRingCat.ofHom g)).base x) ∈
        Set.range (hU.fromSpec).base := Set.mem_range_self _
    rwa [hr] at h2
  have hwsharp : pointSharp w hwU = CommRingCat.ofHom g := by
    have h2 := pointSharp_specMap_comp (CommRingCat.ofHom g) htaut hwU
    rw [(pointSharp_congr (show w = Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec from hw)
      hwU (fun x => by rw [← hw]; exact hwU x)).trans h2, pointSharp_fromSpec hU htaut,
      Category.id_comp]
  have hwπ : w ≫ F.π = t := by
    have h0 := hU.SpecMap_appLE_fromSpec w (isAffineOpen_top (Spec R)) (fun x _ => hwU x)
    rw [IsAffineOpen.fromSpec_top] at h0
    have hwfac : w = (Spec R).isoSpec.hom ≫ Spec.map (w.appLE U ⊤ (fun x _ => hwU x)) ≫
        hU.fromSpec := by rw [h0, Iso.hom_inv_id_assoc]
    have happ : F.π.appLE ⊤ U (fun _ _ => trivial) ≫ w.appLE U ⊤ (fun x _ => hwU x) =
        t.appLE ⊤ ⊤ le_top := by
      have h1 : w.appLE U ⊤ (fun x _ => hwU x) =
          CommRingCat.ofHom g ≫ (Scheme.ΓSpecIso R).inv := by
        have h3 : pointSharp w hwU ≫ (Scheme.ΓSpecIso R).inv =
            w.appLE U ⊤ (fun x _ => hwU x) := by
          show (w.appLE U ⊤ (fun x _ => hwU x) ≫ (Scheme.ΓSpecIso R).hom) ≫
            (Scheme.ΓSpecIso R).inv = _
          rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        rw [← h3, hwsharp]
      rw [h1]
      refine CommRingCat.hom_ext (RingHom.ext fun c₀ => ?_)
      show (Scheme.ΓSpecIso R).inv.hom (g (F.π.appLE ⊤ U (fun _ _ => trivial) c₀)) =
        (t.appLE ⊤ ⊤ le_top).hom c₀
      rw [hgπ c₀]
      have h3 := congrArg (fun (m : Γ(Spec R, ⊤) ⟶ Γ(Spec R, ⊤)) =>
        m.hom ((t.appLE ⊤ ⊤ le_top).hom c₀)) (Scheme.ΓSpecIso R).hom_inv_id
      exact h3
    refine (congrArg (· ≫ F.π) hwfac).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg ((Spec R).isoSpec.hom ≫ ·) (Category.assoc _ _ _)).trans ?_
    refine (congrArg ((Spec R).isoSpec.hom ≫ ·)
      (congrArg (Spec.map (w.appLE U ⊤ (fun x _ => hwU x)) ≫ ·)
        (specMap_π_appLE_fromSpec (F := F) hU).symm)).trans ?_
    refine (congrArg ((Spec R).isoSpec.hom ≫ ·) ((Category.assoc _ _ _).symm)).trans ?_
    refine (congrArg ((Spec R).isoSpec.hom ≫ ·) (congrArg
      (· ≫ (isAffineOpen_top (Spec B)).fromSpec)
      ((Spec.map_comp _ _).symm))).trans ?_
    refine (congrArg ((Spec R).isoSpec.hom ≫ ·) (congrArg
      (fun m => Spec.map m ≫ (isAffineOpen_top (Spec B)).fromSpec) happ)).trans ?_
    refine (congrArg ((Spec R).isoSpec.hom ≫ ·)
      ((isAffineOpen_top (Spec B)).SpecMap_appLE_fromSpec t
        (isAffineOpen_top (Spec R)) le_top)).trans ?_
    rw [IsAffineOpen.fromSpec_top, Iso.hom_inv_id_assoc]
  exact ⟨⟨w, hwπ⟩, hwU, hwsharp⟩

/-- **(CHART-DIV)** Square-zero kernel points are `N`-divisible in the chart, for `N` a
unit: the `β + N⁻¹·(sharp − β)` comorphism is a ring map by the square-zero kill, and its
point is the required `δ`. -/
theorem exists_kernel_div (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    (hz : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U)
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec B} (N : ℕ) (hN : IsUnit ((N : ℕ) : ↑R))
    (P : F.Point t) (hP : Point.restrict F (Spec.map φ) P = 0) :
    ∃ δ : F.Point t, Point.restrict F (Spec.map φ) δ = 0 ∧ (N : ℤ) • δ = P := by
  classical
  have hp := kernel_mem heU hφ hφ2 P hP
  have h0K : Point.restrict F (Spec.map φ) (0 : F.Point t) = 0 :=
    restrict_zero F (Spec.map φ)
  have hz₀ := kernel_mem heU hφ hφ2 (0 : F.Point t) h0K
  -- the unit inverse
  set u : ↑R := ↑hN.unit⁻¹ with hu_def
  have huN : ((N : ℕ) : ↑R) * u = 1 := by
    rw [hu_def]
    exact hN.mul_val_inv
  -- the difference and its square-zero bounds
  set β : ↑Γ(F.E, U) →+* ↑R := (pointSharp ((0 : F.Point t) : Spec R ⟶ F.E) hz₀).hom
    with hβ
  set i : ↑Γ(F.E, U) → ↑R := fun c => (pointSharp P.1 hp).hom c - β c with hi
  have hII : ∀ a ∈ RingHom.ker φ.hom, ∀ b ∈ RingHom.ker φ.hom, a * b = 0 := by
    intro a ha b hb
    have h1 : a * b ∈ RingHom.ker φ.hom ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul ha hb
    simpa [hφ2] using h1
  have hiI : ∀ c, i c ∈ RingHom.ker φ.hom := by
    intro c
    have h1 := pointSharp_sub_mem_ker heU hφ hφ2 P hP hp c
    have h2 : β c = ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom
        ((F.zero.appLE U ⊤ (fun x _ => heU x)) c) := by
      rw [hβ]
      exact pointSharp_zero_point heU t hz₀ c
    rw [hi]
    show (pointSharp P.1 hp).hom c - β c ∈ RingHom.ker φ.hom
    rw [h2]
    exact h1
  have hi_mul : ∀ c c', i (c * c') = β c * i c' + i c * β c' := by
    intro c c'
    have h1 : (pointSharp P.1 hp).hom (c * c') = (β c + i c) * (β c' + i c') := by
      rw [map_mul]
      congr 1 <;> · rw [hi]; ring
    have h2 : i c * i c' = 0 := hII _ (hiI c) _ (hiI c')
    rw [hi]
    show (pointSharp P.1 hp).hom (c * c') - β (c * c') = _
    rw [h1, map_mul]
    have h3 : (β c + i c) * (β c' + i c') =
        β c * β c' + β c * i c' + i c * β c' + i c * i c' := by ring
    rw [h3, h2]
    ring
  -- the divided comorphism (hoisted)
  have hII' : ∀ c c', ((pointSharp P.1 hp).hom c - β c) *
      ((pointSharp P.1 hp).hom c' - β c') = 0 := fun c c' =>
    hII _ (hiI c) _ (hiI c')
  set g : ↑Γ(F.E, U) →+* ↑R := divSharpHom (pointSharp P.1 hp).hom β u hII' with hg
  have hg_eval : ∀ c, g c = β c + u * i c := fun c => rfl
  -- the base compatibility
  have hgπ : ∀ c₀, g (F.π.appLE ⊤ U (fun _ _ => trivial) c₀) =
      ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom c₀ := by
    intro c₀
    have h1 : (pointSharp P.1 hp).hom (F.π.appLE ⊤ U (fun _ _ => trivial) c₀) =
        ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom c₀ :=
      pointSharp_comp_π P hp c₀
    have h2 : β (F.π.appLE ⊤ U (fun _ _ => trivial) c₀) =
        ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom c₀ := by
      rw [hβ]
      exact pointSharp_comp_π (0 : F.Point t) hz₀ c₀
    rw [hg_eval]
    have h3 : i (F.π.appLE ⊤ U (fun _ _ => trivial) c₀) = 0 := by
      rw [hi]
      show (pointSharp P.1 hp).hom _ - β _ = 0
      rw [h1, h2, sub_self]
    rw [h2, h3, mul_zero, add_zero]
  obtain ⟨δ, hδmem, hδsharp⟩ := exists_point_of_sharp hU htaut g hgπ
  have hδsharpφ : ∀ c, φ.hom (g c) = φ.hom (β c) := by
    intro c
    rw [hg_eval, map_add, map_mul]
    have h1 : φ.hom (i c) = 0 := hiI c
    rw [h1, mul_zero, add_zero]
  -- δ is a kernel point
  have hδK : Point.restrict F (Spec.map φ) δ = 0 := by
    refine Subtype.ext ?_
    show Spec.map φ ≫ δ.1 = ((0 : F.Point (Spec.map φ ≫ t)) : Spec S' ⟶ F.E)
    have hcomp : ∀ x : ↑(Spec S'), (Spec.map φ ≫ δ.1).base x ∈ U := fun x => by
      rw [Scheme.Hom.comp_apply]; exact hδmem _
    have hz0' : ∀ x : ↑(Spec S'),
        ((0 : F.Point (Spec.map φ ≫ t)) : Spec S' ⟶ F.E).base x ∈ U := by
      intro x
      rw [F.point_zero_val]
      rw [Scheme.Hom.comp_apply]
      exact heU _
    refine eq_of_pointSharp_eq hU hcomp hz0' ?_
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    have hL : (pointSharp (Spec.map φ ≫ δ.1) hcomp).hom c = φ.hom (g c) := by
      have h2 := pointSharp_specMap_comp φ hδmem hcomp
      have h3 := congrArg (fun (m : Γ(F.E, U) ⟶ S') => m.hom c) h2
      have h4 := congrArg (fun (m : Γ(F.E, U) ⟶ R) => φ.hom (m.hom c)) hδsharp
      exact h3.trans h4
    have hR : (pointSharp ((0 : F.Point (Spec.map φ ≫ t)) : Spec S' ⟶ F.E) hz0').hom c =
        φ.hom (β c) := by
      rw [pointSharp_zero_point heU (Spec.map φ ≫ t) hz0' c]
      have h6 : (Spec.map φ).appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso S').hom =
          (Scheme.ΓSpecIso R).hom ≫ φ := by
        rw [show (Spec.map φ).appLE ⊤ ⊤ le_top = (Spec.map φ).appTop from rfl]
        exact Scheme.ΓSpecIso_naturality φ
      have h5 : ((Spec.map φ ≫ t).appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso S').hom) =
          (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom) ≫ φ := by
        rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) t ⊤ ⊤ ⊤ le_top le_top]
        rw [Category.assoc, h6, Category.assoc]
      have h7 := congrArg (fun (m : Γ(Spec B, ⊤) ⟶ S') =>
        m.hom ((F.zero.appLE U ⊤ (fun x _ => heU x)) c)) h5
      refine h7.trans ?_
      have h8 : β c = ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom
          ((F.zero.appLE U ⊤ (fun x _ => heU x)) c) := by
        rw [hβ]
        exact pointSharp_zero_point heU t hz₀ c
      rw [h8]
      rfl
    rw [hL, hR, hδsharpφ c]
  -- the scalar identity
  have hNδK : Point.restrict F (Spec.map φ) ((N • δ : F.Point t)) = 0 :=
    kernel_nsmul δ hδK N
  have hNδmem := kernel_mem heU hφ hφ2 _ hNδK
  have hsharpδ_eval : ∀ c, (pointSharp δ.1 hδmem).hom c = g c := fun c =>
    congrArg (fun (m : Γ(F.E, U) ⟶ R) => m.hom c) hδsharp
  have hfinal : pointSharp ((N • δ : F.Point t) : Spec R ⟶ F.E) hNδmem =
      pointSharp P.1 hp := by
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    set c₀ := F.π.appLE ⊤ U (fun _ _ => trivial)
      (F.zero.appLE U ⊤ (fun x _ => heU x) c) with hc₀
    have haug : F.zero.appLE U ⊤ (fun x _ => heU x) (c - c₀) = 0 := by
      rw [map_sub, hc₀, zero_appLE_π_appLE, sub_self]
    have hbaseN : (pointSharp ((N • δ : F.Point t) : Spec R ⟶ F.E) hNδmem).hom c₀ =
        ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom
          ((F.zero.appLE U ⊤ (fun x _ => heU x)) c) :=
      pointSharp_comp_π (N • δ : F.Point t) hNδmem _
    have hbaseP : (pointSharp P.1 hp).hom c₀ =
        ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom
          ((F.zero.appLE U ⊤ (fun x _ => heU x)) c) :=
      pointSharp_comp_π P hp _
    have haugN : (pointSharp ((N • δ : F.Point t) : Spec R ⟶ F.E) hNδmem).hom (c - c₀) =
        N • (pointSharp δ.1 (kernel_mem heU hφ hφ2 δ hδK)).hom (c - c₀) :=
      pointSharp_nsmul_of_kernel hU heU htaut hz hφ hφ2 δ hδK (c - c₀) haug N
    have hδmem_eq : (pointSharp δ.1 (kernel_mem heU hφ hφ2 δ hδK)).hom (c - c₀) =
        g (c - c₀) := hsharpδ_eval (c - c₀)
    have hβaug : β (c - c₀) = 0 := by
      rw [hβ, pointSharp_zero_point heU t hz₀ (c - c₀), haug, map_zero]
    have hgaug : g (c - c₀) = u * i (c - c₀) := by
      rw [hg_eval, hβaug, zero_add]
    have haugP : i (c - c₀) = (pointSharp P.1 hp).hom (c - c₀) := by
      rw [hi]
      show _ - β _ = _
      rw [hβaug, sub_zero]
    have hNu : N • (u * i (c - c₀)) = i (c - c₀) := by
      rw [nsmul_eq_mul, ← _root_.mul_assoc, huN, _root_.one_mul]
    have hcN : (pointSharp ((N • δ : F.Point t) : Spec R ⟶ F.E) hNδmem).hom c =
        (pointSharp ((N • δ : F.Point t) : Spec R ⟶ F.E) hNδmem).hom c₀ +
        (pointSharp ((N • δ : F.Point t) : Spec R ⟶ F.E) hNδmem).hom (c - c₀) := by
      rw [← map_add]
      congr 1
      ring
    have hcP : (pointSharp P.1 hp).hom c =
        (pointSharp P.1 hp).hom c₀ + (pointSharp P.1 hp).hom (c - c₀) := by
      rw [← map_add]
      congr 1
      ring
    rw [hcN, hcP, hbaseN, hbaseP, haugN]
    congr 1
    rw [hδmem_eq, hgaug, hNu, haugP]
  refine ⟨δ, hδK, ?_⟩
  have h9 : ((N : ℤ) • δ : F.Point t) = (N • δ : F.Point t) := natCast_zsmul δ N
  rw [h9]
  exact Subtype.ext (eq_of_pointSharp_eq hU hNδmem hp hfinal)

/-- **(CHART-INJ)** `N`-multiplication is injective on square-zero kernel points in the
chart, for `N` a unit: a kernel point killed by `N` is zero. -/
theorem kernel_eq_zero_of_nsmul_eq_zero (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    (hz : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U)
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec B} (N : ℕ) (hN : IsUnit ((N : ℕ) : ↑R))
    (P : F.Point t) (hP : Point.restrict F (Spec.map φ) P = 0)
    (h0 : (N • P : F.Point t) = 0) : P = 0 := by
  classical
  have hp := kernel_mem heU hφ hφ2 P hP
  have h0K : Point.restrict F (Spec.map φ) (0 : F.Point t) = 0 :=
    restrict_zero F (Spec.map φ)
  have hz₀ := kernel_mem heU hφ hφ2 (0 : F.Point t) h0K
  have hNmem := kernel_mem heU hφ hφ2 _ (kernel_nsmul P hP N)
  refine Subtype.ext (eq_of_pointSharp_eq hU hp hz₀ ?_)
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  set c₀ := F.π.appLE ⊤ U (fun _ _ => trivial)
    (F.zero.appLE U ⊤ (fun x _ => heU x) c) with hc₀
  have haug : F.zero.appLE U ⊤ (fun x _ => heU x) (c - c₀) = 0 := by
    rw [map_sub, hc₀, zero_appLE_π_appLE, sub_self]
  -- base parts agree for any two points
  have hbaseP : (pointSharp P.1 hp).hom c₀ =
      ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom
        ((F.zero.appLE U ⊤ (fun x _ => heU x)) c) :=
    pointSharp_comp_π P hp _
  have hbase0 : (pointSharp ((0 : F.Point t) : Spec R ⟶ F.E) hz₀).hom c₀ =
      ((t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)).hom
        ((F.zero.appLE U ⊤ (fun x _ => heU x)) c) :=
    pointSharp_comp_π (0 : F.Point t) hz₀ _
  -- the augmentation part of `P` vanishes, from `N • P = 0` and `N` a unit
  have haug0 : (pointSharp ((0 : F.Point t) : Spec R ⟶ F.E) hz₀).hom (c - c₀) = 0 := by
    rw [pointSharp_zero_point heU t hz₀ (c - c₀), haug, map_zero]
  have haugP : (pointSharp P.1 hp).hom (c - c₀) = 0 := by
    have h1 : (pointSharp ((N • P : F.Point t) : Spec R ⟶ F.E) hNmem).hom (c - c₀) =
        N • (pointSharp P.1 (kernel_mem heU hφ hφ2 P hP)).hom (c - c₀) :=
      pointSharp_nsmul_of_kernel hU heU htaut hz hφ hφ2 P hP (c - c₀) haug N
    have h2 : (pointSharp ((N • P : F.Point t) : Spec R ⟶ F.E) hNmem).hom (c - c₀) = 0 := by
      have h3 : ((N • P : F.Point t) : Spec R ⟶ F.E) =
          ((0 : F.Point t) : Spec R ⟶ F.E) := congrArg Subtype.val h0
      rw [(congrArg (fun (m : Γ(F.E, U) ⟶ R) => m.hom (c - c₀))
        (pointSharp_congr h3 hNmem hz₀))]
      exact haug0
    have h4 : (N : ↑R) * (pointSharp P.1 hp).hom (c - c₀) = 0 := by
      have h5 := h1.symm.trans h2
      rwa [nsmul_eq_mul] at h5
    have h6 := congrArg (fun r => (↑hN.unit⁻¹ : ↑R) * r) h4
    simpa [← _root_.mul_assoc, IsUnit.val_inv_mul hN] using h6
  -- assemble on the split
  have hcP : (pointSharp P.1 hp).hom c =
      (pointSharp P.1 hp).hom c₀ + (pointSharp P.1 hp).hom (c - c₀) := by
    rw [← map_add]; congr 1; ring
  have hc0 : (pointSharp ((0 : F.Point t) : Spec R ⟶ F.E) hz₀).hom c =
      (pointSharp ((0 : F.Point t) : Spec R ⟶ F.E) hz₀).hom c₀ +
      (pointSharp ((0 : F.Point t) : Spec R ⟶ F.E) hz₀).hom (c - c₀) := by
    rw [← map_add]; congr 1; ring
  rw [hcP, hc0, hbaseP, hbase0, haugP, haug0]

end Box
