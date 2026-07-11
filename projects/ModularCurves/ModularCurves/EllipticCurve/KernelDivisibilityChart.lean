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
    Spec.map (F.π.appLE ⊤ U (fun x _ => trivial)) ≫
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

/-- The chart comorphism of a point over `t` restricts along `π` to the `t`-comorphism. -/
private theorem pointSharp_comp_π {U : (F.E).Opens} {t : Spec R ⟶ Spec B} (P : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (c : Γ(Spec B, ⊤)) :
    pointSharp P.1 hp (F.π.appLE ⊤ U (fun x _ => trivial) c) =
      (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom) c := by
  show ((F.π.appLE ⊤ U _ ≫ P.1.appLE U ⊤ _) ≫ (Scheme.ΓSpecIso R).hom) c = _
  rw [Scheme.Hom.appLE_comp_appLE P.1 F.π ⊤ U ⊤ _ _,
    FiniteLocallyFreeSubgroup.AffineChartPatch.appLE_congr_hom P.2 ⊤ ⊤]

/-- The augmentation retracts the structure map: `ζ ∘ π♯ = id` (`Γ`-dual of `zero ≫ π = 𝟙`). -/
private theorem zero_appLE_π_appLE {U : (F.E).Opens}
    (heU : ∀ x : ↑(Spec B), (F.zero).base x ∈ U) (c : Γ(Spec B, ⊤)) :
    F.zero.appLE U ⊤ (fun x _ => heU x) (F.π.appLE ⊤ U (fun x _ => trivial) c) = c := by
  show (F.π.appLE ⊤ U _ ≫ F.zero.appLE U ⊤ _) c = c
  rw [Scheme.Hom.appLE_comp_appLE F.zero F.π ⊤ U ⊤ _ _,
    FiniteLocallyFreeSubgroup.AffineChartPatch.appLE_congr_hom F.zero_π ⊤ ⊤,
    FiniteLocallyFreeSubgroup.AffineChartPatch.appLE_id]
  rfl


section Box

variable {U : (F.E).Opens}

/-- The chart's `k'`-algebra structure via the structure morphism. -/
private noncomputable local instance chartAlgebra :
    Algebra ↑Γ(Spec B, ⊤) ↑Γ(F.E, U) :=
  (F.π.appLE ⊤ U (fun x _ => trivial)).hom.toAlgebra

private theorem chartAlgebra_ofHom :
    CommRingCat.ofHom (algebraMap ↑Γ(Spec B, ⊤) ↑Γ(F.E, U)) =
      F.π.appLE ⊤ U (fun x _ => trivial) := rfl

/-- The affine Künneth box of the chart (`patchKunneth`, consumed from NEW-HOPF's
`PatchKunneth.lean`). -/
private noncomputable def boxIso (hU : IsAffineOpen U) :
    pullback (F.π.resLE ⊤ U (fun x _ => trivial)) (F.π.resLE ⊤ U (fun x _ => trivial)) ≅
      Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec B, ⊤)] ↑Γ(F.E, U))) :=
  patchKunneth F.π F.π (isAffineOpen_top _) hU hU chartAlgebra_ofHom chartAlgebra_ofHom

/-- The box sits inside the fibre square of `E`. -/
private noncomputable def boxι :
    (pullback (F.π.resLE ⊤ U (fun x _ => trivial))
      (F.π.resLE ⊤ U (fun x _ => trivial)) : Scheme) ⟶ pullback F.π F.π :=
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

/-- The pairing of two points through the box. -/
private noncomputable def pairBox {t : Spec R ⟶ Spec B} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    Spec R ⟶ pullback (F.π.resLE ⊤ U (fun x _ => trivial))
      (F.π.resLE ⊤ U (fun x _ => trivial)) :=
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

/-- **(TAUT-SHARP)** The chart comorphism of `fromSpec` is the identity. -/
private theorem pointSharp_fromSpec (hU : IsAffineOpen U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U) :
    pointSharp (R := Γ(F.E, U)) hU.fromSpec htaut = 𝟙 Γ(F.E, U) := by
  show hU.fromSpec.appLE U ⊤ _ ≫ (Scheme.ΓSpecIso Γ(F.E, U)).hom = 𝟙 _
  have hdef : hU.fromSpec = hU.isoSpec.inv ≫ U.ι := rfl
  rw [FiniteLocallyFreeSubgroup.AffineChartPatch.appLE_congr_hom hdef U ⊤,
    ← Scheme.Hom.appLE_comp_appLE hU.isoSpec.inv U.ι U ⊤ ⊤
      U.ι_preimage_self.ge le_top,
    FiniteLocallyFreeSubgroup.AffineChartPatch.ι_appLE_top,
    FiniteLocallyFreeSubgroup.AffineChartPatch.appLE_top_top]
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
      F.zero.appLE U ⊤ (fun x _ => heU x) ≫ F.π.appLE ⊤ U (fun x _ => trivial) := by
  refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
  have h0 := pointSharp_zero_point (R := Γ(F.E, U)) heU (hU.fromSpec ≫ F.π) hz c
  rw [h0]
  show ((hU.fromSpec ≫ F.π).appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso Γ(F.E, U)).hom)
      (F.zero.appLE U ⊤ (fun x _ => heU x) c) = _
  rw [← Scheme.Hom.appLE_comp_appLE hU.fromSpec F.π ⊤ U ⊤ (fun x _ => trivial)
    (fun x _ => htaut x)]
  show (pointSharp (R := Γ(F.E, U)) hU.fromSpec htaut)
      ((F.π.appLE ⊤ U (fun x _ => trivial)) (F.zero.appLE U ⊤ (fun x _ => heU x) c)) = _
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

/-- Chart evaluation of a `Spec`-precomposition: `(Spec.map g ≫ v)♯ = v♯ ≫ g`. -/
private theorem pointSharp_specMap_comp {R' R'' : CommRingCat.{u}} (g : R'' ⟶ R')
    {v : Spec R'' ⟶ F.E} (hv : ∀ x : ↑(Spec R''), v.base x ∈ U)
    (hcomp : ∀ x : ↑(Spec R'), (Spec.map g ≫ v).base x ∈ U) :
    pointSharp (Spec.map g ≫ v) hcomp = pointSharp v hv ≫ g := by
  have hnat : pointSharp v hv ≫ g = (Spec.map g ≫ v).appLE U ⊤
      (fun x _ => hcomp x) ≫ (Scheme.ΓSpecIso R').hom := by
    rw [pointSharp, Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← FiniteLocallyFreeSubgroup.AffineChartPatch.appLE_top_top (Spec.map g),
      Scheme.Hom.appLE_comp_appLE]
  rw [hnat]
  rfl


end Box

end AugmentationScheme

end EllipticCurve

end ModularCurves
