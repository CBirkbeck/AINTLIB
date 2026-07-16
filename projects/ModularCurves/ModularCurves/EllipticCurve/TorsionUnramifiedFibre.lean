/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.TorsionFibre
import ModularCurves.ForMathlib.FormallyUnramifiedFibre
import ModularCurves.ForMathlib.NilpotentKerSpecMap
import ModularCurves.GroupScheme.PatchHopf
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# L-BC: `E[N] ⟶ S` is formally unramified when `N` is invertible (BB-DIFF, the fibre leg)

The [T-B6′]-fill session's `hfib` discharge (CHARTER-Y1-CLOSER S2; board v10.123/124-CASCADE):
the residue-field fibres of `E.torsionπ N` are formally unramified, hence — through the
pre-wired T-DISC funnel — so is `E[N] ⟶ S` itself.

**The fibre-level core is the augmentation-ideal rigidity of torsion** (KM 2.3.1 p. 74, in
infinitesimal form; no invariant differentials, no degree counts): over a field `k`, a point
`D` of `E` that (i) reduces to the zero section along a square-zero thickening `R ↠ R/I` and
(ii) is killed by an `N` invertible in `k`, is the zero point. Route: `D` factors through an
affine chart `U ∋ e` and its comorphism sends the augmentation ideal `J = ker (ε : Γ(U) → k)`
into `I`; on such points, evaluation at `J` is *additive* — the co-multiplication satisfies
`μ♯ f ≡ f ⊗ 1 + 1 ⊗ f mod J ⊗ J` (the counit laws), and `J ⊗ J`-terms die in `I² = 0` — so
`N • D = 0` forces `N · D♯(f) = 0`, and `N ∈ k˟` forces `D♯(J) = 0`, i.e. `D` *is* the zero
section. This gives `Torsionπ.formallyUnramified_of_isUnit` over every field via
`FormallyUnramified.of_hom_ext`, and `Torsionπ.formallyUnramified_of_nIsInvertible` (= L-BC)
over every base via `FormallyUnramified.of_finite_fiberToSpecResidueField` (T-DISC) +
`torsion_baseChange_isPullback`.

The three `Point`-restriction lemmas at the head are relocated byte-identically from
`MulByHomUnramified.lean` (which now imports this file; pointer comments at the old site) —
they are needed on both sides of the L-A/L-BC split.
-/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

open scoped TensorProduct

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

namespace EllipticCurve

variable {S : Scheme.{u}} (E : EllipticCurve S)

/-- `pointEquivOverHom` carries point-subtraction to the division of `Over`-homs (companion to
`pointEquivOverHom_add`). -/
theorem pointEquivOverHom_sub {T : Scheme.{u}} (g : T ⟶ S) (P Q : E.Point g) :
    letI : CommGroup (Over.mk g ⟶ E.asOver) := Hom.commGroup
    (E.pointEquivOverHom g) (P - Q) =
      (E.pointEquivOverHom g) P / (E.pointEquivOverHom g) Q := rfl

/-- Restriction of a point along `k` corresponds, under `pointEquivOverHom`, to precomposition by
the induced `Over`-morphism `Over.mk (k ≫ g) ⟶ Over.mk g`. -/
theorem pointEquivOverHom_restrict {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P : E.Point g) :
    E.pointEquivOverHom (k ≫ g) (Point.restrict E k P) =
      (Over.homMk k : Over.mk (k ≫ g) ⟶ Over.mk g) ≫ E.pointEquivOverHom g P := by
  apply Over.OverMorphism.ext
  simp only [pointEquivOverHom, Equiv.coe_fn_mk, Point.restrict, Over.comp_left, Over.homMk_left]
  rfl

/-- `Point.restrict` is additive on subtraction (precomposition is a group homomorphism). -/
theorem restrict_sub {T T' : Scheme.{u}} {g : T ⟶ S} (k : T' ⟶ T) (P Q : E.Point g) :
    Point.restrict E k (P - Q) = Point.restrict E k P - Point.restrict E k Q := by
  apply (E.pointEquivOverHom (k ≫ g)).injective
  simp only [E.pointEquivOverHom_restrict, E.pointEquivOverHom_sub, GrpObj.comp_div]

section AugmentationAlgebra

/-! ### The pure-algebra layer of the L-BC core

Everything scheme-free about the augmentation argument, over an abstract base ring `k'`
(instantiated at `Γ(Spec k, ⊤)`): two `k'`-algebra maps `p₁ p₂ : C → R` that agree with the
augmentation `algebraMap ∘ ε` modulo an ideal `I` with `I·I = 0` satisfy the **key identity**

  `lift p₁ p₂ x = p₂ (r₁ x) + p₁ (r₂ x) − algebraMap (fold x)`   (`pairLift_key`)

where `r₁, r₂ : C ⊗ C → C` are the two axis restrictions and `fold = ε ⊗ ε`. On a pure tensor
the difference of the two sides is `(p₁ c − alg (ε c)) · (p₂ c' − alg (ε c')) ∈ I·I = 0` — the
`𝔴`-operator computation that replaces every flatness/splitting argument. -/

variable {k' C R : Type u} [CommRing k'] [CommRing C] [CommRing R]
  [Algebra k' C] [Algebra k' R]

/-- The left axis restriction `C ⊗ C → C`, `c ⊗ c' ↦ ε(c)·c'`. -/
private noncomputable def axisL (ε : C →ₐ[k'] k') : C ⊗[k'] C →ₐ[k'] C :=
  Algebra.TensorProduct.lift ((Algebra.ofId k' C).comp ε) (AlgHom.id k' C)
    fun _ _ ↦ Commute.all _ _

/-- The right axis restriction `C ⊗ C → C`, `c ⊗ c' ↦ c·ε(c')`. -/
private noncomputable def axisR (ε : C →ₐ[k'] k') : C ⊗[k'] C →ₐ[k'] C :=
  Algebra.TensorProduct.lift (AlgHom.id k' C) ((Algebra.ofId k' C).comp ε)
    fun _ _ ↦ Commute.all _ _

/-- The double augmentation `C ⊗ C → k'`. -/
private noncomputable def foldε (ε : C →ₐ[k'] k') : C ⊗[k'] C →ₐ[k'] k' :=
  Algebra.TensorProduct.lift ε ε fun _ _ ↦ Commute.all _ _

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
    Algebra.TensorProduct.lift p₁ p₂ (fun _ _ ↦ Commute.all _ _) x =
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
  refine RingHom.ext fun x ↦ ?_
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
    Algebra.TensorProduct.lift p₁ p₂ (fun _ _ ↦ Commute.all _ _) x = 0 := by
  have hfold : foldε ε x = 0 := by rw [foldε_eq_axisL, hx₁, map_zero]
  rw [pairLift_key ε p₁ p₂ h₁ h₂ hII, hx₁, hx₂, hfold, map_zero, map_zero, map_zero]
  ring

end AugmentationAlgebra

section AugmentationScheme

/-! ### The scheme layer of the L-BC core

The kernel-of-reduction points of `E/Spec k` all factor through one affine chart `U` at the
zero section; their chart comorphisms are `I`-close to the augmentation, and evaluation on
the augmentation ideal is additive (`pointSharp_add`, through the affine Künneth box and the
key identity of the algebra layer). `N • D = 0` then forces the comorphism of `D` to *be*
the augmentation, i.e. `D` is the zero point. -/

variable {S : Scheme.{u}}

/-- `Point.restrict` sends zero to zero. -/
theorem restrict_zero (E : EllipticCurve S) {T T' : Scheme.{u}} {g : T ⟶ S} (m : T' ⟶ T) :
    Point.restrict E m (0 : E.Point g) = 0 := by
  refine Subtype.ext ?_
  show m ≫ ((0 : E.Point g) : T ⟶ E.E) = ((0 : E.Point (m ≫ g)) : T' ⟶ E.E)
  rw [E.point_zero_val, E.point_zero_val, ← Category.assoc]

/-- `Point.restrict` is additive. -/
theorem restrict_add (E : EllipticCurve S) {T T' : Scheme.{u}} {g : T ⟶ S} (m : T' ⟶ T)
    (P Q : E.Point g) :
    Point.restrict E m (P + Q) = Point.restrict E m P + Point.restrict E m Q := by
  have h : P + Q = P - (0 - Q) := by abel
  rw [h, E.restrict_sub, E.restrict_sub, restrict_zero]
  abel

/-- The underlying morphism of a point sum, through `pointEquivOverHom_add` (the
`Hom.commGroup` multiplication made explicit). -/
theorem point_add_val_mu (E : EllipticCurve S) {T : Scheme.{u}} {g : T ⟶ S}
    (P Q : E.Point g) :
    ((P + Q : E.Point g) : T ⟶ E.E) =
      (lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)).left ≫
        (μ[E.asOver]).left :=
  (congrArg CommaMorphism.left (E.pointEquivOverHom_add g P Q)).trans
    (Over.comp_left _ _ _ _ _)

/-- First projection of the pairing of two points. -/
theorem point_pair_left_fst (E : EllipticCurve S) {T : Scheme.{u}} {g : T ⟶ S}
    (P Q : E.Point g) :
    (lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)).left ≫
      pullback.fst E.asOver.hom E.asOver.hom = P.1 :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst _ _))

/-- Second projection of the pairing of two points. -/
theorem point_pair_left_snd (E : EllipticCurve S) {T : Scheme.{u}} {g : T ⟶ S}
    (P Q : E.Point g) :
    (lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)).left ≫
      pullback.snd E.asOver.hom E.asOver.hom = Q.1 :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_snd _ _))

variable {k : Type u} [Field k] {F : EllipticCurve (Spec (CommRingCat.of k))}
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
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec (CommRingCat.of k)} {w : Spec R ⟶ F.E}
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
  w.appLE U ⊤ (fun x _ ↦ hw x) ≫ (Scheme.ΓSpecIso R).hom

/-- Morphisms into `E` landing in the affine chart are determined by their chart
comorphism (`IsAffineOpen.SpecMap_appLE_fromSpec` recovery). -/
private theorem eq_of_pointSharp_eq {U : (F.E).Opens} (hU : IsAffineOpen U)
    {w w' : Spec R ⟶ F.E} (hw : ∀ x : ↑(Spec R), w.base x ∈ U)
    (hw' : ∀ x : ↑(Spec R), w'.base x ∈ U)
    (h : pointSharp w hw = pointSharp w' hw') : w = w' := by
  have happ : w.appLE U ⊤ (fun x _ ↦ hw x) = w'.appLE U ⊤ (fun x _ ↦ hw' x) := by
    have := congrArg (· ≫ (Scheme.ΓSpecIso R).inv) h
    simpa [pointSharp] using this
  have h1 := hU.SpecMap_appLE_fromSpec w (isAffineOpen_top (Spec R)) (fun x _ ↦ hw x)
  have h2 := hU.SpecMap_appLE_fromSpec w' (isAffineOpen_top (Spec R)) (fun x _ ↦ hw' x)
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
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    (t : Spec R ⟶ Spec (CommRingCat.of k))
    (hz : ∀ x : ↑(Spec R), ((0 : F.Point t) : Spec R ⟶ F.E).base x ∈ U)
    (f : Γ(F.E, U)) :
    pointSharp ((0 : F.Point t) : Spec R ⟶ F.E) hz f =
      (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom)
        (F.zero.appLE U ⊤ (fun x _ ↦ heU x) f) := by
  have hz' : ∀ x : ↑(Spec R), (t ≫ F.zero).base x ∈ U := by
    intro x
    simpa using heU (t.base x)
  rw [pointSharp_congr (F.point_zero_val t) hz hz']
  show ((t ≫ F.zero).appLE U ⊤ _ ≫ (Scheme.ΓSpecIso R).hom) f = _
  rw [← Scheme.Hom.appLE_comp_appLE t F.zero U ⊤ ⊤ (fun x _ ↦ heU x) le_top]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The chart comorphism of a point over `t` restricts along `π` to the `t`-comorphism. -/
private theorem pointSharp_comp_π {U : (F.E).Opens}
    {t : Spec R ⟶ Spec (CommRingCat.of k)} (P : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (c : Γ(Spec (CommRingCat.of k), ⊤)) :
    pointSharp P.1 hp (F.π.appLE ⊤ U (fun _ _ ↦ trivial) c) =
      (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom) c := by
  show ((F.π.appLE ⊤ U _ ≫ P.1.appLE U ⊤ _) ≫ (Scheme.ΓSpecIso R).hom) c = _
  rw [Scheme.Hom.appLE_comp_appLE P.1 F.π ⊤ U ⊤ _ _,
    appLE_congr_hom P.2 ⊤ ⊤]

set_option backward.isDefEq.respectTransparency.types false in
/-- The augmentation retracts the structure map: `ζ ∘ π♯ = id` (`Γ`-dual of `zero ≫ π = 𝟙`). -/
private theorem zero_appLE_π_appLE {U : (F.E).Opens}
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    (c : Γ(Spec (CommRingCat.of k), ⊤)) :
    F.zero.appLE U ⊤ (fun x _ ↦ heU x) (F.π.appLE ⊤ U (fun _ _ ↦ trivial) c) = c := by
  show (F.π.appLE ⊤ U _ ≫ F.zero.appLE U ⊤ _) c = c
  rw [Scheme.Hom.appLE_comp_appLE F.zero F.π ⊤ U ⊤ _ _,
    appLE_congr_hom F.zero_π ⊤ ⊤,
    appLE_id]
  rfl


section Box

variable {U : (F.E).Opens}

/-- The chart's `k'`-algebra structure via the structure morphism. -/
private noncomputable local instance chartAlgebra :
    Algebra ↑Γ(Spec (CommRingCat.of k), ⊤) ↑Γ(F.E, U) :=
  (F.π.appLE ⊤ U (fun _ _ ↦ trivial)).hom.toAlgebra

private theorem chartAlgebra_ofHom :
    CommRingCat.ofHom (algebraMap ↑Γ(Spec (CommRingCat.of k), ⊤) ↑Γ(F.E, U)) =
      F.π.appLE ⊤ U (fun _ _ ↦ trivial) := rfl

/-- The affine Künneth box of the chart (`patchKunneth`, consumed from NEW-HOPF's
`PatchKunneth.lean`). -/
private noncomputable def boxIso (hU : IsAffineOpen U) :
    pullback (F.π.resLE ⊤ U (fun _ _ ↦ trivial)) (F.π.resLE ⊤ U (fun _ _ ↦ trivial)) ≅
      Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))) :=
  patchKunneth F.π F.π (isAffineOpen_top _) hU hU chartAlgebra_ofHom chartAlgebra_ofHom

/-- The box sits inside the fibre square of `E`. -/
private noncomputable def boxι :
    (pullback (F.π.resLE ⊤ U (fun _ _ ↦ trivial))
      (F.π.resLE ⊤ U (fun _ _ ↦ trivial)) : Scheme) ⟶ pullback F.π F.π :=
  pullback.map _ _ _ _ U.ι U.ι (⊤ : (Spec (CommRingCat.of k)).Opens).ι
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
  have h0 := hU.SpecMap_appLE_fromSpec w (isAffineOpen_top (Spec R)) (fun x _ ↦ hw x)
  rw [IsAffineOpen.fromSpec_top] at h0
  have hfromSpec : hU.fromSpec = hU.isoSpec.inv ≫ U.ι := rfl
  have hw' : (Spec R).isoSpec.hom ≫ Spec.map (w.appLE U ⊤ (fun x _ ↦ hw x)) ≫
      hU.fromSpec = w := by
    rw [h0, Iso.hom_inv_id_assoc]
  have hlift : liftU hw = (Spec R).isoSpec.hom ≫
      Spec.map (w.appLE U ⊤ (fun x _ ↦ hw x)) ≫ hU.isoSpec.inv := by
    rw [← cancel_mono U.ι, liftU_ι hw]
    rw [show ((Spec R).isoSpec.hom ≫ Spec.map (w.appLE U ⊤ (fun x _ ↦ hw x)) ≫
        hU.isoSpec.inv) ≫ U.ι = (Spec R).isoSpec.hom ≫
        Spec.map (w.appLE U ⊤ (fun x _ ↦ hw x)) ≫ hU.fromSpec from by
      rw [hfromSpec]; simp only [Category.assoc]]
    exact hw'.symm
  rw [hlift, ← hU.isoSpec_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The pairing of two points through the box. -/
private noncomputable def pairBox {t : Spec R ⟶ Spec (CommRingCat.of k)} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    Spec R ⟶ pullback (F.π.resLE ⊤ U (fun _ _ ↦ trivial))
      (F.π.resLE ⊤ U (fun _ _ ↦ trivial)) :=
  pullback.lift (liftU hp) (liftU hq) (by
    rw [← cancel_mono (⊤ : (Spec (CommRingCat.of k)).Opens).ι]
    simp only [Category.assoc, Scheme.Hom.resLE_comp_ι]
    rw [← Category.assoc, ← Category.assoc, liftU_ι, liftU_ι, P.2, Q.2])

private theorem pairBox_fst {t : Spec R ⟶ Spec (CommRingCat.of k)} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    pairBox P Q hp hq ≫ pullback.fst _ _ = liftU hp :=
  pullback.lift_fst _ _ _

private theorem pairBox_snd {t : Spec R ⟶ Spec (CommRingCat.of k)} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    pairBox P Q hp hq ≫ pullback.snd _ _ = liftU hq :=
  pullback.lift_snd _ _ _

/-- The pairing of `Hom.commGroup` is the box pairing followed by the box inclusion. -/
private theorem pairing_eq_pairBox {t : Spec R ⟶ Spec (CommRingCat.of k)} (P Q : F.Point t)
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
    {t : Spec R ⟶ Spec (CommRingCat.of k)} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    pairBox P Q hp hq ≫ (boxIso hU).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
          (R := ↑Γ(Spec (CommRingCat.of k), ⊤)) (A := ↑Γ(F.E, U)) (B := ↑Γ(F.E, U)))) =
      Spec.map (pointSharp P.1 hp) := by
  rw [boxIso, patchKunneth_hom_comp_includeLeft, ← Category.assoc, pairBox_fst,
    liftU_toSpecΓ hU]

set_option backward.isDefEq.respectTransparency.types false in
/-- The right leg of the Künneth identification of the pairing. -/
private theorem pairBox_boxIso_includeRight (hU : IsAffineOpen U)
    {t : Spec R ⟶ Spec (CommRingCat.of k)} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U) :
    pairBox P Q hp hq ≫ (boxIso hU).hom ≫
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight
          (R := ↑Γ(Spec (CommRingCat.of k), ⊤)) (A := ↑Γ(F.E, U))
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
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    (hz : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U) :
    pointSharp (R := Γ(F.E, U)) ((0 : F.Point (hU.fromSpec ≫ F.π)) : _ ⟶ F.E) hz =
      F.zero.appLE U ⊤ (fun x _ ↦ heU x) ≫ F.π.appLE ⊤ U (fun _ _ ↦ trivial) := by
  refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
  have h0 := pointSharp_zero_point (R := Γ(F.E, U)) heU (hU.fromSpec ≫ F.π) hz c
  rw [h0]
  show ((hU.fromSpec ≫ F.π).appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso Γ(F.E, U)).hom)
      (F.zero.appLE U ⊤ (fun x _ ↦ heU x) c) = _
  rw [← Scheme.Hom.appLE_comp_appLE hU.fromSpec F.π ⊤ U ⊤ (fun _ _ ↦ trivial)
    (fun x _ ↦ htaut x)]
  show (pointSharp (R := Γ(F.E, U)) hU.fromSpec htaut)
      ((F.π.appLE ⊤ U (fun _ _ ↦ trivial)) (F.zero.appLE U ⊤ (fun x _ ↦ heU x) c)) = _
  rw [pointSharp_fromSpec hU htaut]
  rfl

/-- The Künneth identification of the pairing, map form (instance-free statement: the
target ring map is characterised by its two inclusion legs). -/
private theorem pairBox_boxIso_eq_specMap (hU : IsAffineOpen U)
    {t : Spec R ⟶ Spec (CommRingCat.of k)} (P Q : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (hq : ∀ x : ↑(Spec R), (Q.1).base x ∈ U)
    {pT : CommRingCat.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U)) ⟶ R}
    (hL : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ↑Γ(Spec (CommRingCat.of k), ⊤))) ≫ pT = pointSharp P.1 hp)
    (hR : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := ↑Γ(Spec (CommRingCat.of k), ⊤)) (A := ↑Γ(F.E, U))).toRingHom ≫ pT =
      pointSharp Q.1 hq) :
    pairBox P Q hp hq ≫ (boxIso hU).hom = Spec.map pT := by
  have hu : pairBox P Q hp hq ≫ (boxIso hU).hom =
      Spec.map (Spec.preimage (pairBox P Q hp hq ≫ (boxIso hU).hom)) :=
    (Spec.map_preimage _).symm
  rw [hu]
  refine congrArg Spec.map ?_
  have hLu : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := ↑Γ(Spec (CommRingCat.of k), ⊤))) ≫
        Spec.preimage (pairBox P Q hp hq ≫ (boxIso hU).hom) = pointSharp P.1 hp := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, Spec.map_preimage, ← pairBox_boxIso_includeLeft hU P Q hp hq,
      Category.assoc]
  have hRu : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
      (R := ↑Γ(Spec (CommRingCat.of k), ⊤)) (A := ↑Γ(F.E, U))).toRingHom ≫
        Spec.preimage (pairBox P Q hp hq ≫ (boxIso hU).hom) = pointSharp Q.1 hq := by
    refine Spec.map_injective ?_
    rw [Spec.map_comp, Spec.map_preimage, ← pairBox_boxIso_includeRight hU P Q hp hq,
      Category.assoc]
  refine CommRingCat.hom_ext (tensor_ringHom_ext (fun a ↦ ?_) (fun b ↦ ?_))
  · have h1 := congrArg (fun (m : _ ⟶ R) ↦ m.hom a) (hLu.trans hL.symm)
    exact h1
  · have h1 := congrArg (fun (m : _ ⟶ R) ↦ m.hom b) (hRu.trans hR.symm)
    exact h1

/-- The augmentation of the chart, as an algebra map over the base sections. -/
private noncomputable def chartAug
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U) :
    ↑Γ(F.E, U) →ₐ[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(Spec (CommRingCat.of k), ⊤) :=
  { toRingHom := (F.zero.appLE U ⊤ (fun x _ ↦ heU x)).hom
    commutes' := fun c ↦ zero_appLE_π_appLE heU c }

set_option backward.isDefEq.respectTransparency.types false in
/-- **The left axis law, `Spec` form**: `Spec` of the left axis restriction, through the
Künneth box and the multiplication, is the tautological chart inclusion (the geometric
content of `0 + X = X`). -/
private theorem axisL_spec_law (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    (htaut : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    (hz : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U) :
    Spec.map (CommRingCat.ofHom (axisL (chartAug heU)).toRingHom) ≫ (boxIso hU).inv ≫
        boxι ≫ (μ[F.asOver]).left = hU.fromSpec := by
  have hident : pairBox (0 : F.Point (hU.fromSpec ≫ F.π)) (tautPoint hU) hz htaut ≫
      (boxIso hU).hom = Spec.map (CommRingCat.ofHom (axisL (chartAug heU)).toRingHom) := by
    refine pairBox_boxIso_eq_specMap hU _ _ hz htaut ?_ ?_
    · rw [pointSharp_zero_taut hU heU htaut hz]
      refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
      show axisL (chartAug heU) (c ⊗ₜ 1) = _
      rw [axisL_tmul, _root_.mul_one]
      rfl
    · rw [pointSharp_congr (show ((tautPoint hU : F.Point (hU.fromSpec ≫ F.π)) :
          Spec Γ(F.E, U) ⟶ F.E) = hU.fromSpec from rfl) htaut htaut,
        pointSharp_fromSpec hU htaut]
      refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
      show axisL (chartAug heU) (1 ⊗ₜ c) = c
      rw [axisL_tmul, map_one, map_one, _root_.one_mul]
  rw [← hident]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← pairing_eq_pairBox]
  exact zero_pairing_mul hU

set_option backward.isDefEq.respectTransparency.types false in
/-- **The right axis law, `Spec` form** (the geometric content of `X + 0 = X`). -/
private theorem axisR_spec_law (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
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
      refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
      show axisR (chartAug heU) (c ⊗ₜ 1) = c
      rw [axisR_tmul, map_one, map_one, _root_.mul_one]
    · rw [pointSharp_zero_taut hU heU htaut hz]
      refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
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
      (fun x _ ↦ hcomp x) ≫ (Scheme.ΓSpecIso R').hom := by
    rw [pointSharp, Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← appLE_top_top (Spec.map g),
      Scheme.Hom.appLE_comp_appLE]
  rw [hnat]
  rfl

/-- `Spec` of a commuting `CommRingCat` square, composed with a classified base leg
(abstract objects: no localization unfolds). -/
private theorem specMap_square_comp {A B C D : CommRingCat.{u}} {f : A ⟶ B} {g : B ⟶ C}
    {f' : A ⟶ D} {g' : D ⟶ C} (hsq : f ≫ g = f' ≫ g') {X : Scheme.{u}}
    {q : Spec A ⟶ X} {m : Spec D ⟶ X} (hq : Spec.map f' ≫ q = m) :
    Spec.map g ≫ Spec.map f ≫ q = Spec.map g' ≫ m := by
  rw [← hq, ← Category.assoc, ← Spec.map_comp, hsq, Spec.map_comp, Category.assoc]

/-- The abstract localization package for the `pointSharp_add` tail: the two localizations
(at the double-augmentation prime of the box ring and at the augmentation prime of the
chart ring) exported as OPAQUE `CommRingCat` objects carrying exactly the facts the tail
consumes. The tail's `pointSharp` elaborations then never unfold a localization — the
`whnf` wall of the ledger stops at the fvars. -/
private structure AugLocPackage {U : (F.E).Opens} (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    [Algebra ↑Γ(Spec (CommRingCat.of k), ⊤) ↑R]
    [hker : (RingHom.ker (foldε (chartAug heU)).toRingHom).IsPrime]
    [hkerε : (RingHom.ker (chartAug heU).toRingHom).IsPrime]
    (pT : ↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U) →ₐ[↑Γ(Spec
      (CommRingCat.of k), ⊤)] ↑R)
    (q : Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))) ⟶ F.E) where
  L : CommRingCat.{u}
  LεL : CommRingCat.{u}
  LεR : CommRingCat.{u}
  algL : CommRingCat.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U)) ⟶ L
  algLεL : Γ(F.E, U) ⟶ LεL
  algLεR : Γ(F.E, U) ⟶ LεR
  φL : L ⟶ R
  aL : L ⟶ LεL
  aR : L ⟶ LεR
  hφLalg : ∀ y, φL.hom (algL.hom y) = pT y
  hrangeL : ∀ x : ↑(Spec L), (Spec.map algL ≫ q).base x ∈ U
  hsurj : ∀ a : ↑L, ∃ (y : ↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))
    (sden : (RingHom.ker (foldε (chartAug heU)).toRingHom).primeCompl),
    a * algL.hom ↑sden = algL.hom y
  haLalg : ∀ y, aL.hom (algL.hom y) = algLεL.hom ((axisL (chartAug heU)) y)
  haRalg : ∀ y, aR.hom (algL.hom y) = algLεR.hom ((axisR (chartAug heU)) y)
  hkerLεL : ∀ c : ↑Γ(F.E, U), algLεL.hom c = 0 →
    ∃ u : (RingHom.ker (chartAug heU).toRingHom).primeCompl, (u : ↑Γ(F.E, U)) * c = 0
  hkerLεR : ∀ c : ↑Γ(F.E, U), algLεR.hom c = 0 →
    ∃ u : (RingHom.ker (chartAug heU).toRingHom).primeCompl, (u : ↑Γ(F.E, U)) * c = 0
  haxSpecL : Spec.map aL ≫ Spec.map algL ≫ q = Spec.map algLεL ≫ hU.fromSpec
  haxSpecR : Spec.map aR ≫ Spec.map algL ≫ q = Spec.map algLεR ≫ hU.fromSpec

/-- One axis-side of the chart-prime localization data (fields abstract for the tail). -/
private structure EpsHalf {U : (F.E).Opens} (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    [hker : (RingHom.ker (foldε (chartAug heU)).toRingHom).IsPrime]
    [hkerε : (RingHom.ker (chartAug heU).toRingHom).IsPrime]
    (ax : ↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U) →ₐ[↑Γ(Spec
      (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))
    (q : Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))) ⟶ F.E)
    where
  Lε : CommRingCat.{u}
  algLε : Γ(F.E, U) ⟶ Lε
  a : CommRingCat.of (Localization.AtPrime
    (RingHom.ker (foldε (chartAug heU)).toRingHom)) ⟶ Lε
  halg : ∀ y, a.hom (algebraMap _ (Localization.AtPrime
      (RingHom.ker (foldε (chartAug heU)).toRingHom)) y) = algLε.hom (ax y)
  hker' : ∀ c : ↑Γ(F.E, U), algLε.hom c = 0 →
    ∃ u : (RingHom.ker (chartAug heU).toRingHom).primeCompl, (u : ↑Γ(F.E, U)) * c = 0
  hspec : Spec.map a ≫ Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.AtPrime
    (RingHom.ker (foldε (chartAug heU)).toRingHom)))) ≫ q = Spec.map algLε ≫ hU.fromSpec

/-- The commuting square of the axis localization map (own heartbeat budget). -/
private theorem epsHalf_square {U : (F.E).Opens}
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    [hker : (RingHom.ker (foldε (chartAug heU)).toRingHom).IsPrime]
    [hkerε : (RingHom.ker (chartAug heU).toRingHom).IsPrime]
    (ax : ↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U) →ₐ[↑Γ(Spec
      (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))
    (hcompat : (RingHom.ker (foldε (chartAug heU)).toRingHom).primeCompl ≤
      Submonoid.comap ax.toRingHom (RingHom.ker (chartAug heU).toRingHom).primeCompl) :
    CommRingCat.ofHom (algebraMap (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)]
        ↑Γ(F.E, U)) (Localization.AtPrime
      (RingHom.ker (foldε (chartAug heU)).toRingHom))) ≫
      CommRingCat.ofHom (IsLocalization.map
        (M := (RingHom.ker (foldε (chartAug heU)).toRingHom).primeCompl)
        (T := (RingHom.ker (chartAug heU).toRingHom).primeCompl)
        (Localization.AtPrime (RingHom.ker (chartAug heU).toRingHom))
        ax.toRingHom hcompat) =
    CommRingCat.ofHom ax.toRingHom ≫ CommRingCat.ofHom (algebraMap ↑Γ(F.E, U)
      (Localization.AtPrime (RingHom.ker (chartAug heU).toRingHom))) := by
  have hraw : (IsLocalization.map
      (M := (RingHom.ker (foldε (chartAug heU)).toRingHom).primeCompl)
      (T := (RingHom.ker (chartAug heU).toRingHom).primeCompl)
      (Localization.AtPrime (RingHom.ker (chartAug heU).toRingHom))
      ax.toRingHom hcompat).comp (algebraMap (↑Γ(F.E, U) ⊗[↑Γ(Spec
        (CommRingCat.of k), ⊤)] ↑Γ(F.E, U)) (Localization.AtPrime
        (RingHom.ker (foldε (chartAug heU)).toRingHom))) =
      (algebraMap ↑Γ(F.E, U) (Localization.AtPrime
        (RingHom.ker (chartAug heU).toRingHom))).comp ax.toRingHom :=
    IsLocalization.map_comp hcompat
  rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hraw]

/-- Constructor of one axis-side (own heartbeat budget; generic in the axis map). -/
private theorem epsHalf_exists {U : (F.E).Opens} (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    [hker : (RingHom.ker (foldε (chartAug heU)).toRingHom).IsPrime]
    [hkerε : (RingHom.ker (chartAug heU).toRingHom).IsPrime]
    (ax : ↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U) →ₐ[↑Γ(Spec
      (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))
    {q : Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))) ⟶ F.E}
    (hcompat : (RingHom.ker (foldε (chartAug heU)).toRingHom).primeCompl ≤
      Submonoid.comap ax.toRingHom (RingHom.ker (chartAug heU).toRingHom).primeCompl)
    (haxq : Spec.map (CommRingCat.ofHom ax.toRingHom) ≫ q = hU.fromSpec) :
    Nonempty (EpsHalf hU heU ax q) := by
  classical
  refine ⟨⟨CommRingCat.of (Localization.AtPrime
      (RingHom.ker (chartAug heU).toRingHom)),
    CommRingCat.ofHom (algebraMap ↑Γ(F.E, U) (Localization.AtPrime
      (RingHom.ker (chartAug heU).toRingHom))),
    CommRingCat.ofHom (IsLocalization.map
      (M := (RingHom.ker (foldε (chartAug heU)).toRingHom).primeCompl)
      (T := (RingHom.ker (chartAug heU).toRingHom).primeCompl)
      (Localization.AtPrime (RingHom.ker (chartAug heU).toRingHom))
      ax.toRingHom hcompat),
    fun y ↦ IsLocalization.map_eq hcompat y,
    fun c hc ↦ (IsLocalization.map_eq_zero_iff
      (RingHom.ker (chartAug heU).toRingHom).primeCompl _ _).mp hc,
    specMap_square_comp (epsHalf_square heU ax hcompat) haxq⟩⟩

/-- Constructor of the localization package (own heartbeat budget: every localization
unfolding happens here, in a small context). -/
private theorem augLocPackage_exists {U : (F.E).Opens} (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    [Algebra ↑Γ(Spec (CommRingCat.of k), ⊤) ↑R]
    [hker : (RingHom.ker (foldε (chartAug heU)).toRingHom).IsPrime]
    [hkerε : (RingHom.ker (chartAug heU).toRingHom).IsPrime]
    (pT : ↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U) →ₐ[↑Γ(Spec
      (CommRingCat.of k), ⊤)] ↑R)
    (hunits : ∀ y : (RingHom.ker (foldε (chartAug heU)).toRingHom).primeCompl,
      IsUnit (pT y))
    {q : Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))) ⟶ F.E}
    (hqp : q.base ⟨RingHom.ker (foldε (chartAug heU)).toRingHom, hker⟩ ∈ U)
    (haxLq : Spec.map (CommRingCat.ofHom (axisL (chartAug heU)).toRingHom) ≫ q =
      hU.fromSpec)
    (haxRq : Spec.map (CommRingCat.ofHom (axisR (chartAug heU)).toRingHom) ≫ q =
      hU.fromSpec) :
    Nonempty (AugLocPackage hU heU pT q) := by
  classical
  set ε' := chartAug heU with hε'
  set p𝔭 : ↑(Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U)))) :=
    ⟨RingHom.ker (foldε ε').toRingHom, hε' ▸ hker⟩ with hp𝔭
  set L := CommRingCat.of (Localization.AtPrime (RingHom.ker (foldε ε').toRingHom))
    with hLdef
  set algL : CommRingCat.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U)) ⟶
      L := CommRingCat.ofHom
    (algebraMap _ (Localization.AtPrime (RingHom.ker (foldε ε').toRingHom))) with halgL
  set φL : ↑L →+* ↑R := IsLocalization.lift
    (M := (RingHom.ker (foldε ε').toRingHom).primeCompl) (g := pT.toRingHom) hunits
    with hφLdef
  have hφLalg : ∀ y, φL (algL.hom y) = pT y := fun y ↦ IsLocalization.lift_eq hunits y
  have hrangeL : ∀ x : ↑(Spec L), (Spec.map algL ≫ q).base x ∈ U := by
    intro x
    have hle : ((Spec.map algL).base x).asIdeal ≤ p𝔭.asIdeal := by
      intro a ha
      by_contra hnot
      have hu : IsUnit (algL.hom a) := IsLocalization.map_units
        (M := (RingHom.ker (foldε ε').toRingHom).primeCompl) _ ⟨a, hnot⟩
      exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ ha hu)
    have hspec : ((Spec.map algL).base x) ⤳ p𝔭 :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hle
    have hspec2 : (q.base ((Spec.map algL).base x)) ⤳ (q.base p𝔭) :=
      hspec.map q.continuous
    exact hspec2.mem_open U.2 hqp
  have hcompatL : (RingHom.ker (foldε ε').toRingHom).primeCompl ≤
      Submonoid.comap (axisL ε').toRingHom (RingHom.ker ε'.toRingHom).primeCompl := by
    intro y hy h0
    refine hy (RingHom.mem_ker.mpr ?_)
    have h1 : ε' ((axisL ε') y) = 0 := RingHom.mem_ker.mp h0
    rw [show (foldε ε').toRingHom y = ε' ((axisL ε') y) from foldε_eq_axisL ε' y, h1]
  have hcompatR : (RingHom.ker (foldε ε').toRingHom).primeCompl ≤
      Submonoid.comap (axisR ε').toRingHom (RingHom.ker ε'.toRingHom).primeCompl := by
    intro y hy h0
    refine hy (RingHom.mem_ker.mpr ?_)
    have h1 : ε' ((axisR ε') y) = 0 := RingHom.mem_ker.mp h0
    rw [show (foldε ε').toRingHom y = ε' ((axisR ε') y) from foldε_eq_axisR ε' y, h1]
  obtain ⟨eL⟩ := epsHalf_exists hU heU (axisL ε') hcompatL haxLq
  obtain ⟨eR⟩ := epsHalf_exists hU heU (axisR ε') hcompatR haxRq
  refine ⟨⟨L, eL.Lε, eR.Lε, algL, eL.algLε, eR.algLε, CommRingCat.ofHom φL, eL.a, eR.a,
    hφLalg, hrangeL, ?_, eL.halg, eR.halg, eL.hker', eR.hker', eL.hspec, eR.hspec⟩⟩
  intro a
  obtain ⟨⟨y, sden⟩, hys⟩ := IsLocalization.surj
    (M := (RingHom.ker (foldε ε').toRingHom).primeCompl) a
  exact ⟨y, sden, hys⟩

/-- **The hoisted tail of `pointSharp_add`** (6e′–6g): standalone so the localization
`set`s run against a small context (the inline form blows the `whnf` budget). All
box-geometry enters through the five morphism-level hypotheses. -/
private theorem pointSharp_add_tail {U : (F.E).Opens} (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    (htautU : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U)
    [Algebra ↑Γ(Spec (CommRingCat.of k), ⊤) ↑R]
    [hker : (RingHom.ker (foldε (chartAug heU)).toRingHom).IsPrime]
    [hkerε : (RingHom.ker (chartAug heU).toRingHom).IsPrime]
    {t : Spec R ⟶ Spec (CommRingCat.of k)} {P₁ P₂ : F.Point t}
    (hp₁ : ∀ x : ↑(Spec R), (P₁.1).base x ∈ U)
    (hp₂ : ∀ x : ↑(Spec R), (P₂.1).base x ∈ U)
    (hp₁₂ : ∀ x : ↑(Spec R), ((P₁ + P₂ : F.Point t) : Spec R ⟶ F.E).base x ∈ U)
    (p₁ p₂ : ↑Γ(F.E, U) →ₐ[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑R)
    (pT : ↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U) →ₐ[↑Γ(Spec
      (CommRingCat.of k), ⊤)] ↑R)
    (hpTdef : pT = Algebra.TensorProduct.lift p₁ p₂ (fun _ _ ↦ Commute.all _ _))
    (hcl₁ : ∀ c, p₁ c - algebraMap _ ↑R (chartAug heU c) ∈ RingHom.ker φ.hom)
    (hcl₂ : ∀ c, p₂ c - algebraMap _ ↑R (chartAug heU c) ∈ RingHom.ker φ.hom)
    (hII : ∀ a ∈ RingHom.ker φ.hom, ∀ b ∈ RingHom.ker φ.hom, a * b = 0)
    (hunits : ∀ y : (RingHom.ker (foldε (chartAug heU)).toRingHom).primeCompl,
      IsUnit (pT y))
    {q : Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))) ⟶ F.E}
    (hqp : q.base ⟨RingHom.ker (foldε (chartAug heU)).toRingHom, hker⟩ ∈ U)
    (hsum : ((P₁ + P₂ : F.Point t) : Spec R ⟶ F.E) =
      Spec.map (CommRingCat.ofHom pT.toRingHom) ≫ q)
    (haxLq : Spec.map (CommRingCat.ofHom (axisL (chartAug heU)).toRingHom) ≫ q =
      hU.fromSpec)
    (haxRq : Spec.map (CommRingCat.ofHom (axisR (chartAug heU)).toRingHom) ≫ q =
      hU.fromSpec)
    (hidL : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
        (R := ↑Γ(Spec (CommRingCat.of k), ⊤))) ≫ CommRingCat.ofHom pT.toRingHom =
      pointSharp P₁.1 hp₁)
    (hidR : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
        (R := ↑Γ(Spec (CommRingCat.of k), ⊤)) (A := ↑Γ(F.E, U))).toRingHom ≫
        CommRingCat.ofHom pT.toRingHom = pointSharp P₂.1 hp₂)
    (f : Γ(F.E, U)) (hf : F.zero.appLE U ⊤ (fun x _ ↦ heU x) f = 0) :
    pointSharp (P₁ + P₂ : F.Point t).1 hp₁₂ f =
      pointSharp P₁.1 hp₁ f + pointSharp P₂.1 hp₂ f := by
  classical
  obtain ⟨pkg⟩ := augLocPackage_exists hU heU pT hunits hqp haxLq haxRq
  set ε' := chartAug heU with hε'
  have hεf : ε' f = 0 := hf
  -- 6e′ (abstract): the chart evaluation of the localized box point
  set ψ' := pointSharp (Spec.map pkg.algL ≫ q) pkg.hrangeL with hψ'
  -- 6f. the sum's chart evaluation factors through the localization
  have hfacSpec : Spec.map (CommRingCat.ofHom pT.toRingHom) =
      Spec.map pkg.φL ≫ Spec.map pkg.algL := by
    rw [← Spec.map_comp]
    refine congrArg Spec.map ?_
    refine CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_)
    exact (pkg.hφLalg y).symm
  have hkey : pointSharp ((P₁ + P₂ : F.Point t) : Spec R ⟶ F.E) hp₁₂ =
      ψ' ≫ pkg.φL := by
    have hcomp2 : ∀ x : ↑(Spec R),
        (Spec.map pkg.φL ≫ Spec.map pkg.algL ≫ q).base x ∈ U := by
      intro x
      have h0 : (Spec.map pkg.φL ≫ Spec.map pkg.algL ≫ q).base x =
          (Spec.map pkg.algL ≫ q).base ((Spec.map pkg.φL).base x) := rfl
      rw [h0]
      exact pkg.hrangeL _
    rw [pointSharp_congr (show ((P₁ + P₂ : F.Point t) : Spec R ⟶ F.E) =
        Spec.map pkg.φL ≫ Spec.map pkg.algL ≫ q by
      rw [hsum, hfacSpec, Category.assoc]) hp₁₂ hcomp2]
    exact pointSharp_specMap_comp pkg.φL pkg.hrangeL hcomp2
  -- 6g. the axis moves kill the augmentation defect
  have haxψ : ∀ (Lε' : CommRingCat.{u}) (ā : pkg.L ⟶ Lε') (algLε' : Γ(F.E, U) ⟶ Lε')
      (axSpec : Spec.map ā ≫ Spec.map pkg.algL ≫ q = Spec.map algLε' ≫ hU.fromSpec),
      ψ' ≫ ā = pointSharp hU.fromSpec htautU ≫ algLε' := by
    intro Lε' ā algLε' axSpec
    have hcomp3 : ∀ x : ↑(Spec Lε'),
        (Spec.map ā ≫ Spec.map pkg.algL ≫ q).base x ∈ U := by
      intro x
      have h0 : (Spec.map ā ≫ Spec.map pkg.algL ≫ q).base x =
          (Spec.map pkg.algL ≫ q).base ((Spec.map ā).base x) := rfl
      rw [h0]
      exact pkg.hrangeL _
    have h1 := pointSharp_specMap_comp ā pkg.hrangeL hcomp3
    have hcomp4 : ∀ x : ↑(Spec Lε'),
        (Spec.map algLε' ≫ hU.fromSpec).base x ∈ U := by
      intro x
      exact htautU _
    have h2 : pointSharp (Spec.map ā ≫ Spec.map pkg.algL ≫ q) hcomp3 =
        pointSharp (Spec.map algLε' ≫ hU.fromSpec) hcomp4 :=
      pointSharp_congr axSpec hcomp3 hcomp4
    have h3 := pointSharp_specMap_comp algLε' htautU hcomp4
    rw [← h1, h2, h3]
  have haxLψ := haxψ _ pkg.aL pkg.algLεL pkg.haxSpecL
  have haxRψ := haxψ _ pkg.aR pkg.algLεR pkg.haxSpecR
  rw [pointSharp_fromSpec hU htautU, Category.id_comp] at haxLψ haxRψ
  have haxL := congrArg (fun (m : Γ(F.E, U) ⟶ pkg.LεL) ↦ m.hom f) haxLψ
  have haxR := congrArg (fun (m : Γ(F.E, U) ⟶ pkg.LεR) ↦ m.hom f) haxRψ
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at haxL haxR
  -- the defect and its kill
  set a : ↑pkg.L := ψ'.hom f - pkg.algL.hom (f ⊗ₜ 1) - pkg.algL.hom (1 ⊗ₜ f) with hadef
  have haLa : pkg.aL.hom a = 0 := by
    rw [hadef, map_sub, map_sub, pkg.haLalg, pkg.haLalg, haxL, axisL_tmul, axisL_tmul,
      hεf]
    simp only [map_zero, map_one, _root_.one_mul, _root_.mul_one, sub_zero, sub_self]
  have haRa : pkg.aR.hom a = 0 := by
    rw [hadef, map_sub, map_sub, pkg.haRalg, pkg.haRalg, haxR, axisR_tmul, axisR_tmul,
      hεf]
    simp only [map_zero, map_one, mul_zero, _root_.mul_one, sub_self]
  obtain ⟨y, sden, hys⟩ := pkg.hsurj a
  have hyL0 : pkg.algLεL.hom ((axisL ε') y) = 0 := by
    have h1 := congrArg pkg.aL.hom hys
    rw [map_mul, haLa, zero_mul, pkg.haLalg] at h1
    exact h1.symm
  have hyR0 : pkg.algLεR.hom ((axisR ε') y) = 0 := by
    have h1 := congrArg pkg.aR.hom hys
    rw [map_mul, haRa, zero_mul, pkg.haRalg] at h1
    exact h1.symm
  obtain ⟨u, hu⟩ := pkg.hkerLεL _ hyL0
  obtain ⟨v, hv⟩ := pkg.hkerLεR _ hyR0
  set y' := ((1 : ↑Γ(F.E, U)) ⊗ₜ[↑Γ(Spec (CommRingCat.of k), ⊤)] (u : ↑Γ(F.E, U))) *
    ((((v : ↑Γ(F.E, U)) ⊗ₜ[↑Γ(Spec (CommRingCat.of k), ⊤)] (1 : ↑Γ(F.E, U)))) * y)
    with hy'
  have haxLy' : (axisL ε') y' = 0 := by
    rw [hy', map_mul, map_mul, axisL_tmul, axisL_tmul]
    linear_combination (algebraMap _ ↑Γ(F.E, U) (ε' (1 : ↑Γ(F.E, U))) *
      algebraMap _ ↑Γ(F.E, U) (ε' (v : ↑Γ(F.E, U)))) * hu
  have haxRy' : (axisR ε') y' = 0 := by
    rw [hy', map_mul, map_mul, axisR_tmul, axisR_tmul]
    linear_combination (algebraMap _ ↑Γ(F.E, U) (ε' (1 : ↑Γ(F.E, U))) *
      algebraMap _ ↑Γ(F.E, U) (ε' (u : ↑Γ(F.E, U)))) * hv
  have hpTy' : pT y' = 0 := by
    rw [hpTdef]
    exact pairLift_eq_zero_of_axes ε' p₁ p₂ hcl₁ hcl₂ hII haxLy' haxRy'
  have hpTy : pT y = pkg.φL.hom a * pT sden := by
    have h1 := congrArg pkg.φL.hom hys
    rw [map_mul, pkg.hφLalg, pkg.hφLalg] at h1
    exact h1.symm
  have hunit_u : IsUnit (pT ((1 : ↑Γ(F.E, U)) ⊗ₜ (u : ↑Γ(F.E, U)))) := by
    refine hunits ⟨_, fun h0 ↦ u.2 (RingHom.mem_ker.mpr ?_)⟩
    have h1 : ε' (1 : ↑Γ(F.E, U)) * ε' (u : ↑Γ(F.E, U)) = 0 :=
      (foldε_tmul ε' (1 : ↑Γ(F.E, U)) (u : ↑Γ(F.E, U))).symm.trans
        (RingHom.mem_ker.mp h0)
    rwa [map_one, _root_.one_mul] at h1
  have hunit_v : IsUnit (pT ((v : ↑Γ(F.E, U)) ⊗ₜ (1 : ↑Γ(F.E, U)))) := by
    refine hunits ⟨_, fun h0 ↦ v.2 (RingHom.mem_ker.mpr ?_)⟩
    have h1 : ε' (v : ↑Γ(F.E, U)) * ε' (1 : ↑Γ(F.E, U)) = 0 :=
      (foldε_tmul ε' (v : ↑Γ(F.E, U)) (1 : ↑Γ(F.E, U))).symm.trans
        (RingHom.mem_ker.mp h0)
    rwa [map_one, _root_.mul_one] at h1
  have hφLa : pkg.φL.hom a = 0 := by
    have h0 : pT ((1 : ↑Γ(F.E, U)) ⊗ₜ (u : ↑Γ(F.E, U))) *
        (pT ((v : ↑Γ(F.E, U)) ⊗ₜ (1 : ↑Γ(F.E, U))) * (pkg.φL.hom a * pT sden)) = 0 := by
      rw [← hpTy, ← map_mul, ← map_mul, ← hy']
      exact hpTy'
    have h1 := (hunit_u.mul_right_eq_zero).mp h0
    have h2 := (hunit_v.mul_right_eq_zero).mp h1
    have h3 : pkg.φL.hom a * pT sden = 0 := h2
    exact (hunits sden).mul_left_eq_zero.mp h3
  have hψ'f : pkg.φL.hom (ψ'.hom f) = pT (f ⊗ₜ 1) + pT (1 ⊗ₜ f) := by
    have h1 : pkg.φL.hom a = pkg.φL.hom (ψ'.hom f) - pT (f ⊗ₜ 1) - pT (1 ⊗ₜ f) := by
      rw [hadef, map_sub, map_sub, pkg.hφLalg, pkg.hφLalg]
    rw [hφLa] at h1
    linear_combination h1.symm
  have hfinal := congrArg (fun (m : Γ(F.E, U) ⟶ R) ↦ m.hom f) hkey
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hfinal
  show (pointSharp ((P₁ + P₂ : F.Point t) : Spec R ⟶ F.E) hp₁₂).hom f = _
  rw [hfinal, hψ'f]
  have hpT1 : pT (f ⊗ₜ 1) = (pointSharp P₁.1 hp₁).hom f := by
    have h2 := congrArg (fun (m : _ ⟶ R) ↦ m.hom f) hidL
    simpa using h2
  have hpT2 : pT (1 ⊗ₜ f) = (pointSharp P₂.1 hp₂).hom f := by
    have h2 := congrArg (fun (m : _ ⟶ R) ↦ m.hom f) hidR
    simpa using h2
  rw [hpT1, hpT2]

/- EXECUTION LEDGER (chunk (iii), the only remaining gap; chunks (i)/(ii) proven below):
0. `letI` k'-algebra on `R` via `t.appLE ⊤ ⊤ ≫ ΓSpecIso`; AlgHoms `p₁ p₂` from
   `pointSharp` (commutes' := `pointSharp_comp_π`); `pT := Algebra.TensorProduct.lift p₁ p₂`;
   `ε'` from `F.zero.appLE` (commutes' := `zero_appLE_π_appLE`).
1. I-closeness `h₁ h₂`: `φ.hom (sharp P c) = φ.hom (sharp 0 c)` via
   `appLE_comp_appLE` on `Spec.map φ ≫ P.1 = Spec.map φ ≫ (0).1` (from the `restrict`
   hypotheses) + `ΓSpecIso_naturality`; then `pointSharp_zero_point` computes `sharp 0`.
2. Identification: `pairBox P₁ P₂ ≫ (boxIso hU).hom = Spec.map (ofHom pT.toRingHom)` —
   `Spec.preimage`-injectivity + `tensor_ringHom_ext` (add to algebra layer: two ring maps
   out of `C ⊗ C` agreeing on `a⊗1`/`1⊗b` are equal, by `tmul_mul_tmul`-induction) with
   legs `pairBox_boxIso_includeLeft/Right` + `Algebra.TensorProduct.lift_comp_includeLeft`.
3. `(P₁+P₂).1 = Spec.map pT ≫ q̃` for `q̃ := (boxIso hU).inv ≫ boxι ≫ (μ[F.asOver]).left`
   — `point_add_val_mu` + `pairing_eq_pairBox` + `Iso.hom_inv_id_assoc`.
4. Stalk: `𝔭 := ker (foldε ε')` prime (`IsDomain ↑Γ(Spec k,⊤)` transported across
   `ΓSpecIso` via `Function.Injective.isDomain`); `q̃.base p𝔭 ∈ U` from step 5's axis law:
   `p𝔭 = aL.base pₑ` (`comap`-of-`ker` + `foldε_eq_axisL`), so `q̃(p𝔭) ∈ range fromSpec = U`
   (`IsAffineOpen.range_fromSpec`).
5. Axis laws, `Spec`-form: `aL := Spec.map (ofHom (axisL ε').toRingHom)` satisfies
   `aL ≫ q̃ = hU.fromSpec`: `aL ≫ (boxIso hU).inv = pairBox 0 taut` (tensor-ext, legs:
   `lift_comp_includeLeft/Right` vs (TAUT-ZERO) `sharp (0 over tC) = πC ∘ ζ` and
   (TAUT-SHARP) `sharp fromSpec = 𝟙 C`, both via `IsAffineOpen.fromSpec_app_self` +
   `appLE_comp_appLE`), then `pairing_eq_pairBox`.symm + `zero_pairing_mul`. Mirror for
   `aR` with `pairing_zero_mul`.
6. Assembly (REFINED after chunks i-iii landed; everything referenced is now PROVEN):
   6a. `letI` k'-algebra on `R`; `p₁ p₂` AlgHoms (commutes' = `pointSharp_comp_π`, defeq);
       `pT := lift p₁ p₂`; `hclose : sharp P c − alg (ε' c) ∈ I := ker φ` for P ∈ K, via
       (H-φ) `φ ∘ sharp w = φ ∘ sharp w'` when `Spec.map φ ≫ w = Spec.map φ ≫ w'`
       (appLE_comp_appLE + `Scheme.ΓSpecIso_naturality`) at w' := 0-point +
       `pointSharp_zero_point`; `hII` from `hφ2`.
   6b. `hid := pairBox_boxIso_eq_specMap` at pT (legs: `lift_comp_includeLeft/Right` +
       `CommRingCat.ofHom_comp`); `q := (boxIso hU).inv ≫ boxι ≫ μ.left`;
       `hsum : (P₁+P₂).1 = Spec.map (ofHom pT) ≫ q` via `point_add_val_mu` +
       `pairing_eq_pairBox` + `Iso.hom_inv_id_assoc`.
   6c. `foldε_eq_axisR` (mirror of `foldε_eq_axisL`, add to algebra layer);
       `hfoldCong : pT x − alg (foldε ε' x) ∈ I` from `pairLift_key` + `hclose` +
       `foldε_eq_axisL/R`; units: `y ∉ 𝔭 := ker (foldε ε')` ⟹ `foldε y ≠ 0` ⟹ unit in k'
       (transport along `(ΓSpecIso (of k)).commRingCatIsoToRingEquiv`, field k) ⟹
       `alg (fold y)` unit in R ⟹ `pT y` = unit + I-nilpotent = unit
       (`IsNilpotent.isUnit_add_right_of_commute`-family; I-elements nilpotent since I²=⊥).
   6d. `𝔭` prime (`RingHom.ker_isPrime`, `IsDomain k'` via `Function.Injective.isDomain`
       along the ΓSpecIso equiv); `p𝔭 := ⟨𝔭, _⟩`; `hqp : q.base p𝔭 ∈ U`: `p𝔭 =
       (Spec.map (ofHom (axisL ε'))).base pₑ` (PrimeSpectrum.ext, comap-of-ker,
       `foldε_eq_axisL`) then `axisL_spec_law` + `IsAffineOpen.range_fromSpec`.
   6e. `L := stalk p𝔭` with `IsLocalization.AtPrime L 𝔭`
       (`StructureSheaf.IsLocalization.to_stalk`, transported to the Scheme-Spec);
       `ψ := germ U (q p𝔭) hqp ≫ q.stalkMap p𝔭 : Γ(F.E,U) ⟶ L`;
       `φL := IsLocalization.lift (units from 6c)`.
   6f. `hkey : sharp (P₁+P₂) c = φL (ψ c)`: both sides' `(ΓSpecIso R).inv`-images have
       equal germs at every `x : Spec R` — LHS-germ = `((P₁+P₂).1).stalkMap x ∘ germ` and
       `(P₁+P₂).1.stalkMap = q.stalkMap ∘ (Spec.map pT).stalkMap`-chain (`stalkMap_comp`
       along `hsum`, `stalkMap_germ` twice); RHS-germ: `germ ∘ iso.inv ∘ φL = (Spec.map
       (ofHom pT)).stalkMap x` on L by `IsLocalization.ringHom_ext` (both invert
       𝔭-complement, agree on `algebraMap` by `stalkMap_germ`-at-⊤ + `IsLocalization.lift_eq`);
       conclude by sheaf `section_ext` (`(Spec R).sheaf`) + `ΓSpecIso`-injectivity.
   6g. Kill: `a := ψ f − algL (f ⊗ 1) − algL (1 ⊗ f)`; the two axis stalk maps
       `rL := (Spec.map (ofHom axisL)).stalkMap pₑ`-forms kill `a`: `rL (ψ f) = algLₑ f`
       from `axisL_spec_law`-stalk-functoriality (`stalkMap_comp` + `stalkMap_germ` +
       `IsAffineOpen.fromSpec`-germ = localization-map), `rL (algL (f⊗1)) = algLₑ (ιε f) = 0`
       (hf), `rL (algL (1⊗f)) = algLₑ f`; then `IsLocalization.surj`-clear denominators,
       `IsLocalization.map_eq_zero_iff` twice, the `(1⊗u)(v⊗1)`-trick,
       `pairLift_eq_zero_of_axes`, and 6c-units transport `φL a = 0`; unwind
       `φL (algL _) = pT _` (`IsLocalization.lift_eq`) + `Algebra.TensorProduct.lift_tmul`:
       `sharp-sum f = φL (ψ f) = pT (f⊗1) + pT (1⊗f) = sharp P₁ f + sharp P₂ f`. 
-/

set_option backward.isDefEq.respectTransparency.types false in
/-- **(H-φ)** The square-zero reduction collapses chart evaluations: if two chart-supported
morphisms `w, w'` into `E` land in the chart `U` and agree after restriction along `φ`, then
`φ` identifies their chart comorphisms on every chart element. Uses the `ΓSpecIso`-naturality
of `pointSharp` and `appLE` functoriality. -/
private theorem phi_pointSharp_eq_of_specMap_comp_eq
    (w w' : Spec R ⟶ F.E) (hw : ∀ x : ↑(Spec R), w.base x ∈ U)
    (hw' : ∀ x : ↑(Spec R), w'.base x ∈ U)
    (hval : Spec.map φ ≫ w = Spec.map φ ≫ w') (c : ↑Γ(F.E, U)) :
    φ.hom ((pointSharp w hw).hom c) = φ.hom ((pointSharp w' hw').hom c) := by
  have hnat : ∀ (v : Spec R ⟶ F.E) (hv : ∀ x : ↑(Spec R), v.base x ∈ U),
      pointSharp v hv ≫ φ = (Spec.map φ ≫ v).appLE U ⊤
          (fun x _ ↦ by simpa using hv ((Spec.map φ).base x)) ≫
        (Scheme.ΓSpecIso S').hom := by
    intro v hv
    rw [pointSharp, Category.assoc, ← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← appLE_top_top (Spec.map φ),
      Scheme.Hom.appLE_comp_appLE]
  have h1 := congrArg (fun (m : Γ(F.E, U) ⟶ S') ↦ m.hom c) (hnat w hw)
  have h2 := congrArg (fun (m : Γ(F.E, U) ⟶ S') ↦ m.hom c) (hnat w' hw')
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1 h2
  rw [h1, h2]
  congr 1
  have h5 := appLE_congr_hom hval U ⊤
    (fun x _ ↦ by simpa using hw ((Spec.map φ).base x))
  exact congrArg (fun (m : Γ(F.E, U) ⟶ Γ(Spec S', ⊤)) ↦ m.hom c) h5

/-- **Additivity of the chart evaluation on kernel-of-reduction points** (the geometric
heart): for `P₁ P₂` reducing to zero along the square-zero `φ` and `f` in the augmentation
ideal of the chart, `(P₁+P₂)♯ f = P₁♯ f + P₂♯ f`. Through the affine Künneth box and
`pairLift_key`. -/
private theorem pointSharp_add {U : (F.E).Opens} (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    (_hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec (CommRingCat.of k)} (P₁ P₂ : F.Point t)
    (h₁ : Point.restrict F (Spec.map φ) P₁ = 0) (h₂ : Point.restrict F (Spec.map φ) P₂ = 0)
    (hz : ∀ x : ↑(Spec R), ((0 : F.Point t) : Spec R ⟶ F.E).base x ∈ U)
    (hp₁ : ∀ x : ↑(Spec R), (P₁ : Spec R ⟶ F.E).base x ∈ U)
    (hp₂ : ∀ x : ↑(Spec R), (P₂ : Spec R ⟶ F.E).base x ∈ U)
    (hp₁₂ : ∀ x : ↑(Spec R), ((P₁ + P₂ : F.Point t) : Spec R ⟶ F.E).base x ∈ U)
    (f : Γ(F.E, U)) (hf : F.zero.appLE U ⊤ (fun x _ ↦ heU x) f = 0) :
    pointSharp (P₁ + P₂ : F.Point t).1 hp₁₂ f =
      pointSharp P₁.1 hp₁ f + pointSharp P₂.1 hp₂ f := by
  classical
  -- 6a. the algebra package
  letI : Algebra ↑Γ(Spec (CommRingCat.of k), ⊤) ↑R :=
    ((t.appLE ⊤ ⊤ le_top) ≫ (Scheme.ΓSpecIso R).hom).hom.toAlgebra
  set ε' := chartAug heU with hε'
  set p₁ : ↑Γ(F.E, U) →ₐ[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑R :=
    { toRingHom := (pointSharp P₁.1 hp₁).hom
      commutes' := fun c ↦ pointSharp_comp_π P₁ hp₁ c } with hp₁'
  set p₂ : ↑Γ(F.E, U) →ₐ[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑R :=
    { toRingHom := (pointSharp P₂.1 hp₂).hom
      commutes' := fun c ↦ pointSharp_comp_π P₂ hp₂ c } with hp₂'
  set pT := Algebra.TensorProduct.lift p₁ p₂ (fun _ _ ↦ Commute.all _ _) with hpT
  set I : Ideal ↑R := RingHom.ker φ.hom with hI
  have hII : ∀ a ∈ I, ∀ b ∈ I, a * b = 0 := by
    intro a ha b hb
    have h2 : a * b ∈ RingHom.ker φ.hom ^ 2 := by
      rw [sq]; exact Ideal.mul_mem_mul ha hb
    rw [hφ2, Ideal.mem_bot] at h2
    exact h2
  have hclose : ∀ (P : F.Point t) (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U)
      (hres0 : Point.restrict F (Spec.map φ) P = 0) (c : ↑Γ(F.E, U)),
      (pointSharp P.1 hp).hom c - algebraMap _ ↑R (ε' c) ∈ I := by
    intro P hp hres0 c
    have hval : Spec.map φ ≫ P.1 = Spec.map φ ≫ ((0 : F.Point t) : Spec R ⟶ F.E) := by
      have h := congrArg Subtype.val hres0
      simp only [Point.restrict] at h
      rw [h, F.point_zero_val, F.point_zero_val, ← Category.assoc]
    have h1 := phi_pointSharp_eq_of_specMap_comp_eq P.1
      ((0 : F.Point t) : Spec R ⟶ F.E) hp hz hval c
    have h2 := pointSharp_zero_point heU t hz c
    have h3 : algebraMap ↑Γ(Spec (CommRingCat.of k), ⊤) ↑R (ε' c) =
        (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom).hom
          ((F.zero.appLE U ⊤ (fun x _ ↦ heU x)).hom c) := rfl
    rw [hI, RingHom.mem_ker, map_sub]
    have h4 : φ.hom ((pointSharp P.1 hp).hom c) =
        φ.hom (algebraMap ↑Γ(Spec (CommRingCat.of k), ⊤) ↑R (ε' c)) := by
      rw [h1]
      exact congrArg φ.hom (h2.trans h3.symm)
    rw [h4, sub_self]
  -- 6b. the sum through the box
  have hidL : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom
      (R := ↑Γ(Spec (CommRingCat.of k), ⊤))) ≫ CommRingCat.ofHom pT.toRingHom =
      pointSharp P₁.1 hp₁ := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom
      (congrArg AlgHom.toRingHom
        (Algebra.TensorProduct.lift_comp_includeLeft p₁ p₂ (fun _ _ ↦ Commute.all _ _)))
  have hidR : CommRingCat.ofHom (Algebra.TensorProduct.includeRight
      (R := ↑Γ(Spec (CommRingCat.of k), ⊤)) (A := ↑Γ(F.E, U))).toRingHom ≫
      CommRingCat.ofHom pT.toRingHom = pointSharp P₂.1 hp₂ := by
    rw [← CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.ofHom
      (congrArg AlgHom.toRingHom
        (Algebra.TensorProduct.lift_comp_includeRight p₁ p₂ (fun _ _ ↦ Commute.all _ _)))
  have hid := pairBox_boxIso_eq_specMap hU P₁ P₂ hp₁ hp₂ hidL hidR
  set q : Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U))) ⟶ F.E :=
    (boxIso hU).inv ≫ boxι ≫ (μ[F.asOver]).left with hq
  have hsum : ((P₁ + P₂ : F.Point t) : Spec R ⟶ F.E) =
      Spec.map (CommRingCat.ofHom pT.toRingHom) ≫ q := by
    rw [← hid, hq]
    rw [point_add_val_mu F P₁ P₂, pairing_eq_pairBox P₁ P₂ hp₁ hp₂]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact Category.assoc _ _ _
  -- 6c. units of the pair-lift away from the augmentation prime
  have hfold : ∀ x, pT x - algebraMap _ ↑R (foldε ε' x) ∈ I := by
    intro x
    have hkey := pairLift_key ε' p₁ p₂ (hclose P₁ hp₁ h₁) (hclose P₂ hp₂ h₂) hII x
    have e1 := hclose P₂ hp₂ h₂ (axisL ε' x)
    have e2 := hclose P₁ hp₁ h₁ (axisR ε' x)
    have hsplit : pT x - algebraMap _ ↑R (foldε ε' x) =
        (p₂ (axisL ε' x) - algebraMap _ ↑R (ε' (axisL ε' x))) +
        (p₁ (axisR ε' x) - algebraMap _ ↑R (ε' (axisR ε' x))) := by
      rw [hkey, ← foldε_eq_axisL, ← foldε_eq_axisR]
      ring
    rw [hsplit]
    exact I.add_mem e1 e2
  have hdom : IsDomain ↑Γ(Spec (CommRingCat.of k), ⊤) :=
    Function.Injective.isDomain
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toRingHom
      (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.injective
  have h𝔭 : (RingHom.ker (foldε ε').toRingHom).IsPrime := RingHom.ker_isPrime _
  have h𝔢 : (RingHom.ker ε'.toRingHom).IsPrime := RingHom.ker_isPrime _
  have hunits : ∀ y : (RingHom.ker (foldε ε').toRingHom).primeCompl, IsUnit (pT y) := by
    rintro ⟨y, hy⟩
    have hy0 : foldε ε' y ≠ 0 := by
      intro h0
      exact hy (by simpa [RingHom.mem_ker] using h0)
    have hyk : IsUnit (foldε ε' y) := by
      set e := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv with he
      have h1 : e (foldε ε' y) ≠ 0 := fun h0 ↦ hy0 (by
        have h2 := congrArg e.symm h0
        simpa using h2)
      have h2 : IsUnit (e (foldε ε' y)) := isUnit_iff_ne_zero.mpr h1
      have h3 := e.symm.toRingHom.isUnit_map h2
      simpa using h3
    have halg : IsUnit (algebraMap ↑Γ(Spec (CommRingCat.of k), ⊤) ↑R (foldε ε' y)) :=
      hyk.map (algebraMap ↑Γ(Spec (CommRingCat.of k), ⊤) ↑R)
    have hnil : IsNilpotent (pT y - algebraMap _ ↑R (foldε ε' y)) := by
      refine ⟨2, ?_⟩
      have hm := hfold y
      have h2 := hII _ hm _ hm
      rw [sq]
      exact h2
    have hdecomp : pT y = algebraMap ↑Γ(Spec (CommRingCat.of k), ⊤) ↑R (foldε ε' y) +
        (pT y - algebraMap _ ↑R (foldε ε' y)) := by ring
    rw [hdecomp]
    exact hnil.isUnit_add_left_of_commute halg (Commute.all _ _)
  -- 6d. the augmentation prime lands in the chart
  set p𝔭 : ↑(Spec (.of (↑Γ(F.E, U) ⊗[↑Γ(Spec (CommRingCat.of k), ⊤)] ↑Γ(F.E, U)))) :=
    ⟨RingHom.ker (foldε ε').toRingHom, h𝔭⟩ with hp𝔭
  set pₑ : ↑(Spec Γ(F.E, U)) := ⟨RingHom.ker ε'.toRingHom, h𝔢⟩ with hpₑ
  have htautU : ∀ x : ↑(Spec Γ(F.E, U)), (hU.fromSpec).base x ∈ U := by
    intro x
    have h1 : (hU.fromSpec).base x ∈ Set.range (hU.fromSpec).base := Set.mem_range_self x
    rwa [hU.range_fromSpec] at h1
  have hzT : ∀ x : ↑(Spec Γ(F.E, U)),
      ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E).base x ∈ U := by
    intro x
    have h0 : ((0 : F.Point (hU.fromSpec ≫ F.π)) : Spec Γ(F.E, U) ⟶ F.E) =
        (hU.fromSpec ≫ F.π) ≫ F.zero := F.point_zero_val _
    rw [h0]
    simpa using heU (((hU.fromSpec ≫ F.π)).base x)
  have hcomap : (Spec.map (CommRingCat.ofHom (axisL ε').toRingHom)).base pₑ = p𝔭 := by
    rw [hp𝔭, hpₑ]
    refine PrimeSpectrum.ext ?_
    show Ideal.comap (axisL ε').toRingHom (RingHom.ker ε'.toRingHom) =
      RingHom.ker (foldε ε').toRingHom
    refine Ideal.ext fun x ↦ ?_
    simp only [Ideal.mem_comap, RingHom.mem_ker]
    constructor
    · intro hx
      rw [show (foldε ε').toRingHom x = ε' ((axisL ε') x) from foldε_eq_axisL ε' x]
      exact hx
    · intro hx
      rw [show (foldε ε').toRingHom x = ε' ((axisL ε') x) from foldε_eq_axisL ε' x] at hx
      exact hx
  have hqp : q.base p𝔭 ∈ U := by
    rw [← hcomap]
    have hlaw' : Spec.map (CommRingCat.ofHom (axisL ε').toRingHom) ≫ q = hU.fromSpec := by
      rw [hq]
      exact axisL_spec_law hU heU htautU hzT
    have h2 : q.base ((Spec.map (CommRingCat.ofHom (axisL ε').toRingHom)).base pₑ) =
        (Spec.map (CommRingCat.ofHom (axisL ε').toRingHom) ≫ q).base pₑ := rfl
    rw [h2, hlaw']
    exact htautU pₑ
  -- the hoisted tail closes it
  have hkerI : (RingHom.ker (foldε (chartAug heU)).toRingHom).IsPrime :=
    RingHom.ker_isPrime _
  have hkerεI : (RingHom.ker (chartAug heU).toRingHom).IsPrime :=
    RingHom.ker_isPrime _
  exact pointSharp_add_tail hU heU htautU hp₁ hp₂ hp₁₂ p₁ p₂ pT hpT
    (fun c ↦ hI.symm ▸ hclose P₁ hp₁ h₁ c)
    (fun c ↦ hI.symm ▸ hclose P₂ hp₂ h₂ c)
    (fun a ha b hb ↦ hII a (hI.symm ▸ ha) b (hI.symm ▸ hb)) hunits hqp hsum
    (by rw [hq]; exact axisL_spec_law hU heU htautU hzT)
    (by rw [hq]; exact axisR_spec_law hU heU htautU hzT)
    hidL hidR f hf

end Box

end AugmentationScheme

/-- **(L-BC core: augmentation-ideal rigidity of torsion)** Over a field `k`, a point of `E`
over `Spec R` that reduces to the zero point along a square-zero quotient `φ : R ↠ S'` and is
killed by an `N` invertible in `k` is the zero point. This is the infinitesimal-fibre content
of KM 2.3.1 ("its tangent map at the origin being multiplication by N"), proven without
differentials: the kernel of reduction is `N`-torsion-free because evaluation on the
augmentation ideal of a chart at the zero section is additive modulo `I² = 0`
(`pointSharp_add`). -/
theorem Point.eq_zero_of_killed_restrict
    {k : Type u} [Field k] (F : EllipticCurve (Spec (CommRingCat.of k)))
    {R S' : CommRingCat.{u}} (φ : R ⟶ S') (hφ : Function.Surjective φ.hom)
    (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec (CommRingCat.of k)} (D : F.Point t)
    (hres : Point.restrict F (Spec.map φ) D = 0)
    (N : ℕ) (hN : IsUnit (N : k)) (hND : (N : ℤ) • D = 0) :
    D = 0 := by
  classical
  -- the chart at the zero point
  haveI : Unique ↑(Spec (CommRingCat.of k)) := inferInstanceAs (Unique (PrimeSpectrum k))
  obtain ⟨U, hUaff, heU0⟩ : ∃ U : (F.E).Opens, IsAffineOpen U ∧ (F.zero).base default ∈ U := by
    obtain ⟨U, hU, hxU, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (Scheme.isBasis_affineOpens F.E)
      (show (F.zero).base default ∈ (⊤ : (F.E).Opens) from trivial)
    exact ⟨U, hU, hxU⟩
  have heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U := fun x ↦ by
    rw [Unique.eq_default x]; exact heU0
  -- the zero point and every `n • D` land in the chart
  have hz : ∀ x : ↑(Spec R), ((0 : F.Point t) : Spec R ⟶ F.E).base x ∈ U := by
    intro x
    have h0 : ((0 : F.Point t) : Spec R ⟶ F.E) = t ≫ F.zero := F.point_zero_val t
    rw [h0]
    exact heU _
  have hK : ∀ n : ℕ, Point.restrict F (Spec.map φ) ((n • D : F.Point t)) = 0 := by
    intro n
    induction n with
    | zero => simpa using restrict_zero F (Spec.map φ)
    | succ m ih =>
        rw [succ_nsmul, restrict_add, ih, hres, add_zero]
  have hred : ∀ n : ℕ, Spec.map φ ≫ ((n • D : F.Point t) : Spec R ⟶ F.E) =
      Spec.map φ ≫ (t ≫ F.zero) := by
    intro n
    have := congrArg Subtype.val (hK n)
    simp only [Point.restrict] at this
    rw [this, F.point_zero_val, Category.assoc]
  have hrangeN : ∀ n : ℕ, ∀ x : ↑(Spec R),
      ((n • D : F.Point t) : Spec R ⟶ F.E).base x ∈ U := fun n ↦
    range_base_subset_of_reduction heU hφ hφ2 (hred n)
  have hrangeD : ∀ x : ↑(Spec R), (D.1).base x ∈ U := by
    intro x
    have h1 := hrangeN 1 x
    rwa [one_nsmul] at h1
  set ζ : Γ(F.E, U) ⟶ Γ(Spec (CommRingCat.of k), ⊤) := F.zero.appLE U ⊤ (fun x _ ↦ heU x) with hζ
  -- scaling: the chart evaluation of `n • D` on the augmentation ideal is `n •` that of `D`
  have hscale : ∀ (n : ℕ) (f : Γ(F.E, U)), ζ f = 0 →
      pointSharp ((n • D : F.Point t) : Spec R ⟶ F.E) (hrangeN n) f =
        n • pointSharp (D.1) hrangeD f := by
    intro n
    induction n with
    | zero =>
        intro f hf
        rw [pointSharp_congr (congrArg Subtype.val (zero_nsmul D)) (hrangeN 0) hz,
          pointSharp_zero_point heU t hz f, hf, map_zero, zero_nsmul]
    | succ m ih =>
        intro f hf
        have hrangeSum : ∀ x : ↑(Spec R),
            ((m • D + D : F.Point t) : Spec R ⟶ F.E).base x ∈ U := by
          intro x
          have h1 := hrangeN (m + 1) x
          rwa [succ_nsmul] at h1
        have hstep := pointSharp_add hUaff heU hφ hφ2 (m • D) D (hK m) hres hz
          (hrangeN m) hrangeD hrangeSum f hf
        rw [pointSharp_congr (congrArg Subtype.val (succ_nsmul D m)) (hrangeN (m + 1))
            hrangeSum, hstep, ih f hf, succ_nsmul]
  -- the `N`-kill: evaluation of `D` on the augmentation ideal vanishes
  have hNk' : IsUnit ((N : ℕ) : Γ(Spec (CommRingCat.of k), ⊤)) := by
    have h1 := (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom.isUnit_map hN
    rwa [map_natCast] at h1
  have hNR : IsUnit ((N : ℕ) : R) := by
    have h1 := (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom).hom.isUnit_map hNk'
    rwa [map_natCast] at h1
  have hDkill : ∀ f : Γ(F.E, U), ζ f = 0 → pointSharp D.1 hrangeD f = 0 := by
    intro f hf
    have hNnat : (N • D : F.Point t) = 0 := by
      rw [← natCast_zsmul]; exact hND
    have h1 := hscale N f hf
    rw [pointSharp_congr (congrArg Subtype.val hNnat) (hrangeN N) hz,
      pointSharp_zero_point heU t hz f, hf, map_zero] at h1
    have h2 : (N : R) * pointSharp D.1 hrangeD f = 0 := by
      rw [← nsmul_eq_mul]; exact h1.symm
    exact (hNR.mul_right_eq_zero).mp h2
  -- conclude: the chart comorphism of `D` is the augmentation, so `D` is the zero point
  have hs : pointSharp D.1 hrangeD = pointSharp ((0 : F.Point t) : Spec R ⟶ F.E) hz := by
    refine CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)
    have hdec : c = F.π.appLE ⊤ U (fun _ _ ↦ trivial) (ζ c) +
        (c - F.π.appLE ⊤ U (fun _ _ ↦ trivial) (ζ c)) := by ring
    have haug : ζ (c - F.π.appLE ⊤ U (fun _ _ ↦ trivial) (ζ c)) = 0 := by
      rw [map_sub, hζ]
      rw [zero_appLE_π_appLE heU (ζ c)]
      ring
    calc pointSharp D.1 hrangeD c
        = pointSharp D.1 hrangeD (F.π.appLE ⊤ U (fun _ _ ↦ trivial) (ζ c)) +
            pointSharp D.1 hrangeD (c - F.π.appLE ⊤ U (fun _ _ ↦ trivial) (ζ c)) := by
          rw [← map_add, ← hdec]
      _ = (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom) (ζ c) := by
          rw [pointSharp_comp_π D hrangeD (ζ c), hDkill _ haug, add_zero]
      _ = pointSharp ((0 : F.Point t) : Spec R ⟶ F.E) hz c :=
          (pointSharp_zero_point heU t hz c).symm
  have hval := eq_of_pointSharp_eq hUaff hrangeD hz hs
  exact Subtype.ext hval

/-- **(L-B, field case)** Over a field in which `N` is invertible, the `N`-torsion
`E[N] ⟶ Spec k` is formally unramified: lifts along square-zero thickenings are unique,
because the difference of two lifts is an `N`-torsion point of `E` reducing to zero
(`Point.eq_zero_of_killed_restrict`). -/
theorem Torsionπ.formallyUnramified_of_isUnit
    {k : Type u} [Field k] (F : EllipticCurve (Spec (CommRingCat.of k)))
    (N : ℕ) (hN : IsUnit (N : k)) :
    FormallyUnramified (F.torsionπ N) := by
  apply FormallyUnramified.of_hom_ext
  intro R S' φ hφ hφ2 g₁ g₂ hthick hf
  set t : Spec R ⟶ Spec (CommRingCat.of k) := g₁ ≫ F.torsionπ N with ht
  have ht₂ : g₂ ≫ F.torsionπ N = t := hf.symm
  -- the two lifts as `N`-torsion points of `E`
  set T₁ := F.torsionPointsEquiv N t ⟨g₁, ht.symm⟩ with hT₁
  set T₂ := F.torsionPointsEquiv N t ⟨g₂, ht₂⟩ with hT₂
  -- their difference is `N`-torsion and reduces to zero
  have hND : (N : ℤ) • ((T₁ : F.Point t) - (T₂ : F.Point t)) = 0 := by
    rw [smul_sub, (Submodule.mem_torsionBy_iff _ _).mp T₁.2,
      (Submodule.mem_torsionBy_iff _ _).mp T₂.2, sub_zero]
  have hresD : Point.restrict F (Spec.map φ) ((T₁ : F.Point t) - (T₂ : F.Point t)) = 0 := by
    rw [F.restrict_sub]
    have hPeq : Point.restrict F (Spec.map φ) (T₁ : F.Point t) =
        Point.restrict F (Spec.map φ) (T₂ : F.Point t) := by
      refine Subtype.ext ?_
      show Spec.map φ ≫ (g₁ ≫ F.torsionι N) = Spec.map φ ≫ (g₂ ≫ F.torsionι N)
      rw [← Category.assoc, ← Category.assoc, hthick]
    rw [hPeq, sub_self]
  -- the core kills the difference
  have hD0 : (T₁ : F.Point t) - (T₂ : F.Point t) = 0 :=
    Point.eq_zero_of_killed_restrict F φ hφ hφ2 _ hresD N hN hND
  have hT : T₁ = T₂ := Subtype.ext (sub_eq_zero.mp hD0)
  have := congrArg (fun z ↦ ((F.torsionPointsEquiv N t).symm z).1) hT
  simpa [hT₁, hT₂, Equiv.symm_apply_apply] using this

/-- `N` invertible on `S` is `N` invertible in every residue field of `S`. -/
theorem nIsInvertible_residueField {X : Scheme.{u}} {N : ℕ} (h : NIsInvertible X N) (x : X) :
    IsUnit (N : X.residueField x) := by
  have h0 : IsUnit ((N : ℕ) : Γ(X, ⊤)) := h
  have h1 := (X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.isUnit_map h0
  rwa [map_natCast] at h1

set_option backward.isDefEq.respectTransparency.types false in
/-- **(L-BC = `Torsionπ.formallyUnramified`, the arithmetic input of BB-DIFF)** If `N` is
invertible on `S`, the `N`-torsion `E[N] ⟶ S` is formally unramified: by T-DISC
(`FormallyUnramified.of_finite_fiberToSpecResidueField`, using `torsionπ_isFinite`) it
suffices that every residue-field fibre is formally unramified; the fibre at `y` is the
torsion of the base change to `Spec κ(y)` (`torsion_baseChange_isPullback`), which is
formally unramified by the field case. -/
theorem Torsionπ.formallyUnramified_of_nIsInvertible (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.torsionπ N) := by
  rcases eq_or_ne N 0 with rfl | hN0
  · have hS : IsEmpty S := ModularCurves.isEmpty_of_nIsInvertible_zero h
    have hT : IsEmpty (E.torsion 0) := ⟨fun x ↦ hS.false ((E.torsionπ 0).base x)⟩
    infer_instance
  · have : NeZero N := ⟨hN0⟩
    have := E.torsionπ_isFinite N
    apply FormallyUnramified.of_finite_fiberToSpecResidueField
    intro y
    -- the base-changed torsion over the residue field is formally unramified
    have hbc : FormallyUnramified ((E.baseChange (S.fromSpecResidueField y)).torsionπ N) :=
      Torsionπ.formallyUnramified_of_isUnit
        (E.baseChange (S.fromSpecResidueField y)) N (nIsInvertible_residueField h y)
    -- both are pullbacks of `torsionπ` along `Spec κ(y) ⟶ S`: transfer across the iso
    have h1 : IsPullback (E.torsionBaseChangeHom N (S.fromSpecResidueField y))
        ((E.baseChange (S.fromSpecResidueField y)).torsionπ N)
        (E.torsionπ N) (S.fromSpecResidueField y) :=
      E.torsion_baseChange_isPullback N (S.fromSpecResidueField y)
    have h2 : IsPullback ((E.torsionπ N).fiberι y) ((E.torsionπ N).fiberToSpecResidueField y)
        (E.torsionπ N) (S.fromSpecResidueField y) :=
      IsPullback.of_hasPullback (E.torsionπ N) (S.fromSpecResidueField y)
    rw [← h2.isoIsPullback_hom_snd _ _ h1,
      MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.FormallyUnramified)]
    exact hbc

end EllipticCurve

end ModularCurves