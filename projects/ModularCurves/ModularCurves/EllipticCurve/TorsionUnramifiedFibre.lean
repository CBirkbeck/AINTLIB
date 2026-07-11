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
section. This gives `formallyUnramified_torsionπ_of_isUnit` over every field via
`FormallyUnramified.of_hom_ext`, and `formallyUnramified_torsionπ_of_nIsInvertible` (= L-BC)
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
      pullback.fst E.π E.π = P.1 :=
  (Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left (lift_fst _ _))

/-- Second projection of the pairing of two points. -/
theorem point_pair_left_snd (E : EllipticCurve S) {T : Scheme.{u}} {g : T ⟶ S}
    (P Q : E.Point g) :
    (lift (E.pointEquivOverHom g P) (E.pointEquivOverHom g Q)).left ≫
      pullback.snd E.π E.π = Q.1 :=
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

/-- **Additivity of the chart evaluation on kernel-of-reduction points** (the geometric
heart): for `P₁ P₂` reducing to zero along the square-zero `φ` and `f` in the augmentation
ideal of the chart, `(P₁+P₂)♯ f = P₁♯ f + P₂♯ f`. Through the affine Künneth box and
`pairLift_key`. -/
private theorem pointSharp_add {U : (F.E).Opens} (hU : IsAffineOpen U)
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U)
    (hφ : Function.Surjective φ.hom) (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    {t : Spec R ⟶ Spec (CommRingCat.of k)} (P₁ P₂ : F.Point t)
    (h₁ : Point.restrict F (Spec.map φ) P₁ = 0) (h₂ : Point.restrict F (Spec.map φ) P₂ = 0)
    (hz : ∀ x : ↑(Spec R), ((0 : F.Point t) : Spec R ⟶ F.E).base x ∈ U)
    (hp₁ : ∀ x : ↑(Spec R), (P₁ : Spec R ⟶ F.E).base x ∈ U)
    (hp₂ : ∀ x : ↑(Spec R), (P₂ : Spec R ⟶ F.E).base x ∈ U)
    (hp₁₂ : ∀ x : ↑(Spec R), ((P₁ + P₂ : F.Point t) : Spec R ⟶ F.E).base x ∈ U)
    (f : Γ(F.E, U)) (hf : F.zero.appLE U ⊤ (fun x _ => heU x) f = 0) :
    pointSharp (P₁ + P₂ : F.Point t).1 hp₁₂ f =
      pointSharp P₁.1 hp₁ f + pointSharp P₂.1 hp₂ f := by
  sorry

/-- `pointSharp` only depends on the morphism. -/
private theorem pointSharp_congr {U : (F.E).Opens} {w w' : Spec R ⟶ F.E} (h : w = w')
    (hw : ∀ x : ↑(Spec R), w.base x ∈ U) (hw' : ∀ x : ↑(Spec R), w'.base x ∈ U) :
    pointSharp w hw = pointSharp w' hw' := by
  subst h; rfl

/-- Evaluation of the zero point: the chart comorphism of `t ≫ zero` is the augmentation
followed by the structure map of `R`. -/
private theorem pointSharp_zero_point {U : (F.E).Opens}
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U) (t : Spec R ⟶ Spec (CommRingCat.of k))
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
private theorem pointSharp_comp_π {U : (F.E).Opens} {t : Spec R ⟶ Spec (CommRingCat.of k)} (P : F.Point t)
    (hp : ∀ x : ↑(Spec R), (P.1).base x ∈ U) (c : Γ(Spec (CommRingCat.of k), ⊤)) :
    pointSharp P.1 hp (F.π.appLE ⊤ U (fun x _ => trivial) c) =
      (t.appLE ⊤ ⊤ le_top ≫ (Scheme.ΓSpecIso R).hom) c := by
  show ((F.π.appLE ⊤ U _ ≫ P.1.appLE U ⊤ _) ≫ (Scheme.ΓSpecIso R).hom) c = _
  rw [Scheme.Hom.appLE_comp_appLE P.1 F.π ⊤ U ⊤ _ _,
    FiniteLocallyFreeSubgroup.AffineChartPatch.appLE_congr_hom P.2 ⊤ ⊤]

/-- The augmentation retracts the structure map: `ζ ∘ π♯ = id` (`Γ`-dual of `zero ≫ π = 𝟙`). -/
private theorem zero_appLE_π_appLE {U : (F.E).Opens}
    (heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U) (c : Γ(Spec (CommRingCat.of k), ⊤)) :
    F.zero.appLE U ⊤ (fun x _ => heU x) (F.π.appLE ⊤ U (fun x _ => trivial) c) = c := by
  show (F.π.appLE ⊤ U _ ≫ F.zero.appLE U ⊤ _) c = c
  rw [Scheme.Hom.appLE_comp_appLE F.zero F.π ⊤ U ⊤ _ _,
    FiniteLocallyFreeSubgroup.AffineChartPatch.appLE_congr_hom F.zero_π ⊤ ⊤,
    FiniteLocallyFreeSubgroup.AffineChartPatch.appLE_id]
  rfl

end AugmentationScheme

/-- **(L-BC core: augmentation-ideal rigidity of torsion)** Over a field `k`, a point of `E`
over `Spec R` that reduces to the zero point along a square-zero quotient `φ : R ↠ S'` and is
killed by an `N` invertible in `k` is the zero point. This is the infinitesimal-fibre content
of KM 2.3.1 ("its tangent map at the origin being multiplication by N"), proven without
differentials: the kernel of reduction is `N`-torsion-free because evaluation on the
augmentation ideal of a chart at the zero section is additive modulo `I² = 0`
(`pointSharp_add`). -/
theorem point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero
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
  have heU : ∀ x : ↑(Spec (CommRingCat.of k)), (F.zero).base x ∈ U := fun x => by
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
      ((n • D : F.Point t) : Spec R ⟶ F.E).base x ∈ U := fun n =>
    range_base_subset_of_reduction heU hφ hφ2 (hred n)
  have hrangeD : ∀ x : ↑(Spec R), (D.1).base x ∈ U := by
    intro x
    have h1 := hrangeN 1 x
    rwa [one_nsmul] at h1
  set ζ : Γ(F.E, U) ⟶ Γ(Spec (CommRingCat.of k), ⊤) := F.zero.appLE U ⊤ (fun x _ => heU x) with hζ
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
    refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
    have hdec : c = F.π.appLE ⊤ U (fun x _ => trivial) (ζ c) +
        (c - F.π.appLE ⊤ U (fun x _ => trivial) (ζ c)) := by ring
    have haug : ζ (c - F.π.appLE ⊤ U (fun x _ => trivial) (ζ c)) = 0 := by
      rw [map_sub, hζ]
      rw [zero_appLE_π_appLE heU (ζ c)]
      ring
    calc pointSharp D.1 hrangeD c
        = pointSharp D.1 hrangeD (F.π.appLE ⊤ U (fun x _ => trivial) (ζ c)) +
            pointSharp D.1 hrangeD (c - F.π.appLE ⊤ U (fun x _ => trivial) (ζ c)) := by
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
(`point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero`). -/
theorem formallyUnramified_torsionπ_of_isUnit
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
    point_eq_zero_of_smul_eq_zero_of_restrict_eq_zero F φ hφ hφ2 _ hresD N hN hND
  have hT : T₁ = T₂ := Subtype.ext (sub_eq_zero.mp hD0)
  have := congrArg (fun z => ((F.torsionPointsEquiv N t).symm z).1) hT
  simpa [hT₁, hT₂, Equiv.symm_apply_apply] using this

/-- `N` invertible on `S` is `N` invertible in every residue field of `S`. -/
theorem nIsInvertible_residueField {X : Scheme.{u}} {N : ℕ} (h : NIsInvertible X N) (x : X) :
    IsUnit (N : X.residueField x) := by
  have h0 : IsUnit ((N : ℕ) : Γ(X, ⊤)) := h
  have h1 := (X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.isUnit_map h0
  rwa [map_natCast] at h1

/-- **(L-BC = `formallyUnramified_torsionπ`, the arithmetic input of BB-DIFF)** If `N` is
invertible on `S`, the `N`-torsion `E[N] ⟶ S` is formally unramified: by T-DISC
(`FormallyUnramified.of_finite_fiberToSpecResidueField`, using `torsionπ_isFinite`) it
suffices that every residue-field fibre is formally unramified; the fibre at `y` is the
torsion of the base change to `Spec κ(y)` (`torsion_baseChange_isPullback`), which is
formally unramified by the field case. -/
theorem formallyUnramified_torsionπ_of_nIsInvertible (N : ℕ) (h : NIsInvertible S N) :
    FormallyUnramified (E.torsionπ N) := by
  rcases eq_or_ne N 0 with rfl | hN0
  · haveI hS : IsEmpty S := ModularCurves.isEmpty_of_nIsInvertible_zero h
    haveI hT : IsEmpty (E.torsion 0) := ⟨fun x => hS.false ((E.torsionπ 0).base x)⟩
    infer_instance
  · haveI : NeZero N := ⟨hN0⟩
    haveI := E.torsionπ_isFinite N
    apply FormallyUnramified.of_finite_fiberToSpecResidueField
    intro y
    -- the base-changed torsion over the residue field is formally unramified
    have hbc : FormallyUnramified ((E.baseChange (S.fromSpecResidueField y)).torsionπ N) :=
      formallyUnramified_torsionπ_of_isUnit
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
