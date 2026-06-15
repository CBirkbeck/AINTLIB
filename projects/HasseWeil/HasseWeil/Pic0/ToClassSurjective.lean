/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib
import HasseWeil.Ramification

/-!
# Surjectivity of `Point.toClass` and the isomorphism `E ≅ Pic⁰(E)` (affine model)

For a Weierstrass curve `W : WeierstrassCurve.Affine F` over a field `F`, mathlib provides the
group homomorphism

```
WeierstrassCurve.Affine.Point.toClass : W.Point →+ Additive (ClassGroup W.CoordinateRing)
```

(`Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean`) sending the point at infinity to `0`
and an affine point `P = (x, y)` to the class of the fractional ideal `⟨X - x, Y - y⟩`. Mathlib
proves this is **injective** (`WeierstrassCurve.Affine.Point.toClass_injective`), realising
`W.Point` as a subgroup of the affine ideal class group. It does **not** prove surjectivity.

This file packages the surjectivity. The statement that every ideal class is the class of some
`XYIdeal'` (or trivial) is the genus-1 divisor-reduction theorem: on a smooth genus-1 curve every
degree-0 divisor class is represented by `(P) - (O)`. We isolate that statement as the
predicate `ClassRepresentableByPoints W` and prove that it is *equivalent* to surjectivity of
`toClass`, and that surjectivity packages into the group isomorphism
`W.Point ≃+ Additive (ClassGroup W.CoordinateRing)`.

## Main definitions

* `WeierstrassCurve.Affine.Point.ClassRepresentableByPoints`: the predicate that every element of
  `ClassGroup W.CoordinateRing` is trivial or the class of `XYIdeal' h` for a nonsingular point.
* `WeierstrassCurve.Affine.Point.ClassReducesToCodimLEOne`: the genus-1 reduction input — every
  nonzero integral ideal class has a representative of `F`-codimension `≤ 1`. This is now **proved
  unconditionally** (`classReducesToCodimLEOne_holds`).
* `WeierstrassCurve.Affine.Point.toClassEquiv'`: the **unconditional** group isomorphism
  `W.Point ≃+ Additive (ClassGroup W.CoordinateRing)` for `[W.IsElliptic]`, built from injectivity +
  the unconditional surjectivity `toClass_surjective'`.

## Main results

The **norm-degree dictionary** (the surjectivity counterpart of mathlib's `natDegree_norm_ne_one`,
which powers `toClass_injective`), all axiom-clean:

* `eq_XYIdeal_of_finrank_quotient_eq_one`: every nonzero ideal `I` with `finrank F (R/I) = 1` is
  the point ideal `XYIdeal W x (C y)` of a (necessarily nonsingular, under `[W.IsElliptic]`) point.
* `mk0_eq_one_of_finrank_quotient_eq_zero` and
  `mk0_eq_mk_XYIdeal'_of_finrank_quotient_eq_one`: the two codimension endpoints, identifying
  codimension `0` (resp. `1`) ideals with the trivial class (resp. a point class).
* `integralIdealRepresentableByPoints_of_classReducesToCodimLEOne` and
  `toClass_surjective_of_classReducesToCodimLEOne`: the codimension reduction predicate implies the
  integral-ideal reduction, hence surjectivity of `toClass` (using the now axiom-clean Dedekind
  instance `HasseWeil.coordinateRing_isDedekindDomain`).

and the unconditional headline results:

* `toClass_surjective'`: **unconditional** surjectivity of `toClass` for `[W.IsElliptic]`.
* `toClassEquiv'`: the **unconditional** isomorphism `W.Point ≃+ Pic⁰(E)`.

## Implementation notes

The full unconditional surjectivity reduces, via three landed and axiom-clean ingredients, to the
genus-1 codimension reduction `ClassReducesToCodimLEOne`, which is **now also proved**.

1. `IsDedekindDomain W.CoordinateRing` is **available and axiom-clean** via
   `HasseWeil.coordinateRing_isDedekindDomain` (imported here), which fires under `[W.IsElliptic]`.

2. **The ring-theoretic codimension infrastructure** (field-agnostic, no `[Fintype F]`):
   * `finiteDimensional_quotient_of_ne_bot`: every nonzero ideal has finite `F`-codimension.
   * `finrank_quotient_smul`: codimension additivity for multiplication by a *principal* ideal.
   * `finrank_quotient_mul`: the **general** codimension additivity
     `finrank F (R ⧸ I·J) = finrank F (R ⧸ I) + finrank F (R ⧸ J)` for arbitrary nonzero `I, J`,
     via the short exact sequence `0 → I/(I·J) → R/(I·J) → R/I → 0`
     (`Submodule.quotientQuotientEquivQuotient` + `Submodule.finrank_quotient_add_finrank`) and the
     invertible-ideal kernel isomorphism `quotIdealMulEquiv : I/(I·J) ≃ R/J` built from mathlib's
     `FractionalIdeal.quotientEquiv`.

3. **The genus-1 reduction proper**, `classReducesToCodimLEOne_holds`: every nonzero integral ideal
   class has a representative of `F`-codimension `≤ 1` (Riemann–Roch for `g = 1`). Proved from the
   concrete Riemann–Roch inequality `exists_mem_norm_natDegree_le` (every nonzero ideal `I` has a
   nonzero element of norm degree `≤ finrank F (R ⧸ I) + 1`, by an exact `F`-dimension count using
   `CoordinateRing.degree_norm_smul_basis` and rank–nullity) plus the general additivity (2): from a
   small-norm element of a representative of the inverse class, the Dedekind factorisation
   `(a) = I'·J` yields a codimension-`≤ 1` representative of the class.

Everything in this file is `#print axioms`-clean (`[propext, Classical.choice, Quot.sound]`),
including the unconditional `toClass_surjective'` and `toClassEquiv'`.
-/

open Polynomial Module

open scoped nonZeroDivisors Polynomial.Bivariate Pointwise

namespace WeierstrassCurve.Affine.Point

variable {F : Type*} [Field F] {W : WeierstrassCurve.Affine F} [DecidableEq F]

/-- **Divisor-reduction predicate (genus-1).** Every element of the affine ideal class group
`ClassGroup W.CoordinateRing` is either trivial or the class of `XYIdeal' h` for a nonsingular
affine point `(x, y)`. Geometrically: every degree-0 divisor class on the (genus-1) curve is
represented by `(P) - (O)` for a rational point `P`.

This is exactly the image-characterisation needed for surjectivity of `toClass`; see
`toClass_surjective_iff_classRepresentableByPoints`. -/
def ClassRepresentableByPoints (W : WeierstrassCurve.Affine F) : Prop :=
  ∀ g : ClassGroup W.CoordinateRing,
    g = 1 ∨ ∃ (x y : F) (h : W.Nonsingular x y),
      g = ClassGroup.mk W.FunctionField (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h)

/-- Each class of an `XYIdeal'` (and the trivial class) lies in the range of `toClass`. This is the
content-free half of the range characterisation: it just unfolds `toClass`. -/
theorem mem_range_toClass_of_classRep (g : ClassGroup W.CoordinateRing)
    (hg : g = 1 ∨ ∃ (x y : F) (h : W.Nonsingular x y),
      g = ClassGroup.mk W.FunctionField (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h)) :
    Additive.ofMul g ∈ Set.range (toClass (W := W)) := by
  obtain (hg | ⟨x, y, h, hg⟩) := hg
  · exact ⟨0, by rw [toClass_zero, hg]; rfl⟩
  · exact ⟨some x y h, by rw [toClass_some, hg]; rfl⟩

/-- The divisor-reduction predicate implies surjectivity of `toClass` (the axiom-free direction). -/
theorem toClass_surjective_of_classRepresentableByPoints (hrep : ClassRepresentableByPoints W) :
    Function.Surjective (toClass (W := W)) := by
  intro c
  obtain ⟨P, hP⟩ := mem_range_toClass_of_classRep (Additive.toMul c) (hrep _)
  exact ⟨P, by rwa [ofMul_toMul] at hP⟩

/-- Surjectivity of `toClass` implies the divisor-reduction predicate (the converse direction).
Together with the previous lemma this shows the two are equivalent. -/
theorem classRepresentableByPoints_of_toClass_surjective
    (hsurj : Function.Surjective (toClass (W := W))) :
    ClassRepresentableByPoints W := by
  intro g
  obtain ⟨P, hP⟩ := hsurj (Additive.ofMul g)
  cases P with
  | zero =>
      left
      rw [show (zero : W.Point) = 0 from rfl, toClass_zero] at hP
      exact (Additive.ofMul.injective hP).symm
  | some x y h =>
      right
      refine ⟨x, y, h, ?_⟩
      rw [toClass_some] at hP
      exact (Additive.ofMul.injective hP).symm

/-- **Surjectivity of `toClass` is equivalent to the genus-1 divisor-reduction predicate.** This
records, axiom-free, exactly what remains to be proven for full surjectivity: that every ideal
class is represented by a rational point. -/
theorem toClass_surjective_iff_classRepresentableByPoints :
    Function.Surjective (toClass (W := W)) ↔ ClassRepresentableByPoints W :=
  ⟨classRepresentableByPoints_of_toClass_surjective,
    toClass_surjective_of_classRepresentableByPoints⟩

/-- **The group isomorphism `W.Point ≃+ Additive (ClassGroup W.CoordinateRing)`**, parametrised by a
proof of surjectivity. Combined with mathlib's `toClass_injective`, any proof of surjectivity
upgrades `toClass` to an isomorphism. -/
noncomputable def toClassEquiv_of_surjective (hsurj : Function.Surjective (toClass (W := W))) :
    W.Point ≃+ Additive (ClassGroup W.CoordinateRing) :=
  AddEquiv.ofBijective toClass ⟨toClass_injective, hsurj⟩

@[simp]
theorem toClassEquiv_of_surjective_apply
    (hsurj : Function.Surjective (toClass (W := W))) (P : W.Point) :
    toClassEquiv_of_surjective hsurj P = toClass P :=
  rfl

/-- **Integral-ideal reduction predicate.** Every nonzero integral ideal of the coordinate ring is,
in the class group, either trivial or the class of `XYIdeal' h` for a nonsingular point. This is
the Riemann–Roch divisor-reduction step at the level of integral ideals. -/
def IntegralIdealRepresentableByPoints (W : WeierstrassCurve.Affine F)
    [IsDedekindDomain W.CoordinateRing] : Prop :=
  ∀ I : (Ideal W.CoordinateRing)⁰,
    ClassGroup.mk0 I = 1 ∨ ∃ (x y : F) (h : W.Nonsingular x y),
      ClassGroup.mk0 I =
        ClassGroup.mk W.FunctionField (WeierstrassCurve.Affine.CoordinateRing.XYIdeal' h)

omit [DecidableEq F] in
/-- Under `[IsDedekindDomain W.CoordinateRing]`, the integral-ideal reduction predicate implies the
full divisor-reduction predicate: every class has an integral representative
(`ClassGroup.mk0_surjective`), to which the integral reduction applies. -/
theorem classRepresentableByPoints_of_integralIdealRep [IsDedekindDomain W.CoordinateRing]
    (hred : IntegralIdealRepresentableByPoints W) :
    ClassRepresentableByPoints W := by
  intro g
  obtain ⟨I, rfl⟩ := ClassGroup.mk0_surjective g
  exact hred I

/-- **Surjectivity of `toClass` from the two structural ingredients.** Under
`[IsDedekindDomain W.CoordinateRing]` plus the integral-ideal reduction, `toClass` is surjective.
This is the cleanest factorisation of the remaining work: supply a Dedekind instance and prove the
integral reduction, and surjectivity follows. -/
theorem toClass_surjective_of_integralIdealRep [IsDedekindDomain W.CoordinateRing]
    (hred : IntegralIdealRepresentableByPoints W) :
    Function.Surjective (toClass (W := W)) :=
  toClass_surjective_of_classRepresentableByPoints
    (classRepresentableByPoints_of_integralIdealRep hred)

omit [DecidableEq F] in
/-- The `F`-codimension of the maximal ideal `XYIdeal W x (C y)` of a point `(x, y)` on the curve is
`1`: the quotient is `F` itself (`quotientXYIdealEquiv`). -/
theorem finrank_quotient_XYIdeal_eq_one {x y : F} (h : W.Equation x y) :
    Module.finrank F (W.CoordinateRing ⧸ CoordinateRing.XYIdeal W x (C y)) = 1 := by
  have heval : (W.polynomial.eval (C y)).eval x = 0 := h
  rw [(CoordinateRing.quotientXYIdealEquiv heval).toLinearEquiv.finrank_eq, Module.finrank_self]

omit [DecidableEq F] in
/-- The quotient by the ideal of a point on the curve is finite-dimensional over `F`. -/
theorem finiteDimensional_quotient_XYIdeal {x y : F} (h : W.Equation x y) :
    FiniteDimensional F (W.CoordinateRing ⧸ CoordinateRing.XYIdeal W x (C y)) := by
  have heval : (W.polynomial.eval (C y)).eval x = 0 := h
  exact (CoordinateRing.quotientXYIdealEquiv heval).toLinearEquiv.symm.finiteDimensional

omit [DecidableEq F] in
/-- **Ideals with equal finite `F`-codimension and one contained in the other are equal.** The
surjection `R/J ↠ R/I` induced by `J ≤ I` between equal finite-dimensional quotients is an
isomorphism, forcing `I = J`. This is the genus-1 "no room to grow" step. -/
theorem eq_of_le_of_finrank_quotient_eq {I J : Ideal W.CoordinateRing} (hJI : J ≤ I)
    [FiniteDimensional F (W.CoordinateRing ⧸ J)] [FiniteDimensional F (W.CoordinateRing ⧸ I)]
    (heq : Module.finrank F (W.CoordinateRing ⧸ J) = Module.finrank F (W.CoordinateRing ⧸ I)) :
    I = J := by
  let f : (W.CoordinateRing ⧸ J) →ₗ[F] (W.CoordinateRing ⧸ I) :=
    Submodule.mapQ (Submodule.restrictScalars F J) (Submodule.restrictScalars F I)
      LinearMap.id (by simpa using hJI)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ z
    exact ⟨Submodule.mkQ _ w, rfl⟩
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hsurj
  refine le_antisymm ?_ hJI
  intro r hr
  have hf0 : f (Submodule.Quotient.mk r) = 0 := by
    simp only [f]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hr
  have hr0 := hinj (hf0.trans (LinearMap.map_zero f).symm)
  exact (Submodule.Quotient.mk_eq_zero _).mp hr0

omit [DecidableEq F] in
/-- **An `F`-algebra hom `R → F` from a codimension-1 quotient.** If `R/I` is 1-dimensional over the
field `F`, then `algebraMap F (R/I)` is an isomorphism, and composing its inverse with the quotient
map gives an `F`-algebra hom `φ : R →ₐ[F] F` whose kernel is exactly `I`. Evaluating `φ` at the
images of `X` and `Y` will produce the point. -/
theorem exists_algHom_ker_eq_of_finrank_quotient_eq_one (I : Ideal W.CoordinateRing)
    [Nontrivial (W.CoordinateRing ⧸ I)]
    (hfin : Module.finrank F (W.CoordinateRing ⧸ I) = 1) :
    ∃ φ : W.CoordinateRing →ₐ[F] F, ∀ r, r ∈ I ↔ φ r = 0 := by
  have hbij : Function.Bijective (algebraMap F (W.CoordinateRing ⧸ I)) := by
    rw [Algebra.bijective_algebraMap_iff]
    exact ((Subalgebra.bot_eq_top_iff_finrank_eq_one).mpr hfin).symm
  let ψ := (AlgEquiv.ofBijective (Algebra.ofId F _) hbij).symm
  refine ⟨ψ.toAlgHom.comp (Ideal.Quotient.mkₐ F I), fun r => ?_⟩
  rw [AlgHom.comp_apply]
  change r ∈ I ↔ ψ (Ideal.Quotient.mkₐ F I r) = 0
  rw [map_eq_zero_iff ψ ψ.injective, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

omit [DecidableEq F] in
/-- **The point of an `F`-algebra hom `R → F`.** Any `F`-algebra hom `φ : W.CoordinateRing →ₐ[F] F`
yields a point `(x, y) = (φ(X̄), φ(Ȳ))` *on the curve*: pulling back along `mk W` turns `φ` into the
two-variable evaluation `evalEval x y`, which kills `W.polynomial` (since `mk W` does), i.e.
`W.Equation x y`. -/
theorem equation_of_algHom (φ : W.CoordinateRing →ₐ[F] F) :
    W.Equation (φ (CoordinateRing.mk W (C X))) (φ (CoordinateRing.mk W Y)) := by
  set x := φ (CoordinateRing.mk W (C X)) with hx
  set y := φ (CoordinateRing.mk W Y) with hy
  change W.polynomial.evalEval x y = 0
  have key : φ.toRingHom.comp (CoordinateRing.mk W) = (evalRingHom x).comp (evalRingHom (C y)) := by
    apply Polynomial.ringHom_ext'
    · apply Polynomial.ringHom_ext'
      · ext a
        simp only [RingHom.comp_apply, coe_evalRingHom, eval_C]
        rw [show (C (C a) : F[X][Y]) = algebraMap F F[X][Y] a from rfl,
          show (CoordinateRing.mk W) (algebraMap F F[X][Y] a)
            = algebraMap F W.CoordinateRing a from rfl]
        exact φ.commutes a
      · simp only [RingHom.comp_apply, coe_evalRingHom, eval_C, eval_X, AlgHom.toRingHom_eq_coe,
          RingHom.coe_coe, hx]
    · simp only [RingHom.comp_apply, coe_evalRingHom, eval_X, eval_C, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, hy]
  have heq : φ.toRingHom.comp (CoordinateRing.mk W) W.polynomial =
      ((evalRingHom x).comp (evalRingHom (C y))) W.polynomial := by rw [key]
  rw [RingHom.comp_apply,
    show (CoordinateRing.mk W) W.polynomial = 0 from AdjoinRoot.mk_self, RingHom.map_zero] at heq
  rw [show W.polynomial.evalEval x y
    = ((evalRingHom x).comp (evalRingHom (C y))) W.polynomial from rfl]
  exact heq.symm

omit [DecidableEq F] in
/-- The images of `X - x` and `Y - y` in `R` lie in the kernel of `φ` whenever
`x = φ(X̄)` and `y = φ(Ȳ)`. -/
theorem algHom_XClass_eq_zero (φ : W.CoordinateRing →ₐ[F] F) :
    φ (CoordinateRing.XClass W (φ (CoordinateRing.mk W (C X)))) = 0 := by
  set x := φ (CoordinateRing.mk W (C X)) with hx
  have hXC : CoordinateRing.XClass W x
      = CoordinateRing.mk W (C X) - algebraMap F W.CoordinateRing x := by
    rw [CoordinateRing.XClass,
      show (C (X - C x) : F[X][Y]) = C X - C (C x) by rw [map_sub], map_sub]; rfl
  rw [hXC, map_sub, φ.commutes]
  change x - (algebraMap F F) x = 0
  rw [Algebra.algebraMap_self_apply, sub_self]

omit [DecidableEq F] in
/-- The image of `Y - y` in `R` lies in the kernel of `φ` whenever `y = φ(Ȳ)`. -/
theorem algHom_YClass_eq_zero (φ : W.CoordinateRing →ₐ[F] F) :
    φ (CoordinateRing.YClass W (C (φ (CoordinateRing.mk W Y)))) = 0 := by
  set y := φ (CoordinateRing.mk W Y) with hy
  have hYC : CoordinateRing.YClass W (C y)
      = CoordinateRing.mk W Y - algebraMap F W.CoordinateRing y := by
    rw [CoordinateRing.YClass, map_sub]; rfl
  rw [hYC, map_sub, φ.commutes]
  change y - (algebraMap F F) y = 0
  rw [Algebra.algebraMap_self_apply, sub_self]

omit [DecidableEq F] in
/-- **Codimension-1 ideals are point ideals.** Every nonzero ideal `I` of `W.CoordinateRing` with
`finrank F (R/I) = 1` equals `XYIdeal W x (C y)` for a point `(x, y)` on the curve. Under
`[W.IsElliptic]` (so `Δ ≠ 0`), this point is automatically nonsingular. This is the surjectivity
counterpart of mathlib's `natDegree_norm_ne_one`. -/
theorem eq_XYIdeal_of_finrank_quotient_eq_one [W.IsElliptic] (I : Ideal W.CoordinateRing)
    [Nontrivial (W.CoordinateRing ⧸ I)]
    (hfin : Module.finrank F (W.CoordinateRing ⧸ I) = 1) :
    ∃ (x y : F) (_ : W.Nonsingular x y), I = CoordinateRing.XYIdeal W x (C y) := by
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq_of_finrank_quotient_eq_one I hfin
  set x := φ (CoordinateRing.mk W (C X)) with hx
  set y := φ (CoordinateRing.mk W Y) with hy
  have hEq : W.Equation x y := equation_of_algHom φ
  have hNS : W.Nonsingular x y := (equation_iff_nonsingular).mp hEq
  haveI : FiniteDimensional F (W.CoordinateRing ⧸ CoordinateRing.XYIdeal W x (C y)) :=
    finiteDimensional_quotient_XYIdeal hEq
  haveI : FiniteDimensional F (W.CoordinateRing ⧸ I) :=
    Module.finite_of_finrank_eq_succ hfin
  refine ⟨x, y, hNS, ?_⟩
  have hsub : CoordinateRing.XYIdeal W x (C y) ≤ I := by
    rw [CoordinateRing.XYIdeal, Ideal.span_le]
    rintro z (hz | hz) <;> subst hz <;> rw [SetLike.mem_coe, hφ]
    · exact algHom_XClass_eq_zero φ
    · exact algHom_YClass_eq_zero φ
  have hfinXY : Module.finrank F (W.CoordinateRing ⧸ CoordinateRing.XYIdeal W x (C y)) = 1 :=
    finrank_quotient_XYIdeal_eq_one hEq
  exact eq_of_le_of_finrank_quotient_eq hsub (by rw [hfinXY, hfin])

omit [DecidableEq F] in
/-- **Finite-dimensionality of `R ⧸ I` for nonzero `I`.** Every nonzero ideal of the coordinate ring
has finite `F`-codimension, via the Smith-normal-form decomposition
`R ⧸ I ≃ₗ[F] ⨁ᵢ F[X] ⧸ ⟨dᵢ⟩` (`Ideal.quotientEquivDirectSum`) with each summand
finite-dimensional. This is field-agnostic (no `[Fintype F]`). -/
theorem finiteDimensional_quotient_of_ne_bot [W.IsElliptic] (I : Ideal W.CoordinateRing)
    (hI : I ≠ ⊥) : FiniteDimensional F (W.CoordinateRing ⧸ I) := by
  classical
  exact Module.Finite.equiv (Ideal.quotientEquivDirectSum F (CoordinateRing.basis W) hI).symm

/-- **The degree of an ideal of `F[X]`.** For an ideal `J` of the PID `F[X]`, the natural degree of
its monic generator. On `⊥` it is `0`; on a nonzero ideal `⟨g⟩` it is `g.natDegree`. This packages
the codimension `finrank F (F[X] ⧸ J)` purely polynomially. -/
noncomputable def idealNatDegree (J : Ideal F[X]) : ℕ :=
  (Submodule.IsPrincipal.generator J).natDegree

omit [DecidableEq F] in
/-- `idealNatDegree ⟨g⟩ = g.natDegree`: the generator of `⟨g⟩` is associated to `g`, hence has the
same degree. -/
theorem idealNatDegree_span (g : F[X]) : idealNatDegree (Ideal.span {g}) = g.natDegree := by
  unfold idealNatDegree
  have h : Associated (Submodule.IsPrincipal.generator (Ideal.span ({g} : Set F[X]))) g := by
    rw [← Ideal.span_singleton_eq_span_singleton, Ideal.span_singleton_generator]
  exact natDegree_eq_of_degree_eq (degree_eq_degree_of_associated h)

omit [DecidableEq F] in
/-- **`idealNatDegree` is additive over products of nonzero ideals of `F[X]`.** The generator of a
product is the product of the generators, and `natDegree` is additive over products of nonzero
polynomials. -/
theorem idealNatDegree_mul {A B : Ideal F[X]} (hA : A ≠ ⊥) (hB : B ≠ ⊥) :
    idealNatDegree (A * B) = idealNatDegree A + idealNatDegree B := by
  have e1 : A = Ideal.span {Submodule.IsPrincipal.generator A} :=
    (Ideal.span_singleton_generator A).symm
  have e2 : B = Ideal.span {Submodule.IsPrincipal.generator B} :=
    (Ideal.span_singleton_generator B).symm
  have hgA : Submodule.IsPrincipal.generator A ≠ 0 := by
    intro h; exact hA (by rw [e1, h, Ideal.span_singleton_zero])
  have hgB : Submodule.IsPrincipal.generator B ≠ 0 := by
    intro h; exact hB (by rw [e2, h, Ideal.span_singleton_zero])
  calc idealNatDegree (A * B)
      = idealNatDegree (Ideal.span {Submodule.IsPrincipal.generator A *
          Submodule.IsPrincipal.generator B}) := by
        conv_lhs => rw [e1, e2, Ideal.span_singleton_mul_span_singleton]
    _ = (Submodule.IsPrincipal.generator A * Submodule.IsPrincipal.generator B).natDegree :=
        idealNatDegree_span _
    _ = idealNatDegree A + idealNatDegree B := by rw [natDegree_mul hgA hgB]; rfl

omit [DecidableEq F] in
/-- **The relative-norm degree invariant is additive.** For nonzero ideals `I, J` of `R`,
`idealNatDegree (relNorm F[X] (I * J)) = idealNatDegree (relNorm F[X] I) + idealNatDegree
(relNorm F[X] J)`. This is `idealNatDegree_mul` fed by multiplicativity of the relative norm
`Ideal.relNorm` (`map_mul`). -/
theorem idealNatDegree_relNorm_mul [W.IsElliptic] {I J : Ideal W.CoordinateRing}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    idealNatDegree (Ideal.relNorm F[X] (I * J))
      = idealNatDegree (Ideal.relNorm F[X] I) + idealNatDegree (Ideal.relNorm F[X] J) := by
  rw [map_mul (Ideal.relNorm F[X])]
  exact idealNatDegree_mul (fun h => hI (Ideal.relNorm_eq_bot_iff.mp h))
    (fun h => hJ (Ideal.relNorm_eq_bot_iff.mp h))

omit [DecidableEq F] in
/-- **Principal-ideal codimension via the norm degree.** For a nonzero `a ∈ R`, the relative-norm
degree of `⟨a⟩` is `(Algebra.norm F[X] a).natDegree`, which by mathlib's
`finrank_quotient_span_eq_natDegree_norm` equals `finrank F (R ⧸ ⟨a⟩)`. This is the principal base
case of the codimension/norm-degree bridge. -/
theorem idealNatDegree_relNorm_span_singleton [W.IsElliptic] {a : W.CoordinateRing} :
    idealNatDegree (Ideal.relNorm F[X] (Ideal.span {a})) = (Algebra.norm F[X] a).natDegree := by
  rw [Ideal.relNorm_singleton, Algebra.intNorm_eq_norm, idealNatDegree_span]

omit [DecidableEq F] in
/-- **The codimension as a sum of Smith degrees.** For a nonzero ideal `I`, the `F`-codimension
`finrank F (R ⧸ I)` is the sum of the natural degrees of the Smith coefficients `dᵢ` of `I` (with
respect to the rank-`2` `F[X]`-basis of `R`). This is the `R`-side of the codimension/norm-degree
bridge, obtained from `Ideal.finrank_quotient_eq_sum` and the principal computation
`finrank F (F[X] ⧸ ⟨dᵢ⟩) = dᵢ.natDegree`. -/
theorem finrank_quotient_eq_sum_smithCoeffs [W.IsElliptic] (I : Ideal W.CoordinateRing)
    (hI : I ≠ ⊥) :
    Module.finrank F (W.CoordinateRing ⧸ I)
      = ∑ i, (Ideal.smithCoeffs (CoordinateRing.basis W) I hI i).natDegree := by
  classical
  haveI hFree : ∀ i, Module.Free F
      (F[X] ⧸ Ideal.span ({Ideal.smithCoeffs (CoordinateRing.basis W) I hI i} : Set F[X])) :=
    fun i => inferInstance
  haveI hFin : ∀ i, Module.Finite F
      (F[X] ⧸ Ideal.span ({Ideal.smithCoeffs (CoordinateRing.basis W) I hI i} : Set F[X])) :=
    fun i => inferInstance
  rw [Ideal.finrank_quotient_eq_sum (I := I) (hI := hI) F (CoordinateRing.basis W)]
  exact Finset.sum_congr rfl (fun i _ => finrank_quotient_span_eq_natDegree)

omit [DecidableEq F] in
/-- `a • I = ⟨a⟩ * I` for an element `a` and an ideal `I`: scaling an ideal by `a` is the same as
multiplying it by the principal ideal `⟨a⟩`. -/
theorem smul_ideal_eq_span_mul (a : W.CoordinateRing) (I : Ideal W.CoordinateRing) :
    a • I = Ideal.span {a} * I := by
  ext x
  rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton_mul]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, by rw [smul_eq_mul]⟩
  · rintro ⟨z, hz, rfl⟩; exact ⟨z, hz, by rw [smul_eq_mul]⟩

omit [DecidableEq F] in
/-- **Codimension additivity for multiplication by a principal ideal.** For a nonzero `a ∈ R` and a
nonzero ideal `I`, `finrank F (R ⧸ ⟨a⟩·I) = finrank F (R ⧸ I) + finrank F (R ⧸ ⟨a⟩)`. This is the
additivity of `F`-codimension along the multiplication-by-`a` short exact sequence
`R ⧸ I → R ⧸ (a•I) → R ⧸ ⟨a⟩` (`Ideal.mulQuot`/`Ideal.quotOfMul`, restricted to `F`-linear maps and
fed to `Module.length_eq_add_of_exact`, with `Module.length F = finrank F` over the field `F`).
It is the special case of the genus-1 norm-degree additivity for a principal factor. -/
theorem finrank_quotient_smul [W.IsElliptic] {a : W.CoordinateRing} (ha : a ≠ 0)
    (I : Ideal W.CoordinateRing) (hI : I ≠ ⊥) :
    Module.finrank F (W.CoordinateRing ⧸ (a • I)) =
      Module.finrank F (W.CoordinateRing ⧸ I)
        + Module.finrank F (W.CoordinateRing ⧸ Ideal.span {a}) := by
  classical
  have hanz : a ∈ nonZeroDivisors W.CoordinateRing := mem_nonZeroDivisors_iff_ne_zero.mpr ha
  have haspan : Ideal.span ({a} : Set W.CoordinateRing) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have haI : a • I ≠ ⊥ := by rw [smul_ideal_eq_span_mul]; exact mul_ne_zero haspan hI
  haveI : FiniteDimensional F (W.CoordinateRing ⧸ I) := finiteDimensional_quotient_of_ne_bot _ hI
  haveI : FiniteDimensional F (W.CoordinateRing ⧸ Ideal.span ({a} : Set W.CoordinateRing)) :=
    finiteDimensional_quotient_of_ne_bot _ haspan
  haveI : FiniteDimensional F (W.CoordinateRing ⧸ (a • I)) :=
    finiteDimensional_quotient_of_ne_bot _ haI
  have hlen := Module.length_eq_add_of_exact
    ((Ideal.mulQuot a I).restrictScalars F) ((Ideal.quotOfMul a I).restrictScalars F)
    (Ideal.mulQuot_injective I hanz) (Ideal.quotOfMul_surjective I)
    (Ideal.exact_mulQuot_quotOfMul I)
  rw [Module.length_eq_finrank, Module.length_eq_finrank, Module.length_eq_finrank,
    ← Nat.cast_add, ENat.coe_inj] at hlen
  exact hlen

omit [DecidableEq F] in
private noncomputable def quotComapEquivCoeIdealQuot_aux [W.IsElliptic]
    {I J : Ideal W.CoordinateRing}
    (hinj : Function.Injective (Algebra.linearMap W.CoordinateRing W.FunctionField)) :
    ((I : Submodule W.CoordinateRing W.CoordinateRing) ⧸ Submodule.comap
        (I : Submodule W.CoordinateRing W.CoordinateRing).subtype
          ((I * J) : Submodule W.CoordinateRing W.CoordinateRing))
      ≃ₗ[W.CoordinateRing]
        ((↑I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule ⧸
          Submodule.comap
            (↑I : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule.subtype
            ((↑(I * J) : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule)) := by
  set R := W.CoordinateRing
  set K := W.FunctionField
  have hcoeI : Submodule.map (Algebra.linearMap R K) (I : Submodule R R)
      = (↑I : FractionalIdeal R⁰ K).coeToSubmodule := by rw [FractionalIdeal.coe_coeIdeal]; rfl
  let μ : (I : Submodule R R) ≃ₗ[R] (↑I : FractionalIdeal R⁰ K).coeToSubmodule :=
    (Submodule.equivMapOfInjective (Algebra.linearMap R K) hinj (I : Submodule R R)).trans
      (LinearEquiv.ofEq _ _ hcoeI)
  refine Submodule.Quotient.equiv _ _ μ ?_
  apply le_antisymm
  · rintro _ ⟨⟨x, hxI⟩, hxIJ, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap] at hxIJ
    rw [Submodule.mem_comap]
    change (μ ⟨x, hxI⟩ : K) ∈ (↑(I * J) : FractionalIdeal R⁰ K).coeToSubmodule
    have hμ : (μ ⟨x, hxI⟩ : K) = algebraMap R K x := by
      simp only [μ, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
        Submodule.coe_equivMapOfInjective_apply, Algebra.linearMap_apply]
    rw [hμ, FractionalIdeal.mem_coe]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ hxIJ
  · rintro ⟨y, hyI⟩ hy
    rw [Submodule.mem_comap] at hy
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hy
    obtain ⟨r, hrIJ, hry⟩ := hy
    have hrI : r ∈ I := Ideal.mul_le_right hrIJ
    refine ⟨⟨r, hrI⟩, ?_, ?_⟩
    · rw [SetLike.mem_coe, Submodule.mem_comap]; exact hrIJ
    · apply Subtype.ext
      change (μ ⟨r, hrI⟩ : K) = y
      simp only [μ, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
        Submodule.coe_equivMapOfInjective_apply, Algebra.linearMap_apply]
      exact hry

omit [DecidableEq F] in
private noncomputable def quotEquivOneCoeIdealQuot_aux [W.IsElliptic] {J : Ideal W.CoordinateRing}
    (hinj : Function.Injective (Algebra.linearMap W.CoordinateRing W.FunctionField)) :
    (W.CoordinateRing ⧸ J) ≃ₗ[W.CoordinateRing]
      ((1 : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule ⧸
        Submodule.comap
          (1 : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule.subtype
          ((↑J : FractionalIdeal W.CoordinateRing⁰ W.FunctionField).coeToSubmodule)) := by
  set R := W.CoordinateRing
  set K := W.FunctionField
  have hone : LinearMap.range (Algebra.linearMap R K)
      = (1 : FractionalIdeal R⁰ K).coeToSubmodule := by
    rw [FractionalIdeal.coe_one]; exact (Submodule.one_eq_range).symm
  let ν : R ≃ₗ[R] (1 : FractionalIdeal R⁰ K).coeToSubmodule :=
    (LinearEquiv.ofInjective (Algebra.linearMap R K) hinj).trans (LinearEquiv.ofEq _ _ hone)
  refine Submodule.Quotient.equiv (J : Submodule R R) _ ν ?_
  apply le_antisymm
  · rintro _ ⟨r, hr, rfl⟩
    rw [Submodule.mem_comap]
    change (ν r : K) ∈ (↑J : FractionalIdeal R⁰ K).coeToSubmodule
    have hν : (ν r : K) = algebraMap R K r := by
      change ((ν r : (1 : FractionalIdeal R⁰ K).coeToSubmodule) : K) = algebraMap R K r
      rw [show ν r = (LinearEquiv.ofEq _ _ hone)
          (LinearEquiv.ofInjective (Algebra.linearMap R K) hinj r) from rfl,
        LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply, Algebra.linearMap_apply]
    rw [hν, FractionalIdeal.mem_coe]
    exact FractionalIdeal.mem_coeIdeal_of_mem _ hr
  · rintro ⟨y, hy1⟩ hy2
    rw [Submodule.mem_comap] at hy2
    rw [FractionalIdeal.mem_coe, FractionalIdeal.mem_coeIdeal] at hy2
    obtain ⟨r, hr, hry⟩ := hy2
    refine ⟨r, hr, ?_⟩
    apply Subtype.ext
    change (ν r : K) = y
    rw [show ν r = (LinearEquiv.ofEq _ _ hone)
        (LinearEquiv.ofInjective (Algebra.linearMap R K) hinj r) from rfl,
      LinearEquiv.coe_ofEq_apply, LinearEquiv.ofInjective_apply, Algebra.linearMap_apply]
    exact hry

omit [DecidableEq F] in
/-- **The invertible-ideal quotient isomorphism `I/(I·J) ≃ R/J`.** For nonzero ideals `I, J` of the
(Dedekind) coordinate ring `R`, the `R`-module quotient of the ideal `I` (viewed as a submodule of
`R`) by its submodule `I·J` is `R`-linearly isomorphic to `R/J`; this holds because `I` is
invertible. -/
noncomputable def quotIdealMulEquiv [W.IsElliptic] {I J : Ideal W.CoordinateRing}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    ((I : Submodule W.CoordinateRing W.CoordinateRing) ⧸
        Submodule.comap (I : Submodule W.CoordinateRing W.CoordinateRing).subtype
          ((I * J) : Submodule W.CoordinateRing W.CoordinateRing))
      ≃ₗ[W.CoordinateRing] (W.CoordinateRing ⧸ J) := by
  set R := W.CoordinateRing
  set K := W.FunctionField
  have hinj : Function.Injective (Algebra.linearMap R K) := FaithfulSMul.algebraMap_injective R K
  have hH : (↑I : FractionalIdeal R⁰ K) * (↑J : FractionalIdeal R⁰ K)
      = (1 : FractionalIdeal R⁰ K) * (↑(I * J) : FractionalIdeal R⁰ K) := by
    rw [one_mul, ← FractionalIdeal.coeIdeal_mul]
  have hle1 : (↑(I * J) : FractionalIdeal R⁰ K) ≤ (↑I : FractionalIdeal R⁰ K) := by
    rw [FractionalIdeal.coeIdeal_le_coeIdeal]; exact Ideal.mul_le_right
  have hle2 : (↑J : FractionalIdeal R⁰ K) ≤ (1 : FractionalIdeal R⁰ K) :=
    FractionalIdeal.coeIdeal_le_one
  have hJne : (↑J : FractionalIdeal R⁰ K) ≠ 0 := by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  have hIne : (↑I : FractionalIdeal R⁰ K) ≠ 0 := by rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
  have eqe := FractionalIdeal.quotientEquiv (R := R) (K := K) (↑I) (↑(I * J)) 1 (↑J)
    hH hle1 hle2 hJne hIne
  exact (quotComapEquivCoeIdealQuot_aux hinj).trans
    (eqe.trans (quotEquivOneCoeIdealQuot_aux hinj).symm)

omit [DecidableEq F] in
/-- **General codimension additivity.** For arbitrary nonzero ideals `I, J` of
`R := W.CoordinateRing`,
`finrank F (R ⧸ I·J) = finrank F (R ⧸ I) + finrank F (R ⧸ J)`. This upgrades `finrank_quotient_smul`
(the principal-factor case) to all factors, via the short exact sequence
`0 → I/(I·J) → R/(I·J) → R/I → 0` (`Submodule.quotientQuotientEquivQuotient` +
`Submodule.finrank_quotient_add_finrank`) together with the invertible-ideal kernel identification
`I/(I·J) ≃ R/J` (`quotIdealMulEquiv`). It is the genus-1 norm-degree additivity in `F`-codimension
form. -/
theorem finrank_quotient_mul [W.IsElliptic] {I J : Ideal W.CoordinateRing}
    (hI : I ≠ ⊥) (hJ : J ≠ ⊥) :
    Module.finrank F (W.CoordinateRing ⧸ (I * J)) =
      Module.finrank F (W.CoordinateRing ⧸ I) + Module.finrank F (W.CoordinateRing ⧸ J) := by
  have hIJ : I * J ≠ ⊥ := mul_ne_zero hI hJ
  haveI : FiniteDimensional F (W.CoordinateRing ⧸ (I * J)) :=
    finiteDimensional_quotient_of_ne_bot _ hIJ
  haveI : FiniteDimensional F (W.CoordinateRing ⧸ I) := finiteDimensional_quotient_of_ne_bot _ hI
  haveI : FiniteDimensional F (W.CoordinateRing ⧸ J) := finiteDimensional_quotient_of_ne_bot _ hJ
  have hIJ_le : I * J ≤ I := Ideal.mul_le_right
  set M : Submodule (W.CoordinateRing) (W.CoordinateRing ⧸ (I * J)) :=
    Submodule.map (Submodule.mkQ (I * J))
      (I : Submodule (W.CoordinateRing) (W.CoordinateRing)) with hM
  have e1 : ((W.CoordinateRing ⧸ (I * J)) ⧸ M) ≃ₗ[W.CoordinateRing] W.CoordinateRing ⧸ I :=
    Submodule.quotientQuotientEquivQuotient (I * J) I hIJ_le
  have e2a : M ≃ₗ[W.CoordinateRing]
      ((I : Submodule W.CoordinateRing W.CoordinateRing) ⧸
        Submodule.comap (I : Submodule W.CoordinateRing W.CoordinateRing).subtype
          ((I * J) : Submodule W.CoordinateRing W.CoordinateRing)) := by
    set R := W.CoordinateRing
    set g : (I : Submodule R R) →ₗ[R] (R ⧸ (I * J)) :=
      (Submodule.mkQ (I * J)).comp (I : Submodule R R).subtype with hg
    have hrange : LinearMap.range g = M := by
      rw [hM, hg, LinearMap.range_comp]; congr 1; exact Submodule.range_subtype _
    have hker : LinearMap.ker g
        = Submodule.comap (I : Submodule R R).subtype ((I * J) : Submodule R R) := by
      rw [hg, LinearMap.ker_comp, Submodule.ker_mkQ]
    have e3 : (LinearMap.range g) ≃ₗ[R] M := LinearEquiv.ofEq _ _ hrange
    exact ((Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivRange.trans e3)).symm
  have eM : M ≃ₗ[W.CoordinateRing] (W.CoordinateRing ⧸ J) := e2a.trans (quotIdealMulEquiv hI hJ)
  haveI : FiniteDimensional F M := (eM.restrictScalars F).symm.finiteDimensional
  have key : Module.finrank F ((W.CoordinateRing ⧸ (I * J)) ⧸ (M.restrictScalars F))
      + Module.finrank F (M.restrictScalars F) = Module.finrank F (W.CoordinateRing ⧸ (I * J)) :=
    Submodule.finrank_quotient_add_finrank (M.restrictScalars F)
  have hA : Module.finrank F ((W.CoordinateRing ⧸ (I * J)) ⧸ (M.restrictScalars F))
      = Module.finrank F (W.CoordinateRing ⧸ I) := (e1.restrictScalars F).finrank_eq
  have hB : Module.finrank F (M.restrictScalars F) = Module.finrank F (W.CoordinateRing ⧸ J) :=
    (eM.restrictScalars F).finrank_eq
  rw [hA, hB] at key
  lia

omit [DecidableEq F] in
/-- **Class-group linkage.** The class `ClassGroup.mk0` of the integral point ideal
`XYIdeal W x (C y)` equals the class `ClassGroup.mk (XYIdeal' h)` appearing in the target predicate:
both are the class of the same fractional ideal. -/
theorem mk0_eq_mk_XYIdeal' [W.IsElliptic] {x y : F} (h : W.Nonsingular x y)
    (hmem : CoordinateRing.XYIdeal W x (C y) ∈ (Ideal W.CoordinateRing)⁰) :
    ClassGroup.mk0 ⟨CoordinateRing.XYIdeal W x (C y), hmem⟩
      = ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' h) := by
  rw [← ClassGroup.mk_mk0 W.FunctionField]
  congr 1
  apply Units.ext
  rw [FractionalIdeal.coe_mk0, CoordinateRing.XYIdeal'_eq h]

omit [DecidableEq F] in
/-- **Codimension-0 endpoint.** A nonzero integral ideal `I` with `finrank F (R/I) = 0` is the whole
ring, hence principal: its class is trivial. -/
theorem mk0_eq_one_of_finrank_quotient_eq_zero [W.IsElliptic] (I : Ideal W.CoordinateRing)
    (hmem : I ∈ (Ideal W.CoordinateRing)⁰)
    [FiniteDimensional F (W.CoordinateRing ⧸ I)]
    (hfin : Module.finrank F (W.CoordinateRing ⧸ I) = 0) :
    ClassGroup.mk0 ⟨I, hmem⟩ = 1 := by
  have hss : Subsingleton (W.CoordinateRing ⧸ I) := Module.finrank_zero_iff.mp hfin
  have htop : I = ⊤ := by rw [Ideal.Quotient.subsingleton_iff] at hss; exact hss
  rw [ClassGroup.mk0_eq_one_iff, htop]
  exact top_isPrincipal

omit [DecidableEq F] in
/-- **Codimension-1 endpoint.** A nonzero integral ideal `J` with `finrank F (R/J) = 1` has class
equal to that of an `XYIdeal'` for a nonsingular point: combine the point-ideal characterisation
(`eq_XYIdeal_of_finrank_quotient_eq_one`) with the class-group linkage. -/
theorem mk0_eq_mk_XYIdeal'_of_finrank_quotient_eq_one [W.IsElliptic] (J : Ideal W.CoordinateRing)
    (hmem : J ∈ (Ideal W.CoordinateRing)⁰)
    (hfin : Module.finrank F (W.CoordinateRing ⧸ J) = 1) :
    ∃ (x y : F) (h : W.Nonsingular x y),
      ClassGroup.mk0 ⟨J, hmem⟩ = ClassGroup.mk W.FunctionField (CoordinateRing.XYIdeal' h) := by
  haveI : Nontrivial (W.CoordinateRing ⧸ J) := Module.nontrivial_of_finrank_eq_succ hfin
  obtain ⟨x, y, h, hJ⟩ := eq_XYIdeal_of_finrank_quotient_eq_one J hfin
  have hmem' : CoordinateRing.XYIdeal W x (C y) ∈ (Ideal W.CoordinateRing)⁰ := hJ ▸ hmem
  refine ⟨x, y, h, ?_⟩
  rw [show (⟨J, hmem⟩ : (Ideal W.CoordinateRing)⁰) = ⟨CoordinateRing.XYIdeal W x (C y), hmem'⟩ from
    Subtype.ext hJ, mk0_eq_mk_XYIdeal' h hmem']

/-- **The class-group reduction predicate (genus-1 Riemann–Roch core).** Every nonzero integral
ideal class has a representative of `F`-codimension `≤ 1`: it is either trivial, or `mk0`-equal to a
codimension-1 ideal. This is the single remaining genus-1 input; geometrically it is the statement
that every degree-0 divisor class on the curve has an effective representative of degree `≤ 1`
(Riemann–Roch with `g = 1`). It is the surjectivity dual of the codimension lower bound that powers
mathlib's `toClass_injective`. -/
def ClassReducesToCodimLEOne (W : WeierstrassCurve.Affine F) [IsDedekindDomain W.CoordinateRing] :
    Prop :=
  ∀ I : (Ideal W.CoordinateRing)⁰,
    ClassGroup.mk0 I = 1 ∨
      ∃ (J : Ideal W.CoordinateRing) (hmem : J ∈ (Ideal W.CoordinateRing)⁰),
        Module.finrank F (W.CoordinateRing ⧸ J) = 1 ∧
          ClassGroup.mk0 I = ClassGroup.mk0 ⟨J, hmem⟩

omit [DecidableEq F] in
/-- **The codimension reduction implies the integral-ideal reduction.** Feeding the codimension-1
representative through the codimension-1 endpoint converts `ClassReducesToCodimLEOne` into
`IntegralIdealRepresentableByPoints`. This is the bridge that makes the genus-1 input the *only*
remaining gap. -/
theorem integralIdealRepresentableByPoints_of_classReducesToCodimLEOne [W.IsElliptic]
    (hred : ClassReducesToCodimLEOne W) :
    IntegralIdealRepresentableByPoints W := by
  intro I
  obtain (h1 | ⟨J, hmem, hfin, hIJ⟩) := hred I
  · exact Or.inl h1
  · obtain ⟨x, y, h, hJcl⟩ := mk0_eq_mk_XYIdeal'_of_finrank_quotient_eq_one J hmem hfin
    exact Or.inr ⟨x, y, h, hIJ.trans hJcl⟩

/-- **Surjectivity of `toClass` from the genus-1 codimension reduction.** Combining
`ClassReducesToCodimLEOne` with the (free, axiom-clean) Dedekind instance on `W.CoordinateRing`
yields surjectivity of `toClass`. This is the cleanest factorisation of the remaining work: the only
input is the genus-1 codimension reduction. -/
theorem toClass_surjective_of_classReducesToCodimLEOne [W.IsElliptic]
    (hred : ClassReducesToCodimLEOne W) :
    Function.Surjective (toClass (W := W)) :=
  toClass_surjective_of_integralIdealRep
    (integralIdealRepresentableByPoints_of_classReducesToCodimLEOne hred)

omit [DecidableEq F] in
private theorem two_nsmul_degree_le' {p : F[X]} {n : ℕ} (hp : p.degree < (n : ℕ)) :
    2 • p.degree ≤ ((2 * (n - 1) : ℕ) : WithBot ℕ) := by
  by_cases h0 : p = 0
  · simp [h0]
  · have hnd : p.natDegree ≤ n - 1 := by
      have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hp; lia
    rw [Polynomial.degree_eq_natDegree h0,
      show (2 : ℕ) • (p.natDegree : WithBot ℕ) = ((2 * p.natDegree : ℕ) : WithBot ℕ) by
        rw [nsmul_eq_mul]; push_cast; ring, Nat.cast_le]
    lia

/-- **The basis-combination map** `(p, q) ↦ p · 1 + q · Ȳ`, restricted to polynomials of bounded
degree (`degreeLT F a × degreeLT F b`), as an `F`-linear map into `R`. Its image is the space of
elements whose norm degree we can control; its kernel intersected with the codimension count gives
the Riemann–Roch element. -/
noncomputable def basisCombMap (W : WeierstrassCurve.Affine F) (a b : ℕ) :
    (Polynomial.degreeLT F a × Polynomial.degreeLT F b) →ₗ[F] W.CoordinateRing where
  toFun pq := (pq.1 : F[X]) • (1 : W.CoordinateRing) + (pq.2 : F[X]) • (CoordinateRing.basis W 1)
  map_add' x y := by
    simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, add_smul]; abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, RingHom.id_apply, smul_add]
    rw [smul_assoc, smul_assoc]

omit [DecidableEq F] in
/-- **Norm-degree bound for basis combinations.** If `deg p < da` and `deg q < db`, the norm degree
of `p · 1 + q · Ȳ` is at most `max (2(da-1)) (2 db + 1)`. From `degree_norm_smul_basis`
(`= max (2 deg p) (2 deg q + 3)`): the first term is `≤ 2(da-1)`; the second is `≤ 2 db + 1`
(when `q = 0` the term is `⊥`, otherwise `db ≥ 1` and `2 deg q + 3 ≤ 2(db-1) + 3 = 2 db + 1`). -/
theorem natDegree_norm_basisComb_le {p q : F[X]} {da db : ℕ}
    (hp : p.degree < (da : ℕ)) (hq : q.degree < (db : ℕ)) :
    (Algebra.norm F[X] (p • (1 : W.CoordinateRing) + q • CoordinateRing.basis W 1)).natDegree
      ≤ max (2 * (da - 1)) (2 * db + 1) := by
  rw [CoordinateRing.basis_one, Polynomial.natDegree_le_iff_degree_le,
    CoordinateRing.degree_norm_smul_basis]
  rw [show ((max (2 * (da - 1)) (2 * db + 1) : ℕ) : WithBot ℕ)
      = max ((2 * (da - 1) : ℕ) : WithBot ℕ) ((2 * db + 1 : ℕ) : WithBot ℕ) by rfl]
  apply max_le_max
  · exact two_nsmul_degree_le' hp
  · by_cases h0 : q = 0
    · simp only [h0, degree_zero]
      rw [show (2 : ℕ) • (⊥ : WithBot ℕ) = ⊥ by simp]; simp
    · have hqd : q.natDegree ≤ db - 1 := by
        have := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hq; lia
      have hdb1 : 1 ≤ db := by
        by_contra hc
        rw [Nat.lt_one_iff.mp (Nat.not_le.mp hc), Nat.cast_zero] at hq
        exact absurd ((Polynomial.zero_le_degree_iff.mpr h0).trans_lt hq) (by simp)
      rw [Polynomial.degree_eq_natDegree h0,
        show (2 : ℕ) • (q.natDegree : WithBot ℕ) = ((2 * q.natDegree : ℕ) : WithBot ℕ) by
          rw [nsmul_eq_mul]; push_cast; ring]
      have h3 : (3 : WithBot ℕ) = ((3 : ℕ) : WithBot ℕ) := by norm_cast
      rw [h3, ← Nat.cast_add, Nat.cast_le]; lia

omit [DecidableEq F] in
/-- **Injectivity of basis combinations.** A nonzero `(p, q)` maps to a nonzero element of `R`,
since `{1, Ȳ}` is `F[X]`-linearly independent (`CoordinateRing.smul_basis_eq_zero`). -/
theorem basisCombMap_ne_zero {a b : ℕ} (pq : Polynomial.degreeLT F a × Polynomial.degreeLT F b)
    (h : pq ≠ 0) : basisCombMap W a b pq ≠ 0 := by
  intro hz
  apply h
  rw [basisCombMap] at hz
  simp only [LinearMap.coe_mk, AddHom.coe_mk] at hz
  rw [CoordinateRing.basis_one] at hz
  obtain ⟨hp, hq⟩ := CoordinateRing.smul_basis_eq_zero hz
  exact Prod.ext (Subtype.ext hp) (Subtype.ext hq)

omit [DecidableEq F] in
/-- **The genus-1 Riemann–Roch inequality (concrete form).** Every nonzero ideal `I` of
`R := W.CoordinateRing` contains a nonzero element `a` with `(Algebra.norm F[X] a).natDegree ≤
finrank F (R ⧸ I) + 1`. This is `ℓ(D) ≥ deg D` for `g = 1` made explicit, proved by the exact
`F`-dimension count: the bounded-degree basis combinations form an `F`-subspace of dimension
`ℓ + 1 > ℓ = finrank F (R ⧸ I)`, so rank–nullity for its composite into `R ⧸ I` forces a nonzero
kernel element. No finiteness of `F` is needed (`F[X]` is Euclidean). -/
theorem exists_mem_norm_natDegree_le [W.IsElliptic] (I : Ideal W.CoordinateRing) (hI : I ≠ ⊥) :
    ∃ a ∈ I, a ≠ 0 ∧
      (Algebra.norm F[X] a).natDegree ≤ Module.finrank F (W.CoordinateRing ⧸ I) + 1 := by
  classical
  set R := W.CoordinateRing
  set ℓ := Module.finrank F (R ⧸ I) with hℓ
  haveI : FiniteDimensional F (R ⧸ I) := finiteDimensional_quotient_of_ne_bot _ hI
  obtain ⟨da, hda⟩ : ∃ da, da = (ℓ + 1) / 2 + 1 := ⟨_, rfl⟩
  obtain ⟨db, hdb⟩ : ∃ db, db = ℓ / 2 := ⟨_, rfl⟩
  set ψ : (Polynomial.degreeLT F da × Polynomial.degreeLT F db) →ₗ[F] (R ⧸ I) :=
    ((Submodule.mkQ I).restrictScalars F).comp (basisCombMap W da db) with hψ
  have hdimdom :
      Module.finrank F (Polynomial.degreeLT F da × Polynomial.degreeLT F db) = da + db := by
    rw [Module.finrank_prod, (Polynomial.degreeLTEquiv F da).finrank_eq,
      (Polynomial.degreeLTEquiv F db).finrank_eq, Module.finrank_fin_fun, Module.finrank_fin_fun]
  have hdomℓ : Module.finrank F (Polynomial.degreeLT F da × Polynomial.degreeLT F db) = ℓ + 1 := by
    rw [hdimdom, hda, hdb]; lia
  have hrn : Module.finrank F (LinearMap.range ψ) + Module.finrank F (LinearMap.ker ψ)
      = Module.finrank F (Polynomial.degreeLT F da × Polynomial.degreeLT F db) :=
    ψ.finrank_range_add_finrank_ker
  have hrange_le : Module.finrank F (LinearMap.range ψ) ≤ ℓ :=
    le_trans (Submodule.finrank_le _) (le_of_eq hℓ.symm)
  have hker_pos : 0 < Module.finrank F (LinearMap.ker ψ) := by lia
  haveI : Nontrivial (LinearMap.ker ψ) := Module.nontrivial_of_finrank_pos hker_pos
  obtain ⟨z, hz⟩ := exists_ne (0 : LinearMap.ker ψ)
  set pq := (z : Polynomial.degreeLT F da × Polynomial.degreeLT F db) with hpq
  have hpq_ne : pq ≠ 0 := fun h => hz (Subtype.ext h)
  refine ⟨basisCombMap W da db pq, ?_, basisCombMap_ne_zero pq hpq_ne, ?_⟩
  · have hz0 : ψ pq = 0 := z.2
    rw [hψ, LinearMap.comp_apply, LinearMap.restrictScalars_apply, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hz0
    exact hz0
  · obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := pq
    rw [Polynomial.mem_degreeLT] at hp hq
    have hbound := natDegree_norm_basisComb_le (W := W) hp hq
    rw [basisCombMap]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    refine le_trans hbound ?_
    rw [hda, hdb]; omega

omit [DecidableEq F] in
/-- **Codimension-`≤ 1` representative of an inverse class.** For any nonzero integral ideal `I'`,
there is an integral ideal `J` of `F`-codimension `≤ 1` whose class is `(ClassGroup.mk0 I')⁻¹`.
Proof: a Riemann–Roch element `a ∈ I'` (norm degree `≤ finrank F (R ⧸ I') + 1`) gives
`(a) = I' · J`; additivity (`finrank_quotient_mul`) bounds `finrank F (R ⧸ J) ≤ 1`, and
`[I'] · [J] = [(a)] = 1`. -/
theorem exists_codimLEOne_inv [W.IsElliptic] (I' : (Ideal W.CoordinateRing)⁰) :
    ∃ (J : Ideal W.CoordinateRing) (hmem : J ∈ (Ideal W.CoordinateRing)⁰),
      Module.finrank F (W.CoordinateRing ⧸ J) ≤ 1 ∧
        ClassGroup.mk0 ⟨J, hmem⟩ = (ClassGroup.mk0 I')⁻¹ := by
  have hI'ne : (I' : Ideal W.CoordinateRing) ≠ ⊥ :=
    mem_nonZeroDivisors_iff_ne_zero.mp I'.2
  obtain ⟨a, ha_mem, ha, hbound⟩ :=
    exists_mem_norm_natDegree_le (F := F) (I' : Ideal W.CoordinateRing) hI'ne
  have hle : Ideal.span {a} ≤ (I' : Ideal W.CoordinateRing) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]; exact ha_mem
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.mpr hle
  have hspan_ne : Ideal.span ({a} : Set W.CoordinateRing) ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  have hJne : J ≠ ⊥ := by intro h; rw [h, Ideal.mul_bot] at hJ; exact hspan_ne hJ
  have hJmem : J ∈ (Ideal W.CoordinateRing)⁰ := mem_nonZeroDivisors_iff_ne_zero.mpr hJne
  refine ⟨J, hJmem, ?_, ?_⟩
  · have h1 : Module.finrank F (W.CoordinateRing ⧸ Ideal.span {a})
        = Module.finrank F (W.CoordinateRing ⧸ (I' : Ideal W.CoordinateRing))
          + Module.finrank F (W.CoordinateRing ⧸ J) := by
      rw [hJ]; exact finrank_quotient_mul hI'ne hJne
    have h2 : Module.finrank F (W.CoordinateRing ⧸ Ideal.span {a})
        = (Algebra.norm F[X] a).natDegree :=
      finrank_quotient_span_eq_natDegree_norm (CoordinateRing.basis W) ha
    lia
  · rw [eq_inv_iff_mul_eq_one, mul_comm,
      ← MonoidHom.map_mul ClassGroup.mk0, ClassGroup.mk0_eq_one_iff, Submonoid.coe_mul, ← hJ]
    exact ⟨a, rfl⟩

omit [DecidableEq F] in
/-- **The genus-1 codimension reduction holds unconditionally** for an elliptic curve. Apply
`exists_codimLEOne_inv` to a representative of the inverse class `(ClassGroup.mk0 I)⁻¹`: the
resulting codimension-`≤ 1` ideal `J` has class `(ClassGroup.mk0 I')⁻¹ = ClassGroup.mk0 I`, and
codimension `0` collapses to the trivial class. -/
theorem classReducesToCodimLEOne_holds [W.IsElliptic] :
    ClassReducesToCodimLEOne W := by
  intro I
  obtain ⟨I', hI'⟩ := ClassGroup.mk0_surjective (ClassGroup.mk0 I)⁻¹
  obtain ⟨J, hJmem, hfinle, hmk0⟩ := exists_codimLEOne_inv (F := F) I'
  rw [hI', inv_inv] at hmk0
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hfinle with h0 | h1
  · left
    haveI : FiniteDimensional F (W.CoordinateRing ⧸ J) :=
      finiteDimensional_quotient_of_ne_bot _ (mem_nonZeroDivisors_iff_ne_zero.mp hJmem)
    have hone : ClassGroup.mk0 ⟨J, hJmem⟩ = 1 :=
      mk0_eq_one_of_finrank_quotient_eq_zero J hJmem h0
    rw [hmk0] at hone; exact hone
  · right
    exact ⟨J, hJmem, h1, hmk0.symm⟩

/-- **Surjectivity of `WeierstrassCurve.Affine.Point.toClass`**, under the genus-1 divisor-reduction
hypothesis `ClassRepresentableByPoints W`. See `toClass_surjective'` for the unconditional form. -/
theorem toClass_surjective (hrep : ClassRepresentableByPoints W) :
    Function.Surjective (toClass (W := W)) :=
  toClass_surjective_of_classRepresentableByPoints hrep

/-- **The isomorphism `E ≅ Pic⁰(E)` (affine model)**: the group isomorphism
`W.Point ≃+ Additive (ClassGroup W.CoordinateRing)`, under the genus-1 divisor-reduction hypothesis
`ClassRepresentableByPoints W`. See `toClassEquiv'` for the unconditional form. -/
noncomputable def toClassEquiv (hrep : ClassRepresentableByPoints W) :
    W.Point ≃+ Additive (ClassGroup W.CoordinateRing) :=
  toClassEquiv_of_surjective (toClass_surjective hrep)

@[simp]
theorem toClassEquiv_apply (hrep : ClassRepresentableByPoints W) (P : W.Point) :
    toClassEquiv hrep P = toClass P :=
  rfl

/-- **Unconditional surjectivity of `toClass`** for an elliptic curve `W`. Every element of the
affine ideal class group `Pic⁰(E)` is in the range of `toClass`, i.e. is represented by a rational
point. Combines the genus-1 codimension reduction `classReducesToCodimLEOne_holds` with the
axiom-clean Dedekind structure on `W.CoordinateRing`. -/
theorem toClass_surjective' [W.IsElliptic] :
    Function.Surjective (toClass (W := W)) :=
  toClass_surjective_of_classReducesToCodimLEOne classReducesToCodimLEOne_holds

/-- **The isomorphism `E ≅ Pic⁰(E)` (affine model), unconditional.** For an elliptic curve `W`, the
group isomorphism `W.Point ≃+ Additive (ClassGroup W.CoordinateRing)`, built from mathlib's
`toClass_injective` and the unconditional surjectivity `toClass_surjective'`. -/
noncomputable def toClassEquiv' [W.IsElliptic] :
    W.Point ≃+ Additive (ClassGroup W.CoordinateRing) :=
  toClassEquiv_of_surjective toClass_surjective'

@[simp]
theorem toClassEquiv'_apply [W.IsElliptic] (P : W.Point) :
    toClassEquiv' P = toClass P :=
  rfl

end WeierstrassCurve.Affine.Point
