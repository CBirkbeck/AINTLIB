/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.Moduli.EllCategory
import ModularCurves.ForMathlib.TateNormalForm
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Representability: Tate normal form, Y₁(N), Y(N) (Loeffler §§3.3–3.4, 3.8; KM Ch. 3–5)

The concrete representability results. The **elementary spine** (Loeffler §3.3) is stated
at ring level, where mathlib's Weierstrass API applies *today* — these are the first
provable (not merely stateable) targets of the project:

* **Tate normal form** (Loeffler Prop 3.3.4): for an elliptic `W/R` with a point `(x, y)`
  nowhere of order 1, 2, 3, there is a unique change of variables bringing `(W, (x,y))`
  to the form `Y² + αXY + βY = X³ + βX²` with the point at `(0,0)`.
* **The universal Tate curve** (Loeffler Cor 3.3.5): `Spec ℤ[A,B][Δ⁻¹]` "represents the
  functor `S ↦ {eq. classes of pairs (E,P), E/S elliptic curve, P ∈ E(S) not of order
  1, 2, 3 in any fibre}`."
* **`Y₁(N)`** (Loeffler Def 3.3.6 & Thm 3.4.4): for `N ≥ 4` the naive-`Γ₁(N)` moduli
  problem over `ℤ[1/N]` is representable, smooth and affine. Built on the spine below; the
  representability theorem `gammaOneNaive_representable` now lives in
  `Moduli/NaiveProblems.lean` (assembled in `ModularCurve/YOneAssembly.lean`).
* **`Y(N)`** (Loeffler Fact 3.8.1–3.8.3; KM 3.1, 4.7, 5.1): for `N ≥ 3`, `[Γ(N)]` is
  rigid and representable, smooth affine over `ℤ[1/N]`; `gammaFullNaive_representable`
  likewise now lives in `Moduli/NaiveProblems.lean`.

The nowhere-order-≤3 condition is expressed ring-theoretically through the division
polynomials (`ψ₂`, `ψ₃` — mathlib `WeierstrassCurve.Ψ`): a function on `Spec R` is nowhere
zero iff it is a unit.
-/

open AlgebraicGeometry CategoryTheory Polynomial

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

universe u

namespace ModularCurves

section TateNormalForm

variable {R : Type u} [CommRing R]

/-- Tate normal form: `Y² + αXY + βY = X³ + βX²`, i.e. `a₂ = a₃ ( = β)`, `a₄ = a₆ = 0`.
Source: Loeffler §3.3 Def 3.3.3 (with `α = a₁`, `β = a₂ = a₃`). -/
def _root_.WeierstrassCurve.IsTateNormal (W : WeierstrassCurve R) : Prop :=
  W.a₂ = W.a₃ ∧ W.a₄ = 0 ∧ W.a₆ = 0

/-- The point `(x, y)` on `W` is *nowhere of order 1, 2 or 3*: the product
`ψ₂(x,y) · ψ₃(x,y)` of division-polynomial values is a unit of `R` (equivalently: in no
residue field does `P` become `0`, 2-torsion, or 3-torsion; the affine point is nowhere
`0` automatically). The order-3 direction of the dictionary uses nonsingularity —
supplied by `[W.IsElliptic]` at every use site, not by this definition.
Source: Loeffler Prop 3.3.4 hypothesis "`P, 2P, 3P ≠ 0` in any
fibre"; division-polynomial dictionary: Silverman III Ex. 3.7 / mathlib
`WeierstrassCurve.Ψ`. -/
def NowhereOrderLEThree (W : WeierstrassCurve R) (x y : R) : Prop :=
  IsUnit ((W.Ψ 2).evalEval x y * (W.Ψ 3).evalEval x y)

open WeierstrassCurve.Affine in
/-- **(T-E1 = Loeffler Prop 3.3.4, ring level — PROVABLE-NOW target)** If `W/R` is
elliptic and `(x, y)` is a rational point nowhere of order `≤ 3`, there exist unique
`(α, β)` and a unique change of variables `vc` with `vc • W` in Tate normal form and
`(x, y) ↦ (0, 0)` (i.e. `vc.r = x`, `vc.t = y`).
Proof route (Loeffler): translate `P` to `(0,0)`; not 2-torsion ⇒ tangent line
non-vertical ⇒ shear to kill `a₄`-term; not an inflexion (not 3-torsion) ⇒ `a₂`-scaling;
uniqueness by comparing coefficients. All at the level of mathlib's `VariableChange`. -/
theorem exists_unique_variableChange_isTateNormal (W : WeierstrassCurve R) [W.IsElliptic]
    (x y : R) (h : W.toAffine.Equation x y) (hord : NowhereOrderLEThree W x y) :
    ∃! vc : WeierstrassCurve.VariableChange R,
      (vc • W).IsTateNormal ∧ vc.r = x ∧ vc.t = y := by
  obtain hR | hR := subsingleton_or_nontrivial R
  · exact ⟨⟨1, x, 0, y⟩, ⟨⟨Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _⟩,
      rfl, rfl⟩, fun vc _ ↦ by ext <;> subsingleton⟩
  · obtain ⟨h2, h3⟩ := IsUnit.mul_iff.mp hord
    simp only [W.Ψ_two, W.Ψ_three, evalEval_C] at h2 h3
    have hns : W.toAffine.Nonsingular x y := ⟨h, Or.inr h2.ne_zero⟩
    have : (Point.some x y hns).NeZero := ⟨Point.some_ne_zero hns⟩
    have : (Point.some x y hns).TwiceNeZero := Point.twiceNeZero_of_isUnit _ h2
    have : (Point.some x y hns).ThriceNeZero := Point.thriceNeZero_of_isUnit _ h3
    exact ⟨W.toAffine.toTateNF (.some x y hns), ⟨⟨toTateNF_a₂₃ W (.some x y hns),
      toTateNF_a₄ W (.some x y hns), toTateNF_a₆ W (.some x y hns)⟩, rfl, rfl⟩,
      fun vc hvc ↦ toTateNF_unique W (.some x y hns) vc hvc.2.1 hvc.2.2 hvc.1.2.1 hvc.1.1⟩

/-- The universal Tate-normal Weierstrass curve `E(A, B) : Y² + AXY + BY = X³ + BX²` over
`ℤ[A, B]`. Source: Loeffler Def 3.3.3. -/
noncomputable def tateCurve : WeierstrassCurve (MvPolynomial (Fin 2) ℤ) :=
  { a₁ := MvPolynomial.X 0
    a₂ := MvPolynomial.X 1
    a₃ := MvPolynomial.X 1
    a₄ := 0
    a₆ := 0 }

/-- The universal Tate curve is in Tate normal form. Sanity pin with no downstream
consumer: it certifies `tateCurve` matches `IsTateNormal` by construction. -/
theorem tateCurve_isTateNormal : tateCurve.IsTateNormal := ⟨rfl, rfl, rfl⟩

/-- The coordinate ring `ℤ[A, B][Δ(A,B)⁻¹]` of the universal Tate curve — the affine ring
of (the coarse ring-level avatar of) the universal elliptic curve with a point of nowhere
order ≤ 3. Source: Loeffler Cor 3.3.5. -/
noncomputable abbrev tateRing : Type :=
  Localization.Away tateCurve.Δ

private lemma tateRing_eval₂Hom_comp (A : Type u) [CommRing A] (φ : tateRing →+* A) :
    MvPolynomial.eval₂Hom (Int.castRingHom A) (fun i : Fin 2 ↦ if i = 0 then
        φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing (MvPolynomial.X 0))
        else φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing (MvPolynomial.X 1))) =
      φ.comp (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing) :=
  MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun i ↦ by fin_cases i <;> simp

/-- **(T-E2 = Loeffler Cor 3.3.5, ring level — PROVABLE-NOW target)** For every ring `A`,
ring homomorphisms `tateRing →+* A` correspond exactly to pairs `(α, β) ∈ A²` with
`Δ(α, β)` a unit — i.e. to Tate-normal elliptic curves over `A` marked at `(0, 0)`.
(Universal property of polynomial ring + localization; with `T-E1` this is Loeffler's
"`(Spec ℤ[A,B,Δ(A,B)⁻¹], (E(A,B),(0:0:1)))` represents the functor `S ↦ {eq. classes of
pairs (E,P) … P ∈ E(S) not of order 1,2,3 in any fibre}`".)

ADVERSARIAL FIX (2026-07-06): the bare `Nonempty (≃)` form was a cardinality-only
claim (dischargeable for e.g. `A = ℂ` by counting); the equivalence is now PINNED to
the canonical evaluation map `φ ↦ (φ A, φ B)` — naturality in `A` follows from the
pin.

Proven register item: this is the **absolute (ℤ-base)** form of Loeffler Cor 3.3.5,
kept as the register anchor, and has no direct code consumer project-wide. The Y₁ tower
instead uses the `R`-relative analogue `TateAtlas.ringOverLift` (and its `→ₐ[R]` form
`TateAtlas.ringOverAlgLift`) in `ModularCurve/YOneAtlasClassify.lean`. -/
theorem tateRing_homEquiv (A : Type u) [CommRing A] :
    ∃ e : (tateRing →+* A) ≃
        { c : A × A //
          IsUnit ((tateCurve.map (MvPolynomial.eval₂Hom (Int.castRingHom A)
            (fun i ↦ if i = 0 then c.1 else c.2))).Δ) },
      ∀ φ : tateRing →+* A,
        ((e φ).1 : A × A) =
          (φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing (MvPolynomial.X 0)),
           φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing (MvPolynomial.X 1))) := by
  refine ⟨⟨fun φ ↦ ⟨(φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing (MvPolynomial.X 0)),
      φ (algebraMap (MvPolynomial (Fin 2) ℤ) tateRing (MvPolynomial.X 1))), ?_⟩,
    fun c ↦ IsLocalization.Away.lift tateCurve.Δ
      (WeierstrassCurve.map_Δ (A := A) tateCurve _ ▸ c.2), fun φ ↦ ?_, fun c ↦ ?_⟩, fun φ ↦ rfl⟩
  · rw [WeierstrassCurve.map_Δ, tateRing_eval₂Hom_comp A φ]
    exact (IsLocalization.Away.algebraMap_isUnit tateCurve.Δ).map φ
  · exact IsLocalization.ringHom_ext (Submonoid.powers tateCurve.Δ)
      ((IsLocalization.Away.lift_comp _ _).trans (tateRing_eval₂Hom_comp A φ))
  · simp

end TateNormalForm

section LevelModuli

variable (R : CommRingCat.{u})

/-- Sections pull back along `Ell/R` morphisms (contravariantly): given
`f : X ⟶ Y` in `Ell/R` and a section of `Y.curve`, the cartesian square produces a
section of `X.curve`. -/
noncomputable def EllHom.pullSection {X Y : EllObj R} (f : X ⟶ Y)
    (P : Y.curve.Section) : X.curve.Section :=
  ⟨f.isPullback.lift (f.baseHom ≫ P.1) (𝟙 X.base)
      (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp]),
    f.isPullback.lift_snd _ _ _⟩

/-- Pulling a section back along the identity gives the section back. -/
theorem EllHom.pullSection_id {X : EllObj R} (P : X.curve.Section) :
    EllHom.pullSection R (𝟙 X) P = P := by
  refine Subtype.ext ?_
  refine (𝟙 X : X ⟶ X).isPullback.hom_ext ?_ ?_
  · have h1 : (EllHom.pullSection R (𝟙 X) P).1 ≫ (𝟙 X : X ⟶ X).top =
        (𝟙 X : X ⟶ X).baseHom ≫ P.1 :=
      (𝟙 X : X ⟶ X).isPullback.lift_fst _ _ _
    rw [h1]
    show 𝟙 X.base ≫ P.1 = P.1 ≫ 𝟙 X.curve.E
    rw [Category.id_comp, Category.comp_id]
  · rw [(EllHom.pullSection R (𝟙 X) P).2, P.2]

/-- Pulling sections back is compatible with composition. -/
theorem EllHom.pullSection_comp {X Y Z : EllObj R} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : Z.curve.Section) :
    EllHom.pullSection R (f ≫ g) P =
      EllHom.pullSection R f (EllHom.pullSection R g P) := by
  refine Subtype.ext ?_
  refine (f ≫ g : X ⟶ Z).isPullback.hom_ext ?_ ?_
  · have h0 : (EllHom.pullSection R (f ≫ g) P).1 ≫ (f ≫ g : X ⟶ Z).top =
        (f ≫ g : X ⟶ Z).baseHom ≫ P.1 :=
      (f ≫ g : X ⟶ Z).isPullback.lift_fst _ _ _
    rw [h0]
    have h1 : (EllHom.pullSection R f (EllHom.pullSection R g P)).1 ≫ f.top =
        f.baseHom ≫ (EllHom.pullSection R g P).1 := f.isPullback.lift_fst _ _ _
    have h2 : (EllHom.pullSection R g P).1 ≫ g.top = g.baseHom ≫ P.1 :=
      g.isPullback.lift_fst _ _ _
    show (f.baseHom ≫ g.baseHom) ≫ P.1 =
      (EllHom.pullSection R f (EllHom.pullSection R g P)).1 ≫ f.top ≫ g.top
    calc (f.baseHom ≫ g.baseHom) ≫ P.1
        = f.baseHom ≫ g.baseHom ≫ P.1 := Category.assoc _ _ _
      _ = f.baseHom ≫ (EllHom.pullSection R g P).1 ≫ g.top := by rw [h2]
      _ = (f.baseHom ≫ (EllHom.pullSection R g P).1) ≫ g.top :=
          (Category.assoc _ _ _).symm
      _ = ((EllHom.pullSection R f (EllHom.pullSection R g P)).1 ≫ f.top) ≫ g.top := by
          rw [h1]
      _ = (EllHom.pullSection R f (EllHom.pullSection R g P)).1 ≫ f.top ≫ g.top :=
          Category.assoc _ _ _
  · rw [(EllHom.pullSection R (f ≫ g) P).2,
      (EllHom.pullSection R f (EllHom.pullSection R g P)).2]

/- **RELOCATED (Y1-CLOSER S4, v10.117 doctrine)**: `EllHom.pullSection_add`, the naive
problem functors `gammaOneNaiveProblem` / `gammaFullNaiveProblem`, and the held theorems
`gammaOneNaive_representable` / `gammaFullNaive_representable` now live BYTE-IDENTICAL
(statements unchanged; the three parked `sorry`s replaced by their designed fills through
A's `PullSectionCanonicity.lean`, per its in-file wiring note) in
`Moduli/NaiveProblems.lean` — which imports `PullSectionCanonicity`; the import here would
be cyclic (PullSectionCanonicity → PullSectionAdd → this file). -/

end LevelModuli


-- Ported from dev's Representability: main's version does not carry it, and
-- Moduli/GammaH + ModularCurve/YRho consume it.
/-- **(T-E4b ★, the level-preservation input — de-parks the naive functor sorries)**
`pullSection` preserves the naive full-level condition: killing transports through the
additivity (T-E4a), and fibrewise generation transports through the point-level
comparison `pointTransportEquiv` followed by the base-change dictionary — the
`EllHom`-form of `isNaiveFullLevel_pullAlong`. -/
theorem EllHom.isNaiveFullLevel_pullSection {N : ℕ} [NeZero N]
    {P Q : Y.curve.Section} (h : Y.curve.IsNaiveFullLevel N P Q) :
    X.curve.IsNaiveFullLevel N
      (EllHom.pullSection R f P) (EllHom.pullSection R f Q) := by
  obtain ⟨⟨hP, hQ⟩, hgen⟩ := h
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · calc (N : ℤ) • EllHom.pullSection R f P
        = AddMonoidHom.mk' (EllHom.pullSection R f)
            (EllHom.pullSection_add R f) ((N : ℤ) • P) :=
          (map_zsmul (AddMonoidHom.mk' (EllHom.pullSection R f)
            (EllHom.pullSection_add R f)) (N : ℤ) P).symm
      _ = AddMonoidHom.mk' (EllHom.pullSection R f)
            (EllHom.pullSection_add R f) 0 := by rw [hP]
      _ = 0 := map_zero _
  · calc (N : ℤ) • EllHom.pullSection R f Q
        = AddMonoidHom.mk' (EllHom.pullSection R f)
            (EllHom.pullSection_add R f) ((N : ℤ) • Q) :=
          (map_zsmul (AddMonoidHom.mk' (EllHom.pullSection R f)
            (EllHom.pullSection_add R f)) (N : ℤ) Q).symm
      _ = AddMonoidHom.mk' (EllHom.pullSection R f)
            (EllHom.pullSection_add R f) 0 := by rw [hQ]
      _ = 0 := map_zero _
  · intro k _ _ t x hx
    set ψ := (EllHom.pointTransportEquiv R f t).trans
      (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom t) with hψ
    have hdx : (N : ℤ) • ψ x = 0 := by
      rw [← map_zsmul ψ, hx, map_zero]
    have h1 := hgen k (t ≫ f.baseHom) (ψ x) hdx
    have hcompatP : ψ (EllipticCurve.Point.pull X.curve t
        (EllHom.pullSection R f P)) =
      EllipticCurve.Point.pull Y.curve (t ≫ f.baseHom) P :=
      EllHom.pointTransportEquiv_pull_pullSection R f t P
    have hcompatQ : ψ (EllipticCurve.Point.pull X.curve t
        (EllHom.pullSection R f Q)) =
      EllipticCurve.Point.pull Y.curve (t ≫ f.baseHom) Q :=
      EllHom.pointTransportEquiv_pull_pullSection R f t Q
    rw [← hcompatP, ← hcompatQ] at h1
    have hKle : AddSubgroup.closure
        ({ψ (EllipticCurve.Point.pull X.curve t (EllHom.pullSection R f P)),
          ψ (EllipticCurve.Point.pull X.curve t (EllHom.pullSection R f Q))} :
          Set (Y.curve.Point (t ≫ f.baseHom)))
        ≤ (AddSubgroup.closure
            {EllipticCurve.Point.pull X.curve t (EllHom.pullSection R f P),
             EllipticCurve.Point.pull X.curve t (EllHom.pullSection R f Q)}).map
          ψ.toAddMonoidHom := by
      rw [AddSubgroup.closure_le]
      rintro z (rfl | rfl)
      · exact ⟨_, AddSubgroup.subset_closure (Set.mem_insert _ _), rfl⟩
      · exact ⟨_, AddSubgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
    obtain ⟨y, hy, hyx⟩ := hKle h1
    exact (ψ.injective hyx) ▸ hy

end ModularCurves
