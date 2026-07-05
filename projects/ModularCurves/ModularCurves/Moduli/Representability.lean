import ModularCurves.Moduli.EllCategory
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
* **`Y₁(N)`** (Loeffler Def 3.3.6 & Thm 3.4.4): for `N ≥ 4` (representability needs
  rigidity, which fails for small `N`) the naive-Γ₁(N) moduli problem over `ℤ[1/N]` is
  representable by a scheme, smooth and affine over `ℤ[1/N]`.
* **`Y(N)`** (Loeffler Fact 3.8.1–3.8.3; KM 3.1, 4.7, 5.1): for `N ≥ 3`, `[Γ(N)]` is
  rigid and representable; over `ℤ[1/N]` the representing scheme is smooth affine.

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
`0` automatically). Source: Loeffler Prop 3.3.4 hypothesis "`P, 2P, 3P ≠ 0` in any
fibre"; division-polynomial dictionary: Silverman III Ex. 3.7 / mathlib
`WeierstrassCurve.Ψ`. -/
def NowhereOrderLEThree (W : WeierstrassCurve R) (x y : R) : Prop :=
  IsUnit ((W.Ψ 2).evalEval x y * (W.Ψ 3).evalEval x y)

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
      (vc • W).IsTateNormal ∧ vc.r = x ∧ vc.t = y := by sorry

/-- The universal Tate-normal Weierstrass curve `E(A, B) : Y² + AXY + BY = X³ + BX²` over
`ℤ[A, B]`. Source: Loeffler Def 3.3.3. -/
noncomputable def tateCurve : WeierstrassCurve (MvPolynomial (Fin 2) ℤ) :=
  { a₁ := MvPolynomial.X 0
    a₂ := MvPolynomial.X 1
    a₃ := MvPolynomial.X 1
    a₄ := 0
    a₆ := 0 }

/-- The coordinate ring `ℤ[A, B][Δ(A,B)⁻¹]` of the universal Tate curve — the affine ring
of (the coarse ring-level avatar of) the universal elliptic curve with a point of nowhere
order ≤ 3. Source: Loeffler Cor 3.3.5. -/
noncomputable abbrev tateRing : Type :=
  Localization.Away tateCurve.Δ

/-- **(T-E2 = Loeffler Cor 3.3.5, ring level — PROVABLE-NOW target)** For every ring `A`,
ring homomorphisms `tateRing →+* A` correspond exactly to pairs `(α, β) ∈ A²` with
`Δ(α, β)` a unit — i.e. to Tate-normal elliptic curves over `A` marked at `(0, 0)`.
(Universal property of polynomial ring + localization; with `T-E1` this is Loeffler's
"`(Spec ℤ[A,B,Δ(A,B)⁻¹], (E(A,B),(0:0:1)))` represents the functor `S ↦ {eq. classes of
pairs (E,P) … P ∈ E(S) not of order 1,2,3 in any fibre}`".) -/
theorem tateRing_homEquiv (A : Type u) [CommRing A] :
    Nonempty ((tateRing →+* A) ≃
      { c : A × A //
        IsUnit ((tateCurve.map (MvPolynomial.eval₂Hom (Int.castRingHom A)
          (fun i => if i = 0 then c.1 else c.2))).Δ) }) := by sorry

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

/-- The naive `Γ₁(N)` moduli problem over `R`: `E/S ↦ {P ∈ E(S) : P` has naive exact
order `N}` (fibrewise; the right notion for `N` invertible, KM 1.4.4). Functor laws are
`T-E4`. Source: Loeffler §3.3/§3.8; KM 3.2 + 3.7. -/
noncomputable def gammaOneNaiveProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { P : X.unop.curve.Section // X.unop.curve.IsNaiveGammaOne N P }
  map f := ↾fun P => ⟨EllHom.pullSection R f.unop P.1, by sorry⟩
  map_id := by sorry
  map_comp := by sorry

/-- The naive full-level-`N` (`Γ(N)`) moduli problem over `R`:
`E/S ↦ {(P, Q) generating E[N] in every fibre}`. Source: Loeffler Fact 3.8.1 (verbatim:
"pairs of sections `P, Q ∈ E[S]` generating `E[N]` in every fibre"); KM 3.1 + 3.7. -/
noncomputable def gammaFullNaiveProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { PQ : X.unop.curve.Section × X.unop.curve.Section //
    X.unop.curve.IsNaiveFullLevel N PQ.1 PQ.2 }
  map f := ↾fun PQ => ⟨⟨EllHom.pullSection R f.unop PQ.1.1,
    EllHom.pullSection R f.unop PQ.1.2⟩, by sorry⟩
  map_id := by sorry
  map_comp := by sorry

/-- **(T-E7 = Loeffler Thm 3.4.4 + Def 3.3.6; KM 5.x for the Drinfeld upgrade)** For
`N ≥ 4` and `N` invertible in `R`, the naive `Γ₁(N)` problem is representable, and the
representing base scheme is smooth and affine over `Spec R`.
Loeffler (verbatim, Thm 3.4.4): "`Y₁(N)_{ℤ[1/N]}` is smooth over `ℤ[1/N]`." -/
theorem gammaOneNaive_representable (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaOneNaiveProblem R N).Representable ∧
      ∀ X : EllObj R, Nonempty ((gammaOneNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by sorry

/-- **(T-E9 = Loeffler Prop 3.8.2–3.8.3; KM 3.1/4.7/5.1)** For `N ≥ 3` and `N` invertible
in `R`, the naive full-level problem `[Γ(N)]` is rigid and representable; the representing
scheme `Y(N)` is smooth and affine over `Spec R`.
(Rigidity per Loeffler Prop 3.8.3: the preimage of `H = {1}` in `SL₂(ℤ)` has no elliptic
points and does not contain `−1` for `N ≥ 3`.) -/
theorem gammaFullNaive_representable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaFullNaiveProblem R N).Rigid ∧ (gammaFullNaiveProblem R N).Representable := by
  sorry

end LevelModuli

end ModularCurves
