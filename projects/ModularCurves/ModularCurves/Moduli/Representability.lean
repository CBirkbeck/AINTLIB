import ModularCurves.Moduli.EllCategory
import ModularCurves.EllipticCurve.RecordGroupUnique
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

/-- The universal Tate curve is in Tate normal form (sanity pin). -/
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
pin. -/
theorem tateRing_homEquiv (A : Type u) [CommRing A] :
    ∃ e : (tateRing →+* A) ≃
        { c : A × A //
          IsUnit ((tateCurve.map (MvPolynomial.eval₂Hom (Int.castRingHom A)
            (fun i => if i = 0 then c.1 else c.2))).Δ) },
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

section PullSectionAdditivity

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {X Y : EllObj R} (f : X ⟶ Y)

/-- The comparison isomorphism from the total space of `X.curve` onto the total space of
the base change of `Y.curve` along `f.baseHom`, from the cartesian square of `f`. -/
noncomputable def EllHom.curveIsoPullback : X.curve.E ≅ pullback Y.curve.π f.baseHom :=
  f.isPullback.isoPullback

/-- The comparison isomorphism is pointed. -/
lemma EllHom.zero_curveIsoPullback :
    X.curve.zero ≫ (EllHom.curveIsoPullback R f).hom =
      (Y.curve.baseChange f.baseHom).zero := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (X.curve.zero ≫ ·) (f.isPullback.isoPullback_hom_fst)).trans <|
      f.zero_w.trans (pullback.lift_fst _ _ _).symm
  · exact (Category.assoc _ _ _).trans <|
      (congrArg (X.curve.zero ≫ ·) (f.isPullback.isoPullback_hom_snd)).trans <|
      X.curve.zero_π.trans (pullback.lift_snd _ _ _).symm

/-- The comparison isomorphism as an isomorphism over the base. -/
noncomputable def EllHom.curveIsoPullbackOverIso :
    X.curve.asOver ≅ (Y.curve.baseChange f.baseHom).asOver :=
  Over.isoMk (EllHom.curveIsoPullback R f) (f.isPullback.isoPullback_hom_snd)

/-- The comparison isomorphism as a morphism over the base (the pre-existing
consumer-facing form). -/
noncomputable def EllHom.curveIsoPullbackOver :
    X.curve.asOver ⟶ (Y.curve.baseChange f.baseHom).asOver :=
  Over.homMk (EllHom.curveIsoPullback R f).hom (f.isPullback.isoPullback_hom_snd)

/-- The transport of sections along the comparison isomorphism. -/
noncomputable def EllHom.transportSection (s : X.curve.Section) :
    (Y.curve.baseChange f.baseHom).Section :=
  ⟨s.1 ≫ (EllHom.curveIsoPullback R f).hom,
    (Category.assoc _ _ _).trans <|
      (congrArg (s.1 ≫ ·) (f.isPullback.isoPullback_hom_snd)).trans s.2⟩

lemma EllHom.transportSection_injective :
    Function.Injective (EllHom.transportSection R f) := by
  intro s s' h
  refine Subtype.ext ?_
  have h1 : s.1 ≫ (EllHom.curveIsoPullback R f).hom =
      s'.1 ≫ (EllHom.curveIsoPullback R f).hom :=
    congrArg Subtype.val h
  simpa using congrArg (· ≫ (EllHom.curveIsoPullback R f).inv) h1

/-- The transport of a pulled section is the base-changed pullback section. -/
lemma EllHom.transportSection_pullSection (P : Y.curve.Section) :
    (EllHom.transportSection R f (EllHom.pullSection R f P)).1
      = pullback.lift (f.baseHom ≫ P.1) (𝟙 X.base)
          (by rw [Category.assoc, P.2, Category.comp_id, Category.id_comp]) := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans <|
      (congrArg ((EllHom.pullSection R f P).1 ≫ ·)
        (f.isPullback.isoPullback_hom_fst)).trans <|
      (f.isPullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
  · exact (Category.assoc _ _ _).trans <|
      (congrArg ((EllHom.pullSection R f P).1 ≫ ·)
        (f.isPullback.isoPullback_hom_snd)).trans <|
      (f.isPullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

/-- The dictionary image of a transported pullback section is the plain pullback of the
section along the composite. -/
lemma EllHom.dict_transportSection_pullSection (P : Y.curve.Section) :
    EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom (𝟙 X.base)
        (EllHom.transportSection R f (EllHom.pullSection R f P))
      = EllipticCurve.Point.pull Y.curve (𝟙 X.base ≫ f.baseHom) P := by
  refine Subtype.ext ?_
  show (EllHom.transportSection R f (EllHom.pullSection R f P)).1
      ≫ pullback.fst Y.curve.π f.baseHom = _
  rw [EllHom.transportSection_pullSection]
  exact (pullback.lift_fst _ _ _).trans
    (congrArg (· ≫ P.1) (Category.id_comp f.baseHom)).symm

set_option backward.isDefEq.respectTransparency false in
/-- **(GME Cor 2.2.5, arbitrary base)** The transport along the pointed comparison
isomorphism is additive: the two independent group structures correspond by the
records-level canonicity primitive `isMonHom_of_pointedIso_records` (the K4 supply —
no noetherian hypothesis). -/
lemma EllHom.transportSection_add (s s' : X.curve.Section) :
    EllHom.transportSection R f (s + s')
      = EllHom.transportSection R f s + EllHom.transportSection R f s' := by
  have hη : (η[X.curve.asOver] : 𝟙_ (Over X.base) ⟶ X.curve.asOver) ≫
      (EllHom.curveIsoPullbackOverIso R f).hom
      = η[(Y.curve.baseChange f.baseHom).asOver] := by
    apply Over.OverMorphism.ext
    show (η[X.curve.asOver] : _ ⟶ X.curve.asOver).left ≫
      (EllHom.curveIsoPullback R f).hom = _
    exact (congrArg (· ≫ (EllHom.curveIsoPullback R f).hom)
        X.curve.one_eq_zero).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg ((𝟙_ (Over X.base)).hom ≫ ·)
        (EllHom.zero_curveIsoPullback R f)).trans <|
      (Y.curve.baseChange f.baseHom).one_eq_zero.symm
  have h64 := isMonHom_of_pointedIso_records X.curve
    (Y.curve.baseChange f.baseHom) (EllHom.curveIsoPullbackOverIso R f) hη
  have h64l : (μ[X.curve.asOver]).left ≫ (EllHom.curveIsoPullback R f).hom
      = (MonoidalCategory.tensorHom (EllHom.curveIsoPullbackOverIso R f).hom
          (EllHom.curveIsoPullbackOverIso R f).hom).left
        ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left :=
    ((Over.comp_left _ _ _ _ _).symm.trans (congrArg CommaMorphism.left h64)).trans
      (Over.comp_left _ _ _ _ _)
  have hcs : X.curve.pointEquivOverHom (𝟙 X.base) s ≫
      (EllHom.curveIsoPullbackOverIso R f).hom
      = (Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
          (EllHom.transportSection R f s) :=
    Over.OverMorphism.ext rfl
  have hcs' : X.curve.pointEquivOverHom (𝟙 X.base) s' ≫
      (EllHom.curveIsoPullbackOverIso R f).hom
      = (Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
          (EllHom.transportSection R f s') :=
    Over.OverMorphism.ext rfl
  refine Subtype.ext ?_
  have hx : (s + s').1
      = (lift (X.curve.pointEquivOverHom (𝟙 X.base) s)
          (X.curve.pointEquivOverHom (𝟙 X.base) s')).left
        ≫ (μ[X.curve.asOver]).left :=
    (congrArg CommaMorphism.left
      (X.curve.pointEquivOverHom_add (𝟙 X.base) s s')).trans
      (Over.comp_left _ _ _ _ _)
  have hRR : (EllHom.transportSection R f s + EllHom.transportSection R f s').1
      = (lift ((Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
            (EllHom.transportSection R f s))
          ((Y.curve.baseChange f.baseHom).pointEquivOverHom (𝟙 X.base)
            (EllHom.transportSection R f s'))).left
        ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left :=
    (congrArg CommaMorphism.left
      ((Y.curve.baseChange f.baseHom).pointEquivOverHom_add (𝟙 X.base) _ _)).trans
      (Over.comp_left _ _ _ _ _)
  show (s + s').1 ≫ (EllHom.curveIsoPullback R f).hom = _
  rw [hRR]
  exact (congrArg (· ≫ (EllHom.curveIsoPullback R f).hom) hx).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((lift (X.curve.pointEquivOverHom (𝟙 X.base) s)
        (X.curve.pointEquivOverHom (𝟙 X.base) s')).left ≫ ·) h64l).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ (μ[(Y.curve.baseChange f.baseHom).asOver]).left)
      ((Over.comp_left _ _ _ _ _).symm.trans
        (congrArg CommaMorphism.left
          ((lift_map _ _ _ _).trans
            (congrArg₂ lift hcs hcs')))))

/-- The comparison isomorphism is a monoid-object homomorphism: the pointedness plus
the records-level canonicity primitive (K4 supply). NOT an instance — a global
`IsMonHom`-instance with these metavariable-heavy arguments sends unrelated
typeclass searches (e.g. `AddMonoidHomClass` on point-equivs) into timeouts. -/
theorem EllHom.isMonHom_curveIsoPullbackOverIso_hom :
    IsMonHom (EllHom.curveIsoPullbackOverIso R f).hom := by
  constructor
  · apply Over.OverMorphism.ext
    show (η[X.curve.asOver] : _ ⟶ X.curve.asOver).left ≫
      (EllHom.curveIsoPullback R f).hom = _
    exact (congrArg (· ≫ (EllHom.curveIsoPullback R f).hom)
        X.curve.one_eq_zero).trans <|
      (Category.assoc _ _ _).trans <|
      (congrArg ((𝟙_ (Over X.base)).hom ≫ ·)
        (EllHom.zero_curveIsoPullback R f)).trans <|
      (Y.curve.baseChange f.baseHom).one_eq_zero.symm
  · exact isMonHom_of_pointedIso_records X.curve
      (Y.curve.baseChange f.baseHom) (EllHom.curveIsoPullbackOverIso R f) (by
        apply Over.OverMorphism.ext
        show (η[X.curve.asOver] : _ ⟶ X.curve.asOver).left ≫
          (EllHom.curveIsoPullback R f).hom = _
        exact (congrArg (· ≫ (EllHom.curveIsoPullback R f).hom)
            X.curve.one_eq_zero).trans <|
          (Category.assoc _ _ _).trans <|
          (congrArg ((𝟙_ (Over X.base)).hom ≫ ·)
            (EllHom.zero_curveIsoPullback R f)).trans <|
          (Y.curve.baseChange f.baseHom).one_eq_zero.symm)

/-- The point-level transport along the comparison isomorphism, as an additive
equivalence (the arbitrary-`t` form of `transportSection`; additivity via
`MonObj.mul_comp` at the `IsMonHom` comparison). -/
noncomputable def EllHom.pointTransportEquiv {T : Scheme.{u}} (t : T ⟶ X.base) :
    X.curve.Point t ≃+ (Y.curve.baseChange f.baseHom).Point t where
  toFun x := ((Y.curve.baseChange f.baseHom).pointEquivOverHom t).symm
    (X.curve.pointEquivOverHom t x ≫ (EllHom.curveIsoPullbackOverIso R f).hom)
  invFun y := (X.curve.pointEquivOverHom t).symm
    ((Y.curve.baseChange f.baseHom).pointEquivOverHom t y ≫
      (EllHom.curveIsoPullbackOverIso R f).inv)
  left_inv x := by
    show (X.curve.pointEquivOverHom t).symm
      (((Y.curve.baseChange f.baseHom).pointEquivOverHom t)
        (((Y.curve.baseChange f.baseHom).pointEquivOverHom t).symm
          (X.curve.pointEquivOverHom t x ≫
            (EllHom.curveIsoPullbackOverIso R f).hom)) ≫
        (EllHom.curveIsoPullbackOverIso R f).inv) = x
    rw [Equiv.apply_symm_apply, Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Equiv.symm_apply_apply]
  right_inv y := by
    show ((Y.curve.baseChange f.baseHom).pointEquivOverHom t).symm
      ((X.curve.pointEquivOverHom t)
        ((X.curve.pointEquivOverHom t).symm
          ((Y.curve.baseChange f.baseHom).pointEquivOverHom t y ≫
            (EllHom.curveIsoPullbackOverIso R f).inv)) ≫
        (EllHom.curveIsoPullbackOverIso R f).hom) = y
    rw [Equiv.apply_symm_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Equiv.symm_apply_apply]
  map_add' x y := by
    apply ((Y.curve.baseChange f.baseHom).pointEquivOverHom t).injective
    rw [Equiv.apply_symm_apply]
    letI : CommGroup (Over.mk t ⟶ (Y.curve.baseChange f.baseHom).asOver) :=
      CategoryTheory.Hom.commGroup
    letI : CommGroup (Over.mk t ⟶ X.curve.asOver) := CategoryTheory.Hom.commGroup
    haveI : IsMonHom (EllHom.curveIsoPullbackOverIso R f).hom :=
      EllHom.isMonHom_curveIsoPullbackOverIso_hom R f
    have hadd : (Y.curve.baseChange f.baseHom).pointEquivOverHom t
        (((Y.curve.baseChange f.baseHom).pointEquivOverHom t).symm
          (X.curve.pointEquivOverHom t x ≫
            (EllHom.curveIsoPullbackOverIso R f).hom) +
         ((Y.curve.baseChange f.baseHom).pointEquivOverHom t).symm
          (X.curve.pointEquivOverHom t y ≫
            (EllHom.curveIsoPullbackOverIso R f).hom)) =
      (X.curve.pointEquivOverHom t x ≫ (EllHom.curveIsoPullbackOverIso R f).hom) *
        (X.curve.pointEquivOverHom t y ≫
          (EllHom.curveIsoPullbackOverIso R f).hom) := by
      rw [(Y.curve.baseChange f.baseHom).pointEquivOverHom_add,
        Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rw [hadd, X.curve.pointEquivOverHom_add,
      MonObj.mul_comp (X.curve.pointEquivOverHom t x)
        (X.curve.pointEquivOverHom t y)
        (EllHom.curveIsoPullbackOverIso R f).hom]

/-- The transport-then-base-change dictionary sends the pull of a pulled section to the
plain pull along the composite. -/
lemma EllHom.pointTransportEquiv_pull_pullSection {T : Scheme.{u}} (t : T ⟶ X.base)
    (P : Y.curve.Section) :
    EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom t
        (EllHom.pointTransportEquiv R f t
          (EllipticCurve.Point.pull X.curve t (EllHom.pullSection R f P)))
      = EllipticCurve.Point.pull Y.curve (t ≫ f.baseHom) P := by
  refine Subtype.ext ?_
  show ((EllHom.pointTransportEquiv R f t
      (EllipticCurve.Point.pull X.curve t (EllHom.pullSection R f P))).1 ≫
    pullback.fst Y.curve.π f.baseHom) = (t ≫ f.baseHom) ≫ P.1
  have hval : (EllHom.pointTransportEquiv R f t
      (EllipticCurve.Point.pull X.curve t (EllHom.pullSection R f P))).1 =
    (t ≫ (EllHom.pullSection R f P).1) ≫ (EllHom.curveIsoPullback R f).hom := rfl
  rw [hval]
  show t ≫ (EllHom.pullSection R f P).1 ≫ ((EllHom.curveIsoPullback R f).hom ≫
    pullback.fst Y.curve.π f.baseHom) = (t ≫ f.baseHom) ≫ P.1
  rw [show (EllHom.curveIsoPullback R f).hom ≫ pullback.fst Y.curve.π f.baseHom =
    f.top from f.isPullback.isoPullback_hom_fst]
  rw [show (EllHom.pullSection R f P).1 ≫ f.top = f.baseHom ≫ P.1 from
    f.isPullback.lift_fst _ _ _]
  rw [← Category.assoc]

end PullSectionAdditivity

/-- **(T-E4a, additivity of section-pullback — surfaced by the adversarial pass
2026-07-06)** `pullSection` is a group homomorphism. NOT free: `EllHom` carries no
group-compatibility field and the two curves' `grp` data are independent, so this
consumes uniqueness of the group law with given unit (`abelEnrichment_unique`,
GME Cor 2.2.5 — a pointed isomorphism onto the pullback is automatically a group
isomorphism). Every moduli-functor `map` below (Γ₁/Γ(N)/P_H, naive and Drinfeld)
consumes this lemma; it restores the dependency edge from the level functors to the
canonicity chain A6.δ that the earlier "nothing depends on it" amendment dropped. -/
theorem EllHom.pullSection_add {X Y : EllObj R} (f : X ⟶ Y)
    (P Q : Y.curve.Section) :
    EllHom.pullSection R f (P + Q) =
      EllHom.pullSection R f P + EllHom.pullSection R f Q := by
  -- DE-SORRIED (STREAM-OMEGA 2026-07-14): the T-W7.8 park-reason dissolved — the
  -- records-level canonicity primitive `isMonHom_of_pointedIso_records` (K4 supply,
  -- `RecordGroupUnique.lean`) needs no noetherian hypothesis. Proof: transport along
  -- the pointed comparison isomorphism onto the base-changed curve; the two group
  -- structures correspond by the K4 supply; the base-changed side is additive by the
  -- `Point.baseChangeEquiv` dictionary and `Point.pull_add`; the transport is
  -- injective.
  apply EllHom.transportSection_injective R f
  rw [EllHom.transportSection_add]
  apply (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom (𝟙 X.base)).injective
  rw [map_add, EllHom.dict_transportSection_pullSection,
    EllHom.dict_transportSection_pullSection,
    EllHom.dict_transportSection_pullSection, EllipticCurve.Point.pull_add]

section LevelPreservation

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {X Y : EllObj R} (f : X ⟶ Y)

/-- `pullSection` sends zero to zero (both are the zero section, by `hom_ext` on the
cartesian square). -/
lemma EllHom.pullSection_zero :
    EllHom.pullSection R f (0 : Y.curve.Section) = (0 : X.curve.Section) := by
  have h := EllHom.pullSection_add R f (0 : Y.curve.Section) 0
  rw [add_zero] at h
  exact (add_left_cancel (a := EllHom.pullSection R f 0)
    (by rw [← h, add_zero])).symm

/-- **[T-YR-2a] `[n]`-naturality along an `Ell/R`-morphism**: the top map of an
`EllHom` intertwines multiplication-by-`n` (the morphism-level form of T-E4a; the
K4-canonicity MonHom `curveIsoPullbackOverIso` + `mulByHom_comp_left_of_isMonHom` +
`mulByHom_baseChange_fst`). -/
theorem EllHom.mulByHom_top (n : ℤ) :
    X.curve.mulByHom n ≫ f.top = f.top ≫ Y.curve.mulByHom n := by
  haveI : IsMonHom (EllHom.curveIsoPullbackOverIso R f).hom :=
    EllHom.isMonHom_curveIsoPullbackOverIso_hom R f
  have h1 : X.curve.mulByHom n ≫ (EllHom.curveIsoPullback R f).hom =
      (EllHom.curveIsoPullback R f).hom ≫
        (Y.curve.baseChange f.baseHom).mulByHom n :=
    EllipticCurve.mulByHom_comp_left_of_isMonHom X.curve
      (Y.curve.baseChange f.baseHom) (EllHom.curveIsoPullbackOverIso R f).hom n
  have hfst : (EllHom.curveIsoPullback R f).hom ≫
      pullback.fst Y.curve.π f.baseHom = f.top := f.isPullback.isoPullback_hom_fst
  have hbc : (Y.curve.baseChange f.baseHom).mulByHom n ≫
      pullback.fst Y.curve.π f.baseHom =
      pullback.fst Y.curve.π f.baseHom ≫ Y.curve.mulByHom n :=
    EllipticCurve.mulByHom_baseChange_fst Y.curve f.baseHom n
  calc X.curve.mulByHom n ≫ f.top
      = X.curve.mulByHom n ≫ (EllHom.curveIsoPullback R f).hom ≫
          pullback.fst Y.curve.π f.baseHom := by rw [hfst]
    _ = ((EllHom.curveIsoPullback R f).hom ≫
          (Y.curve.baseChange f.baseHom).mulByHom n) ≫
          pullback.fst Y.curve.π f.baseHom := by
        rw [← Category.assoc]
        exact congrArg (· ≫ pullback.fst Y.curve.π f.baseHom) h1
    _ = (EllHom.curveIsoPullback R f).hom ≫ pullback.fst Y.curve.π f.baseHom ≫
          Y.curve.mulByHom n := by
        rw [Category.assoc]
        exact congrArg ((EllHom.curveIsoPullback R f).hom ≫ ·) hbc
    _ = f.top ≫ Y.curve.mulByHom n := by
        rw [← Category.assoc, hfst]

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


/-- **(T-E4b ★)** `pullSection` preserves the naive `Γ₁(N)` condition: killing via
the additivity, and both fibrewise clauses via the point-level comparison equivalence
(order is preserved and reflected by an `AddEquiv`). -/
theorem EllHom.isNaiveGammaOne_pullSection {N : ℕ} [NeZero N]
    {P : Y.curve.Section} (h : Y.curve.IsNaiveGammaOne N P) :
    X.curve.IsNaiveGammaOne N (EllHom.pullSection R f P) := by
  obtain ⟨hP, hfib⟩ := h
  refine ⟨?_, ?_⟩
  · calc (N : ℤ) • EllHom.pullSection R f P
        = AddMonoidHom.mk' (EllHom.pullSection R f)
            (EllHom.pullSection_add R f) ((N : ℤ) • P) :=
          (map_zsmul (AddMonoidHom.mk' (EllHom.pullSection R f)
            (EllHom.pullSection_add R f)) (N : ℤ) P).symm
      _ = AddMonoidHom.mk' (EllHom.pullSection R f)
            (EllHom.pullSection_add R f) 0 := by rw [hP]
      _ = 0 := map_zero _
  · intro k _ _ t
    obtain ⟨hkill, hord⟩ := hfib k (t ≫ f.baseHom)
    set ψ := (EllHom.pointTransportEquiv R f t).trans
      (EllipticCurve.Point.baseChangeEquiv Y.curve f.baseHom t) with hψ
    have hcompat : ψ (EllipticCurve.Point.pull X.curve t
        (EllHom.pullSection R f P)) =
      EllipticCurve.Point.pull Y.curve (t ≫ f.baseHom) P :=
      EllHom.pointTransportEquiv_pull_pullSection R f t P
    refine ⟨?_, ?_⟩
    · apply ψ.injective
      rw [map_zsmul, hcompat, map_zero]
      exact hkill
    · intro a ha haN hcon
      refine hord a ha haN ?_
      have := congrArg ψ hcon
      rwa [map_zsmul, hcompat, map_zero] at this

end LevelPreservation

/-- The naive `Γ₁(N)` moduli problem over `R`: `E/S ↦ {P ∈ E(S) : P` has naive exact
order `N}` (fibrewise; the right notion for `N` invertible, KM 1.4.4). Functor laws are
`T-E4`. Source: Loeffler §3.3/§3.8; KM 3.2 + 3.7. -/
noncomputable def gammaOneNaiveProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { P : X.unop.curve.Section // X.unop.curve.IsNaiveGammaOne N P }
  map f := ↾fun P => ⟨EllHom.pullSection R f.unop P.1,
    EllHom.isNaiveGammaOne_pullSection R f.unop P.2⟩
  map_id X := by
    ext P
    exact congrArg Subtype.val (EllHom.pullSection_id R P.1)
  map_comp f g := by
    ext P
    exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop P.1)

/-- The naive full-level-`N` (`Γ(N)`) moduli problem over `R`:
`E/S ↦ {(P, Q) generating E[N] in every fibre}`. Source: Loeffler Fact 3.8.1 (verbatim:
"pairs of sections `P, Q ∈ E[S]` generating `E[N]` in every fibre"); KM 3.1 + 3.7. -/
noncomputable def gammaFullNaiveProblem (N : ℕ) [NeZero N] : ModuliProblem R where
  obj X := { PQ : X.unop.curve.Section × X.unop.curve.Section //
    X.unop.curve.IsNaiveFullLevel N PQ.1 PQ.2 }
  map f := ↾fun PQ => ⟨⟨EllHom.pullSection R f.unop PQ.1.1,
    EllHom.pullSection R f.unop PQ.1.2⟩,
    EllHom.isNaiveFullLevel_pullSection R f.unop PQ.2⟩
  map_id X := by
    ext PQ
    · exact congrArg Subtype.val (EllHom.pullSection_id R PQ.1.1)
    · exact congrArg Subtype.val (EllHom.pullSection_id R PQ.1.2)
  map_comp f g := by
    ext PQ
    · exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop PQ.1.1)
    · exact congrArg Subtype.val (EllHom.pullSection_comp R g.unop f.unop PQ.1.2)

/-- **(T-E7 = Loeffler Thm 3.4.4 + Def 3.3.6; KM 5.x for the Drinfeld upgrade)** For
`N ≥ 4` and `N` invertible in `R`, the naive `Γ₁(N)` problem is representable, and the
representing base scheme is smooth and affine over `Spec R`.
Loeffler (verbatim, Thm 3.4.4): "`Y₁(N)_{ℤ[1/N]}` is smooth over `ℤ[1/N]`."

Notes (adversarial pass 2026-07-06): TRUE only after `IsNaiveGammaOne` gained its
global killing clause (without it a `ℚ̄[ε]`-family gave pro-representation
`ℚ̄[[t,s]]`, contradicting smooth + quasi-finite-over-j). General `R` follows from
`ℤ[1/N]` by base change (`Smooth`, `IsAffineHom` stable). Affineness for general `N`
is QUOTE-PARTIAL: Loeffler's `Spec` display is verbatim only for `N = 5`; attach the
KM affine-over-the-j-line locator when the full text lands. -/
theorem gammaOneNaive_representable (N : ℕ) [NeZero N] (hN : 4 ≤ N)
    (hinv : IsUnit (N : R)) :
    (gammaOneNaiveProblem R N).Representable ∧
      ∀ X : EllObj R, Nonempty ((gammaOneNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by sorry

/-- **(T-E9 = Loeffler Prop 3.8.2–3.8.3; KM 3.1/4.7/5.1)** For `N ≥ 3` and `N` invertible
in `R`, the naive full-level problem `[Γ(N)]` is rigid and representable; the representing
scheme `Y(N)` is smooth and affine over `Spec R`.
(Rigidity: Loeffler Prop 3.8.3 covers `Ell/R[1/6]` only; for residue characteristics
2 and 3 the source of record is the GME 2.6.4 Aut-computation ("`ε ∈ Aut(E,φ)`,
`n ≥ 3` invertible ⟹ `ε = 1`", chain B9 in decomposition-gme2 — valid in all
characteristics with `N` invertible); KM locator pending. Smooth+affine conjunct
restored 2026-07-06 — it was in this docstring but missing from the statement.) -/
theorem gammaFullNaive_representable (N : ℕ) [NeZero N] (hN : 3 ≤ N)
    (hinv : IsUnit (N : R)) :
    ((gammaFullNaiveProblem R N).Rigid ∧ (gammaFullNaiveProblem R N).Representable) ∧
      ∀ X : EllObj R, Nonempty ((gammaFullNaiveProblem R N).RepresentableBy X) →
        (Smooth X.structMap ∧ IsAffineHom X.structMap) := by
  sorry

end LevelModuli

end ModularCurves
