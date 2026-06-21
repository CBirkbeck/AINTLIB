import HasseWeil.Curves.FiniteOverKx
import HasseWeil.Curves.Valuation
import HasseWeil.Curves.IntegralClosure
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Norm.Defs
import Mathlib.NumberTheory.RamificationInertia.Basic

/-!
# Curve maps via function-field pullback

A **curve map** `φ : C₁ → C₂` between smooth plane curves (over a common
field `F`) is specified by its pullback on function fields: an `F`-algebra
homomorphism `φ* : K(C₂) → K(C₁)`. Nonconstant maps correspond to
injective pullbacks (automatic, since `F`-algebra homs between fields are
injective).

The **degree** of `φ` is the dimension of `K(C₁)` as a `K(C₂)`-module via
the pullback: `deg φ = [K(C₁) : φ*K(C₂)]`.

This closes tickets T-II-INFRA-B-006/007 of the Stream-A infrastructure plan
and provides the foundational object for T-II-2-002..011 (which will add
surjectivity, ramification, and the fiber-card formula).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.4 (curves-fields
  correspondence), II.2 definition of degree
-/

namespace HasseWeil.Curves

/-- A curve map `φ : C₁ → C₂` between smooth plane curves, defined by its
pullback on function fields.

An `F`-algebra hom between two fields is automatically injective, so this
structure models the **nonconstant** maps (the image of the pullback is a
subfield of finite index in `K(C₁)`). Reference: Silverman II.2.4(b). -/
structure CurveMap {F : Type*} [Field F] (C₁ C₂ : SmoothPlaneCurve F) where
  /-- The pullback `φ* : K(C₂) → K(C₁)` on function fields. -/
  pullback : C₂.FunctionField →ₐ[F] C₁.FunctionField

namespace CurveMap

variable {F : Type*} [Field F] {C₁ C₂ C₃ : SmoothPlaneCurve F}

/-- The pullback of a curve map is injective (as any `F`-algebra hom
between fields is). -/
theorem pullback_injective (φ : CurveMap C₁ C₂) :
    Function.Injective φ.pullback :=
  φ.pullback.toRingHom.injective

/-- The identity curve map. -/
noncomputable def id (C : SmoothPlaneCurve F) : CurveMap C C where
  pullback := AlgHom.id F C.FunctionField

@[simp] theorem id_pullback (C : SmoothPlaneCurve F) :
    (id C).pullback = AlgHom.id F C.FunctionField := rfl

/-- Composition of curve maps: `(ψ ∘ φ)* = φ* ∘ ψ*`. -/
noncomputable def comp (ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) : CurveMap C₁ C₃ where
  pullback := φ.pullback.comp ψ.pullback

@[simp] theorem comp_pullback (ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) :
    (ψ.comp φ).pullback = φ.pullback.comp ψ.pullback := rfl

/-- Extensionality: two curve maps are equal iff their pullbacks agree. -/
@[ext] theorem ext {φ ψ : CurveMap C₁ C₂} (h : φ.pullback = ψ.pullback) :
    φ = ψ := by
  cases φ; cases ψ; congr

/-- Composition is associative. -/
theorem comp_assoc {C₄ : SmoothPlaneCurve F}
    (χ : CurveMap C₃ C₄) (ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) :=
  CurveMap.ext (AlgHom.comp_assoc _ _ _).symm

/-- Left identity for composition. -/
@[simp] theorem id_comp (φ : CurveMap C₁ C₂) : (id C₂).comp φ = φ :=
  CurveMap.ext (AlgHom.comp_id _)

/-- Right identity for composition. -/
@[simp] theorem comp_id (φ : CurveMap C₁ C₂) : φ.comp (id C₁) = φ :=
  CurveMap.ext (AlgHom.id_comp _)

/-! ### Degree -/

/-- The algebra structure on `K(C₁)` induced by the pullback of `φ`. -/
@[reducible]
noncomputable def toAlgebra (φ : CurveMap C₁ C₂) :
    Algebra C₂.FunctionField C₁.FunctionField :=
  φ.pullback.toRingHom.toAlgebra

/-- The **degree** of a curve map `φ : C₁ → C₂`, defined as `[K(C₁) : φ*K(C₂)]`
where `K(C₁)` is viewed as a `K(C₂)`-module via the pullback.
Reference: Silverman II.2 (after Theorem 2.4). -/
noncomputable def degree (φ : CurveMap C₁ C₂) : ℕ :=
  @Module.finrank C₂.FunctionField C₁.FunctionField _ _ φ.toAlgebra.toModule

/-- The identity curve map has degree 1. -/
@[simp] theorem degree_id (C : SmoothPlaneCurve F) : (id C).degree = 1 := by
  change @Module.finrank C.FunctionField C.FunctionField _ _
    (id C).toAlgebra.toModule = 1
  exact Module.finrank_self C.FunctionField

/-- The pullback of a composition factors as a composition of pullbacks. -/
theorem comp_algebraMap_eq (ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂)
    (x : C₃.FunctionField) :
    (ψ.comp φ).pullback x = φ.pullback (ψ.pullback x) := rfl

set_option maxHeartbeats 800000 in
-- The tower law for `FunctionField` needs extra heartbeats.
/-- **Degree multiplicativity**: `deg(ψ ∘ φ) = deg(φ) · deg(ψ)`.
    Follows from the tower law for field extensions.
    Reference: Silverman II.2 (after Theorem 2.4). -/
theorem degree_comp (ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂) :
    (ψ.comp φ).degree = φ.degree * ψ.degree := by
  unfold degree
  letI inst₁ : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
  letI inst₂ : Algebra C₃.FunctionField C₂.FunctionField := ψ.toAlgebra
  letI inst₃ : Algebra C₃.FunctionField C₁.FunctionField := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower C₃.FunctionField C₂.FunctionField C₁.FunctionField :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Module.Free C₂.FunctionField C₁.FunctionField :=
    Module.Free.of_divisionRing _ _
  rw [mul_comm]
  exact (Module.finrank_mul_finrank
    C₃.FunctionField C₂.FunctionField C₁.FunctionField).symm

/-- The **separable degree** of a curve map `φ`, using mathlib's
`Field.finSepDegree`. Reference: Silverman II.2 (after Thm 2.4,
definition of `deg_s`). -/
noncomputable def separableDegree (φ : CurveMap C₁ C₂) : ℕ :=
  @Field.finSepDegree C₂.FunctionField C₁.FunctionField _ _ φ.toAlgebra

/-- The **inseparable degree** of a curve map `φ`: `deg_i φ = deg φ / deg_s φ`.
Reference: Silverman II.2. -/
noncomputable def inseparableDegree (φ : CurveMap C₁ C₂) : ℕ :=
  φ.degree / φ.separableDegree

/-- A curve map is **separable** if its inseparable degree is 1. -/
def IsSeparable (φ : CurveMap C₁ C₂) : Prop := φ.inseparableDegree = 1

/-- A curve map is **purely inseparable** if its separable degree is 1. -/
def IsPurelyInseparable (φ : CurveMap C₁ C₂) : Prop := φ.separableDegree = 1

-- **Silverman II.2.4.1** (pullback half, deferred): if `φ : C₁ → C₂` has
-- degree 1, its pullback is surjective.
-- Proof sketch: `finrank_eq_one_iff'` gives `v ≠ 0` with `K(C₁) = K(C₂) • v`.
-- From `c₀ • v = 1` in a field, `v = (algebraMap c₀)⁻¹`, so every `x ∈ K(C₁)`
-- is `c_x • v = algebraMap c_x / algebraMap c₀ = algebraMap (c_x / c₀)`.
-- The Lean proof needs `algebraMap C₂.FunctionField C₁.FunctionField` to
-- resolve to `φ.pullback.toRingHom` via `haveI : Algebra ... := φ.toAlgebra`,
-- but instance synthesis tends to pick unrelated `Algebra` instances.
-- Deferred for future cleanup.

/-! ### Ramification order -/

/-- The order of the pullback of a function `t ∈ K(C₂)` at a smooth point
`P ∈ C₁`: `ord_P (φ* t)`. When `t` is a uniformizer at the image point
`φ(P) ∈ C₂`, this equals Silverman's ramification index `e_φ(P)` of II.2.5.

Our formulation takes the test function `t` as an explicit argument rather
than deriving it from an intrinsic "image point" `φ(P)`, since the
point-image correspondence (Silverman II.2.4(c)) is deferred to later
infrastructure. Downstream users supply a uniformizer at the intended
image point.
Reference: Silverman II.2.5 (definition). -/
noncomputable def ramificationIndex (φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint)
    (t : C₂.FunctionField) : WithTop ℤ :=
  C₁.ord_P P (φ.pullback t)

/-- Ramification order for the identity map reduces to `ord_P`. -/
@[simp] theorem ramificationIndex_id (C : SmoothPlaneCurve F) (P : C.SmoothPoint)
    (t : C.FunctionField) :
    (id C).ramificationIndex P t = C.ord_P P t := rfl

/-- **Chain rule** for ramification order: the order of `(ψ∘φ)* t` at `P`
equals the order of `φ* (ψ* t)` at `P`. This is the algebraic content of
Silverman's II.2.6(c) (ramification chain rule) at the pullback level. -/
theorem ramificationIndex_comp (ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂)
    (P : C₁.SmoothPoint) (t : C₃.FunctionField) :
    (ψ.comp φ).ramificationIndex P t =
      φ.ramificationIndex P (ψ.pullback t) := rfl

/-- The ramification order of a nonzero function is not `⊤`: pullback
preserves nonzeroness (pullbacks are injective), so `ord_P (φ* t) ≠ ⊤`. -/
theorem ramificationIndex_ne_top (φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint)
    {t : C₂.FunctionField} (ht : t ≠ 0) :
    φ.ramificationIndex P t ≠ ⊤ :=
  (C₁.ord_P_eq_top_iff (φ.pullback t)).not.mpr fun h ↦
    ht (φ.pullback_injective (h.trans (map_zero _).symm))

/-- The pullback of a nonzero function is nonzero: `φ*` is injective. -/
theorem pullback_ne_zero (φ : CurveMap C₁ C₂) {t : C₂.FunctionField}
    (ht : t ≠ 0) : φ.pullback t ≠ 0 :=
  fun h ↦ ht (φ.pullback_injective (h.trans (map_zero _).symm))

/-- An `ℤ`-valued form of the ramification index, using `WithTop.untopD 0` to
coerce. For nonzero `t`, this coincides with the pullback-ord as an integer. -/
noncomputable def ramificationIndexℤ (φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint)
    (t : C₂.FunctionField) : ℤ :=
  (φ.ramificationIndex P t).untopD 0

/-- `ramificationIndexℤ` for the identity map at `P` is `(ord_P t).untopD 0`. -/
@[simp] theorem ramificationIndexℤ_id (C : SmoothPlaneCurve F) (P : C.SmoothPoint)
    (t : C.FunctionField) :
    (id C).ramificationIndexℤ P t = (C.ord_P P t).untopD 0 := rfl

/-- **Chain rule, `ℤ`-form**: `(ψ ∘ φ).ramificationIndexℤ P t =
  φ.ramificationIndexℤ P (ψ.pullback t)`. -/
@[simp] theorem ramificationIndexℤ_comp (ψ : CurveMap C₂ C₃) (φ : CurveMap C₁ C₂)
    (P : C₁.SmoothPoint) (t : C₃.FunctionField) :
    (ψ.comp φ).ramificationIndexℤ P t =
      φ.ramificationIndexℤ P (ψ.pullback t) := rfl

/-- A morphism `φ` is **unramified at `P`** with test function `t` if the
pullback `φ*(t)` has `ord_P = 1` — i.e. `φ*(t)` is itself a uniformizer at `P`.
When `t` is a uniformizer at the image point `φ(P)`, this matches Silverman's
definition of unramified.
Reference: Silverman II.2 (definition before II.2.6). -/
def IsUnramifiedAt (φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint)
    (t : C₂.FunctionField) : Prop :=
  φ.ramificationIndex P t = 1

theorem isUnramifiedAt_iff_uniformizer_pullback (φ : CurveMap C₁ C₂)
    (P : C₁.SmoothPoint) (t : C₂.FunctionField) :
    φ.IsUnramifiedAt P t ↔ SmoothPlaneCurve.Uniformizer C₁ P (φ.pullback t) :=
  Iff.rfl

/-- The identity map is unramified everywhere, when tested against any
uniformizer at the same point. -/
theorem id_isUnramifiedAt (C : SmoothPlaneCurve F) (P : C.SmoothPoint)
    {t : C.FunctionField} (ht : SmoothPlaneCurve.Uniformizer C P t) :
    (id C).IsUnramifiedAt P t := ht

/-- **Ramification positivity (witness-parametric)**: when the pullback
`φ*(t)` lies in the maximal ideal at `P` (i.e. `pointValuation < 1`), the
ramification index satisfies `1 ≤ e_φ(P, t)`. This is the "P is over the
zero of `t`" condition — Silverman's condition for `t` being a uniformizer
at the image point `φ(P)`.
Reference: Silverman II.2.5 (motivation for `e_φ(P) ≥ 1`). -/
theorem one_le_ramificationIndex_of_pullback_pointValuation_lt_one
    (φ : CurveMap C₁ C₂) (P : C₁.SmoothPoint) {t : C₂.FunctionField}
    (ht : t ≠ 0) (h : C₁.pointValuation P (φ.pullback t) < 1) :
    (1 : WithTop ℤ) ≤ φ.ramificationIndex P t :=
  (C₁.one_le_ord_P_iff_pointValuation_lt_one (φ.pullback_ne_zero ht)).mpr h

/-! ### Pushforward / Norm map (T-II-2-005) -/

/-- The **pushforward** (norm map) `φ_* : K(C₁) →* K(C₂)` for a curve map
`φ : C₁ → C₂`, defined as the `K(C₂)`-algebra norm on `K(C₁)` via `φ.toAlgebra`.
Silverman's `φ_* = (φ*)⁻¹ ∘ N_{K(C₁)/φ*K(C₂)}` simplifies to the direct
algebra norm since mathlib's `Algebra.norm` already lands in the base
`K(C₂)`. Reference: Silverman II.2 (definition). -/
noncomputable def pushforward (φ : CurveMap C₁ C₂) :
    C₁.FunctionField →* C₂.FunctionField :=
  @Algebra.norm C₂.FunctionField C₁.FunctionField _ _ φ.toAlgebra

/-- The pushforward of the pullback of `g` is `g^(deg φ)`: this is
`Algebra.norm_algebraMap` for our pullback-induced algebra structure.
Reference: Silverman II.2 (after definition of `φ_*`). -/
theorem pushforward_pullback (φ : CurveMap C₁ C₂) (g : C₂.FunctionField) :
    φ.pushforward (φ.pullback g) = g ^ φ.degree := by
  letI : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
  exact Algebra.norm_algebraMap g

/-- The pushforward is multiplicative. -/
@[simp] theorem pushforward_mul (φ : CurveMap C₁ C₂) (f g : C₁.FunctionField) :
    φ.pushforward (f * g) = φ.pushforward f * φ.pushforward g :=
  φ.pushforward.map_mul f g

/-- The pushforward of `1` is `1`. -/
@[simp] theorem pushforward_one (φ : CurveMap C₁ C₂) :
    φ.pushforward (1 : C₁.FunctionField) = 1 :=
  φ.pushforward.map_one

/-! ### Fiber cardinality (T-II-2-011): Silverman II.2.7

The classical Silverman II.2.7 asserts that a nonconstant curve map `φ` is
unramified iff every geometric fiber has cardinality `deg(φ)`. Since our
`CurveMap` models the function-field side only (no explicit `fiber` type),
we record the combinatorial content as a **witness-parametric** statement:
given a `Finset` of points, their ramification indices, and the sum formula
II.2.6(a) (`Σ e_φ(P) = deg(φ)` witness), the fiber-count equals `deg(φ)` iff
every index is `1`. Once II.2.6(a) is formalized, this immediately gives
T-II-2-011 for every image point `Q`.
-/

/-- **Combinatorial lemma**: if `e : α → ℤ` is ≥ 1 on every element of a
finset `S`, then `∑ P ∈ S, e P = #S` iff each `e P = 1`.

This is the pure combinatorial content underlying Silverman II.2.7. -/
theorem _root_.Finset.sum_eq_card_iff_forall_eq_one_of_one_le
    {α : Type*} {S : Finset α} {e : α → ℤ}
    (hle : ∀ P ∈ S, 1 ≤ e P) :
    ∑ P ∈ S, e P = (S.card : ℤ) ↔ ∀ P ∈ S, e P = 1 := by
  have hconst : ∑ _ ∈ S, (1 : ℤ) = (S.card : ℤ) := by simp
  refine ⟨fun hsum P hP ↦ ?_, fun h ↦ ?_⟩
  · have hsub : ∑ P ∈ S, (e P - 1) = 0 := by
      rw [Finset.sum_sub_distrib, hconst, hsum, sub_self]
    rw [Finset.sum_eq_zero_iff_of_nonneg
      (fun P hP ↦ by linarith [hle P hP])] at hsub
    have := hsub P hP
    linarith
  · exact (Finset.sum_congr rfl h).trans hconst

/-- **Witness-parametric Silverman II.2.7** (T-II-2-011): given a finite
fiber `S` with ramification indices ≥ 1 summing to `deg(φ)`, the fiber
count equals `deg(φ)` iff every ramification index equals `1`.

The hypotheses encode:
* `hle`: each `ramificationIndexℤ` is ≥ 1 on `S` — holds whenever `t` is a
  uniformizer at the common image point (see
  `one_le_ramificationIndex_of_pullback_pointValuation_lt_one`).
* `hsum`: Silverman II.2.6(a) — the sum-of-indices formula, supplied as a
  witness until II.2.6(a) itself is formalized.

Combining this with II.2.6(a) yields the classical: a curve map is
unramified over `Q` iff `#φ⁻¹(Q) = deg(φ)`. -/
theorem fiber_card_eq_degree_iff_all_ramificationIndexℤ_one
    (φ : CurveMap C₁ C₂) (t : C₂.FunctionField)
    (S : Finset C₁.SmoothPoint)
    (hle : ∀ P ∈ S, 1 ≤ φ.ramificationIndexℤ P t)
    (hsum : ∑ P ∈ S, φ.ramificationIndexℤ P t = (φ.degree : ℤ)) :
    (S.card : ℤ) = (φ.degree : ℤ) ↔
      ∀ P ∈ S, φ.ramificationIndexℤ P t = 1 := by
  rw [← hsum, eq_comm]
  exact Finset.sum_eq_card_iff_forall_eq_one_of_one_le hle

/-! ### Degree-one morphisms are isomorphisms on function fields (T-II-2-006) -/

/-- **Silverman II.2.4.1 (pullback-surjectivity form)**: if a curve map `φ`
has degree 1, its pullback `φ*` is surjective. Combined with the automatic
injectivity of pullbacks, `φ*` is then a bijection of function fields. -/
theorem pullback_surjective_of_degree_one (φ : CurveMap C₁ C₂)
    (h : φ.degree = 1) : Function.Surjective φ.pullback := by
  letI : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
  haveI : Module.Free C₂.FunctionField C₁.FunctionField :=
    Module.Free.of_divisionRing _ _
  have hfr : Module.finrank C₂.FunctionField C₁.FunctionField = 1 := h
  obtain ⟨v, _hv_ne, hv⟩ := finrank_eq_one_iff'.mp hfr
  intro w
  obtain ⟨c, hcv⟩ := hv w
  obtain ⟨c₀, hc₀v⟩ := hv (1 : C₁.FunctionField)
  have hc₀_am : algebraMap C₂.FunctionField C₁.FunctionField c₀ * v = 1 := by
    rw [← Algebra.smul_def]; exact hc₀v
  refine ⟨c / c₀, ?_⟩
  have hv_eq : v = (algebraMap C₂.FunctionField C₁.FunctionField c₀)⁻¹ :=
    eq_inv_of_mul_eq_one_right hc₀_am
  change algebraMap C₂.FunctionField C₁.FunctionField (c / c₀) = w
  rw [map_div₀, div_eq_mul_inv, ← hv_eq, ← Algebra.smul_def]
  exact hcv

/-! ### Silverman II.2.6(a): `Σ e_φ(P) · f_φ(P) = deg(φ)` (T-II-2-008 via
coordinate-ring algebra witness)

`CurveMap` stores only the function-field pullback; a generic Dedekind-style
sum-of-ramification-indices formula requires the pullback to restrict to a
ring hom `C₂.CoordinateRing → C₁.CoordinateRing`. We expose this as an
**auxiliary data bundle** (`CurveMap.CoordHom`) together with a compatibility
condition. For the specific coordinate function `x : C → A¹`
(`algebraMap F[X] → F[C]`), see `HasseWeil/Curves/NormValuation.lean`'s
`sum_ramificationIdx_over_fiber` for the unconditional instance. -/

/-- **Coordinate-ring pullback witness**: for a `CurveMap φ : C₁ → C₂`, a
ring hom `C₂.CoordinateRing → C₁.CoordinateRing` compatible with the
function-field pullback. Not every function-field pullback restricts to
coordinate rings (rational-map case), hence this is data rather than
automatic. -/
structure CoordHom (φ : CurveMap C₁ C₂) where
  /-- The `F`-algebra hom on coordinate rings. -/
  toAlgHom : C₂.CoordinateRing →ₐ[F] C₁.CoordinateRing
  /-- Compatibility with the function-field pullback: the induced diagram
      `C₂.CoordinateRing → C₁.CoordinateRing → C₁.FunctionField` commutes
      with `C₂.CoordinateRing → C₂.FunctionField → C₁.FunctionField`. -/
  compat : ∀ u : C₂.CoordinateRing,
    φ.pullback (algebraMap C₂.CoordinateRing C₂.FunctionField u) =
      algebraMap C₁.CoordinateRing C₁.FunctionField (toAlgHom u)

/-- The algebra structure on `C₁.CoordinateRing` over `C₂.CoordinateRing`
induced by a `CoordHom` witness. -/
@[reducible]
noncomputable def CoordHom.toAlgebra {φ : CurveMap C₁ C₂} (coordHom : φ.CoordHom) :
    Algebra C₂.CoordinateRing C₁.CoordinateRing :=
  coordHom.toAlgHom.toRingHom.toAlgebra

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in
/-- **Silverman II.2.6(a), Σ e·f form** (T-II-2-008, generic `CurveMap`):
for a `CurveMap φ : C₁ → C₂` with coordinate-ring pullback witness
`coordHom` and finite-module structure, the sum `Σ_{P over p} e_P · f_P`
equals the function-field degree `φ.degree`.

The proof hinges on two scalar-tower instances:
* `IsScalarTower C₂.CR C₁.CR C₁.FF` — auto-derived from `algCR` (from
  `coordHom`) plus the canonical `Algebra C₁.CR C₁.FF`.
* `IsScalarTower C₂.CR C₂.FF C₁.FF` — proved via `of_algebraMap_smul`
  by unfolding `Algebra.smul_def` and invoking `coordHom.compat`.

The cross-algebra `Algebra C₂.CR C₁.FF` is left for Lean's instance
synthesis (via `OreLocalization.instAlgebra`-based derivation), so the
SMul instances match what mathlib provides by default. -/
theorem sum_ramificationIdx_mul_inertiaDeg_eq_degree
    [IsIntegrallyClosed C₂.CoordinateRing]
    [IsIntegrallyClosed C₁.CoordinateRing]
    (φ : CurveMap C₁ C₂) (coordHom : φ.CoordHom)
    (hfin : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      coordHom.toAlgebra.toModule)
    {p : Ideal C₂.CoordinateRing} (hpMax : p.IsMaximal) (hp0 : p ≠ ⊥) :
    letI : Algebra C₂.CoordinateRing C₁.CoordinateRing := coordHom.toAlgebra
    ∑ P ∈ IsDedekindDomain.primesOverFinset p C₁.CoordinateRing,
        Ideal.ramificationIdx p P *
        Ideal.inertiaDeg p P = φ.degree := by
  letI algCR : Algebra C₂.CoordinateRing C₁.CoordinateRing :=
    coordHom.toAlgebra
  letI algFF : Algebra C₂.FunctionField C₁.FunctionField := φ.toAlgebra
  haveI tower2 : IsScalarTower C₂.CoordinateRing C₁.CoordinateRing
      C₁.FunctionField := inferInstance
  haveI tower1 : IsScalarTower C₂.CoordinateRing C₂.FunctionField
      C₁.FunctionField := by
    refine IsScalarTower.of_algebraMap_smul fun r x ↦ ?_
    rw [Algebra.smul_def]
    show φ.pullback ((algebraMap C₂.CoordinateRing C₂.FunctionField) r) * x =
      r • x
    rw [coordHom.compat r, ← IsScalarTower.algebraMap_smul C₁.CoordinateRing r x,
      ← Algebra.smul_def]
    rfl
  haveI hpMax' : p.IsMaximal := hpMax
  letI modCR : Module C₂.CoordinateRing C₁.CoordinateRing := algCR.toModule
  haveI hfin' : @Module.Finite C₂.CoordinateRing C₁.CoordinateRing _ _
      modCR := hfin
  exact Ideal.sum_ramification_inertia (R := C₂.CoordinateRing)
    (S := C₁.CoordinateRing) C₂.FunctionField C₁.FunctionField hp0

end CurveMap

end HasseWeil.Curves

