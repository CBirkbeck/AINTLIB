import HasseWeil.Curves.Basic
import HasseWeil.Curves.Infinity
import Mathlib.Data.Finsupp.Defs

open scoped Polynomial.Bivariate

/-!
# Divisors on a smooth plane curve

The divisor group `Div C` of a smooth plane curve `C` is the free abelian group
on its smooth points: a formal sum `Σ nₚ (P)` with integer coefficients that
are zero for all but finitely many points.

This closes tickets `T-II-3-001` (`Divisor`) and `T-II-3-002`
(`Divisor.degree`, `Divisor.degreeHom`).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.3 (definition)
-/

namespace HasseWeil.Curves

variable {F : Type*} [Field F]

/-- The divisor group of a smooth plane curve: the free abelian group on its
smooth points, realized as finitely supported functions from `SmoothPoint` to
`ℤ`.
Reference: Silverman II.3 (definition). -/
abbrev Divisor (C : SmoothPlaneCurve F) : Type _ := C.SmoothPoint →₀ ℤ

namespace Divisor

variable {C : SmoothPlaneCurve F}

/-- The degree `Σ n_P` of a divisor `D = Σ n_P (P)`.
Reference: Silverman II.3 (definition). -/
def degree (D : Divisor C) : ℤ :=
  (D : C.SmoothPoint →₀ ℤ).sum fun _ n => n

@[simp] theorem degree_zero : degree (0 : Divisor C) = 0 :=
  Finsupp.sum_zero_index

@[simp] theorem degree_add (D₁ D₂ : Divisor C) :
    (D₁ + D₂).degree = D₁.degree + D₂.degree :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

/-- The degree map as an additive group homomorphism `Div(C) →+ ℤ`.
Reference: Silverman II.3 (definition). -/
def degreeHom (C : SmoothPlaneCurve F) : Divisor C →+ ℤ where
  toFun := degree
  map_zero' := degree_zero
  map_add' := degree_add

@[simp] theorem degreeHom_apply (D : Divisor C) : degreeHom C D = D.degree := rfl

@[simp] theorem degree_neg (D : Divisor C) : (-D).degree = -D.degree :=
  (degreeHom C).map_neg D

@[simp] theorem degree_sub (D₁ D₂ : Divisor C) :
    (D₁ - D₂).degree = D₁.degree - D₂.degree :=
  (degreeHom C).map_sub D₁ D₂

/-- The subgroup of degree-zero divisors, `Div⁰(C) = ker(deg)`.
Reference: Silverman II.3 (definition). -/
noncomputable def degZero (C : SmoothPlaneCurve F) : AddSubgroup (Divisor C) :=
  (degreeHom C).ker

@[simp] theorem mem_degZero {D : Divisor C} : D ∈ degZero C ↔ D.degree = 0 :=
  AddMonoidHom.mem_ker

/-- A divisor `D` is **effective** (or positive), written `D ≥ 0` in Silverman,
if all its coefficients are non-negative: `D = Σ n_P (P)` with `n_P ≥ 0`.
Reference: Silverman II.3 (definition). -/
def IsEffective (D : Divisor C) : Prop := ∀ P, 0 ≤ D P

@[simp] theorem isEffective_zero : IsEffective (0 : Divisor C) := fun _ => le_refl 0

theorem IsEffective.add {D₁ D₂ : Divisor C} (h₁ : D₁.IsEffective)
    (h₂ : D₂.IsEffective) : (D₁ + D₂).IsEffective := fun P => by
  rw [Finsupp.add_apply]; exact add_nonneg (h₁ P) (h₂ P)

theorem degree_nonneg_of_isEffective {D : Divisor C} (hD : D.IsEffective) :
    0 ≤ D.degree :=
  Finsupp.sum_nonneg fun P _ => hD P

end Divisor

/-- The group of degree-zero divisors on `C`. -/
noncomputable abbrev Divisor₀ (C : SmoothPlaneCurve F) : AddSubgroup (Divisor C) :=
  Divisor.degZero C

/-! ### `divisorOf f`: the principal divisor (T-II-3-005) -/

namespace SmoothPlaneCurve

variable {C : SmoothPlaneCurve F}

/-- The principal divisor of a rational function `f ∈ F(C)`:
`div(f) := Σ_P ord_P(f) · (P)`. Well-defined thanks to
`finite_setOf_ord_P_nonzero` (Silverman II.1.2). Returns the zero divisor
when `f = 0`. Reference: Silverman II.3 (definition). -/
noncomputable def divisorOf (C : SmoothPlaneCurve F) (f : C.FunctionField) :
    Divisor C := by
  classical
  refine Finsupp.ofSupportFinite (fun P => (C.ord_P P f).untopD 0) ?_
  by_cases hf : f = 0
  · subst hf
    have : Function.support (fun P : C.SmoothPoint =>
        (C.ord_P P (0 : C.FunctionField)).untopD 0) = ∅ := by
      ext P; simp [C.ord_P_zero]
    rw [this]; exact Set.finite_empty
  · refine (C.finite_setOf_ord_P_nonzero hf).subset ?_
    intro P hP
    simp only [Set.mem_setOf_eq]
    intro h0
    apply hP
    simp [h0]

theorem divisorOf_apply (C : SmoothPlaneCurve F) (f : C.FunctionField)
    (P : C.SmoothPoint) :
    C.divisorOf f P = (C.ord_P P f).untopD 0 := rfl

@[simp] theorem divisorOf_zero (C : SmoothPlaneCurve F) :
    C.divisorOf (0 : C.FunctionField) = 0 := by
  refine Finsupp.ext fun P => ?_
  rw [divisorOf_apply, C.ord_P_zero]; rfl

/-- The divisor of a product is the sum of divisors (for nonzero inputs). -/
theorem divisorOf_mul (C : SmoothPlaneCurve F) {f g : C.FunctionField}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    C.divisorOf (f * g) = C.divisorOf f + C.divisorOf g := by
  refine Finsupp.ext fun P => ?_
  rw [Finsupp.add_apply, divisorOf_apply, divisorOf_apply, divisorOf_apply,
    C.ord_P_mul]
  have hvf : C.ord_P P f ≠ ⊤ := (C.ord_P_eq_top_iff f).not.mpr hf
  have hvg : C.ord_P P g ≠ ⊤ := (C.ord_P_eq_top_iff g).not.mpr hg
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hvf
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hvg
  rw [← ha, ← hb, ← WithTop.coe_add, WithTop.untopD_coe, WithTop.untopD_coe,
    WithTop.untopD_coe]

@[simp] theorem divisorOf_one (C : SmoothPlaneCurve F) :
    C.divisorOf (1 : C.FunctionField) = 0 := by
  refine Finsupp.ext fun P => ?_
  rw [divisorOf_apply, ord_P_one]; rfl

/-- The divisor of the inverse of a nonzero function is the negation of its
divisor: `div(f⁻¹) = -div(f)`. -/
theorem divisorOf_inv (C : SmoothPlaneCurve F) {f : C.FunctionField}
    (hf : f ≠ 0) :
    C.divisorOf f⁻¹ = -(C.divisorOf f) := by
  refine Finsupp.ext fun P => ?_
  rw [Finsupp.neg_apply, divisorOf_apply, divisorOf_apply,
    C.ord_P_inv f hf]
  have hvf : C.ord_P P f ≠ ⊤ := (C.ord_P_eq_top_iff f).not.mpr hf
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hvf
  rw [← ha, show -(↑a : WithTop ℤ) = ((-a : ℤ) : WithTop ℤ) from rfl,
    WithTop.untopD_coe, WithTop.untopD_coe]

/-- The divisor of a positive power: `div(f^n) = n · div(f)` for `f ≠ 0`. -/
theorem divisorOf_pow (C : SmoothPlaneCurve F) {f : C.FunctionField}
    (hf : f ≠ 0) (n : ℕ) :
    C.divisorOf (f ^ n) = n • C.divisorOf f := by
  refine Finsupp.ext fun P => ?_
  rw [Finsupp.coe_smul, Pi.smul_apply, divisorOf_apply, divisorOf_apply,
    C.ord_P_pow f n]
  have hvf : C.ord_P P f ≠ ⊤ := (C.ord_P_eq_top_iff f).not.mpr hf
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hvf
  rw [← ha, ← WithTop.coe_nsmul, WithTop.untopD_coe, WithTop.untopD_coe]

/-- The divisor map as a monoid homomorphism from the units of `F(C)` to
the additive divisor group. -/
noncomputable def divisorHom (C : SmoothPlaneCurve F) :
    C.FunctionFieldˣ →* Multiplicative (Divisor C) where
  toFun u := Multiplicative.ofAdd (C.divisorOf (u : C.FunctionField))
  map_one' := by simp
  map_mul' u v := by
    simp only [Units.val_mul, ← ofAdd_add]
    congr 1
    exact C.divisorOf_mul u.ne_zero v.ne_zero

/-! ### Principal divisors and linear equivalence (T-II-3-006) -/

/-- A divisor `D` on `C` is **principal** if `D = div(f)` for some nonzero
rational function `f ∈ F(C)`. Equivalently, `D` lies in the image of the
divisor map `divisorHom : F(C)ˣ → Div(C)`. Reference: Silverman II.3
(definition, pre-II.3.1). -/
def IsPrincipal (C : SmoothPlaneCurve F) (D : Divisor C) : Prop :=
  ∃ f : C.FunctionField, f ≠ 0 ∧ C.divisorOf f = D

theorem isPrincipal_zero (C : SmoothPlaneCurve F) : C.IsPrincipal 0 :=
  ⟨1, one_ne_zero, C.divisorOf_one⟩

theorem IsPrincipal.add {C : SmoothPlaneCurve F} {D₁ D₂ : Divisor C}
    (h₁ : C.IsPrincipal D₁) (h₂ : C.IsPrincipal D₂) :
    C.IsPrincipal (D₁ + D₂) := by
  obtain ⟨f, hf, hDf⟩ := h₁
  obtain ⟨g, hg, hDg⟩ := h₂
  exact ⟨f * g, mul_ne_zero hf hg, by rw [C.divisorOf_mul hf hg, hDf, hDg]⟩

theorem IsPrincipal.neg {C : SmoothPlaneCurve F} {D : Divisor C}
    (h : C.IsPrincipal D) :
    C.IsPrincipal (-D) := by
  obtain ⟨f, hf, hDf⟩ := h
  exact ⟨f⁻¹, inv_ne_zero hf, by rw [C.divisorOf_inv hf, hDf]⟩

/-- The **subgroup of principal divisors** on `C`: the image of the divisor
map from `F(C)ˣ` to `Divisor C`. Reference: Silverman II.3 (definition). -/
noncomputable def principalSubgroup (C : SmoothPlaneCurve F) :
    AddSubgroup (Divisor C) where
  carrier := {D | C.IsPrincipal D}
  zero_mem' := C.isPrincipal_zero
  add_mem' := IsPrincipal.add
  neg_mem' := IsPrincipal.neg

@[simp] theorem mem_principalSubgroup {C : SmoothPlaneCurve F} {D : Divisor C} :
    D ∈ C.principalSubgroup ↔ C.IsPrincipal D := Iff.rfl

/-- Two divisors are **linearly equivalent** iff their difference is principal.
Silverman writes `D₁ ~ D₂`. -/
def LinearlyEquiv (C : SmoothPlaneCurve F) (D₁ D₂ : Divisor C) : Prop :=
  C.IsPrincipal (D₁ - D₂)

theorem LinearlyEquiv.refl (C : SmoothPlaneCurve F) (D : Divisor C) :
    C.LinearlyEquiv D D := by
  change C.IsPrincipal (D - D)
  simpa using C.isPrincipal_zero

theorem LinearlyEquiv.symm {C : SmoothPlaneCurve F} {D₁ D₂ : Divisor C}
    (h : C.LinearlyEquiv D₁ D₂) : C.LinearlyEquiv D₂ D₁ := by
  change C.IsPrincipal (D₂ - D₁)
  rw [show D₂ - D₁ = -(D₁ - D₂) by abel]
  exact h.neg

theorem LinearlyEquiv.trans {C : SmoothPlaneCurve F} {D₁ D₂ D₃ : Divisor C}
    (h₁ : C.LinearlyEquiv D₁ D₂) (h₂ : C.LinearlyEquiv D₂ D₃) :
    C.LinearlyEquiv D₁ D₃ := by
  change C.IsPrincipal (D₁ - D₃)
  rw [show D₁ - D₃ = (D₁ - D₂) + (D₂ - D₃) by abel]
  exact h₁.add h₂

/-! ### T-II-3-008: constants have zero divisor -/

/-- `ord_P` of an `F`-constant `c ≠ 0` is zero: a nonzero constant is a unit
at every smooth point (image of the F-subfield, which lives in the local
ring units). -/
theorem ord_P_algebraMap_F_of_ne_zero (C : SmoothPlaneCurve F) {c : F}
    (hc : c ≠ 0) (P : C.SmoothPoint) :
    C.ord_P P (algebraMap F C.FunctionField c) = 0 := by
  -- Factor algebraMap F → F(C) = (algebraMap F[C] → F(C)) ∘ (algebraMap F → F[C]).
  let u : C.CoordinateRing := algebraMap F C.CoordinateRing c
  have hu_ne : u ≠ 0 := by
    intro h
    apply hc
    have h' : (algebraMap F C.CoordinateRing) c =
        (algebraMap F C.CoordinateRing) 0 := by rw [map_zero]; exact h
    exact FaithfulSMul.algebraMap_injective F C.CoordinateRing h'
  -- Rewrite u as (C c) • 1 + 0 • Y to apply the public membership lemma.
  have hu_eq : u = (Polynomial.C c) • (1 : C.CoordinateRing) +
      (0 : Polynomial F) •
        WeierstrassCurve.Affine.CoordinateRing.mk C.toAffine Y := by
    change algebraMap F C.CoordinateRing c = _
    rw [zero_smul, add_zero, Algebra.smul_def, mul_one,
      IsScalarTower.algebraMap_apply F (Polynomial F) C.CoordinateRing c]
    rfl
  have hu_notmem : u ∉ C.maximalIdealAt P := by
    rw [hu_eq, C.mem_maximalIdealAt_iff_eval_zero P (Polynomial.C c) 0]
    simp [hc]
  -- So ord_P (algebraMap u) = 0 (bridge from ord ≠ 0 to M_P).
  have h_ord_zero : C.ord_P P
      (algebraMap C.CoordinateRing C.FunctionField u) = 0 := by
    by_contra h_ne
    exact hu_notmem ((C.ord_P_algebraMap_ne_zero_iff_mem_maximalIdealAt
      hu_ne P).mp h_ne)
  -- Convert algebraMap F F(C) c to algebraMap F[C] F(C) u via scalar tower.
  rw [show (algebraMap F C.FunctionField c : C.FunctionField) =
    algebraMap C.CoordinateRing C.FunctionField u from
    IsScalarTower.algebraMap_apply F C.CoordinateRing C.FunctionField c]
  exact h_ord_zero

/-- The divisor of an `F`-constant is zero: `div(algebraMap c) = 0` for any
`c : F`. This is the (⇐) direction of Silverman II.3.1(a): constants have no
zeros or poles. -/
@[simp] theorem divisorOf_algebraMap_F (C : SmoothPlaneCurve F) (c : F) :
    C.divisorOf (algebraMap F C.FunctionField c) = 0 := by
  by_cases hc : c = 0
  · rw [hc, map_zero, C.divisorOf_zero]
  refine Finsupp.ext fun P => ?_
  rw [divisorOf_apply, C.ord_P_algebraMap_F_of_ne_zero hc P]; rfl

/-! ### T-II-3-008 (⇒): `divisorOf = 0 ⇒ const` (prime-indexed via IC-006) -/

/-- **T-II-3-008 (⇒), prime-indexed**: if `f ∈ F(C)` has valuation at most 1
at every nonzero prime of `C.CoordinateRing` **and** has nonnegative order at
infinity, then `f` is the image of a constant from `F`. This is the content
of Silverman II.3.1(a) `⇒` in the prime-indexed reformulation made available
by IC-006; the SmoothPoint-indexed statement follows once every nonzero
prime is in the image of `SmoothPoint.toHeightOneSpectrum` (the surjection
step under `[IsAlgClosed F]`, tracked separately). -/
theorem const_of_valuation_le_one_of_ordAtInfty_nonneg
    [IsIntegrallyClosed C.CoordinateRing] (f : C.FunctionField)
    (h_primes : ∀ v : IsDedekindDomain.HeightOneSpectrum C.CoordinateRing,
      v.valuation C.FunctionField f ≤ 1)
    (h_inf : (0 : WithTop ℤ) ≤ C.ordAtInfty f) :
    ∃ c : F, f = algebraMap F C.FunctionField c :=
  C.const_of_no_poles_of_valuation_of_ordAtInfty f h_primes h_inf

/-! ### Pic and Pic₀ (T-II-3-007) -/

/-- The **Picard group** of `C`: divisors modulo principal divisors.
Silverman II.3 (definition). -/
abbrev Pic (C : SmoothPlaneCurve F) : Type _ :=
  Divisor C ⧸ C.principalSubgroup

/-- The **degree-zero Picard group** `Pic⁰(C)`: degree-zero divisors modulo
principal divisors (principal divisors automatically have degree zero by
Silverman II.3.1(b), tracked as T-II-3-009). -/
abbrev Pic₀ (C : SmoothPlaneCurve F) : Type _ :=
  (Divisor.degZero C) ⧸ (C.principalSubgroup.addSubgroupOf (Divisor.degZero C))

end SmoothPlaneCurve

end HasseWeil.Curves
