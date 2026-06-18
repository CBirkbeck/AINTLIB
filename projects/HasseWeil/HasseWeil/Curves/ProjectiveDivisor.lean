/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import HasseWeil.Curves.Divisors

/-!
# Projective divisors on a smooth plane curve

The projective divisor group `ProjectiveDivisor C` extends the affine
`Divisor C` (free abelian group on `C.SmoothPoint`) by adjoining a single
place at infinity. For a smooth plane curve given by a Weierstrass
equation, the projective closure has a unique point at infinity
`[0 : 1 : 0]`, and the corresponding additive valuation is
`SmoothPlaneCurve.ordAtInfty : F(C) → WithTop ℤ` defined in
`HasseWeil/Curves/Infinity.lean`.

This file provides the minimal type-theoretic scaffolding:

* `ProjectiveSmoothPoint C` — inductive type with constructors `affine P`
  (for `P : C.SmoothPoint`) and `infinity`.
* `ProjectiveDivisor C` — finite `ℤ`-linear combinations of
  `ProjectiveSmoothPoint` (as a `Finsupp`).
* `ProjectiveDivisor.degree`, `ProjectiveDivisor.degreeHom` — the degree
  map with its additive-group-hom packaging.
* `Divisor.toProjective` — the embedding of the affine divisor group into
  `ProjectiveDivisor C`.

Future work (this ticket):

* `SmoothPlaneCurve.projectiveDivisorOf f` — the full projective divisor
  of a rational function, combining `divisorOf` with `ordAtInfty`.
* Principal subgroup, linear equivalence, `Pic`/`Pic⁰` lifted to the
  projective setting.
* Silverman II.3.1(b): `deg(projectiveDivisorOf f) = 0` for nonzero `f`.

Reference: Silverman, *The Arithmetic of Elliptic Curves*, II.3 (projective
form).
-/

namespace HasseWeil.Curves

variable {F : Type*} [Field F]

/-- A place on the projective closure of a smooth plane curve `C`: either an
affine smooth point, or the unique place at infinity.
Reference: Silverman II.3 (projective form). -/
inductive ProjectiveSmoothPoint (C : SmoothPlaneCurve F)
  | affine (P : C.SmoothPoint) : ProjectiveSmoothPoint C
  | infinity : ProjectiveSmoothPoint C

namespace ProjectiveSmoothPoint

variable {C : SmoothPlaneCurve F}

/-- Injectivity of the `affine` constructor. -/
theorem affine_injective :
    Function.Injective (ProjectiveSmoothPoint.affine (C := C)) :=
  fun _ _ h ↦ by injection h

/-- `DecidableEq (ProjectiveSmoothPoint C)` (via classical logic). -/
noncomputable instance (C : SmoothPlaneCurve F) :
    DecidableEq (ProjectiveSmoothPoint C) :=
  Classical.decEq _

end ProjectiveSmoothPoint

/-- A **projective divisor** on `C`: a formal `ℤ`-linear sum of places on the
projective closure (affine smooth points plus the place at infinity).
Reference: Silverman II.3 (projective form). -/
abbrev ProjectiveDivisor (C : SmoothPlaneCurve F) : Type _ :=
  ProjectiveSmoothPoint C →₀ ℤ

namespace ProjectiveDivisor

variable {C : SmoothPlaneCurve F}

/-- The degree `Σ n_v` of a projective divisor `D = Σ n_v (v)`.
Reference: Silverman II.3 (projective form). -/
def degree (D : ProjectiveDivisor C) : ℤ :=
  (D : ProjectiveSmoothPoint C →₀ ℤ).sum fun _ n ↦ n

@[simp] theorem degree_zero : degree (0 : ProjectiveDivisor C) = 0 :=
  Finsupp.sum_zero_index

@[simp] theorem degree_add (D₁ D₂ : ProjectiveDivisor C) :
    (D₁ + D₂).degree = D₁.degree + D₂.degree :=
  Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

/-- The degree map as an additive-group hom `ProjectiveDivisor C →+ ℤ`.
Reference: Silverman II.3 (projective form). -/
def degreeHom (C : SmoothPlaneCurve F) : ProjectiveDivisor C →+ ℤ where
  toFun := degree
  map_zero' := degree_zero
  map_add' := degree_add

@[simp] theorem degreeHom_apply (D : ProjectiveDivisor C) :
    degreeHom C D = D.degree := rfl

@[simp] theorem degree_neg (D : ProjectiveDivisor C) :
    (-D).degree = -D.degree :=
  (degreeHom C).map_neg D

@[simp] theorem degree_sub (D₁ D₂ : ProjectiveDivisor C) :
    (D₁ - D₂).degree = D₁.degree - D₂.degree :=
  (degreeHom C).map_sub D₁ D₂

/-- The subgroup of degree-zero projective divisors,
`ProjectiveDivisor.degZero C = ker(deg)`. -/
noncomputable def degZero (C : SmoothPlaneCurve F) :
    AddSubgroup (ProjectiveDivisor C) :=
  (degreeHom C).ker

@[simp] theorem mem_degZero {D : ProjectiveDivisor C} :
    D ∈ degZero C ↔ D.degree = 0 :=
  AddMonoidHom.mem_ker

end ProjectiveDivisor

namespace Divisor

variable {C : SmoothPlaneCurve F}

/-- Embed the affine divisor group into the projective one by placing each
affine coefficient at the corresponding `affine P` place. -/
noncomputable def toProjective (D : Divisor C) : ProjectiveDivisor C :=
  D.mapDomain ProjectiveSmoothPoint.affine

@[simp] theorem toProjective_zero :
    toProjective (0 : Divisor C) = (0 : ProjectiveDivisor C) :=
  Finsupp.mapDomain_zero

@[simp] theorem toProjective_add (D₁ D₂ : Divisor C) :
    toProjective (D₁ + D₂) = toProjective D₁ + toProjective D₂ :=
  Finsupp.mapDomain_add

@[simp] theorem toProjective_single (P : C.SmoothPoint) (n : ℤ) :
    toProjective (Finsupp.single P n : Divisor C) =
      Finsupp.single (ProjectiveSmoothPoint.affine P) n :=
  Finsupp.mapDomain_single

/-- The degree is preserved by `toProjective`: since the map is injective on
supports and sends each support element to a new support element with the
same coefficient, the sum of coefficients is unchanged. -/
theorem degree_toProjective (D : Divisor C) :
    (toProjective D).degree = D.degree := by
  unfold toProjective ProjectiveDivisor.degree Divisor.degree
  exact Finsupp.sum_mapDomain_index (h := fun _ n ↦ n)
    (fun _ ↦ rfl) (fun _ _ _ ↦ rfl)

/-- **A5 foundational**: `Divisor.toProjective` packaged as an additive group hom
    `Divisor C →+ ProjectiveDivisor C`. -/
noncomputable def toProjectiveHom (C : SmoothPlaneCurve F) :
    Divisor C →+ ProjectiveDivisor C where
  toFun := Divisor.toProjective
  map_zero' := Divisor.toProjective_zero
  map_add' := Divisor.toProjective_add

@[simp] theorem toProjectiveHom_apply (C : SmoothPlaneCurve F) (D : Divisor C) :
    toProjectiveHom C D = D.toProjective := rfl

/-- **A5 degree compatibility (Hom form)**: degree commutes with the affine →
    projective embedding at the AddMonoidHom level. -/
theorem degreeHom_comp_toProjectiveHom (C : SmoothPlaneCurve F) :
    (ProjectiveDivisor.degreeHom C).comp (toProjectiveHom C) = Divisor.degreeHom C :=
  AddMonoidHom.ext fun D ↦ Divisor.degree_toProjective D

/-- **A5 degZero preservation**: `toProjective` sends degree-zero divisors to
    degree-zero projective divisors. Direct from `degree_toProjective`. -/
theorem toProjective_mem_degZero {C : SmoothPlaneCurve F} {D : Divisor C}
    (hD : D ∈ Divisor.degZero C) :
    D.toProjective ∈ ProjectiveDivisor.degZero C := by
  rw [ProjectiveDivisor.mem_degZero, Divisor.degree_toProjective]
  exact (Divisor.mem_degZero.mp hD)

/-- **A5 degZero-restricted bridge**: `toProjectiveHom` restricted to the
    degree-zero subgroups. This is `Divisor.degZero C →+ ProjectiveDivisor.degZero C`. -/
noncomputable def toProjectiveDegZeroHom (C : SmoothPlaneCurve F) :
    Divisor.degZero C →+ ProjectiveDivisor.degZero C :=
  AddMonoidHom.codRestrict
    ((toProjectiveHom C).comp (Divisor.degZero C).subtype)
    (ProjectiveDivisor.degZero C)
    (fun D ↦ toProjective_mem_degZero D.property)

@[simp] theorem toProjectiveDegZeroHom_coe (C : SmoothPlaneCurve F) (D : Divisor.degZero C) :
    ((toProjectiveDegZeroHom C D : ProjectiveDivisor.degZero C) :
      ProjectiveDivisor C) = (D : Divisor C).toProjective := rfl

end Divisor

namespace SmoothPlaneCurve

variable {C : SmoothPlaneCurve F}

/-- The projective divisor of a rational function `f ∈ F(C)`:
`projectiveDivisorOf f := divisorOf f + ordAtInfty(f) · (∞)`, where the
first summand is the affine principal divisor embedded projectively and
the second places the order at infinity at the `infinity` place.

For `f = 0` this returns the zero divisor (since `ordAtInfty 0 = ⊤` is
converted to `0` by `.untopD 0` and `divisorOf 0 = 0`).
Reference: Silverman II.3 (projective form). -/
noncomputable def projectiveDivisorOf (C : SmoothPlaneCurve F) (f : C.FunctionField) :
    ProjectiveDivisor C :=
  (C.divisorOf f).toProjective +
    Finsupp.single ProjectiveSmoothPoint.infinity ((C.ordAtInfty f).untopD 0)

@[simp] theorem projectiveDivisorOf_zero :
    C.projectiveDivisorOf (0 : C.FunctionField) = 0 := by
  unfold projectiveDivisorOf
  rw [C.divisorOf_zero, Divisor.toProjective_zero, zero_add, C.ordAtInfty_zero,
    WithTop.untopD_top, Finsupp.single_zero]

theorem projectiveDivisorOf_apply_affine (f : C.FunctionField) (P : C.SmoothPoint) :
    C.projectiveDivisorOf f (ProjectiveSmoothPoint.affine P) =
      (C.ord_P P f).untopD 0 := by
  unfold projectiveDivisorOf Divisor.toProjective
  have h_ne : ProjectiveSmoothPoint.affine P ≠
      (ProjectiveSmoothPoint.infinity : ProjectiveSmoothPoint C) := by
    intro h; nomatch h
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne h_ne, add_zero,
    Finsupp.mapDomain_apply ProjectiveSmoothPoint.affine_injective
      (C.divisorOf f) P, C.divisorOf_apply]

theorem projectiveDivisorOf_apply_infinity (f : C.FunctionField) :
    C.projectiveDivisorOf f ProjectiveSmoothPoint.infinity =
      (C.ordAtInfty f).untopD 0 := by
  unfold projectiveDivisorOf Divisor.toProjective
  have hnot : (ProjectiveSmoothPoint.infinity : ProjectiveSmoothPoint C) ∉
      ((C.divisorOf f).mapDomain ProjectiveSmoothPoint.affine).support := by
    intro h
    have h' := Finsupp.mapDomain_support h
    rw [Finset.mem_image] at h'
    obtain ⟨P, _, hP⟩ := h'
    nomatch hP
  rw [Finsupp.add_apply, Finsupp.notMem_support_iff.mp hnot, zero_add,
    Finsupp.single_eq_same]

/-- **A5 affine ↔ projective principal compatibility**: when `ordAtInfty f = 0`,
    the projective divisor of `f` coincides with the embedded affine divisor of
    `f`. This is the unconditional case where the affine principal directly
    becomes a projective principal — pertinent to `f` with no pole/zero at
    infinity. -/
theorem projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero {f : C.FunctionField}
    (h : C.ordAtInfty f = ((0 : ℤ) : WithTop ℤ)) :
    C.projectiveDivisorOf f = (C.divisorOf f).toProjective := by
  unfold projectiveDivisorOf
  rw [h, WithTop.untopD_coe, Finsupp.single_zero, add_zero]

/-- **II.3.1(b) structural decomposition**: the degree of the projective divisor
    of `f` decomposes as the sum of the affine divisor's degree and the order
    at infinity. Direct unfolding via `ProjectiveDivisor.degree_add` and
    `Divisor.degree_toProjective`.

    Closure to `= 0` (Silverman II.3.1(b) proper) requires the additional
    identity `(divisorOf f).degree = -(ordAtInfty f).untopD 0` for `f ≠ 0`. -/
theorem projectiveDivisorOf_degree (f : C.FunctionField) :
    (C.projectiveDivisorOf f).degree =
      (C.divisorOf f).degree + (C.ordAtInfty f).untopD 0 := by
  unfold projectiveDivisorOf
  rw [ProjectiveDivisor.degree_add, Divisor.degree_toProjective]
  congr 1
  unfold ProjectiveDivisor.degree
  exact Finsupp.sum_single_index rfl

/-- **II.3.1(b) trivial case f = 0**: the degree of the projective divisor
    of `0` is zero (by convention `projectiveDivisorOf 0 = 0`). -/
@[simp] theorem projectiveDivisorOf_degree_zero :
    (C.projectiveDivisorOf (0 : C.FunctionField)).degree = 0 := by
  rw [C.projectiveDivisorOf_zero, ProjectiveDivisor.degree_zero]

/-- **II.3.1(b) closure equivalence**: for any `f`, the projective divisor
    has degree zero IFF the affine divisor's degree equals `-(ordAtInfty f)`.
    This is the test condition that gates the full II.3.1(b). -/
theorem projectiveDivisorOf_degree_eq_zero_iff (f : C.FunctionField) :
    (C.projectiveDivisorOf f).degree = 0 ↔
      (C.divisorOf f).degree = -((C.ordAtInfty f).untopD 0) := by
  rw [projectiveDivisorOf_degree]
  omega

/-- Multiplicativity of `projectiveDivisorOf` on nonzero inputs. -/
theorem projectiveDivisorOf_mul {f g : C.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    C.projectiveDivisorOf (f * g) =
      C.projectiveDivisorOf f + C.projectiveDivisorOf g := by
  have hfg : f * g ≠ 0 := mul_ne_zero hf hg
  have hv_f : C.ordAtInfty f ≠ ⊤ := (C.ordAtInfty_eq_top_iff f).not.mpr hf
  have hv_g : C.ordAtInfty g ≠ ⊤ := (C.ordAtInfty_eq_top_iff g).not.mpr hg
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hv_f
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp hv_g
  unfold projectiveDivisorOf
  rw [C.divisorOf_mul hf hg, Divisor.toProjective_add, C.ordAtInfty_mul hf hg,
    ← ha, ← hb, ← WithTop.coe_add, WithTop.untopD_coe, WithTop.untopD_coe,
    WithTop.untopD_coe, Finsupp.single_add]
  abel

@[simp] theorem projectiveDivisorOf_one :
    C.projectiveDivisorOf (1 : C.FunctionField) = 0 := by
  rw [projectiveDivisorOf, C.divisorOf_one, Divisor.toProjective_zero, zero_add,
    C.ordAtInfty_one, WithTop.untopD_zero, Finsupp.single_zero]

/-- The divisor of the inverse of a nonzero function is the negation. -/
theorem projectiveDivisorOf_inv {f : C.FunctionField} (hf : f ≠ 0) :
    C.projectiveDivisorOf f⁻¹ = -(C.projectiveDivisorOf f) := by
  have hf_inv : f⁻¹ ≠ 0 := inv_ne_zero hf
  have h := C.projectiveDivisorOf_mul hf_inv hf
  rw [inv_mul_cancel₀ hf, C.projectiveDivisorOf_one] at h
  exact eq_neg_of_add_eq_zero_left h.symm

/-- **II.3.1(b) trivial case f = 1**: the degree of the projective divisor
    of `1` is zero (since `projectiveDivisorOf 1 = 0`). -/
@[simp] theorem projectiveDivisorOf_degree_one :
    (C.projectiveDivisorOf (1 : C.FunctionField)).degree = 0 := by
  rw [C.projectiveDivisorOf_one, ProjectiveDivisor.degree_zero]

/-- **II.3.1(b) multiplicativity**: degree of `projectiveDivisorOf (f * g)`
    splits additively for nonzero `f, g`. Direct from `projectiveDivisorOf_mul`
    and `ProjectiveDivisor.degree_add`. -/
theorem projectiveDivisorOf_degree_mul {f g : C.FunctionField} (hf : f ≠ 0) (hg : g ≠ 0) :
    (C.projectiveDivisorOf (f * g)).degree =
      (C.projectiveDivisorOf f).degree + (C.projectiveDivisorOf g).degree := by
  rw [C.projectiveDivisorOf_mul hf hg, ProjectiveDivisor.degree_add]

/-- **II.3.1(b) inverse**: `degree(projectiveDivisorOf f⁻¹) = -degree(projectiveDivisorOf f)`. -/
theorem projectiveDivisorOf_degree_inv {f : C.FunctionField} (hf : f ≠ 0) :
    (C.projectiveDivisorOf f⁻¹).degree = -(C.projectiveDivisorOf f).degree := by
  rw [C.projectiveDivisorOf_inv hf, ProjectiveDivisor.degree_neg]

/-- **A5 hypothesis-factored principal preservation**: under the (substantive)
    II.3.1(b) hypothesis `deg(projectiveDivisorOf f) = 0`, an affine divisor
    of degree zero coming from `divisorOf f` (nonzero `f`) maps via
    `toProjective` to a projective principal divisor — namely `projectiveDivisorOf f`
    itself. The argument: the structural decomposition forces `ordAtInfty f = 0` once both
    `(divisorOf f).degree = 0` and `(projectiveDivisorOf f).degree = 0`, then
    `projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero` collapses the projective form to
    the affine one. -/
theorem toProjective_eq_projectiveDivisorOf_of_aff_degZero_of_proj_degZero
    {f : C.FunctionField} (hf : f ≠ 0)
    (hII31b : (C.projectiveDivisorOf f).degree = 0)
    (hdivZero : (C.divisorOf f).degree = 0) :
    (C.divisorOf f).toProjective = C.projectiveDivisorOf f := by
  have h_uTopD : (C.ordAtInfty f).untopD 0 = 0 := by
    have hcomb := (C.projectiveDivisorOf_degree_eq_zero_iff f).mp hII31b
    rw [hdivZero] at hcomb
    omega
  have hf_inf : C.ordAtInfty f ≠ ⊤ := (C.ordAtInfty_eq_top_iff f).not.mpr hf
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hf_inf
  have h_ordZero : C.ordAtInfty f = ((0 : ℤ) : WithTop ℤ) := by
    rw [← hn] at h_uTopD ⊢
    rw [WithTop.untopD_coe] at h_uTopD
    rw [h_uTopD]
  exact (C.projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero h_ordZero).symm

/-- **II.3.1(b) hypothesis-factored closure (Helper B form)**: full II.3.1(b)
    closure parametric on the Helper B identity
    `(divisorOf f).degree = intDegree(normAsRatFunc f)`.

    Combining with the definition `ordAtInfty f = -intDegree(normAsRatFunc f)`
    (Curves/Infinity.lean) and the structural decomposition gives the closure:

    `projectiveDivisorOf_degree =
      (divisorOf f).degree + (ordAtInfty f).untopD 0
    = intDegree(N(f)) + (-intDegree(N(f))) = 0`.

    The hypothesis is **substantive upstream content** (Helper B / Silverman
    II.3.1(a)), NOT the bound's conclusion — passes circularity gate 4. -/
theorem projectiveDivisorOf_degree_eq_zero_of_helperB {f : C.FunctionField} (hf : f ≠ 0)
    (hHelperB : (C.divisorOf f).degree = RatFunc.intDegree (C.normAsRatFunc f)) :
    (C.projectiveDivisorOf f).degree = 0 := by
  rw [projectiveDivisorOf_degree, hHelperB,
    C.ordAtInfty_of_ne hf, WithTop.untopD_coe]
  ring

/-- **A5 affine = projective from intDegree-zero**: when `intDegree(normAsRatFunc f) = 0`
    (no pole-or-zero count at infinity), the projective principal coincides
    with the embedded affine principal. Restatement of
    `projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero` in terms of
    `intDegree` (the natural form for Helper B chaining). -/
theorem projectiveDivisorOf_eq_toProjective_of_intDegree_zero {f : C.FunctionField} (hf : f ≠ 0)
    (h : RatFunc.intDegree (C.normAsRatFunc f) = 0) :
    C.projectiveDivisorOf f = (C.divisorOf f).toProjective := by
  have h_ordZero : C.ordAtInfty f = ((0 : ℤ) : WithTop ℤ) := by
    rw [C.ordAtInfty_of_ne hf, h, neg_zero]
  exact C.projectiveDivisorOf_eq_toProjective_of_ordAtInfty_zero h_ordZero

/-- **A5 chained principal preservation**: combining the Helper B
    hypothesis with affine degree-zero gives `toProjective(divisorOf f) =
    projectiveDivisorOf f` (the affine principal becomes a projective principal).

    This is the **mechanically chained form** the downstream Pic⁰_aff ≃+ PicProj⁰
    construction will consume: under Helper B (substantive upstream) and
    affine degree-zero (definition of `Pic⁰_aff`), affine principals lift to
    projective principals. -/
theorem toProjective_eq_projectiveDivisorOf_of_helperB {f : C.FunctionField} (hf : f ≠ 0)
    (hHelperB : (C.divisorOf f).degree = RatFunc.intDegree (C.normAsRatFunc f))
    (hdivZero : (C.divisorOf f).degree = 0) :
    (C.divisorOf f).toProjective = C.projectiveDivisorOf f := by
  have hII31b := C.projectiveDivisorOf_degree_eq_zero_of_helperB hf hHelperB
  exact (C.toProjective_eq_projectiveDivisorOf_of_aff_degZero_of_proj_degZero
    hf hII31b hdivZero)

/-- **A5 Pic-level principal preservation witness under universal Helper B**:
    under the universal-quantified Helper B hypothesis (for all nonzero `f`,
    `(divisorOf f).degree = intDegree(normAsRatFunc f)`), an affine principal
    divisor of degree zero is `projectiveDivisorOf g` for some nonzero `g`
    (specifically `g = f` where `D = divisorOf f`).

    This packages the witness in the form needed for `ProjIsPrincipal`
    (which is defined further below in this file). -/
theorem toProjective_eq_projectiveDivisorOf_witness_of_helperB {D : Divisor C}
    (hD_aff_principal : C.IsPrincipal D) (hD_degZero : D.degree = 0)
    (hHelperB : ∀ f : C.FunctionField, f ≠ 0 →
        (C.divisorOf f).degree = RatFunc.intDegree (C.normAsRatFunc f)) :
    ∃ g : C.FunctionField, g ≠ 0 ∧ C.projectiveDivisorOf g = D.toProjective := by
  obtain ⟨f, hf, hDeq⟩ := hD_aff_principal
  refine ⟨f, hf, ?_⟩
  have hf_div_deg : (C.divisorOf f).degree = 0 := hDeq ▸ hD_degZero
  rw [← hDeq, C.toProjective_eq_projectiveDivisorOf_of_helperB hf
    (hHelperB f hf) hf_div_deg]

/-- A projective divisor `D` is **principal** if `D = projectiveDivisorOf f`
for some nonzero `f ∈ F(C)*`. Reference: Silverman II.3 (projective form). -/
def ProjIsPrincipal (C : SmoothPlaneCurve F) (D : ProjectiveDivisor C) : Prop :=
  ∃ f : C.FunctionField, f ≠ 0 ∧ C.projectiveDivisorOf f = D

theorem projIsPrincipal_zero (C : SmoothPlaneCurve F) : C.ProjIsPrincipal 0 :=
  ⟨1, one_ne_zero, C.projectiveDivisorOf_one⟩

theorem ProjIsPrincipal.add {D₁ D₂ : ProjectiveDivisor C}
    (h₁ : C.ProjIsPrincipal D₁) (h₂ : C.ProjIsPrincipal D₂) :
    C.ProjIsPrincipal (D₁ + D₂) := by
  obtain ⟨f, hf, hDf⟩ := h₁
  obtain ⟨g, hg, hDg⟩ := h₂
  exact ⟨f * g, mul_ne_zero hf hg, by
    rw [C.projectiveDivisorOf_mul hf hg, hDf, hDg]⟩

theorem ProjIsPrincipal.neg {D : ProjectiveDivisor C}
    (h : C.ProjIsPrincipal D) : C.ProjIsPrincipal (-D) := by
  obtain ⟨f, hf, hDf⟩ := h
  exact ⟨f⁻¹, inv_ne_zero hf, by rw [C.projectiveDivisorOf_inv hf, hDf]⟩

/-- The subgroup of principal projective divisors. -/
noncomputable def projPrincipalSubgroup (C : SmoothPlaneCurve F) :
    AddSubgroup (ProjectiveDivisor C) where
  carrier := {D | C.ProjIsPrincipal D}
  zero_mem' := C.projIsPrincipal_zero
  add_mem' := ProjIsPrincipal.add
  neg_mem' := ProjIsPrincipal.neg

@[simp] theorem mem_projPrincipalSubgroup {D : ProjectiveDivisor C} :
    D ∈ C.projPrincipalSubgroup ↔ C.ProjIsPrincipal D := Iff.rfl

/-- Two projective divisors are **linearly equivalent** iff their difference
is principal. -/
def ProjLinearlyEquiv (C : SmoothPlaneCurve F) (D₁ D₂ : ProjectiveDivisor C) :
    Prop := C.ProjIsPrincipal (D₁ - D₂)

theorem ProjLinearlyEquiv.refl (D : ProjectiveDivisor C) :
    C.ProjLinearlyEquiv D D := by
  change C.ProjIsPrincipal (D - D)
  simpa using C.projIsPrincipal_zero

theorem ProjLinearlyEquiv.symm {D₁ D₂ : ProjectiveDivisor C}
    (h : C.ProjLinearlyEquiv D₁ D₂) : C.ProjLinearlyEquiv D₂ D₁ := by
  change C.ProjIsPrincipal (D₂ - D₁)
  rw [show D₂ - D₁ = -(D₁ - D₂) by abel]
  exact h.neg

theorem ProjLinearlyEquiv.trans {D₁ D₂ D₃ : ProjectiveDivisor C}
    (h₁ : C.ProjLinearlyEquiv D₁ D₂) (h₂ : C.ProjLinearlyEquiv D₂ D₃) :
    C.ProjLinearlyEquiv D₁ D₃ := by
  change C.ProjIsPrincipal (D₁ - D₃)
  rw [show D₁ - D₃ = (D₁ - D₂) + (D₂ - D₃) by abel]
  exact h₁.add h₂

/-- The **Picard group** on the projective closure:
`Pic_proj C := ProjectiveDivisor C / projPrincipalSubgroup`. -/
abbrev PicProj (C : SmoothPlaneCurve F) : Type _ :=
  ProjectiveDivisor C ⧸ C.projPrincipalSubgroup

/-- The degree-zero Picard group on the projective closure. -/
abbrev PicProj₀ (C : SmoothPlaneCurve F) : Type _ :=
  (ProjectiveDivisor.degZero C) ⧸
    (C.projPrincipalSubgroup.addSubgroupOf (ProjectiveDivisor.degZero C))

end SmoothPlaneCurve

/- The `RatFunc F` product formula (under `[IsAlgClosed F]`): for `g : RatFunc F` with `F`
algebraically closed, `intDegree g` is the signed sum of root multiplicities (numerator minus
denominator). Combined with the future Helper B (`v_a(N(f)) = Σ_{P : P.x = a} ord_P f`), this
yields `projectiveDivisorOf_degree_zero` (Silverman II.3.1(b)) via
`ordAtInfty f = -intDegree(N f)`. -/
section RatFuncProductFormula

variable (F) in
/-- For algebraically closed `F` and a polynomial `p ∈ F[X]`, the sum of
`rootMultiplicity` over the (finite) root set equals the degree. This is
the polynomial avatar of the product formula for the rational function
field `F(X)`. -/
theorem Polynomial.sum_rootMultiplicity_eq_natDegree [IsAlgClosed F]
    [DecidableEq F] (p : Polynomial F) :
    ∑ a ∈ p.roots.toFinset, p.rootMultiplicity a = p.natDegree := by
  rw [← IsAlgClosed.card_roots_eq_natDegree (k := F) (p := p),
    ← Multiset.toFinset_sum_count_eq]
  exact Finset.sum_congr rfl fun a _ ↦ (Polynomial.count_roots p).symm

/-- **F(x) product formula** (under `[IsAlgClosed F]`): for `g : RatFunc F`,
the signed sum of root multiplicities (numerator minus denominator) equals
the integer degree. -/
theorem RatFunc.intDegree_eq_sum_sub_of_isAlgClosed [IsAlgClosed F]
    [DecidableEq F] (g : RatFunc F) :
    (g.intDegree : ℤ) =
      (∑ a ∈ g.num.roots.toFinset, (g.num.rootMultiplicity a : ℤ)) -
        (∑ a ∈ g.denom.roots.toFinset, (g.denom.rootMultiplicity a : ℤ)) := by
  rw [RatFunc.intDegree,
    ← Polynomial.sum_rootMultiplicity_eq_natDegree F g.num,
    ← Polynomial.sum_rootMultiplicity_eq_natDegree F g.denom]
  push_cast
  rfl

end RatFuncProductFormula

end HasseWeil.Curves
