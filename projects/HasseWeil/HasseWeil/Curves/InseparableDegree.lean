/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.EC.IsogenyAG
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Inseparable degree API for isogenies (Silverman II.2.10-12)

This file builds the inseparable-degree / separable-closure API for
elliptic-curve isogenies, building on mathlib's
`Mathlib.FieldTheory.SeparableClosure` (`Field.sepDegree`,
`Field.finInsepDegree`, `separableClosure`) and
`Mathlib.FieldTheory.PurelyInseparable.Basic` (`IsPurelyInseparable`,
`isPurelyInseparable_iff_pow_mem`, `IsPurelyInseparable.pow_mem`).

## Main results

* `Isogeny.inseparableDegree_dvd_degree` — the inseparable degree
  divides the degree (consequence of `finSepDegree · finInsepDegree =
  finrank`, mathlib `PurelyInseparable/Basic.lean:595`).
* `Isogeny.inseparableDegree_eq_one_iff_separable` — direct from the
  project's definition `IsSeparable := inseparableDegree = 1`.
* `Isogeny.inseparableDegree_isPow_of_charP` — in characteristic `p`,
  the inseparable degree is a power of `p`. Uses
  `isPurelyInseparable_iff_pow_mem` (mathlib).

## References

* [Silverman, *The Arithmetic of Elliptic Curves*], II.2.10-12.
-/

open WeierstrassCurve

namespace HasseWeil.EC.Isogeny

variable {F : Type*} [Field F]
  {W : Affine F} [W.IsElliptic]

/-! ### Bridge to mathlib's `Field.finInsepDegree`

The project's `Isogeny.inseparableDegree α = α.degree / α.separableDegree`
(via `CurveMap.inseparableDegree`). Mathlib's
`Field.finInsepDegree F E = finrank (separableClosure F E) E`. These
agree on finite-dimensional extensions via
`Field.finSepDegree_mul_finInsepDegree`. -/

/-- The project's `Isogeny.separableDegree` equals mathlib's
`Field.finSepDegree` under the pullback algebra structure. Definitional
unfold. -/
theorem separableDegree_eq_finSepDegree (α : Isogeny W W) :
    α.separableDegree =
      @Field.finSepDegree W.FunctionField W.FunctionField _ _ α.toAlgebra := rfl

/-- The project's `Isogeny.degree` equals mathlib's `Module.finrank` under
the pullback algebra structure. Definitional unfold. -/
theorem degree_eq_finrank (α : Isogeny W W) :
    α.degree =
      @Module.finrank W.FunctionField W.FunctionField _ _
        α.toAlgebra.toModule := rfl

/-- **Multiplicativity of degree**: under the pullback algebra structure,
`separableDegree · finInsepDegree = degree`. Direct from mathlib's
`Field.finSepDegree_mul_finInsepDegree`. -/
theorem separableDegree_mul_finInsepDegree (α : Isogeny W W) :
    letI : Algebra W.FunctionField W.FunctionField := α.toAlgebra
    α.separableDegree *
        Field.finInsepDegree W.FunctionField W.FunctionField =
      α.degree := by
  letI : Algebra W.FunctionField W.FunctionField := α.toAlgebra
  rw [separableDegree_eq_finSepDegree, degree_eq_finrank]
  exact Field.finSepDegree_mul_finInsepDegree W.FunctionField W.FunctionField

/-- The project's `Isogeny.inseparableDegree` equals mathlib's
`Field.finInsepDegree` under the pullback algebra structure, provided
the separable degree is nonzero (always the case for nonzero
algebraic extensions, e.g., here where `degree ≥ 1`). -/
theorem inseparableDegree_eq_finInsepDegree (α : Isogeny W W)
    (h_sep_pos : 0 < α.separableDegree) :
    letI : Algebra W.FunctionField W.FunctionField := α.toAlgebra
    α.inseparableDegree =
      Field.finInsepDegree W.FunctionField W.FunctionField := by
  letI : Algebra W.FunctionField W.FunctionField := α.toAlgebra
  -- inseparableDegree = degree / separableDegree
  -- = (separableDegree * finInsepDegree) / separableDegree
  -- = finInsepDegree (since separableDegree > 0)
  show α.degree / α.separableDegree =
      Field.finInsepDegree W.FunctionField W.FunctionField
  have h_mul := separableDegree_mul_finInsepDegree α
  show α.degree / α.separableDegree =
      Field.finInsepDegree W.FunctionField W.FunctionField
  rw [show α.degree = α.separableDegree *
      Field.finInsepDegree W.FunctionField W.FunctionField from h_mul.symm]
  exact Nat.mul_div_cancel_left _ h_sep_pos

/-! ### Core lemmas -/

/-- **Inseparable degree divides degree**: `α.inseparableDegree ∣ α.degree`.
For an isogeny, the degree factors as separable * inseparable. -/
theorem inseparableDegree_dvd_degree (α : Isogeny W W) :
    α.inseparableDegree ∣ α.degree := by
  -- inseparableDegree = degree / separableDegree; degree = separableDegree * finInsepDegree.
  -- So separableDegree | degree, hence (degree / separableDegree) | degree.
  letI : Algebra W.FunctionField W.FunctionField := α.toAlgebra
  have h_mul := separableDegree_mul_finInsepDegree α
  show α.degree / α.separableDegree ∣ α.degree
  rw [show α.degree = α.separableDegree *
      Field.finInsepDegree W.FunctionField W.FunctionField from h_mul.symm]
  by_cases h_sep : α.separableDegree = 0
  · -- separableDegree = 0: division gives 0, and 0 divides 0 = degree
    rw [h_sep]; simp
  · -- separableDegree ≠ 0: (separableDegree * x) / separableDegree = x | (separableDegree * x)
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero h_sep)]
    exact Dvd.intro_left _ rfl

/-- **`IsSeparable` ↔ `inseparableDegree = 1`**: direct from the
project's definition. -/
theorem inseparableDegree_eq_one_iff_separable (α : Isogeny W W) :
    α.inseparableDegree = 1 ↔ α.IsSeparable := by
  rfl

/-- **Inseparable degree is a power of the characteristic**: in
characteristic `p`, the inseparable degree of any nonzero-degree isogeny
is `p^e` for some `e ≥ 0`. Uses mathlib's `Field.finInsepDegree_eq_pow`
applied to the field extension `K(E) / α.pullback(K(E))`. -/
theorem inseparableDegree_isPow_of_charP
    {K : Type*} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    {W : WeierstrassCurve K} [W.toAffine.IsElliptic]
    (α : Isogeny W.toAffine W.toAffine)
    (h_deg_pos : 0 < α.degree) :
    ∃ e : ℕ, α.inseparableDegree = p ^ e := by
  letI alg : Algebra W.toAffine.FunctionField W.toAffine.FunctionField := α.toAlgebra
  -- CharP transports along the algebraMap (it's a ringHom into a field of char p)
  haveI : CharP W.toAffine.FunctionField p :=
    charP_of_injective_algebraMap
      (algebraMap K W.toAffine.FunctionField).injective p
  -- ExpChar from CharP + Prime
  haveI : ExpChar W.toAffine.FunctionField p := ExpChar.prime Fact.out
  -- From h_deg_pos: FiniteDimensional via the matching finrank
  haveI hfin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ alg.toModule :=
    @FiniteDimensional.of_finrank_pos _ _ _ _ alg.toModule h_deg_pos
  -- Pull down the mathlib lemma with explicit instances
  obtain ⟨e, he⟩ : ∃ n, @Field.finInsepDegree W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ alg = p ^ n := by
    exact finInsepDegree_eq_pow (F := W.toAffine.FunctionField)
      (E := W.toAffine.FunctionField) p
  -- separableDegree > 0: instNeZeroFinSepDegree under FiniteDimensional
  have h_sep_pos : 0 < α.separableDegree := by
    rw [separableDegree_eq_finSepDegree]
    exact Nat.pos_of_ne_zero
      (@NeZero.ne _ _ _ (@Field.instNeZeroFinSepDegree _ _ _ _ alg hfin))
  refine ⟨e, ?_⟩
  rw [inseparableDegree_eq_finInsepDegree α h_sep_pos]
  exact he

/-! ### P0-B — `Isogeny.separableSubfield`

The maximal intermediate field over which `K(E)` is purely inseparable.
Direct specialisation of `Mathlib.FieldTheory.separableClosure` to
`α.pullback.fieldRange ⊆ K(E)`. -/

set_option backward.isDefEq.respectTransparency false in
/-- **The separable closure of `α^*(K(E))` inside `K(E)`**. This is the
maximal intermediate field over which `K(E)` is purely inseparable. -/
noncomputable def separableSubfield (α : Isogeny W W) :
    IntermediateField α.pullback.fieldRange W.FunctionField :=
  separableClosure α.pullback.fieldRange W.FunctionField

set_option backward.isDefEq.respectTransparency false in
/-- **Bottom inclusion**: `α^*(K(E)) ⊆ separableSubfield`. -/
theorem separableSubfield_includes_pullbackRange (α : Isogeny W W) :
    ⊥ ≤ α.separableSubfield := bot_le

set_option backward.isDefEq.respectTransparency false in
/-- **`K(E)` is purely inseparable over `α.separableSubfield`**: direct
from mathlib's `separableClosure.isPurelyInseparable`, under the
algebraicity assumption (automatic for `Module.Finite`). -/
theorem function_field_over_separableSubfield_purely_inseparable
    (α : Isogeny W W)
    [Algebra.IsAlgebraic α.pullback.fieldRange W.FunctionField] :
    _root_.IsPurelyInseparable (↥α.separableSubfield) W.FunctionField :=
  separableClosure.isPurelyInseparable _ _

end HasseWeil.EC.Isogeny
