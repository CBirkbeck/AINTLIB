/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.Verschiebung.FieldTower
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Purely-inseparable structure for `K(E) / Im(π*)` (Session 3)

The Frobenius pullback range `Im(π*) = (frobeniusIsog W).pullback.range`
is a Subalgebra (in fact a subfield) of `K(E)`. As a Subalgebra, it
naturally carries an `Algebra Im(π*) K(E)` structure (the inclusion).

This file:

* Establishes the `IsPurelyInseparable Im(π*) K(E)` structural witness:
  every `x ∈ K(E)` has `x^q ∈ Im(π*)` (where `q = #K`), since `π* x = x^q`
  is in `Im(π*)` by definition.
* Provides reduction lemmas: membership characterization for the
  Frobenius range, and the witness form of the inclusion.

## ⚠ Earlier mis-finding corrected (2026-04-27)

A prior session had claimed that `Φ_q(x_gen) / ΨSq_q(x_gen)` is **not**
a q-th power in `F_p(x_gen)` because `Φ_q ∉ F_p[X^q]` (specifically for
`q=3` over char 3, the X^1 coefficient evaluating to
`b_8² + b_4²·b_8 - b_2·b_6·b_8`). **This claim was wrong**: it failed
to apply the **b-relation** `4·b_8 = b_2·b_6 - b_4²`. Reducing modulo
the b-relation, the X^1 coefficient becomes
`b_8 · (b_4² - b_2·b_6 + b_8) = b_8 · 0 = 0`. Verified by sympy in
`scripts/verify_phi_3_char_3.py` and `scripts/verify_phi_q_clean.py`:

* For `q = 2, 3, 4, 5` in their respective characteristics (with
  b-relation applied), `Φ_q ∈ F_p[X^q]` and `ΨSq_q ∈ F_p[X^q]`.

Hence `mulByInt_x q = Φ_q / ΨSq_q ∈ F_p(X^q) = F_p(x_gen)^q` (the
q-th-power subfield of `F_p(x_gen) ⊆ K(E)`). **The q-th root is
explicit**: substitute `X^q ← X` in `Φ_q` and `ΨSq_q` (since they're
in `F_p[X^q]`), giving `Φ_q'(X), ΨSq_q'(X) ∈ F_p[X]` with
`Φ_q'(X^q) = Φ_q(X)`, `ΨSq_q'(X^q) = ΨSq_q(X)`. Then
`(Φ_q'/ΨSq_q')^q = Φ_q'(X)^q / ΨSq_q'(X)^q = Φ_q'(X^q) / ΨSq_q'(X^q)
= Φ_q(X) / ΨSq_q(X) = mulByInt_x q`. (The middle equation uses
`f^q = f(X^q)` for `f ∈ F_p[X]` in char p.)

So the q-th root of `mulByInt_x q` lives in `F_p(x_gen)` itself (not
needing y_gen). The remaining substantive content is the analogous
fact for `mulByInt_y q` (which involves `ω_q/ψ_q^3` and may genuinely
mix in y_gen).

## Forward path

* **`Φ_q ∈ F_p[X^q]` formalised in Lean**: requires either a manual
  proof via the b-relation (~150 LOC) or extraction from mathlib's
  `Polynomial.expand` machinery (~80 LOC if mathlib has the right
  lemmas).
* **q-th root construction for `mulByInt_x q`**: once the above lands,
  the polynomial-substitution construction is direct (~50 LOC).
* **q-th root for `mulByInt_y q`**: similar verification needed for
  `ω_q` and `ψ_q^3`. Likely follows the same pattern but with bivariate
  polynomials. ~150 LOC.

Total ~280-330 LOC of focused work. The structural blocker is now
**resolved**: the inclusion `Im([q]*) ⊆ Im(π*)` IS provable, via
explicit q-th-root construction.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]

/-! ### Membership characterization for `Im(π*)` -/

/-- The image of the `[q]*`-pullback contains its application to any
    `K(E)` element. (Trivial pointer.) -/
theorem mulByInt_q_apply_mem_range (z : W.toAffine.FunctionField) :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z ∈
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range :=
  ⟨z, rfl⟩

/-- The Subalgebra characterization of `(frobeniusIsog W).pullback.range`:
    membership is exactly being a q-th power. -/
theorem mem_frobenius_range_iff (f : W.toAffine.FunctionField) :
    f ∈ (frobeniusIsog W).pullback.range ↔
      ∃ g : W.toAffine.FunctionField, g ^ Fintype.card K = f := by
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    have := frobeniusIsog_pullback_apply W g
    change g ^ Fintype.card K = f
    rw [← this]; exact hg
  · rintro ⟨g, hg⟩
    refine ⟨g, ?_⟩
    change (frobeniusIsog W).pullback g = f
    rw [frobeniusIsog_pullback_apply]; exact hg

/-! ### `K(E)` is purely inseparable over `Im(π*)`

The Frobenius range `Im(π*) ⊆ K(E)` carries an Algebra structure via
inclusion. Every `x ∈ K(E)` has `x^q ∈ Im(π*)` (since `x^q = π* x ∈ Im(π*)`).
For exponential characteristic, this is the `isPurelyInseparable_iff_pow_mem`
characterisation. -/

/-- The `Im(π*)` Subalgebra. Convenient abbreviation. -/
noncomputable abbrev frobeniusIsog_subalgebra : Subalgebra K W.toAffine.FunctionField :=
  (frobeniusIsog W).pullback.range

/-- Every element `x : K(E)` has `x^q ∈ Im(π*)` — this is
    `π* x = x^q ∈ Im(π*)`. Direct from `frobeniusIsog_pullback_apply`. -/
theorem pow_card_mem_frobenius_subalgebra (x : W.toAffine.FunctionField) :
    x ^ Fintype.card K ∈ frobeniusIsog_subalgebra W := by
  refine ⟨x, ?_⟩
  show (frobeniusIsog W).pullback x = x ^ Fintype.card K
  rw [frobeniusIsog_pullback_apply]

/-! ### IntermediateField promotion of the Frobenius range

Route B prerequisite. The Frobenius pullback is a field homomorphism, so
its range is closed under inverses; this promotes the Subalgebra
`Im(π*)` to an `IntermediateField K (FunctionField W)`. Required for
attaching `IsPurelyInseparable` typeclass instances downstream. -/

/-- The Frobenius range is closed under inverses: `(g^q)⁻¹ = (g⁻¹)^q`. -/
theorem frobeniusIsog_subalgebra_inv_mem (f : W.toAffine.FunctionField)
    (hf : f ∈ frobeniusIsog_subalgebra W) :
    f⁻¹ ∈ frobeniusIsog_subalgebra W := by
  rw [mem_frobenius_range_iff] at hf ⊢
  obtain ⟨g, hg⟩ := hf
  exact ⟨g⁻¹, by rw [inv_pow, hg]⟩

/-- The Frobenius range `Im(π*)` as an `IntermediateField K (FunctionField W)`.
    Bridge for Route B: gives a field-typed carrier on which to attach
    `IsPurelyInseparable` (Silverman III.6.2 via purely inseparable extension
    theory). -/
noncomputable def frobeniusIsog_intermediateField :
    IntermediateField K W.toAffine.FunctionField :=
  (frobeniusIsog_subalgebra W).toIntermediateField
    (frobeniusIsog_subalgebra_inv_mem W)

/-- Membership in `frobeniusIsog_intermediateField` ↔ being a q-th power. -/
theorem mem_frobeniusIsog_intermediateField_iff (f : W.toAffine.FunctionField) :
    f ∈ frobeniusIsog_intermediateField W ↔
      ∃ g : W.toAffine.FunctionField, g ^ Fintype.card K = f :=
  mem_frobenius_range_iff W f

/-- Every `x : K(E)` has `x^q ∈ frobeniusIsog_intermediateField W` (as an
    IntermediateField). Direct lift of `pow_card_mem_frobenius_subalgebra`. -/
theorem pow_card_mem_frobeniusIsog_intermediateField (x : W.toAffine.FunctionField) :
    x ^ Fintype.card K ∈ frobeniusIsog_intermediateField W :=
  pow_card_mem_frobenius_subalgebra W x

/-- The IntermediateField in `algebraMap.range` form, as required by
    `isPurelyInseparable_iff_pow_mem`. The `algebraMap` from an
    IntermediateField is its inclusion `val`, whose range coincides with
    the carrier. -/
theorem pow_card_mem_algebraMap_range (x : W.toAffine.FunctionField) :
    x ^ Fintype.card K ∈
      (algebraMap (frobeniusIsog_intermediateField W) W.toAffine.FunctionField).range := by
  refine ⟨⟨x ^ Fintype.card K, ?_⟩, rfl⟩
  exact pow_card_mem_frobeniusIsog_intermediateField W x

set_option backward.isDefEq.respectTransparency false in
/-- **Route B core (Silverman III.6.2 step)**: `K(E) / Im(π*)` is purely
    inseparable. Direct from `pow_card_mem_algebraMap_range`: every
    `x : K(E)` satisfies `x ^ (Fintype.card K) ∈ Im(π*)`, and
    `Fintype.card K = p ^ n` for the prime characteristic `p`, so
    `IsPurelyInseparable.iff_pow_mem` discharges. -/
instance frobeniusIsog_intermediateField_isPurelyInseparable :
    IsPurelyInseparable
      (frobeniusIsog_intermediateField W) W.toAffine.FunctionField := by
  obtain ⟨p, _, ⟨n, _⟩, hp_prime, hcard⟩ := FiniteField.card' K
  haveI : Fact p.Prime := ⟨hp_prime⟩
  rw [isPurelyInseparable_iff_pow_mem _ p]
  intro x
  refine ⟨n, ?_⟩
  rw [show p ^ n = Fintype.card K from hcard.symm]
  exact pow_card_mem_algebraMap_range W x

/-- The IntermediateField bridge agrees with the canonical `AlgHom.fieldRange`
    of the Frobenius pullback. Both have the same carrier set
    `(frobeniusIsog W).pullback.range`; the equality is by
    `IntermediateField.ext`. Useful for transferring finrank facts proved
    with `fieldRange` to the bridge form. -/
theorem frobeniusIsog_intermediateField_eq_fieldRange :
    frobeniusIsog_intermediateField W =
      (frobeniusIsog W).pullback.fieldRange := by
  apply IntermediateField.toSubalgebra_injective
  rfl

/-! ### Toward `Im([q]*) ⊆ Im(π*)` — Silverman III.6.2 final step

Combining the `IsPurelyInseparable` instance above with
`frobeniusIsog_pullback_finrank` (`[K(E) : Im(π*)] = q`) and
`mulByInt_q_pullback_finrank` (`[K(E) : Im([q]*)] = q²`), the final
inclusion `Im([q]*) ⊆ Im(π*)` follows from the **degree decomposition
of `[q]`** (Silverman III.6.1):

* `[q]` has degree `q²`.
* In characteristic `p` with `q = p^k`, the inseparable degree of `[q]`
  is at least `q` (because `[q]` factors through Frobenius); equivalently,
  the separable degree is at most `q`.
* The unique purely-inseparable extension of degree `q` of `K(E)` is
  `Im(π*)` (since `K(E)/Im(π*)` is purely inseparable of degree exactly
  `q` by the instance above).
* Hence the inseparable factor of `[q]*` coincides with `π*`, giving the
  factorization `[q]* = π* ∘ V*` for some K-alg hom `V*` (the Verschiebung
  pullback). This forces `Im([q]*) ⊆ Im(π*)`.

The substantive blocker is **Silverman III.6.1's degree decomposition**
for elliptic curves, which mathlib does not provide directly. Without it,
the inclusion remains witness-parametric in the existing scaffold:

* `mulByInt_q_factor_witness` (FieldTower.lean) — consumes `V*` as a
  hypothesis.
* `mulByInt_q_pullback_image_subset_frobenius_of_element_witness` (below)
  — consumes the q-th-root function.

Discharging either of these unconditionally requires either Silverman
III.6.1 (degree decomposition) or the polynomial-side route (Route A:
`Φ_q, Ψ_q² ∈ K[X^q]` uniformly via the universal MvPolynomial scaffold). -/

/-! ### Witness form of the inclusion (re-exported)

The element-wise q-th-root witness gives the inclusion `Im([q]*) ⊆ Im(π*)`.
This is the residual mathematical input — equivalent to constructing the
Verschiebung. -/

/-- **Element-wise witness form**: given a function producing q-th roots
    for every `[q]*`-pullback element, the inclusion holds. -/
theorem mulByInt_q_pullback_image_subset_frobenius_of_element_witness
    (h_qth_root : ∀ z : W.toAffine.FunctionField,
      ∃ g : W.toAffine.FunctionField,
        g ^ Fintype.card K =
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z) :
    (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
      (frobeniusIsog W).pullback.range :=
  mulByInt_q_pullback_image_subset_frobenius_witness W h_qth_root

end HasseWeil
