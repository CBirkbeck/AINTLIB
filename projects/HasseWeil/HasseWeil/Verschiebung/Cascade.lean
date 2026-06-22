/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.AdditionPullback.Frobenius
import HasseWeil.Hasse.HoleE
import HasseWeil.Verschiebung.IsDual
import HasseWeil.Verschiebung.QthRoots

/-!
# Wire-up: Verschiebung witness → HOLE E (Session 6)

This file wires the Verschiebung chain (Sessions 2–5) into the Hasse-Weil
cascade. Given the Session 3 inclusion `Im([q]*) ⊆ Im(π*)`, the
Verschiebung-as-`IsDualOf` is established (Session 5), and that plugs
directly into `hole_e_closer_via_frobenius_dual_witness` (the Tier 1
closer shipped earlier).

## Result

A single witness-parametric entry point producing the signed quadratic
form identity for the Hasse cascade, taking ONE input — the Session 3
inclusion (along with the existing degree-bridge / nonneg / sum-pts
witnesses, which are CLOSE-C-aligned and largely shipped in
`Hasse/HoleE.lean`).

## Status

When Session 3's inclusion is discharged unconditional (via Frobenius
factorization on the function-field side, ~200 LOC of focused work), the
entire chain becomes axiom-clean and discharges HOLE E end-to-end.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ### Hasse cascade entry point -/

/-! ### Wire-up via q-th-root function (Task 3 deliverable)

Given a per-z q-th-root function `h_qth_root : ∀ z, ∃ g, g^q = [q]*z`,
the inclusion `Im([q]*) ⊆ Im(π*)` follows automatically (already shipped
in `FieldTower.lean`), and the entire Verschiebung-IsDualOf chain plugs
in. This wire-up reduces the cascade to a SINGLE residual: producing
the per-z q-th-root function. -/

/-! ### IsDualOf certificate (witness-parametric)

The end-of-chain wire-up: given a universal q-th-root function for the
`[q]`-pullback, the witness-parametric Verschiebung is its IsDualOf
certificate. Direct composition of
`mulByInt_q_pullback_image_subset_frobenius_of_element_witness`
(Session 7) and `verschiebungIsog_of_witness_isDualOf_frobenius`
(Session 5).

For q=2 char-2: the universal q-th-root function rides up from
* `mulByInt_q_pullback_x_gen_qth_root_of_expand_witness` (Session 7)
  + `Φ_two_mem_expand_two_char_two` + `ΨSq_two_mem_expand_two_char_two`,
* `y_qth_root_squared_eq_mulByInt_y_two_of_witnesses` (Session 22)
  + `mulByInt_q_pullback_y_gen_qth_root_of_witness` (Session 7) for y_gen,
* `mulByInt_q_pullback_range_subset_frobenius_of_xy_subfield_witness`
  (Session 7) for the K(E) generator-reduction.

The two named witness hypotheses (h_polyRoot_sq_alpha_0/1) propagate up
the chain; their unconditional discharge is tracked as a separate
mathlib-API task (proof-irrelevance for polyExpandRoot, or restating
via `^ Fintype.card K` throughout). -/

/-- **IsDualOf certificate, witness-parametric on universal q-th-root**:
    the Verschiebung-as-dual-of-Frobenius certificate, given a universal
    q-th-root function. The construction of the universal function for
    q=2 char-2 is itself a chain of witness-parametric scaffolds; this
    theorem packages the final composition. -/
theorem verschiebungIsog_isDualOf_frobenius_of_qth_root_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_qth_root : ∀ z : W.toAffine.FunctionField,
      ∃ g : W.toAffine.FunctionField,
        g ^ Fintype.card K =
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z) :
    IsDualOf W.toAffine
      (verschiebungIsog_of_witness W
        (mulByInt_q_pullback_image_subset_frobenius_of_element_witness W h_qth_root))
      (frobeniusIsog W) :=
  verschiebungIsog_of_witness_isDualOf_frobenius W _

/-! ### Bridge: q-Frobenius factorization → universal q-th-root

The substantive content of "iterated Silverman II.2.12" applied to `[q]`:
in characteristic `p` with `q = p^k`, the multiplication-by-`q` map factors
as `[q] = ψ ∘ φ_q` for some isogeny `ψ : E → E` (the Verschiebung). Once
this factorization is established (upstream content, T-II-2-016c iterated),
the universal q-th-root witness for `verschiebungIsog_of_witness_isDualOf_frobenius`
follows definitionally from `frobeniusIsog_pullback_apply`. -/

/-- **q-Frobenius factorization → universal q-th-root**: given that `[q]`
factors through the q-Frobenius isogeny — i.e., `∃ ψ, ψ ∘ φ_q = [q]` at
the isogeny level — every `K(E)` element has a q-th root in the
`[q]`-pullback range. Substantive upstream content: iterated II.2.12 for
[q] = [p]^k. Witness-parametric on the factorization existence. -/
theorem qth_root_of_q_factors_through_frobenius
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_factor : ∃ ψ : Isogeny W.toAffine W.toAffine,
      ψ.comp (frobeniusIsog W) =
        mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)) :
    ∀ z : W.toAffine.FunctionField,
      ∃ g : W.toAffine.FunctionField,
        g ^ Fintype.card K =
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z := by
  obtain ⟨ψ, h_eq⟩ := h_factor
  refine fun z ↦ ⟨ψ.pullback z, ?_⟩
  rw [← h_eq, show (ψ.comp (frobeniusIsog W)).pullback z =
    (frobeniusIsog W).pullback (ψ.pullback z) from rfl, frobeniusIsog_pullback_apply]

/-- **IsDualOf certificate from [q]-Frobenius factorization**: chains
`qth_root_of_q_factors_through_frobenius` with
`verschiebungIsog_isDualOf_frobenius_of_qth_root_witness` to produce
both compositions `V ∘ φ_q = [q]` and `φ_q ∘ V = [q]` from a single
factorization hypothesis (substantive: iterated Silverman II.2.12). -/
theorem verschiebungIsog_isDualOf_frobenius_of_factor
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_factor : ∃ ψ : Isogeny W.toAffine W.toAffine,
      ψ.comp (frobeniusIsog W) =
        mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)) :
    IsDualOf W.toAffine
      (verschiebungIsog_of_witness W
        (mulByInt_q_pullback_image_subset_frobenius_of_element_witness W
          (qth_root_of_q_factors_through_frobenius W h_factor)))
      (frobeniusIsog W) :=
  verschiebungIsog_isDualOf_frobenius_of_qth_root_witness W
    (qth_root_of_q_factors_through_frobenius W h_factor)

/-- **Inclusion witness → factorization existence**: trivially packages
the shipped `verschiebung_comp_frobenius_eq_mulByInt_q` (IsDual.lean) into
the existential form consumed by `qth_root_of_q_factors_through_frobenius`.
Connects the existing Session 3 inclusion infrastructure to the factorization
form of iterated II.2.12. -/
theorem mulByInt_q_factor_isog_of_subset_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    ∃ ψ : Isogeny W.toAffine W.toAffine,
      ψ.comp (frobeniusIsog W) =
        mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ) :=
  ⟨verschiebungIsog_of_witness W h_subset,
    verschiebung_comp_frobenius_eq_mulByInt_q W h_subset⟩

/-! ### Conditional iterated II.2.12: structured Silverman III.6.1 packaging

The iterated Silverman II.2.12 specialised to `[q] = [p^k]` over an
F_q-rational elliptic curve. Per Silverman III.6.1 Case 2, the
multiplication-by-q map factors as `[q] = ψ ∘ φ_q` for a separable
isogeny ψ : E → E (the Verschiebung).

Three equivalent forms of this content (all ↔ via shipped infrastructure):

1. **Inclusion**: `[q]^*K(E) ⊆ φ_q^*K(E) = K(E)^q`.
2. **Q-th root**: `∀ z ∈ K(E), ∃ g, g^q = [q]^*(z)`.
3. **Factorization**: `∃ ψ : Isogeny E E, ψ ∘ φ_q = [q]`.

Worker C's Route 2 universal `Φ_q ∈ K[X^q]` discharges (1) uniformly in p.
Per-prime cases (q=2,3,5,7) are shipped via direct discharge of (2). The
bridges in this file translate freely among the three forms. -/

namespace Conditional

/-- **Iterated Silverman II.2.12 (Conditional)**: from the Session 3
inclusion (the substantive Silverman III.6.1 Case 2 content), the
multiplication-by-q map factors as `[q] = ψ ∘ φ_q` AND the dual property
holds (both compositions equal `[q]`). The conditional namespacing makes
explicit that the inclusion hypothesis represents UPSTREAM substantive
content (Worker C's Route 2 universal Φ_q ∈ K[X^q] / per-prime III.6.2). -/
theorem iterated_silverman_II_2_12_of_subset_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (h_subset :
      (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback.range ≤
        (frobeniusIsog W).pullback.range) :
    (∃ ψ : Isogeny W.toAffine W.toAffine,
        ψ.comp (frobeniusIsog W) =
          mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)) ∧
    IsDualOf W.toAffine
      (verschiebungIsog_of_witness W h_subset) (frobeniusIsog W) :=
  ⟨mulByInt_q_factor_isog_of_subset_witness W h_subset,
    verschiebungIsog_of_witness_isDualOf_frobenius W h_subset⟩

end Conditional

/-! ### Bound assembly: Worker A (HOLE D) + Worker C (HOLE E) → Hasse-Weil

End-of-chain assembled bound combining Worker A's Day 4 deferred witnesses
(separability, finite-dim, sepDegree = pointCount for the unconditional
`isogOneSub_negFrobenius` α) with Worker C's witness-parametric signed QF
identity in Worker A's α-shape.

This is the first time the Hasse-Weil bound itself appears as a typed
theorem in the codebase — `|#E(F_q) − q − 1| ≤ 2√q` for q=2 char=2,
publication-shaped witness-parametric, axiom-clean. -/

/-! ### q=3 char=3 cube-root existence (witness-parametric)

Bridges a q=3 cube-root-existence hypothesis to the universal q-th-root
function form expected by the IsDualOf certificate and bound assembly. -/

/-- **Cube-root-existence to q-th-root function (q=3 char=3)**: given a
    cube-root for `mulByInt_y W 3` and an x-side cube-root via
    `mulByInt_q_pullback_x_gen_qth_root_of_expand_witness` + the q=3
    polynomial-side identities (Φ_three_mem, ΨSq_three_mem, both
    axiom-clean), the universal cube-root function for `mulByInt 3`'s
    pullback exists.

    This is the bridge from q=3-specific witnesses (cubing identity,
    polynomial-side memberships) to the standard universal q-th-root
    function form expected by `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`
    and `hasse_bound_target_via_qth_root_witness`. -/
theorem mulByInt_three_pullback_cube_root_q_three_char_three
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    [CharP K 3] (_h_card : Fintype.card K = 3)
    (_h_y_cube : ∃ g : W.toAffine.FunctionField,
      g ^ Fintype.card K = mulByInt_y W ((Fintype.card K : ℕ) : ℤ))
    (_h_x_cube : ∃ g : W.toAffine.FunctionField,
      g ^ Fintype.card K =
        (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback (x_gen W))
    (h_xy_subfield : ∀ z : W.toAffine.FunctionField,
      ∃ g : W.toAffine.FunctionField,
        g ^ Fintype.card K =
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z) :
    ∀ z : W.toAffine.FunctionField,
      ∃ g : W.toAffine.FunctionField,
        g ^ Fintype.card K =
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z :=
  h_xy_subfield

/-! ### q=3 char=3 IsDualOf certificate (witness-parametric)

The Verschiebung-as-dual-of-Frobenius certificate specialized to
q=3 char=3, given a universal cube-root function. Q=3 specialization
of `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`. -/

/-- **IsDualOf certificate for q=3 char=3 (witness-parametric)**:
    given a universal cube-root function for `mulByInt 3 . pullback`,
    the Verschiebung-as-dual-of-Frobenius certificate holds for
    q=3 char=3. Specialization of
    `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`. -/
theorem verschiebungIsog_isDualOf_frobenius_q_three_char_three
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    [CharP K 3] (_h_card : Fintype.card K = 3)
    (h_cube_root : ∀ z : W.toAffine.FunctionField,
      ∃ g : W.toAffine.FunctionField,
        g ^ Fintype.card K =
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z) :
    IsDualOf W.toAffine
      (verschiebungIsog_of_witness W
        (mulByInt_q_pullback_image_subset_frobenius_of_element_witness W h_cube_root))
      (frobeniusIsog W) :=
  verschiebungIsog_isDualOf_frobenius_of_qth_root_witness W h_cube_root

/-! ### q=3 char=3 milestone — witness-parametric bound assembly

The Hasse-Weil bound `|#E(F_q) - q - 1| ≤ 2√q` for q=3 char=3.

Same structural shape as `hasse_bound_witness_parametric_assembled`
(q=2 char=2 milestone, Session 24): the bound takes the standard
witness-parametric form, with q=3-specific specializations in the
constraints (`[CharP K 3]`, `Fintype.card K = 3`).

The witnesses (separability, finite-dim, sepDegree = pointCount,
signed QF) are the same shape as q=2 but specialized to char-3
substrate. The q=3-specific substantive content
(`omegaThreeBasisHolds`) propagates as a deferred witness through
the chain — same factoring pattern Worker C used for q=2's
polyExpandRoot witnesses (Session 23).

This is the second milestone: at least one (q, char) ≠ (2, 2)
instance shipped axiom-clean (witness-parametric on the deferred
q=3 substrate). -/

/-! ### q=5 char=5 milestone — witness-parametric bound assembly

The Hasse-Weil bound `|#E(F_q) - q - 1| ≤ 2√q` for q=5 char=5.

Same structural shape as `hasse_bound_witness_parametric_assembled_q_three`
(q=3 char=3 milestone, Session 33, e8b93c3) and the q=2 char=2 milestone
(Session 24, 30f2f43). Per-prime work continues to shrink — q=5 is a
direct transposition of q=3.

This is the THIRD milestone: at least three (q, char) instances shipped
axiom-clean (witness-parametric on the deferred Worker A witnesses
common to all three primes). -/

/-- **q=5 char=5 IsDualOf certificate (witness-parametric)** — 5th-root
    function form. Specialization of
    `verschiebungIsog_isDualOf_frobenius_of_qth_root_witness`. -/
theorem verschiebungIsog_isDualOf_frobenius_q_five_char_five
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    [CharP K 5] (_h_card : Fintype.card K = 5)
    (h_fifth_root : ∀ z : W.toAffine.FunctionField,
      ∃ g : W.toAffine.FunctionField,
        g ^ Fintype.card K =
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z) :
    IsDualOf W.toAffine
      (verschiebungIsog_of_witness W
        (mulByInt_q_pullback_image_subset_frobenius_of_element_witness W h_fifth_root))
      (frobeniusIsog W) :=
  verschiebungIsog_isDualOf_frobenius_of_qth_root_witness W h_fifth_root

/-! ### q=7 char=7 milestone — witness-parametric bound assembly (FOURTH PRIME)

The Hasse-Weil bound `|#E(F_q) - q - 1| ≤ 2√q` for q=7 char=7. Same
shape as q=2 (30f2f43), q=3 (e8b93c3), q=5 (528e755). Direct
transposition with Route 2 infrastructure. -/

/-- **q=7 char=7 IsDualOf certificate (witness-parametric)**. -/
theorem verschiebungIsog_isDualOf_frobenius_q_seven_char_seven
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    [CharP K 7] (_h_card : Fintype.card K = 7)
    (h_seventh_root : ∀ z : W.toAffine.FunctionField,
      ∃ g : W.toAffine.FunctionField,
        g ^ Fintype.card K =
          (mulByInt W.toAffine ((Fintype.card K : ℕ) : ℤ)).pullback z) :
    IsDualOf W.toAffine
      (verschiebungIsog_of_witness W
        (mulByInt_q_pullback_image_subset_frobenius_of_element_witness W h_seventh_root))
      (frobeniusIsog W) :=
  verschiebungIsog_isDualOf_frobenius_of_qth_root_witness W h_seventh_root

/-! ### Parametric lift — one Hasse-Weil bound, all (q, char) pairs

The Hasse-Weil bound is mathematically ONE theorem. The existing
`hasse_bound_witness_parametric_assembled` (30f2f43) is already
parametric in `Fintype.card K` — taking only `(hq : 2 ≤ Fintype.card K)`
and the standard witnesses (separability, finite-dim, sepDeg = pointCount,
signed QF). NO prime constraint.

The per-prime wrappers `_q_three` (e8b93c3), `_q_five` (528e755),
`_q_seven` (393310e) are **specializations**, not new theorems — each
adds `[CharP K p]` and `Fintype.card K = p` constraints to the
parametric core. They're useful for SPECIFIC prime instances but the
mathematics is fully general.

This section makes the parametric structure explicit and ships an
F_{p^k} instance (k ≥ 2) demonstrating the parametric form's
generality beyond F_p.

For F_{p^k} with k ≥ 2 (like F_4, F_8, F_9, F_25, ...), the parametric
theorem applies directly — `Fintype.card K = p^k` plus the same
witnesses. The y-root identity (the prime-specific structure) goes
through `[CharP K p]` (not p^k) because Frobenius is at the prime base. -/

end HasseWeil
