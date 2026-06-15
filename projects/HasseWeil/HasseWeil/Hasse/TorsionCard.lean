import HasseWeil.EC.IsogenyKernel

/-!
# Cardinality of `E[m]` from the separable-kernel-degree witness (T-III-6-010)

Silverman III.6.4(a): for an elliptic curve `E` and `m : ℤ` with `m` invertible
in `K` (i.e., `m ≠ 0` in `K`), the `m`-torsion subgroup satisfies
`#E[m] = m²`.

In our Lean encoding `W.toAffine[m] = (mulByInt W.toAffine m).kernel`
(definitionally), and `(mulByInt W.toAffine m).degree = (m²).toNat = m.natAbs²`
is already proved unconditionally by `mulByInt_degree` for `m ≠ 0 : ℤ`. The
only missing piece is `#ker [m] = deg [m]`, which is the T-III-4-015 content
(separable ⇒ `#ker = deg`) applied to `[m]`.

This file closes T-III-6-010 in witness-parametric form: the caller supplies
`h_ker_deg : Nat.card (mulByInt W.toAffine m).kernel =
(mulByInt W.toAffine m).degree`, and the cardinality formula falls out.

## Main results

* `torsionSubgroup_card_of_witness` — `#E[m] = m.natAbs²` from the
  kernel-degree witness.

## References
* [Silverman, *The Arithmetic of Elliptic Curves*], III.6.4(a).
-/

open WeierstrassCurve

namespace HasseWeil

variable {F : Type*} [Field F] [DecidableEq F]
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]

/-- **Witness-parametric Silverman III.6.4(a)**: if `#ker [m] = deg [m]`
    (which follows from T-III-4-015 applied to `[m]`, itself true for `m ≠ 0`
    in `K` via T-III-5-004), then `#E[m] = m.natAbs²`.

    Combined with T-III-5-004 + T-III-4-015, this gives the unconditional
    `#E[m] = m²` in the invertible case. -/
theorem torsionSubgroup_card_of_witness
    (m : ℤ) (hm : m ≠ 0)
    (h_ker_deg : Nat.card (mulByInt W.toAffine m).kernel =
      (mulByInt W.toAffine m).degree) :
    (Nat.card W.toAffine[m] : ℤ) = m ^ 2 := by
  have h1 : Nat.card W.toAffine[m] = (mulByInt W.toAffine m).degree := h_ker_deg
  rw [h1, mulByInt_degree W.toAffine m hm]
  exact Int.toNat_of_nonneg (sq_nonneg _)

/-- **Decomposed witness form** (using fiber-theory): given [m] separable,
    finite kernel, fiber witness → `#E[m] = m²`. Combines
    `Isogeny.card_kernel_eq_degree_of_separable_witness` with the degree formula. -/
theorem torsionSubgroup_card_of_separable_witness
    (m : ℤ) (hm : m ≠ 0)
    [h_ker_finite : Finite (mulByInt W.toAffine m).kernel]
    (h_sep : (mulByInt W.toAffine m).IsSeparable)
    (h_fin_dim : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
      _ _ (mulByInt W.toAffine m).toAlgebra.toModule)
    (h_fiber_witness : ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          (mulByInt W.toAffine m).toAddMonoidHom P =
            (mulByInt W.toAffine m).toAddMonoidHom P₀} =
        (mulByInt W.toAffine m).sepDegree) :
    (Nat.card W.toAffine[m] : ℤ) = m ^ 2 :=
  torsionSubgroup_card_of_witness W m hm
    (Isogeny.card_kernel_eq_degree_of_separable_witness
      (mulByInt W.toAffine m) h_sep h_fin_dim h_fiber_witness)

end HasseWeil
