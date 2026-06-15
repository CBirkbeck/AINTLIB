import HasseWeil.AdditionPullback.Frobenius
import HasseWeil.Hasse.Separability
import HasseWeil.Hasse.PointFix

/-!
# Witness assemblers for `isogOneSub_negFrobenius`

Per-isogeny specialisations of the generic witness-parametric chain, anchored
on the genuine `isogOneSub_negFrobenius W hq` (real pullback, axiom-clean from
`AdditionPullback/Frobenius.lean`).

* **Witness #1** — separability `(isogOneSub_negFrobenius W hq).IsSeparable`
  from the omega-pullback coefficient + the differential separability
  criterion (Silverman III.5.5 / T-II-4-004).
* **Witness #3** — `(isogOneSub_negFrobenius W hq).sepDegree = pointCount`
  from Witness #1, Witness #2 (finite-dim, axiom-clean already), the fiber
  witness, and the finite-kernel instance.

(Witness #2 — `FiniteDimensional` of the algebra structure — is shipped
axiom-clean as `isogOneSub_negFrobenius_finiteDimensional` in
`AdditionPullback/Differential.lean`; the placeholder analogue lives in
`Hasse/Unconditional.lean`.)

These specialisations are the inputs the `HasseWitnesses` record
(`Hasse/Witnesses.lean`) was designed to accept — once Worker A's
`omegaPullbackCoeff = 1` proof and Worker C's fiber witness land,
constructing a `HasseWitnesses W hq` is a one-line wiring of the witnesses
through these helpers into the bound consumer in `Hasse/Final.lean`.
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ### Witness #1: Separability of `isogOneSub_negFrobenius` (specialized)

Specializes `oneSubFrobenius_isSeparable_of_witness` from
`HasseWeil/Hasse/Separability.lean` to `β = isogOneSub_negFrobenius W hq`. -/

/-- **Witness #1**: separability of `isogOneSub_negFrobenius W hq`,
specialized from the witness-parametric V.1.2 form.

Takes:
* `h_coeff : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1`
  — the V.1.2 input (Silverman III.5.5 at `m = 1, n = -1`, plus the
    addition-pullback's effect on ω).
* `h_sep_iff : β.IsSeparable ↔ omegaPullbackCoeff W β ≠ 0`
  — the T-II-4-004 differential criterion specialized to this β.

Concludes `(isogOneSub_negFrobenius W hq).IsSeparable`. -/
theorem isogOneSub_negFrobenius_isSeparable_of_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (hq : 2 ≤ Fintype.card K)
    (h_coeff : omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) = 1)
    (h_sep_iff : (isogOneSub_negFrobenius W hq).IsSeparable ↔
      omegaPullbackCoeff W (isogOneSub_negFrobenius W hq) ≠ 0) :
    (isogOneSub_negFrobenius W hq).IsSeparable :=
  oneSubFrobenius_isSeparable_of_witness W
    (isogOneSub_negFrobenius W hq) h_coeff h_sep_iff

/-! ### Witness #3: `sepDegree = pointCount` (specialized + composed)

Composes:
* `isSeparable_iff_sepDegree_eq_degree` (`sepDegree = degree` from
  separability + finite-dim) — `IsogenyKernel.lean:323`.
* `kernel_eq_top_of_hom_eq_id_sub_frobenius` + `card_top` — `degree = pointCount`
  for any β with the right rational-point shape (PointFix.lean:88).
* `Isogeny.card_kernel_eq_degree_of_separable_witness` — T-III-4-015
  witness form (IsogenyKernel.lean:381). -/

/-- **Witness #3**: `(isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine`,
in witness-parametric form.

Takes Witness #1 (separability), Witness #2 (finite-dim of the algebra
structure), the T-III-4-012 fiber witness (one fiber has cardinality =
sepDegree), and a `Finite` instance for the kernel. Concludes the
sepDegree-pointCount identity needed by HOLE D. -/
theorem isogOneSub_negFrobenius_sepDegree_eq_pointCount_of_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (hq : 2 ≤ Fintype.card K)
    (h_pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable)
    (h_pc_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _
      (isogOneSub_negFrobenius W hq).toAlgebra.toModule)
    (h_pc_fiber_witness : ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          (isogOneSub_negFrobenius W hq).toAddMonoidHom P =
            (isogOneSub_negFrobenius W hq).toAddMonoidHom P₀} =
        (isogOneSub_negFrobenius W hq).sepDegree)
    [Finite (isogOneSub_negFrobenius W hq).kernel] :
    (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine := by
  -- `sepDegree = degree` from separability + finite-dim.
  have h_sd_eq_deg : (isogOneSub_negFrobenius W hq).sepDegree =
      (isogOneSub_negFrobenius W hq).degree :=
    (Isogeny.isSeparable_iff_sepDegree_eq_degree _ h_pc_fin).mp h_pc_sep
  -- `#ker = degree` from T-III-4-015 witness form.
  have h_ker_eq_deg : Nat.card (isogOneSub_negFrobenius W hq).kernel =
      (isogOneSub_negFrobenius W hq).degree :=
    Isogeny.card_kernel_eq_degree_of_separable_witness _ h_pc_sep h_pc_fin
      h_pc_fiber_witness
  -- `#ker = pointCount` from the rational-point shape (Piece C: rfl).
  have h_ker_eq_pc : Nat.card (isogOneSub_negFrobenius W hq).kernel =
      pointCount W.toAffine := by
    rw [kernel_eq_top_of_hom_eq_id_sub_frobenius W
      (isogOneSub_negFrobenius W hq) rfl, AddSubgroup.card_top]
    exact Nat.card_eq_fintype_card
  -- Compose: sepDegree = degree = #ker = pointCount.
  rw [h_sd_eq_deg, ← h_ker_eq_deg, h_ker_eq_pc]

end HasseWeil
