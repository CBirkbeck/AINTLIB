import HasseWeil.DiscriminantBounds
import HasseWeil.Hasse.PointFix

/-!
# Witness-parametric Hasse bound

Top-level witness form of Silverman V.1.1 (the Hasse bound).

The existing `hasse_bound` in `HasseWeil/HasseBound.lean` has a residual
`sorry` on the QF non-negativity in `ℤ` (a true statement, deferred until
Silverman III.6.3 lands axiom-clean) and depends on `pointCount_eq`
(`HasseWeil/Frobenius.lean`, also `sorry`-ed). The witness-parametric
companions (`pointCount_eq_of_witness`, `degree_quadratic_nonneg_of_witness`,
the `_qf_nonneg` chain below) bypass both blockers. This file composes them
into `hasse_bound_of_t_witness`, which is axiom-hygienic and *conditionally*
proves the Hasse bound given:

1. an integer `t : ℤ` (the intended trace) such that
   `#E(F_q) = q + 1 − t`;
2. a family of endomorphism isogenies `β_qf r s` whose degrees realise the
   quadratic form `q·r² − t·r·s + s²` for every `r, s : ℤ`.

Both conditions are exactly what the III.5 / III.6 chain + V.1.1 setup produces
in Silverman; once those chains are fully formalised, the witnesses become
internally constructible and the unconditional `hasse_bound` falls out as a
special case.

## Main results

* `traceOfFrobenius_sq_le_of_witness` — the discriminant bound `t² ≤ 4q` given
  a family of quadratic-form degree witnesses.
* `hasse_bound_of_t_witness` — `|#E(F_q) − q − 1| ≤ 2√q` given both witness
  families.
* `hasse_bound_of_full_witnesses` — the same bound from the `1 − π` hom/kernel
  witness (trace computed internally) plus the quadratic-form witness family.
* `hasse_bound_of_all_witnesses` — the top-level plug-in form, gathering every
  upstream dependency (separable + finite-dim + fiber + QF witnesses) into one
  theorem whose hypotheses map one-to-one to the outstanding upstream tickets.

## References
* [Silverman, *The Arithmetic of Elliptic Curves*], V.1.1.
-/

open WeierstrassCurve Real

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-! ### Discriminant bound from a quadratic-form witness family -/

/-- **Discriminant bound, witness form**. Given an integer `t` and a family of
    endomorphism isogenies `β r s` whose degrees realise the binary quadratic
    form `q·r² − t·r·s + s²`, we have `t² ≤ 4q`.

    This is the witness-parametric companion of `traceOfFrobenius_sq_le`. The
    caller supplies the degree equalities (which unconditional III.6.3 would
    produce internally) and this lemma concludes the discriminant bound. -/
theorem traceOfFrobenius_sq_le_of_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic]
    (t : ℤ)
    (β : ℤ → ℤ → Isogeny W.toAffine W.toAffine)
    (h_deg : ∀ r s : ℤ, ((β r s).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 - t * r * s + s ^ 2) :
    t ^ 2 ≤ 4 * (Fintype.card K : ℤ) := by
  apply trace_sq_le_four_mul_deg _ _ Fintype.card_pos
  intro r s
  rw [← h_deg r s]
  exact Int.natCast_nonneg _

/-! ### Real-valued Hasse bound from both witnesses -/

/-- **Hasse's theorem, witness form.** Given the point-count witness `h_pc :
    #E(F_q) = q + 1 − t` and a quadratic-form witness family, we have
    `|#E(F_q) − q − 1| ≤ 2√q`.

    This is the witness-parametric companion of `hasse_bound`. Both witnesses
    are consequences of the III.5/III.6 chain + V.1.1 setup in Silverman; this
    theorem makes the top-level bound sorry-free conditional on those inputs. -/
theorem hasse_bound_of_t_witness
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (t : ℤ)
    (h_pc : (pointCount W.toAffine : ℤ) = Fintype.card K + 1 - t)
    (β : ℤ → ℤ → Isogeny W.toAffine W.toAffine)
    (h_deg : ∀ r s : ℤ, ((β r s).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 - t * r * s + s ^ 2) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * sqrt (Fintype.card K : ℝ) := by
  have htrace : (pointCount W.toAffine : ℤ) - ↑(Fintype.card K) - 1 = -t := by linarith
  have hpc_real : (↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ) = -(t : ℝ) := by
    exact_mod_cast congrArg ((↑) : ℤ → ℝ) htrace
  rw [hpc_real, abs_neg]
  exact abs_le_two_sqrt_of_sq_le _ _
    (traceOfFrobenius_sq_le_of_witness W t β h_deg)

/-! ### Fully-chained Hasse bound (hom + kernel + quadratic witnesses) -/

/-- **Fully-chained Hasse bound**. The Silverman V.1 chain in its most direct
    form: provide the witness isogeny `β_pc` for `1 − π` (with its point-map
    and separable-implies-#ker=deg witness) and the quadratic-form witness
    family. The trace `t` is computed internally as `isogTrace π β_pc`.

    This composes `pointCount_eq_of_hom_kernel_witness` (T-V-1-003 witness)
    with `hasse_bound_of_t_witness` to hand the caller a single lemma that
    mirrors the Silverman V.1 statement exactly. -/
theorem hasse_bound_of_full_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (β_pc : Isogeny W.toAffine W.toAffine)
    (h_pc_hom : β_pc.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    (h_pc_ker_deg : Nat.card β_pc.kernel = β_pc.degree)
    (β : ℤ → ℤ → Isogeny W.toAffine W.toAffine)
    (h_deg : ∀ r s : ℤ, ((β r s).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) β_pc * r * s + s ^ 2) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * sqrt (Fintype.card K : ℝ) :=
  hasse_bound_of_t_witness W (isogTrace (frobeniusIsog W) β_pc)
    (pointCount_eq_of_hom_kernel_witness W β_pc h_pc_hom h_pc_ker_deg) β h_deg

/-! ### Consolidated upstream-parametric Hasse bound

`hasse_bound_of_all_witnesses` below gathers every upstream dependency of the
Silverman V.1 chain into a single theorem whose hypotheses map one-to-one to
the outstanding stream-A / stream-C / stream-D tickets. Once any of those
tickets lands, the corresponding witness is dischargeable and the bound
specialises to unconditional at the call site.

**Witness-to-ticket map**:

| Hypothesis | Silverman | Ticket | Stream |
|------------|-----------|--------|--------|
| `β_pc` + `h_pc_hom` | V.1.1 (E(F_q) = ker(1−π)) | T-V-1-001 | V (done) |
| `h_pc_sep` | V.1.2 (1 − π separable) | T-V-1-002 / III.5.5 | C / E |
| `h_pc_fin` | III.4 finite-dim | T-III-4-001 derived | C (structural) |
| `h_pc_fiber_witness` | III.4.10(a) (#fiber = deg_s) | T-III-4-012 | C ← A (T-II-2-009) |
| `[Finite β_pc.kernel]` | III.4.9 (ker finite) | T-III-4-011 | C ← A (T-II-2-002) |
| `β_qf` + `h_qf_deg` | III.6.3 (deg is pos-def QF) | T-III-6-009 | C ← D (BRIDGE-003) |

The first five combine to give `#ker β_pc = β_pc.degree` via
`Isogeny.card_kernel_eq_degree_of_separable_witness` (T-III-4-015 witness
form); the last pair supplies the discriminant input for the Cauchy-Schwarz
step. -/

/-- **Consolidated Hasse bound from upstream witnesses** (single parametric
    form of Silverman V.1.1).

    This is the top-level "plug-in" theorem: each hypothesis is labelled with
    its Silverman reference and outstanding upstream ticket (see the section
    docstring above). When stream-A lands T-II-2-002/008/009, the separable
    chain discharges; when stream-D lands T-IV-BRIDGE-003, the deg-QF witness
    family discharges. Until then, the unconditional `hasse_bound` in
    `HasseWeil/HasseBound.lean` is the only piece still guarded by the two
    infrastructure sorries.

    The intermediate `h_pc_ker_deg` is derived internally from the separable
    + finite-dim + fiber witnesses via T-III-4-015. -/
theorem hasse_bound_of_all_witnesses
    (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    -- [V.1.1 / T-V-1-001] the `1 − π` isogeny at the point-map level
    (β_pc : Isogeny W.toAffine W.toAffine)
    (h_pc_hom : β_pc.toAddMonoidHom =
      (AddMonoidHom.id _) - (frobeniusIsog W).toAddMonoidHom)
    -- [V.1.2 / T-V-1-002, III.5.5 / T-III-5-005] `1 − π` is separable
    (h_pc_sep : β_pc.IsSeparable)
    -- [structural] the function-field extension is finite-dimensional
    (h_pc_fin : @FiniteDimensional W.toAffine.FunctionField
      W.toAffine.FunctionField _ _ β_pc.toAlgebra.toModule)
    -- [III.4.10(a) / T-III-4-012] witness: one fiber has cardinality = sepDeg
    (h_pc_fiber_witness : ∃ P₀ : W.toAffine.Point,
      Nat.card {P : W.toAffine.Point //
          β_pc.toAddMonoidHom P = β_pc.toAddMonoidHom P₀} =
        β_pc.sepDegree)
    -- [III.4.9 / T-III-4-011] the kernel is finite
    [h_pc_ker_finite : Finite β_pc.kernel]
    -- [III.6.3 / T-III-6-009] degree QF witness family
    (β_qf : ℤ → ℤ → Isogeny W.toAffine W.toAffine)
    (h_qf_deg : ∀ r s : ℤ, ((β_qf r s).degree : ℤ) =
      (Fintype.card K : ℤ) * r ^ 2 -
        isogTrace (frobeniusIsog W) β_pc * r * s + s ^ 2) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * sqrt (Fintype.card K : ℝ) :=
  hasse_bound_of_full_witnesses W β_pc h_pc_hom
    (Isogeny.card_kernel_eq_degree_of_separable_witness β_pc h_pc_sep
      h_pc_fin h_pc_fiber_witness)
    β_qf h_qf_deg

end HasseWeil
