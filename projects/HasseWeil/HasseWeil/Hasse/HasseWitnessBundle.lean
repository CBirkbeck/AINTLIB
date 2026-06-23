import HasseWeil.AdditionPullback.Frobenius
import HasseWeil.Frobenius
import HasseWeil.EC.IsogenyKernel

/-!
# Bundled witnesses for the Hasse bound

`HasseWitnesses W hq` packages every deferred input the Hasse bound needs into
a single record. Once each field is dischargeable (when Worker A's separability
chain, Worker C's fiber witness, and the III.6.3 QF non-negativity all land
axiom-clean), the bound becomes unconditional via the canonical consumer in
`Hasse/Final.lean`.

The fields are scoped to the *genuine* `1 − π` isogeny `isogOneSub_negFrobenius
W hq` (`HasseWeil/AdditionPullback/Frobenius.lean`) — never the placeholder
`oneSubFrobeniusIsog W`. See `.mathlib-quality/isogeny-compatibility-audit.md`
for why the placeholder cannot be wired through the bound.

## Witness-to-stream mapping

| Field | Silverman | Stream |
|-------|-----------|--------|
| `pc_sep` | V.1.2 / III.5.5 | A (ω(γ) = 1 chain) |
| `pc_fin` | III.4 finite-dim | A (`isogOneSub_negFrobenius_finiteDimensional`, axiom-clean) |
| `pc_fiber_witness` | III.4.10(a) / T-III-4-012 | C (translation / fixed-field) |
| `qf_nonneg` | III.6.3 | A (T-FROBENIUS-VERSCHIEBUNG-QF) |
-/

open WeierstrassCurve

namespace HasseWeil

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

/-- **Bundled witnesses sufficient for the Hasse bound** for an elliptic curve
`W/F_q`. Each field is a deferred input that an upstream stream owns; together
they drive `hasse_bound_of_witnesses` (`Hasse/Final.lean`).

The shape is anchored on the genuine `isogOneSub_negFrobenius W hq`, so each
field is provable in principle (no placeholder structures). -/
structure HasseWitnesses (hq : 2 ≤ Fintype.card K) where
  /-- **Witness #1 (V.1.2 / III.5.5)** — `1 − π` is separable. Driven by
  Worker A's ω(γ) = 1 chain. -/
  pc_sep : (isogOneSub_negFrobenius W hq).IsSeparable
  /-- **Witness #2 (III.4 finite-dim)** — `K(E)` is finite-dimensional over
  itself via the `(1 − π)*` algebra structure. Already axiom-clean via
  `isogOneSub_negFrobenius_finiteDimensional`
  (`AdditionPullback/Differential.lean`); included as a field so the record
  is self-contained. -/
  pc_fin : @FiniteDimensional W.toAffine.FunctionField W.toAffine.FunctionField
    _ _ (isogOneSub_negFrobenius W hq).toAlgebra.toModule
  /-- **Witness #3 (V.1.3 / Silverman III.4.10(c) for `1 − π`)** —
  `sepDegree(1 − π) = #E(F_q)`. Equivalently, the F_q-rational kernel of
  `1 − π` (which equals `E(F_q)`) has cardinality matching the separable
  degree.

  **Reframing note (2026-05-08, R1)**: this field replaces the previous
  F_q-rational fiber-witness shape
  `∃ P₀ : W.toAffine.Point, fiber.card = sepDegree`. The previous shape was
  circular for the bound chain at `β = 1 − π` because:
  * `β.toAddMonoidHom = id − π = 0` on F_q-rational points, so every fiber
    `{P : β(P) = β(P₀)}` reduces to `W.toAffine.Point = E(F_q)`;
  * The witness `fiber.card = sepDegree` is then equivalent to
    `pointCount = sepDegree`, i.e. V.1.3 itself.

  Stating V.1.3 directly makes the dependency honest (Anti-drift gate 4):
  this field IS the substantive Hasse content the bound chain consumes.

  **Discharge route** (geometric, non-circular): the shipped Curves-track
  primitives `CurveMap.exists_heightOneSpectrum_fiber_card_eq_sepDegree_unconditional`
  (T-II-2-009 over `[IsAlgClosed F]`) and `Isogeny.fiber_card_eq_sepDegree_of_witness`
  (translation bootstrap) deliver the geometric form
  `∃ P₀ ∈ E(F̄_q), fiber.card = sepDegree`. Combined with the kernel-coincidence
  identity for `1 − π` — `ker(1 − π) on E(F̄_q) = E(F_q)` (since `π` fixes a
  point iff it is F_q-rational) — the geometric fiber over `O` collapses to
  `E(F_q)`, yielding V.1.3 unconditionally. The base-change machinery for
  this discharge is the open follow-on. -/
  pc_sepDeg_eq_pointCount :
    (isogOneSub_negFrobenius W hq).sepDegree = pointCount W.toAffine
  /-- **QF non-negativity (III.6.3)** — the binary quadratic form
  `q·r² − tr·r·s + s²` (with `tr = isogTrace π (1 − π)`) is non-negative for
  all integers `r, s`. Driven by Worker A's `T-FROBENIUS-VERSCHIEBUNG-QF`. -/
  qf_nonneg : ∀ r s : ℤ,
    0 ≤ (Fintype.card K : ℤ) * r ^ 2 -
      isogTrace (frobeniusIsog W) (isogOneSub_negFrobenius W hq) *
        r * s + s ^ 2

end HasseWeil
