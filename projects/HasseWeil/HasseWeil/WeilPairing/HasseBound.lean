/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.WeilPairing.PencilComapWitnesses
import HasseWeil.WeilPairing.FrobeniusGaloisScaling
import HasseWeil.WeilPairing.OneSubProjOrdTransport
import HasseWeil.WeilPairing.FrobMatrixData

/-!
# The unconditional Hasse bound `|#E(𝔽_q) − q − 1| ≤ 2√q`

This is the capstone: it discharges the single geometric leaf `FrobBaseChangeScalingsCoprime` of
`hasse_bound_unconditional_of_baseChange_scalings_coprime` (`FrobMatrixData.lean`) by the three
per-isogeny base-change Weil-pairing scalings now built over `K̄ = AlgebraicClosure K`:

* `frobeniusScaling_holds` (leaf 1, Frobenius `π`) — axiom-clean;
* `oneSubFrobeniusScaling_holds` (leaf 2, `1 − π`) — axiom-clean;
* `pencilScaling_holds_coprime` (leaf 3, `rπ − s` on `p ∤ r' ∧ p ∤ s'`) — axiom-clean, with the
  kernel-cardinality exponent `pencilKerCard`.

The **coprime-BOTH** route (reviewer round-23, Route B) requests the pencil scaling only on the
genuine locus `p ∤ r' ∧ p ∤ s'` — exactly where `rπ − s` is genuine — so the inseparable `p ∣ r'`
geometric input is never demanded.  The resulting Hasse bound is **axiom-clean** (no `sorryAx`).

The exponent `deg` of `hasse_bound_unconditional_of_baseChange_scalings` is fixed **before** the
`∀ p r` quantifier; we pick the canonical `(p₀, n₀)` of `FiniteField.card' K` for it, and inside the
per-`(p, r)` `hscale` discharge we force `p = p₀` (`CharP` uniqueness) and `r = n₀`
(`Nat.pow_right_injective` on `#K = p₀^r = p₀^n₀`) so that the carried exponent
`pencilKerCard W p r (pencilJunkPullback W)` matches.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, V.1.1 (the Hasse bound), III.8.6 (the Weil-pairing
  symplectic scaling).
-/

open WeierstrassCurve HasseWeil.Curves

namespace HasseWeil.WeilPairing

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]

noncomputable local instance : DecidableEq (AlgebraicClosure K) := Classical.decEq _

set_option maxHeartbeats 2000000

/-- **The unconditional Hasse bound** (Silverman V.1.1): for an elliptic curve `E` over a finite field
`𝔽_q`, `|#E(𝔽_q) − q − 1| ≤ 2√q`, with **no hypotheses** beyond `2 ≤ #K`.

Assembled from `hasse_bound_unconditional_of_baseChange_scalings_coprime` (`FrobMatrixData.lean`) with
the kernel-cardinality degree function `pencilKerCard` and the three base-change scalings
`frobeniusScaling_holds`, `oneSubFrobeniusScaling_holds`, `pencilScaling_holds_coprime`.

Instance bookkeeping: `deg` is fixed before `∀ p r`, so it is taken at the canonical `(p₀, n₀)` of
`FiniteField.card' K`; inside the `hscale` discharge `p = p₀` (`CharP.eq`) and `r = n₀`
(`Nat.pow_right_injective`) are forced. -/
theorem hasse_bound_unconditional (hq : 2 ≤ Fintype.card K) :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) := by
  -- The canonical characteristic / exponent of `K`, used to fix the degree function `deg`.
  obtain ⟨p₀, hCharP₀, n₀, hp₀_prime, hcard₀⟩ := FiniteField.card' K
  haveI : Fact p₀.Prime := ⟨hp₀_prime⟩
  haveI : CharP K p₀ := hCharP₀
  haveI : Fact (Fintype.card K = p₀ ^ (n₀ : ℕ)) := ⟨hcard₀⟩
  -- The degree function, at the canonical `(p₀, n₀)`.  Kept as a local definition so the heavy
  -- `Nat.card (… .ker)` underneath `pencilKerCard` is never whnf-reduced during unification.
  set deg₀ : ℤ → ℤ → ℤ := pencilKerCard W p₀ (n₀ : ℕ) (pencilJunkPullback W) with hdeg₀
  refine hasse_bound_unconditional_of_baseChange_scalings_coprime W hq deg₀
    (fun r' s' ↦ hdeg₀ ▸ pencilKerCard_nonneg W p₀ (n₀ : ℕ) (pencilJunkPullback W) r' s')
    (fun p r hp hcp hcard ↦ ?_)
  -- Discharge `FrobBaseChangeScalingsCoprime` for an arbitrary `(p, r)`, forcing `p = p₀`, `r = n₀`
  -- (`obtain rfl` eliminates the RHS canonical vars, keeping the quantified `p`, `r`).
  obtain rfl : p = p₀ := CharP.eq K hcp hCharP₀
  obtain rfl : r = (n₀ : ℕ) := by
    have hpow : p ^ r = p ^ (n₀ : ℕ) := by rw [← hcard.out, hcard₀]
    exact Nat.pow_right_injective hp₀_prime.two_le hpow
  refine ⟨frobeniusScaling_holds W p (n₀ : ℕ), oneSubFrobeniusScaling_holds W p (n₀ : ℕ) hq, ?_⟩
  rw [hdeg₀]
  exact pencilScaling_holds_coprime W p (n₀ : ℕ)

/-- **The Hasse bound, hypothesis-free capstone** (Silverman V.1.1):
`|#E(𝔽_q) − q − 1| ≤ 2√q` with no explicit cardinality hypothesis — `2 ≤ #K` is
automatic for a finite field (`Fintype.one_lt_card`).  This is the hypothesis-free
form that replaced the retired `hasse_bound_universal` stub
(`Hasse/OpenLemmaPrimitives.lean`, deleted 2026-06-11). -/
theorem hasse_bound :
    |(↑(pointCount W.toAffine) - ↑(Fintype.card K) - 1 : ℝ)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) :=
  hasse_bound_unconditional W (Nat.succ_le_of_lt Fintype.one_lt_card)

end HasseWeil.WeilPairing
