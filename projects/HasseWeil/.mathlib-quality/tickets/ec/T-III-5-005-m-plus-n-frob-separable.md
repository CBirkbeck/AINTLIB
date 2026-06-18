# T-III-5-005: m + nπ separable ⇔ p ∤ m

**Status**: PARTIAL (witness-parametric form landed)
**Silverman**: III.5.5
**Module**: `HasseWeil/Hasse/Separability.lean` (witness form); target
`HasseWeil/EC/InvariantDiff.lean` (unconditional form)
**Owner**: (unassigned)
**Estimated lines**: 60
**Difficulty**: medium (CRITICAL)
**Stream**: B/E

## Depends on
- T-III-5-002 (additivity)
- T-III-5-003 ([m]*ω = m·ω)
- T-II-2-014 (Frobenius purely inseparable)

## Blocks
- T-V-1-002 (1 - π separable)
- T-V-1-006 (Hasse bound)

## Statement (Silverman III.5.5)
Let `E/F_q` be an elliptic curve with Frobenius `π : E → E` and characteristic
`p`. For `m, n ∈ ℤ`, the isogeny `[m] + [n] ∘ π` is separable iff `p ∤ m`.

## Acceptance criteria

```lean
namespace HasseWeil.EC

/-- m + n·π separable iff p does not divide m.
    Reference: Silverman III.5.5. -/
theorem WeierstrassCurve.mul_plus_n_frob_isSeparable_iff
    (E : WeierstrassCurve (ZMod p)) [Fact p.Prime] [Fact (E.Δ ≠ 0)]
    (m n : ℤ) (π : Isogeny E E) (hπ : π = E.frobeniusIsogeny) :
    (E.mulByInt m + (E.mulByInt n).comp π).IsSeparable ↔ ¬ (p : ℤ) ∣ m

end HasseWeil.EC
```

## Notes
- Compute `(m + nπ)* ω = m·ω + n·(π*ω)`. Since `π` is purely inseparable
  (T-II-2-014), `π* ω = 0` (by T-II-4-004 contrapositive). So
  `(m + nπ)* ω = m·ω`, which is nonzero iff `m ≠ 0` in `K = F_q`, iff `p ∤ m`.
- Setting `m = 1, n = -1` gives that `1 - π` is separable, which is the key
  fact for counting `#E(F_q)`.

## Progress log
- 2026-04-20 [auto] Witness-parametric form landed at
  `HasseWeil/Hasse/Separability.lean`:
  `m_plus_n_frob_isSeparable_iff_of_witness` (and the more general
  `isSeparable_iff_of_coeff_witness`). Both are axiom-hygienic
  (`propext, Classical.choice, Quot.sound` only). Takes the ω-pullback
  coefficient `= algebraMap K _ m` and the T-II-4-004 criterion
  (`separable ↔ coefficient ≠ 0`) as hypotheses, concludes
  `β.IsSeparable ↔ (m : K) ≠ 0`. The unconditional form remains open
  pending T-III-5-002 (additivity), T-III-5-003 (scalar), and T-II-4-004.
