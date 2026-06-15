# T-IV-3-002: F(M^n) subgroups

**Status**: DONE
**Silverman**: IV.3 (definition)
**Module**: `HasseWeil/FormalGroup/Associated.lean`
**Owner**: (claimed 2026-04-20)
**Estimated lines**: 30 (delivered ~115)
**Difficulty**: easy
**Stream**: D

## Depends on
- T-IV-3-001 (F(M)) — DONE

## Blocks
- T-IV-3-006 (F(M^n)/F(M^{n+1}) ≅ M^n/M^{n+1}) — now unblocked

## Statement (Silverman IV.3 def)
For each `n : ℕ`, the set `M^n ⊆ M` is closed under the formal group operation
`+_F` and negation `-_F`, forming a subgroup of `F(M)`. This yields a decreasing
filtration `F(M) ⊇ F(M²) ⊇ F(M³) ⊇ …`.

(Silverman's original definition starts at `n = 1`, but with the subtype setup
here `M^0 = R` and `M^1 = M` both give the whole group, so indexing from
`n = 0` is harmless.)

## Acceptance criteria (DONE)

```lean
namespace HasseWeil.FormalGroup

/-- Helper: each `M^n` is closed in the M-adic topology. -/
lemma maximalIdeal_pow_isClosed (hAdic : IsAdic (maximalIdeal R)) (n : ℕ) :
    IsClosed (((maximalIdeal R) ^ n : Ideal R) : Set R)

/-- Closure of +_F on M^n. -/
theorem FormalGroup.evalAdd_pow_mem
    (hAdic : IsAdic (maximalIdeal R)) (F : FormalGroup R) (n : ℕ)
    {x y : maximalIdeal R} (hx : x.1 ∈ (maximalIdeal R) ^ n)
    (hy : y.1 ∈ (maximalIdeal R) ^ n) :
    F.evalAdd x y ∈ (maximalIdeal R) ^ n

/-- Closure of -_F on M^n. -/
theorem FormalGroup.evalNeg_pow_mem
    (hAdic : IsAdic (maximalIdeal R)) (F : FormalGroup R) (n : ℕ)
    {x : maximalIdeal R} (hx : x.1 ∈ (maximalIdeal R) ^ n) :
    F.evalNeg x ∈ (maximalIdeal R) ^ n

/-- F(M^n) as a subgroup of F(M). -/
noncomputable def FormalGroup.evalGroup_powerIdeal
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) (n : ℕ) :
    letI := F.evalGroup hAdic
    AddSubgroup (maximalIdeal R)

/-- The filtration is monotone: m ≤ n ⇒ F(M^n) ≤ F(M^m). -/
theorem FormalGroup.evalGroup_powerIdeal_mono
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) {m n : ℕ} (hmn : m ≤ n) :
    letI := F.evalGroup hAdic
    F.evalGroup_powerIdeal hAdic n ≤ F.evalGroup_powerIdeal hAdic m

end HasseWeil.FormalGroup
```

## Notes
- Proof of closure: each term `coeff d F.toSeries * ∏ (![x,y] s)^(d s)` of the
  `hasSum` decomposition is in `M^n`:
  * `d = 0` → `coeff 0 F.toSeries = 0`;
  * `d ≠ 0` → pick `s` with `d s ≥ 1`, then `(![x,y] s)^(d s) ∈ M^n` by
    `Ideal.pow_mem_of_mem`, so the whole product lies in `M^n` (ideal
    absorption).
  The sum then lies in the closed set `M^n` via
  `IsClosed.mem_of_tendsto`.
- Similar argument for `evalNeg`, via `PowerSeries.eval₂` of `F.inverse`.
- Axiom-clean: `propext, Classical.choice, Quot.sound` only.

## Progress log

- 2026-04-20 Delivered `maximalIdeal_pow_isClosed`, `evalAdd_pow_mem`,
  `evalNeg_pow_mem`, `evalGroup_powerIdeal`, `evalGroup_powerIdeal_mono`
  in `HasseWeil/FormalGroup/Associated.lean` (~115 lines added). Axiom-clean.
  Full build passes (2845/2845).
