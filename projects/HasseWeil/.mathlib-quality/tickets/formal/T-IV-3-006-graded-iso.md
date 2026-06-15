# T-IV-3-006: F(M^n)/F(M^{n+1}) ≅ M^n/M^{n+1}

**Status**: DONE (core congruence + forward AddMonoidHom + kernel/range + first-iso packaged equivalence all delivered)
**Silverman**: IV.3.2(a)
**Module**: `HasseWeil/FormalGroup/Associated.lean`
**Owner**: worker-I
**Estimated lines**: 60 (delivered ~280: 196 for Part A + ~80 for Part B)
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-3-002 (F(M^n) subgroups) — DONE

## Blocks
- T-IV-3-007 (torsion p-power)
- T-IV-6-001 (DVR torsion)

## Statement (Silverman IV.3.2(a))
The natural map `F(M^n)/F(M^{n+1}) → M^n/M^{n+1}` (sending `[x] ↦ [x]`) is an
isomorphism of additive groups.

## Acceptance criteria

### Part A (DONE 2026-04-20) — core congruence lemmas

The mathematical heart is the fact `F(x, y) ≡ x + y (mod M^(n+1))` on `M^n`,
plus its negation analogue:

```lean
theorem FormalGroup.evalAdd_sub_add_mem_pow_succ
    (hAdic : IsAdic (maximalIdeal R)) (F : FormalGroup R)
    {n : ℕ} (hn : 1 ≤ n) {x y : maximalIdeal R}
    (hx : x.1 ∈ (maximalIdeal R) ^ n) (hy : y.1 ∈ (maximalIdeal R) ^ n) :
    F.evalAdd x y - (x.1 + y.1) ∈ (maximalIdeal R) ^ (n + 1)

theorem FormalGroup.evalNeg_add_mem_pow_succ
    (hAdic : IsAdic (maximalIdeal R)) (F : FormalGroup R)
    {n : ℕ} (hn : 1 ≤ n) {x : maximalIdeal R}
    (hx : x.1 ∈ (maximalIdeal R) ^ n) :
    F.evalNeg x + x.1 ∈ (maximalIdeal R) ^ (n + 1)
```

Proof strategy used:

* Decompose `eval₂ id ![x, y] F.toSeries` via `MvPowerSeries.hasSum_eval₂` into a
  sum indexed by `d : Fin 2 →₀ ℕ`.
* Isolate the low-degree finset `S = {0, single 0 1, single 1 1}`; on this set the
  sum equals `0 + x + y = x + y` (using `constantCoeff_FG_toSeries`,
  `FormalGroup.coeff_10`, `FormalGroup.coeff_01`).
* For `d ∉ S`, i.e., `d 0 + d 1 ≥ 2`: each term lies in `M^(n·(d 0 + d 1)) ⊆
  M^(2n) ⊆ M^(n+1)` since `n ≥ 1`.
* Shift the `Tendsto` by `-(x + y)` and apply `IsClosed.mem_of_tendsto` with
  `filter_upwards [Filter.eventually_ge_atTop S]`.

Supporting private helpers also added:

* `lowDegFinset : Finset (Fin 2 →₀ ℕ)` and `lowDegFinset_mem_iff`
* `single_zero_one_ne_zero`, `single_one_one_ne_zero`, `single_zero_ne_single_one`
* `two_le_sum_of_not_mem_lowDeg`

Axiom-clean: `propext, Classical.choice, Quot.sound` only.

### Part B (DONE 2026-04-20) — forward map + kernel/range + packaged quot ≃+ range

```lean
namespace HasseWeil.FormalGroup

/-- The forward map F(M^n) → R / M^(n+1). -/
noncomputable def FormalGroup.evalGroup_powerIdeal_toQuot
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) {n : ℕ} (hn : 1 ≤ n) :
    letI := F.evalGroup hAdic
    (F.evalGroup_powerIdeal hAdic n) →+ (R ⧸ (maximalIdeal R) ^ (n + 1))

/-- Its kernel is F(M^(n+1)) (embedded into F(M^n) via `addSubgroupOf`). -/
theorem FormalGroup.evalGroup_powerIdeal_toQuot_ker
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) {n : ℕ} (hn : 1 ≤ n) :
    letI := F.evalGroup hAdic
    (F.evalGroup_powerIdeal_toQuot hAdic hn).ker =
      (F.evalGroup_powerIdeal hAdic (n + 1)).addSubgroupOf (F.evalGroup_powerIdeal hAdic n)

/-- Its range is `Ideal.map (Quotient.mk M^(n+1)) M^n` — i.e., `M^n / M^(n+1)`
realised inside `R / M^(n+1)`. -/
theorem FormalGroup.evalGroup_powerIdeal_toQuot_range
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) {n : ℕ} (hn : 1 ≤ n) :
    letI := F.evalGroup hAdic
    (F.evalGroup_powerIdeal_toQuot hAdic hn).range =
      (Ideal.map (Ideal.Quotient.mk ((maximalIdeal R) ^ (n + 1)))
        ((maximalIdeal R) ^ n)).toAddSubgroup

/-- First-isomorphism-theorem version: F(M^n) / ker ≃+ range. Downstream
callers can transport via the kernel/range characterisations above. -/
noncomputable def FormalGroup.evalGroup_powerIdeal_quotKerEquivRange
    (F : FormalGroup R) (hAdic : IsAdic (maximalIdeal R)) {n : ℕ} (hn : 1 ≤ n) :
    letI := F.evalGroup hAdic
    (F.evalGroup_powerIdeal hAdic n ⧸ (F.evalGroup_powerIdeal_toQuot hAdic hn).ker) ≃+
      (F.evalGroup_powerIdeal_toQuot hAdic hn).range

end HasseWeil.FormalGroup
```

Implementation: `map_add'` uses `evalAdd_sub_add_mem_pow_succ` via
`Ideal.Quotient.eq.mpr`. Kernel via `Ideal.Quotient.eq_zero_iff_mem`. Range via
`Ideal.mem_map_iff_of_surjective` with `Ideal.Quotient.mk_surjective`.
Packaged equivalence is just `QuotientAddGroup.quotientKerEquivRange`. All
axiom-clean.

## Notes
- The `+_F` operation on `F(M^n)` agrees with `+` modulo `M^{n+1}` (by the
  formal group axioms `F(X,Y) ≡ X + Y mod (X,Y)²`). Hence the quotient
  `F(M^n)/F(M^{n+1})` is just the additive `M^n/M^{n+1}`.
- Part A is the mathematical content; Part B is type-level packaging.

## Progress log

- 2026-04-20 Part A delivered in `HasseWeil/FormalGroup/Associated.lean` (~196
  new lines including helpers). `lake build HasseWeil` passes; axiom-clean.
- 2026-04-20 Part B delivered (~80 additional lines): forward AddMonoidHom
  `evalGroup_powerIdeal_toQuot`, kernel/range characterisations, and the
  packaged `evalGroup_powerIdeal_quotKerEquivRange`. Full build passes
  (2848/2848). All axiom-clean.
