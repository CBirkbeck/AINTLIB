# T-IV-7-001: height(f) for hom of formal groups in char p

**Status**: REVIEW
**Silverman**: IV.7 (definition)
**Module**: `HasseWeil/FormalGroup/Height.lean`
**Owner**: worker-G
**Checked out at**: 2026-04-17T19:05Z
**Estimated lines**: 60
**Difficulty**: medium
**Stream**: D

## Depends on
- T-IV-2-002 (FormalGroupHom)
- T-IV-4-006 (Frob decomposition)

## Blocks
- T-IV-7-002 (height(F))

## Statement (Silverman IV.7 def)
Let `R` be a ring of characteristic `p > 0`. For a nonzero formal group hom
`f : F → G` over `R`, the **height** `h(f)` is the unique non-negative integer
such that
`f(T) = a T^{p^h} + (higher order terms)`,
with `a ≠ 0`.

If `f = 0`, define `h(0) = ∞`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- The height of a formal group hom in characteristic p.
    Reference: Silverman IV.7. -/
noncomputable def FormalGroupHom.height {F G : FormalGroup R}
    (p : ℕ) (hp : p.Prime) [CharP R p] (f : FormalGroupHom F G) : ℕ ⊕ {⊤}

end HasseWeil.FormalGroup
```

## Notes
- Used to distinguish ordinary vs supersingular elliptic curves (height 1 vs 2).

## Progress log
- 2026-04-17T19:05Z [worker-G] Checkout (with T-IV-7-002). Plan: define
  height via `padicValNat p (order f.toSeries).toNat`, lifted to `ℕ∞` with
  `⊤` at `order = ⊤` (i.e., `f.toSeries = 0`).
- 2026-04-17T19:20Z [worker-G] DONE. New file
  `HasseWeil/FormalGroup/Height.lean` (~70 lines) provides:
  * `FormalGroupHom.height p f : ℕ∞` — `order.map (padicValNat p)`
  * `FormalGroup.height F p` — height of `mulByNatHom F p` (T-IV-7-002)
  * `height_zero_toSeries` — height = ⊤ when underlying series is zero
  * `height_of_ne_zero` — explicit formula for nonzero case
  Note: semantic "height = exponent of p-power order" only requires
  `order f.toSeries` to be a p-power, which Silverman IV.7 proves is
  automatic for nonzero formal group homs in char p — that theorem remains
  future work (a follow-up ticket).
  Axiom-clean: `propext, Classical.choice, Quot.sound` only.
  Full `lake build` passes.
