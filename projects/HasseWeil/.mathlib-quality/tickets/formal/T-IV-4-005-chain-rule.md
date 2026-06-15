# T-IV-4-005: ω_G ∘ f = f'(T) ω_F (chain rule)

**Status**: REVIEW
**Silverman**: IV.4.3
**Module**: `HasseWeil/FormalGroup/InvariantDiff.lean`
**Owner**: worker-D
**Checked out at**: 2026-04-17T14:00:00Z
**Estimated lines**: 80
**Difficulty**: hard (CRITICAL)
**Stream**: D/E

## Depends on
- T-IV-4-003 (normalized)
- T-IV-2-002 (FormalGroupHom)

## Blocks
- T-IV-BRIDGE-001..004
- T-III-5-002 (additivity, via the bridge)

## Statement (Silverman IV.4.3)
Let `f : F → G` be a hom of formal groups over `R`. Let `ω_F, ω_G` be the
normalized invariant differentials of `F, G`. Then
`ω_G ∘ f = f'(T) · ω_F`,
where `f'(T)` is the formal derivative of `f` and the composition `ω_G ∘ f`
means substituting `f(T)` into `ω_G`.

## Acceptance criteria

```lean
namespace HasseWeil.FormalGroup

/-- Chain rule for invariant differentials of formal group homs.
    Reference: Silverman IV.4.3. -/
theorem FormalGroupHom.invariantDifferential_chain (f : FormalGroupHom F G) :
    G.normalizedDifferential.toSeries.subst f.toSeries =
      f.toSeries.derivative * F.normalizedDifferential.toSeries

end HasseWeil.FormalGroup
```

## Notes
- This is the central tool for connecting "pullback of differentials" to
  "leading coefficient of the formal series".
- Used for the formal-group bridge proof of T-III-5-002 (pullback additivity).

## Progress log
- 2026-04-17T14:00Z [worker-D] Verified: `FormalGroupHom.invariantDifferential_chain`
  proved in `HasseWeil/FormalGroup/InvariantDiff.lean`. Note: the ticket's
  acceptance-criteria formula
  `G.normalizedDifferential.toSeries.subst f.toSeries =
     f.toSeries.derivative * F.normalizedDifferential.toSeries`
  is **mathematically incorrect**: it would claim
  `P_G(f(T)) = f'(T) · P_F(T)`. The correct Silverman IV.4.3 statement is
  `P_G(f(T)) · f'(T) = c₁ · P_F(T)` with `c₁ = f'(0)`, as implemented:
  ```
  PowerSeries.subst f.toSeries G.normalizedDifferential.toSeries *
    PowerSeries.derivative R f.toSeries =
  PowerSeries.C (PowerSeries.coeff 1 f.toSeries) *
    F.normalizedDifferential.toSeries
  ```
  The proof spans `dX_at_zero_chain` (via `coeff_10_lhs` and `coeff_10_rhs`
  in `Differential.lean`) and then inverts the unit `dX_at_zero` to get
  the invariant-differential form. 0 sorries, standard axioms only.
  Status → REVIEW (reviewer should confirm the corrected statement).
