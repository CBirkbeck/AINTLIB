# QF Identity Witness Chain — Status (Worker C, 2026-05-06)

## Discharge chain

The QF identity hypothesis `h_qf_signed` consumed by
`hasse_bound_for_finite_field` (the parametric universal bound) is:

```
∀ r s : ℤ, (isogSmulSub π r s).degree =
  q · r² - t · r · s + s²
```
where `t = isogTrace π (isogOneSub_negFrobenius W hq)`.

Discharge route: `hole_e_closer_via_frobenius_dual_witness`
(HasseWeil/Hasse/HoleE.lean:391) takes:

| Witness | Status | Source |
|---------|--------|--------|
| `IsDualOf verschiebung π` | shipped (per-prime) | Cascade.lean q=2/3/5/7 milestones |
| `h_sum_pts` | UNSHIPPED — needs `π + V = [t]` on points | Future content |
| `h_deg_bridge_family` | UNSHIPPED — comp degree from hom decomposition | Future content |
| `h_dual_deg_family` | shipped via IsDualOf duality | Per-prime |
| `h_nonneg_N` | UNSHIPPED — det of QF nonneg | Future content |

## Three precise propagating witnesses

The QF identity discharge requires THREE named substantive witnesses:

1. **`h_sum_pts`**: `(π + V).toAddMonoidHom = [t].toAddMonoidHom` where
   t is the trace of Frobenius. This is the substantive content of
   "π + verschiebung = [tr(π)]" at the point-map level. Provable from
   the IsDualOf certificate + Vieta / characteristic polynomial of the
   endomorphism ring.

2. **`h_deg_bridge_family`**: for any r, s:
   ```
   (V·(r,s).comp(π·(r,s))).toAddMonoidHom = [N(r,s)].toAddMonoidHom
   ⟹ (V·(r,s).comp(π·(r,s))).degree = N(r,s)²
   ```
   where `N(r,s) = q·r² - t·r·s + s²`. The "deg of comp = deg.toAddMonoidHom"
   bridge depends on the genuine pullback for `r·π - s·id`, currently
   placeholder `AlgHom.id`.

3. **`h_nonneg_N`**: `0 ≤ q·r² - t·r·s + s²` for all r, s. The
   discriminant condition `t² ≤ 4q` makes this nonneg. Equivalent to
   the Hasse bound itself, so this is circular without a separate
   degree-positivity argument.

## Conclusion

The QF identity is NOT axiom-clean composable from current per-prime
infrastructure. Three substantive witnesses (1, 2, 3) remain.

The IsDualOf certificate alone (the per-prime work shipped through
Verschiebung/Cascade.lean for q=2/3/5/7) does NOT propagate to the
QF identity automatically. The h_sum_pts and h_deg_bridge_family
witnesses are FUTURE content depending on:
- Genuine pullback for `r·π - s·id` (replacing the placeholder)
- Characteristic polynomial of Frobenius from IsDualOf

The QF identity is a real wall, not just a verification gap.
