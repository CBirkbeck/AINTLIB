# Development Plan: ROIE — the `A⁺ ⊆ A°` ring-of-integral-elements interface (full option (a))

## Goal

Make the affinoid-ring axiom `A⁺ ⊆ A°` (Wedhorn Def. 7.14(1)) part of the interface, so the
Spa-point / unit-criterion machinery applies to **completions** `B = 𝒪_X(D)` without the
false-for-completions `CompatiblePlusSubring`. Concretely: redefine the completion plus-subring
to the faithful `Ĉ = closure(IntCl(A⁺[T/s]))` (Wedhorn 8.16), register
`IsRingOfIntegralElements ((presheafValue D)⁺)`, and re-route every consumer of the OLD
`A⁺ ⊆ A₀` machinery to the faithful `A⁺ ⊆ A°` route. Refines TaskList #68; supersedes the B2.

## References (all from [Wedhorn], *Adic Spaces*, arXiv:1910.05934v1)

- **Def. 7.14(1)** (p.60): ring of integral elements = open + integrally closed + `⊆ A°`.
- **Remark 7.15(1)** (p.60): `A°` is the largest ring of integral elements.
- **Prop. 7.19 + Lemma 7.20** (p.61): `(A⁺⟨X⟩_T)^int` is a ring of integral elements of `A⟨X⟩_T`
  (open + integrally closed + `⊆ A⟨X⟩_T°`); Lemma 7.20: `(A°)⟨X⟩ ⊆ (A⟨X⟩_T)°`.
- **Lemma 7.47(4)** (p.68) = **[Hu1] 2.4.3**: rings of integral elements correspond under
  completion (`A⁺ ↔ Â⁺`). EXTERNAL cite (Wedhorn does not reprove).
- **Prop. 7.41** (p.66): for `x ∈ Cont(A)` of height 1, `x(a) ≤ 1 ∀ a ∈ A°`; hence
  `x ∈ Spa(A,A⁺)` for every ring of integral elements `A⁺`. Wedhorn proof ≈ 6 lines
  (archimedean value group + continuity ⟹ contradiction).
- **Remark 7.25 / 7.40(5) / 7.42(2)** (p.62/65/66): a non-open-support continuous valuation has a
  height-1 vertical generization in `Spa(A,A⁺)` (microbial; unique by Remark 4.12).
- **Lemma 7.45** (p.67): a non-open prime `𝔭` is dominated by an analytic continuous valuation
  (in-repo: `exists_spa_point_via_restrictToConvex`, a deep sorry ≈ [Hu2] 3.9 area).
- **8.16**: `𝒪_X⁺(U) = A⟨T/s⟩⁺` (the completed ring of integral elements = `Ĉ`).

## Mathlib inventory

| Concept | Status | Action |
|---|---|---|
| `integralClosure ↥B A` (Subalgebra) `.toSubring` | mathlib | USE (verified: `(integralClosure ↥B A).toSubring : Subring A`; `B ≤ it` via `algebraMap_mem`) |
| `Valuation.Integers.mem_of_integral` / valuation integer integrally closed | mathlib | USE (the integral-transfer for the SpaPresheafValueEquivalence re-route) |
| `IsRingOfIntegralElements` (class) | project (AffinoidRings, ROIE-1 foundation, committed 489fe72) | USE |
| `exists_cont_supp_ge_powerBounded_of_nonOpen_prime` (named 7.45+7.41 leaf) | project (Presheaf, committed sorry) | DISCHARGE in T-ROIE-4 |
| `support_eq_maximal_of_le` | project (Presheaf, committed) | USE |

## File structure (touched)

- `Presheaf.lean` — IntCl redefinition of `completedPlusSubring` + `IsRingOfIntegralElements`
  instance + dropped `completedPlusSubring_le_{completedLocSubring}` (ROIE-1, WIP in stash).
- `Cor832.lean` — `exists_spa_point_supp_ge_in_presheafValue` faithful re-proof + dropped
  `isUnit_canonicalMap_s_via_nullstellensatz` (ROIE-1, WIP in stash).
- `SpaPresheafValueEquivalence.lean`, `WedhornCechAcyclicity.lean` — cascade re-routes (ROIE-2).
- `AffinoidRings.lean` — (foundation, committed) the `IsRingOfIntegralElements` class.

## Dependency graph

```
T-ROIE-1 (restore WIP: Presheaf+Cor832 IntCl migration, builds through Cor832)
   └→ T-ROIE-2 (cascade re-route: SpaPresheafValueEquivalence + completedPlusSubring_le_ringOfDef
                + 5 WCA users + downstream → full build GREEN with the deep sorries)
          ├→ T-ROIE-3 (discharge the IsRingOfIntegralElements instance's 3 fields; Wedhorn 7.19/7.20/7.47(4))
          └→ T-ROIE-4 (discharge exists_cont_supp_ge_powerBounded_of_nonOpen_prime; Wedhorn 7.45/7.42/7.41)
```

## Residual after the full cascade (the honest faithful leaves)

- **[Hu1] 2.4.3** (= Lemma 7.47(4)): completion preserves rings of integral elements — EXTERNAL,
  cited (acceptable, like [Hu2] 3.3). Used in T-ROIE-3 (`isIntegrallyClosed` field).
- **Lemma 7.45** (`exists_spa_point_via_restrictToConvex`): the analytic-point existence — in-repo
  deep sorry. Used in T-ROIE-4.
- Everything else (7.19, 7.20, 7.41, the migration, the re-routes) is provable in-project.
