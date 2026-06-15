# Keystone route: the Nullstellensatz bypass (verified 2026-06-01)

This supersedes the closedness/faithful-flatness framing of the keystone in
`docs/ACYCLICITY-CRITICAL-PATH-PLAN.md` (2026-05-21, now stale on this point).

## Audit verdict (downstream deliverable)

`ValuationSpectrum.tateAcyclicity_via_normalizedLaurent_autoCont`
(`TateAcyclicityFinalAssembly.lean`, last theorem) is the real downstream deliverable:
full acyclicity (separation ∧ gluing), **body sorry-free**, but carries `sorryAx`
(verified) and threads ~9 hypotheses (lane suppliers, `hZavyalov_per_E`, the noeth pack).
All 3 of its root sorries trace to the `restrictionMap` layer, which hangs on **T001**
(`Presheaf.lean:905 spa_point_nonOpen_of_rational_subset`) via `isUnit_algebraMap_s_of_huber`.

## Why the closedness / faithful-flatness route is a DEAD END

`coeRingHom_preserves_proper` (the lifted-ideal route to T001) has three wired suppliers in
`Cor832.lean` — `_of_closed`, `_of_stacks00MA`, `_of_locIdeal_le_jacobson` — and **all three
converge on the same residual**:

> `Module.FaithfullyFlat locSubring (AdicCompletion locIdeal locSubring)`

which needs `locIdeal ⊆ Jacobson(locSubring)`. **This is false for the uncompleted
localization**: a topologically-nilpotent `i ∈ locIdeal` only makes `1−ai` invertible *after*
completion, so it is not in `Jacobson(locSubring)` (Cor832 docstrings: "false in degenerate
cases"; `AdicCompletionFaithfullyFlat.lean` boundary block; the `ℤ_p[x]/(px−1)` counterexample).
So "presheafValue Noetherian + complete ⟹ ideals closed" does **not** apply — the closedness
needed lives in the *uncompleted localization*, where it is the deep open residual.

## The FAITHFUL route (Wedhorn's actual argument): Nullstellensatz 7.52(2) via 7.45

`isUnit_algebraMap_s_of_huber` proves `D.s` is a unit in `Loc.Away D'.s` because `D.s` does
not vanish on `rationalOpen D'` (= Spa of the localization): for `v ∈ rationalOpen D' ⊆
rationalOpen D`, `v(D.s) ≠ 0`. The clean tool is **Wedhorn 7.52(2)** (`f` unit iff `v(f)≠0`
∀`v∈Spa`), whose reverse rests on **Wedhorn 7.45** (non-open prime ⟹ Spa point) — and 7.45
(`Lemma745.exists_mem_spa_supp_ge_of_nonOpen_prime`, the `restrictToConvex` construction) is
**axiom-clean**. Key insight: 7.52(2)-reverse needs only the **containment** `𝔪 ≤ supp(v)`,
NOT the exact `supp = 𝔪` (the rank-1-domination residual that makes the old
`exists_spa_point_supp_eq_maxIdeal_of_complete`, Presheaf:2611, a bare sorry).

## Landed 2026-06-01 (both AXIOM-CLEAN, in `Lemma745.lean`)

1. `PairOfDefinition.exists_spa_point_supp_ge_maxIdeal_of_complete` — for a maximal `𝔪` of a
   complete affinoid, `∃ v ∈ Spa A A⁺, 𝔪 ≤ supp v`. Open `𝔪` → trivial valuation
   (`exists_mem_spa_supp_eq`, supp = 𝔪); non-open `𝔪` → 7.45. Containment, not equality.
2. `PairOfDefinition.isUnit_iff_forall_not_vle_zero_of_complete` — complete-affinoid 7.52(2):
   `IsUnit f ↔ ∀ v ∈ Spa A A⁺, ¬ v.vle f 0`, reverse via (1).

## Continuation (next steps)

3. Apply (2) to `B := presheafValue D'` (the completion — it IS a complete affinoid with a
   pair of definition) at `f := D'.canonicalMap D.s`, to get `IsUnit (D'.canonicalMap D.s)`
   from: `∀ w ∈ Spa(presheafValue D'), w(canonicalMap D.s) ≠ 0`.
4. Discharge that via the **comap into `rationalOpen D'`** (⊆ direction of the
   Spa ≅ rationalOpen Equiv): `w ↦ comap w =: v ∈ rationalOpen D' ⊆ rationalOpen D`
   (containment hypothesis `_h`), so `v(D.s) ≠ 0`, hence `w(canonicalMap D.s) = v(D.s) ≠ 0`.
5. Re-route `isUnit_canonicalMap_s_of_huber` (Presheaf:936) onto (3)+(4) under the full
   complete-affinoid bundle (signature refactor of the unit-chain), de-poisoning
   `restrictionMap` and thereby all 3 root sorries of the deliverable.

This bypasses `coeRingHom_preserves_proper` / the faithful-flatness residual entirely.
