# Ticket board — Hasse-bound consolidation (dedup the proof routes)

**Canonical (KEEP — the sole intended public API):** `WeilPairing/HasseBound.lean : hasse_bound_unconditional`
— `|#E(F_q) − q − 1| ≤ 2·√q`, proven axiom-clean, only hypothesis `2 ≤ Fintype.card K`. Consumed in 7 files.

**Problem.** ~30 conditional/witness `hasse_bound_*` / `traceOfFrobenius_*` theorems remain across **earlier,
superseded routes** — the "bad versions with extra hypotheses":
`Hasse/{BoundOfWitnesses, Final, OpenLemmas, L6ViaPoleDivisor, QuadraticForm, HoleE}` + `Verschiebung/Cascade`,
plus the leftover **`HasseWeil/HasseBound.lean`** (its bound theorems were already deleted — it now holds only
the discriminant lemmas `trace_sq_le_four_mul_deg` / `abs_le_two_sqrt_of_sq_le` + a stale `/-! … -/` changelog).

**Why this isn't a mechanical fleet dedup.** The canonical's transitive import closure is **186 modules** —
every suspect file is in it (pulled via shared low-level deps), so the import graph cannot distinguish a dead
route from a live one. Pruning safely needs proof-architecture judgment (which lemmas the canonical proof
actually invokes). Hence a producer/dev task.

## T-HB-CONSOLIDATE (producer)
1. Confirm `hasse_bound_unconditional` is the **sole** public Hasse-bound statement to keep.
2. Trace the canonical proof's **live chain** of lemmas (per the file's own note: `isogOneSub_negFrobenius`
   + `WeilPairing/HasseAssembly.lean` + `Hasse/QuadraticForm.lean`'s `hasse_bound_of_full_qf_nonneg_witnesses`
   / `traceOfFrobenius_sq_le_of_qf_nonneg`). Whatever the proof transitively uses = LIVE.
3. Everything else = a **dead alternative route** → delete the theorems and the files that become orphaned.
   Confirmed dead-end candidates (each declared but referenced only in its own file): `hasse_bound_sq_of_witnesses`,
   `hasse_bound_from_HasseOpenLemmaPack`, `hasse_bound_from_pack`, `hasse_bound_of_qf_nonneg_witnesses`,
   `hasse_bound_for_finite_field`, `hasse_bound_F_four`, `hasse_bound_F_nine`. (The `_witness_parametric_*`
   Cascade chain and the HoleE/Final/OpenLemmas routes are the prime suspects — verify against step 2.)
4. **`HasseWeil/HasseBound.lean` leftover:** drop the stale `/-! … -/` changelog block (deleted-theorem
   narrative), keep the live discriminant lemmas; consider renaming the file (e.g. `DiscriminantBounds.lean`)
   so the duplicate `HasseBound.lean` name no longer collides with the canonical one.
5. **Bar:** `lake build HasseWeil` green, `hasse_bound_unconditional` still axiom-clean, no orphan breakage
   (`lake build HasseWeil.<touched-module>` by name), no `sorry`.

GitHub cross-ref: this is the cleanup-side complement to the QC finding that `HasseWeil/HasseBound.lean`'s
stale changelog survived cleanup (the worker treated it as a docstring; the cleanup-worker rule was tightened
to remove historical/changelog comments).
