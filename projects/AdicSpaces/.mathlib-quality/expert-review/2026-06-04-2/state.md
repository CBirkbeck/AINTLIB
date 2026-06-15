# Expert-review session state (round 2)

- Generated: 2026-06-04
- Audience: Adic-spaces + Mathlib topological-algebra expert
- Goal of brief: Specific blocker (how to proceed) on the two infrastructure obstructions in the 8.28(b) gluing half
- Scope: Whole 8.28(b) acyclicity route
- Reply received: true (2026-06-04)
- Reply integrated: true (2026-06-04)

## Questions in the brief

| # | Question (verbatim from §9) |
|---|------------------------------|
| Q1 | `A°°` as an open ideal without linear topology — cleanest way to get top-nilpotent additive closure under `NonarchimedeanAddGroup` vs Mathlib's `IsLinearTopology`-gated `topologicalNilradical`; existing API? local lemma? upstream? does the ideal (vs additive) structure need more? |
| Q2 | No-archimedean quasi-compactness of `Spa A` (Wedhorn 7.35(2)) — least-infrastructure route; is the Rmk 7.40(2) finite-union argument cleaner than the parked spectral-`Spv` track? |
| Q3 | Whole-space vs relative 7.54 — confirm 7.54 is whole-space (global `T·A=A` incompatible with proper base), proper bases via relative 7.54 over `O_X(U)` + Prop A.3? |
| Q4 | Dominating-unit route — confirm height-1/mul-archimedean lemma false (Rmk 7.40(5)-(6)) AND unnecessary (no-hArch Cor 7.32); is `A⁺⊆A₀` the right inclusion? |

## Reply summary (all four answered, high confidence, plus a key correction)

- Q1: **A°° is NOT an ideal of A** for a Tate ring (Q_p counterexample: p is a top-nilp unit). Build project-local `NonarchimedeanAddGroup` API: `A°°` = open additive subgroup + radical ideal of `A°`; the 7.31 input is `∃ finite T ⊆ A°°, T·A°° open` (via a pair of definition: `I²  ⊆ T·A°°`, `I²` open). Do NOT relax Mathlib's `topologicalNilradical : Ideal A`. Local first; upstream only the additive/`A°`-ideal lemmas.
- Q2: Use Wedhorn 7.35 / spectral `Spv` (the parked SpvAI/Bool-cylinder route is correct). Rmk 7.40(2) finite-union is useful AFTER rational subsets are qc, not foundational.
- Q3: CONFIRMED whole-space; relative via `O_X(U)`, transport `Spa O_X(U) ≃ U`.
- Q4: CONFIRMED height-1 false + unnecessary; Cor 7.32 no-height. AND: do NOT assume a general inclusion between arbitrary `A₀` and `A⁺` in EITHER direction — only `A°°⊆A⁺⊆A°` is universal; a compatible-pair inclusion must be a chosen hypothesis (the project's `CompatiblePlusSubring` is exactly that).

## Ticket-board snapshot at brief time (gluing half)

- DONE/axiom-clean (this session): the whole-space 7.54 combinatorial core (`exists_form_a_refinement_coversSpa` + Steps 3-6 + helpers); `span_top_of_distinguished_products`, `distinguishedProducts_refines`.
- BLOCKED / B2-flagged: general-C `exists_form_a_refinement`/`exists_ideal_gen_refinement` (false-for-proper-base); `mulArchimedean_valueGroup_of_stronglyNoetherianTate` (740-6, false); the no-hArch dominating-unit chain (carries unsatisfiable `IsLinearTopology`).
- Open infra: T-MIGRATE-LINTOP-TATE-QC, T-COMPACT-NO-HARCH, T-CECH-754-STEP1, T-CECH-CONSOL-2 (gluing cocycle), T-CECH-754-REL, T-CECH-PAIR (direction-suspect).

## Stuck points (from §8 of brief)

1. A°° open ideal w/o IsLinearTopology (Q1) — the central blocker.
2. Cor 7.31/7.32 + the 7.54 normalization (Q1 downstream).
3. Mis-stated lemmas: general-base 7.54 false (Q3), height-1 false (Q4).
4. Prop A.3(3) gluing cocycle (context).

## Reference list (from §2.2)

[Wedhorn] Adic Spaces (5.23, 6.13(1), 6.38, 7.17, 7.31, 7.32, 7.35(2), 7.40, 7.41, 7.45, 7.53, 7.54, 8.28(b), 8.33, 8.34, A.3); [Hu1]–[Hu3] (7.54 = [Hu3] 2.6); Mathlib TopologicallyNilpotent / Nonarchimedean.
