# [WP] §6 — the weighted-parity reduced example: final report

**Campaign**: 2026-07-28/29, branch `wp/reduced-example`, worktree
`aintlib-adic-fjp`. Source: `refs/AdicSpaces/uniform_sheafy_domains_with_reduced_example.tex`
(§6, thm:rationally-reduced-example = "Theorem 6.2"). ~65 commits.

## Headline: all four endpoints of [WP] Theorem 6.2 are formalized

Endpoints live in `WP/Main.lean` at the paper's weight `w = id` (`WPAid K`),
in two layers (explicit `ϖ : Uniformizer K` + noetherian-unit-ball input, and
`[IsDiscreteValuationRing 𝒪[K]]`).

| Endpoint | Declarations | Axioms |
|---|---|---|
| (1) uniform complete Tate integral domain, non-noetherian, `𝒜° = 𝒜₀` | `weightedParity_isUniform`, `_isDomain`, `_not_noetherian`, `_powerBounded_eq_unitBall` | clean¹ |
| (2) `(𝒜, B⁺)` sheafy at EVERY pair, strongly sheafy | `weightedParity_isSheafyComplete`, `_stronglySheafy` (+ `wp_structurePresheaf_isSheaf_all`) | clean¹ |
| (3) rationally stably reduced (all finite chains) | `weightedParity_chainReduced` | clean¹ **except**: conditional on `HeadLocsReduced` (declared hypothesis, see below) and transitively on the central library's audit-pass-2 flatness WIP² |
| (4) chart `ℬ` domain + non-uniform ⇒ `𝒜` NOT stably uniform with reduced witness | `weightedParity_chart_isDomain`, `_chart_not_isUniform`, `_not_stablyUniform` | clean¹ |

¹ clean = `[propext, Classical.choice, Quot.sound]`.
² `prop_8_30_flat_clean` (Wedhorn 8.30, `WedhornStronglyNoetherian` audit-pass-2
trio, documented in `AuditCleanWrappers.lean`) — a pre-existing main-library
WIP consumed by R2's flatness step; NOT a campaign sorry. It clears when the
audit lane lands.

## Remaining WP sorries: exactly 4

All in `WP/HeadReduced.lean` — the quarantined head-reducedness wall
(BGR 7.3.2/10 for the heads; HRW-0 adjudicated it a separate sub-campaign,
user-authorized). Endpoint (3) consumes it only through the declared
hypothesis `HeadLocsReduced K w`.

## Major infrastructure delivered (beyond the paper's statement)

- **`RationalTransitivity.lean` (generic)**: existential transitivity of
  rational localization — `exists_rationalLocalization_transitivity` (Huber
  1.5(ii)-(iii) / Wedhorn 8.2(2)+8.4) assembling the library's
  `exists_downstairs_rationalDatum` + `keystone` + `interRational` with the new
  equal-open equivalence `rationalOpenEqEquiv` and
  `imgDatum_interRational_rationalOpen`. Reusable project-wide.
- **`chainReduced_of_ringEquiv`**: `ChainReduced` transport along bicontinuous
  ring equivalences (via `RingEquivPresheafTransport`).
- **The sheafiness engine at `𝒜`** (`WP/Sheafy.lean`, zero sorries): the pushed
  head covers (`PushedHeadData`), `comap_rhoHead_mem_iff` and `mem_liftDatum_iff`
  membership transfers, `liftDatum_mono`, `interDatumHead`, the coefficientwise
  naturality squares (`coeffLoc_restriction_square(P)`), `pushedCompat_head`,
  the injectivity walk, the coefficientwise Čech gluing (`gluing_WPA` — the
  nullity comes from the head embedding's `IsInducing`, no OMT bound needed),
  the OMT embedding assembly, and the full wrapper chain.
- **`tateExtEquiv` + bicontinuity (W24/W24b)**: the Tate-extension flatten
  `𝒜⟨X₁..X_s⟩-restricted ≃+* WPA K (shiftWeight w s)` with
  `tateExtEquiv_bicontinuous` for the canonical mv-Tate topology.
- **Chart theory (W19/W20)**: `chartQHeadEquiv` (isometric), `isDomain_chart`,
  `isReduced_chart`, and the T_n-family witness for non-uniformity.
- The coefficientwise model stack W12–W18 (`coeffLocEquiv`,
  `nonempty_headModelData(_all)`, `PerturbSetup`, `restrictionEquiv`, …).

## Follow-ups (filed)

- HRW-2..6 (the wall; own sub-campaign).
- Central: audit-pass-2 flatness (owner: Wedhorn audit lane).
- Fleet cleanup notes: `interDatumHead` duplicates the generic `interDatum`;
  cadence cleanups CLEANUP-ALL-1/FINAL per AINTLIB rules run on `main`.
- W24b-t4 pair-transport: available generically via
  `PairOfDefinition.mapRingEquiv` + `tateExtEquiv_bicontinuous`; no bespoke
  statement needed.

## Verification protocol

Every group verified before commit: module-scoped `lake build` +
`#print axioms` at the endpoints; full-workspace build (6137 jobs) green
2026-07-29 with the complete campaign integrated; umbrella root imports
`WP.Main`.
