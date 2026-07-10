# CHARTER-A — THE W7 ENDGAME (beastmode-A, v10.32)

## ⏸ STATUS 2026-07-09 — [Y1-D2] transport DISCHARGED + route-a banked; PARKED (coordinator v10.83)

Coordinator pivot (v10.82): from "build all of route-a" → "discharge only the [T-E4-family]
transport gating [Y1-D2] (standalone lemmas + holder wiring note)." **DELIVERED + RATIFIED (v10.83).**

- **`Moduli/PullSectionCanonicity.lean`** (commit `7dac70553`): the *structural fact of record* — the
  whole T-E4 family (unrestricted `pullSection_add`, the Γ₁/Γ(N) map-memberships, Y1-D2
  `isNaiveGammaOne_pullSection_iff`) inherits `[IsLocallyNoetherian]` through a **single** call to
  `isMonHom_of_one_comp_eq'` inside `transportSection_add`. Extracted the noetherian-free algebra as
  `transportSection_add_of_isMonHom` (**AXIOM-CLEAN** — lean_verify) + arbitrary-base
  `pullSection_add_of_finitePresentation`/`_zsmul` (only `sorryAx` = the one primitive) + holder wiring
  note (docstring). **T-E4 family collapsed to ONE primitive: `isMonHom_of_one_comp_eq'_of_finitePresentation`.**
- **route-a** (`EllipticCurve/RigiditySpreadingOut.lean`, commit `590984cce`): green skeleton +
  6-leaf source-faithful decomposition. mathlib has ~80% (AffineTransitionLimit.lean); the one gap =
  property-descent along limits (Stacks 081D, absent). **BANKED as the fallback** to land the primitive.

**⏸ PARKED at this clean boundary (coordinator directive v10.83). Route-a banked, NOT abandoned.**

**▶ RETURN TRIGGER: `T-W7a` lands (c5β's endgame) → the T-E4-family FALLS-SWEEP:**
  1. route-(c) wiring: connect `isMonHom_of_one_comp_eq'_of_finitePresentation` to the landed T-W7a
     canonicity (or supply the group-hom equation by construction);
  2. the holder wiring (Representability `pullSection_add`:207 + the 2 map-memberships → the FP lemmas;
     NEW-Y1 assembles Y1-D2 in YOneAssembly.lean per the docstring note);
  3. Y1-D2, YFULL AFF/FIN, GH1 all go **axiom-clean** in that sweep.
  Fallback if route-c slips: finish route-a (leaf board = tasks; L4c property-descent is the bulk).

---

## ✅ STATUS 2026-07-08 — items 1 & 2 COMPLETE (T-W7.1b DONE)
The faith-infra atomic refactor (item 1) and the T-W7.1b flip (item 2) are **DONE**
(commits 6f531139 → 3f7fc4fd → 7a81d093 → 7b527d7b). The whnf wall fell to the def-level
interface refactor (the "AdicSpaces recipe"): `coordRingToZSection` → small-RHS
`pointedIsoCoordEquiv_apply` → S1 → `pointedIsoΓ_apply` → `appLE_zChart_eq_pointedIsoΓ` →
`pointedIso_hom_eq_of_pointedIsoΓ` (M-recon) → `main` (coordEquiv_ext generation +
transport_general/bridge). Comparison.lean sorry-free; all 4 leaves axiom-clean (lean_verify).

**Charter now BLOCKED on other lanes** (session paused at a PHASE-8 boundary):
- item 3 (ω/T-E-OMEGA): DEMOTED to on-demand (v10.36) — build only when a consumer demands.
- item 4 (0h `mulModelHom_vc`): BLOCKED on c5β's β4(c)/GLC completion (c5β on c4.2b; mulModelHom
  still sorry). c5β board-signals when 0c-ii lands → resume charter, take 0h on the banked route
  (projModel_hom_ext_of_affine + per-chart addOn VC-equivariance). THIS is the next-session opener.
- item 5 (endgame T-W7.12 → CLEANUP-ALL-W7 → T-W7.36/T-W7a): BLOCKED on 0h.
- fallback T-D6b: BLOCKED on P3b3's T-B5D-A (`torsionπ_etale` still sorryAx).

**RESUME 2026-07-09 OUTCOME (board-first):** map_id (`projModelVCIso_one`) DELIVERED axiom-clean
(commit 4f8d2c1b8) but **MOOT** — PIC0 already closed [U/G] map_id via the (1,1)-`_mul` route;
kept as named API gain. **T-A3 also MOOT — already DONE**: `projModel_smooth` axiom-clean at
`WeierstrassModel.lean:1764` since 2026-07-06 (verified). Both dispatched items were pre-completed;
the redistribution churn lost track. **LESSON REINFORCED: board-first, always** — verify a ticket's
code state before working it. Remaining live item: **0h** (c5β signal, not fired) + endgame handshake.

**NEXT-SESSION QUEUE (owner, v10.48 + T-A3 addition — MOSTLY MOOT now, see RESUME note above):**
1. **PIC0 map_id quick favor** — ~3 lines on my private transport machinery (`coordRingCongr`/
   the projModel transport). Do FIRST (unblocks PIC0).
2. **0h interrupt** the moment c5β signals 0c-ii → then the **endgame WITH c5β**: T-W7.12 →
   T-W7.36 (**T-W7a** — the group law on the model over every base; `abelEnrichment_exists`
   becomes `rfl`).
3. **T-A3** (model smooth ⟺ Δ unit) — my lane's original chartwise tickets, now **doubly
   LOAD-BEARING**: fable-P4's engine (smooth leaf 3) AND Y₁(N)'s smoothness leg both consume it.
   **PROMOTE ABOVE the 0h wait if c5β's 0c-ii signal is slow (v10.53)** — T-A3 is independent of
   0h and dispatchable in my own lane, so do NOT idle waiting on 0h when T-A3 is available.
4. **Drafts / standby.** NOTE: [STREAM-GH] is **no longer mine** — p0/beastmode-B claimed the
   first wave (GHB1/GHB3/GHA2/GHA4/GH2/GHC4) per v10.50. (v10.52 Y1-vi absorption RETRACTED —
   a fresh worker took Y1.)

Rebase note (P3b3-relevant, confirmed): T-W7.1b lives on **dev/modular-curves** (my branch),
NOT `main` (the integration branch). Charter ends at **T-W7a**. Next session resumes on the
queue above.

---

Durable record of the multi-session, self-paced charter beastmode-A holds. The session
sentinel (`beastmode_active.beastmode-A`) is recreated each session and holds the
CURRENT-FOCUS line; **this file holds the arc** so a fresh-context session resumes without
re-deriving it from the board. Full charter also on the board (`tickets.md`, Amendments
v10.32 + the faith-infra / 0h / endgame boxes).

## Strategic context (v10.36 — owner directive of record)
**MODULAR CURVES ASAP.** The goal is the **representability theorems** (Y₁(N), Y(N), Γ_H as
representing objects of the moduli problems). Modular forms are shelved; four representability
planning streams are decomposing now (v10.37 charters-in-waiting). faith-infra → **T-W7.1b is
on the critical path**: fable-P4's KM 4.7 engine (route (a), E/G descent — no SGA VIII 7.8, no
algebraic spaces, no ω) is explicitly waiting on the 1b flip, so 1b is now doubly load-bearing.
ω is OFF the critical path (demoted — arc item 4).

## Reporting contract (binding)
Report to owner ONLY on: milestones (1b flip, W7a), genuine post-decomposition walls, B2
events, or charter completion. Everything else → the board. Decompose-don't-grind is
binding; whnf walls fall to **fresh context + decomposition**, not tail-of-session
persistence.

## The arc
1. **NEXT SESSION, full budget, FIRST ACT = the ATOMIC faith-infra refactor.** Definition-
   level irreducibility AT the `ModelVariableChange` def site (not `local irreducible` at
   the consumer — session-2 proved local attrs insufficient) + a complete whnf-free b1
   interface (application / injectivity / cancellation lemmas for `chartZRingEquiv`,
   `basicOpenIsoAway`, `pointedIsoΓ`, `pointedIsoCoordEquiv`) + rebuild the b2 proofs that
   unfold these defs, replaced by interface lemmas. **Land WHOLE — partial leaves the build
   red.** The "AdicSpaces recipe" (def-level irreducible + interface-before-proofs).
2. Close `pointedIsoΓ_eq_of_coordEquiv` (S1) + `pointedIso_exists_variableChange` (main) in
   `Comparison.lean`; axiom sweep; **flip T-W7.1b → DONE** (MILESTONE — report to owner;
   drops 1b from T-W7.12). **Doubly load-bearing (v10.36):** fable-P4's KM 4.7 engine is
   explicitly waiting on this flip — it is now on the critical path to representability, not
   just the W7 endgame. This is the highest-value act after faith-infra.
3. **0h + the W7 endgame.** **0h interrupt (STANDING, interrupt-priority):** trigger corrected
   per v10.36 — fires off **c5β's β4(c) / GroupLawConstruction completion**, NOT "0c-ii
   landing" (that handover timing was stale: c5β's projGlueLift_eq + the crux are already
   proven, so 0h now reads one step earlier). Take **`mulModelHom_vc`** (T-W7.0h) on the
   banked route: `projModel_hom_ext_of_affine` (reduce to Z-chart agreement) + per-chart
   addOn VC-equivariance. `mulModelHom` lives in c5β's GroupLawConstruction.lean — do NOT
   touch until β4(c) lands. Then the **endgame** (deps green: main+1b, 0h, 1a) — assemble
   JOINTLY with c5β, split via the board: T-W7.12 (glued negHom/mulHom) → CLEANUP-ALL-W7 →
   **T-W7.36** (**T-W7a MILESTONE** — report; retires `abelEnrichment_exists`).
4. **ω (T-E-OMEGA) — DEMOTED to last / on-demand (v10.36).** The KM 4.7 engine no longer
   needs ω (route (a) collapses descent to E/G via T-Q5's quotient — no ω). Only **T-E14's
   Legendre half** and **T-A4** still consume it. Build ω (route R1: line bundle glued from
   the atlas, my comparison as transition data; DS-register same commit; opaque interface
   v10.24(b)) **only when a consumer demands it** — do not pre-build it.
5. **Standby tail whenever blocked:** stage PR-draft files for READY upstream candidates.
   **DONE 2026-07-08** — `#1-#4` + README in `pr-drafts/` (commit 98c39995; internal per
   v10.35b — build them, publish nothing). #5/#7 = owner-input, #6 (D2) = defer to a D2
   verify-pass. Tail now exhausted.

**Charter ends when the group law on the model exists over every base.**

## Banked findings (for next session)
- **faith-infra session-2 finding:** `local irreducible` on all four b1 isos + the mathlib
  wrappers DOES fix generic-lemma steps (`hp` chart-iso cancellation compiles) but the wall
  PERSISTS on any `rw [pointedIsoCoordEquiv_apply]` / `change` / `.trans` — the composite is
  huge *as stated*, not merely when unfolded, so opacity doesn't shrink it. Only pure `rfl`
  survives. ⇒ needs DEFINITION-level irreducibility + b2 rebuild. This is why item 1 is
  atomic and next-session-only.
- **Interface citizens already proved (in `Comparison.lean`, compiling):**
  `pointedIsoCoordEquiv_apply` (function-level rfl — the one cheap op on the composite) and
  `ringEquiv_trans_mid_inj` (generic opaque mid-cancel). Reuse; don't re-derive.
- **Landed & axiom-clean:** b2 (`pointedIsoCoordEquiv_filtration`), b3x/b3y/b5 (3 of 4
  comparison leaves), T-D6a-ii (L3/L4/headline + `exists_factor_comap_iff`), T-D33
  (`exists_exactOrderLocus_section`), T-W8 (level spaces Γ₁/Γ/Γ₀), T-UPSTREAM-TRIAGE.
- **T-D6b fallback:** reboxed non-Cartier route (closed-in-étale-over-k̄ via T-B5′) waits on
  P3b3's T-B5D-A; re-check when it lands.
