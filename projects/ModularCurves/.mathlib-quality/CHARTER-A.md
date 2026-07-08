# CHARTER-A — THE W7 ENDGAME (beastmode-A, v10.32)

Durable record of the multi-session, self-paced charter beastmode-A holds. The session
sentinel (`beastmode_active.beastmode-A`) is recreated each session and holds the
CURRENT-FOCUS line; **this file holds the arc** so a fresh-context session resumes without
re-deriving it from the board. Full charter also on the board (`tickets.md`, Amendments
v10.32 + the faith-infra / 0h / endgame boxes).

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
   drops 1b from T-W7.12, unlocks ω).
3. Claim **T-E-OMEGA route R1**: the ω line bundle glued from the atlas with my comparison
   as transition data; DS-register in the same commit; opaque interface per v10.24(b).
4. **0h interrupt (STANDING, interrupt-priority):** the moment c5β lands **0c-ii**
   (`mulModelHom`, currently sorry at GroupLawConstruction.lean:806, c5β's file — do NOT
   touch), take **`mulModelHom_vc`** (T-W7.0h) on the banked route:
   `projModel_hom_ext_of_affine` (reduce to Z-chart agreement) + per-chart addOn
   VC-equivariance. Then return to the charter.
5. **Endgame** (all four deps green: main+1b, 0c-ii, 0h, 1a): assemble JOINTLY with c5β,
   split via the board — T-W7.12 (glued negHom/mulHom) → CLEANUP-ALL-W7 → **T-W7.36**
   (**T-W7a MILESTONE** — report; retires `abelEnrichment_exists`).
6. **Standby tail whenever blocked:** stage PR-draft files for READY upstream candidates.
   **DONE 2026-07-08** — `#1-#4` + README in `pr-drafts/` (commit 98c39995). #5/#7 = owner-
   input, #6 (D2) = defer to D2 verify-pass. Tail now exhausted.

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
