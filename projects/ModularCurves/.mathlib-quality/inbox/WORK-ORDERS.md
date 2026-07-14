# CURRENT WORK ORDERS — the single place to find every seat's session opener

**This is the findable home for the paste-ready openers.** The coordinator keeps it current each
dispatch. To (re)fire a worker: open a `claude` session **from the worktree**
`/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (except YN/y1 work, which also uses
`/Users/mcu22seu/Documents/GitHub/aintlib-mc-b3`), and paste that seat's opener. Each opener points
to the seat's `inbox/STREAM-*.md` for the full banked state; the board (`tickets.md` Amendments) is
the attribution-of-record.

**Four active seats (as of v10.212, 2026-07-14):** G0, KM, GH, OMEGA. Live state: **OMEGA** landed
ω2 ★ + [E12-A] adapted models, on the E13→ω5=T-E14 tail; **GH** landed the [RIG-2] level-agnostic
orbit-freeness core + the [RIG-1] detection engine, on [RIG-1a]→wrappers; **G0** delivered the E[N]
package + NISOG kills + glueTransition — **SIGNAL is one route-(a) refactor + the GlueData assembly
away** (idle, re-fire it); **KM** delivered field-level BB-DEG green-mod-one-sorry, grinding the deep
division-polynomial (K4) bridge. **KEY:** BB-DEG (`mulByHom_finrank`/`endDeg_mulBy=N²`) is a
REGISTER-BOX — every downstream milestone (G0 SIGNAL, GH rigidity, the three `.Representable`)
completes by CONSUMING it sorried; nobody stalls on KM's multi-session bridge. Two live gates to the
headline: OMEGA's T-E14 (engine) + the rigidity assembly (GH+KM, Abel-FREE per v10.212-§B).

---

## STREAM-G0 — Γ₀(N) / Hopf–Galois endgame (SIGNAL one refactor+assembly away)
> You are G0, resuming STREAM-G0. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-G0.md` IN FULL (through v10.212). Rule-5 claim + sentinel `beastmode_active.G0`. E[N] pkg + NISOG kills + `glueTransition` ratified. **The import-cycle question is RULED → route (a) the refactor:** extract `IsInvariant` (+ the six pin statements) into a NEW low-interface file (e.g. `GroupScheme/SubgroupQuotientInterface.lean`); rewire `TranslationAction` to import it; then `SubgroupQuotient` imports the glue construction, sets `quotient := glueQuotient`, discharges all six pins in-place. THEN finish GlueData→quotientπ→UP → six pins → **SIGNAL ★★**. For c4, CONSUME the sorried `mulByHom_finrank` as register-box BB-DEG (do NOT wait on KM). Pathspec commits on the two shared files, `git add` the new file. Marathon v10.162. /beastmode.

## STREAM-KM — the endomorphism-degree keystone (field-level green; grinding the K4 bridge)
> You are KM, resuming STREAM-KM. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-KM.md` IN FULL (through v10.212). Rule-5 claim + sentinel `beastmode_active.KM`. Field-level `modelEllipticCurve_mulByHom_finrank=N²` is green modulo ONE isolated sorry (the L4-core). CONTINUE the **K4 division-polynomial bridge** (`functionFieldMap` + `Dominant.lean`, the finrank↔HasseWeil `mulByInt_degree` bridge) as reusable ForMathlib infra — it ALSO unblocks BB-DIFF, and is the keystone under c4 + rigidity + affineOverEll. **Your Abel-FREE unification finding is the ruling** — define `endDeg` via K4 scheme-finrank ⟹ Abel-free `deg(α−1)`; deliver `[KEY-KER] le_endDeg_of_killed_injective` to GH in the fibre/finrank form (GH replies with the exact signature). **You are NOT the fleet blocker** — BB-DEG is a register-box (downstream consumes it sorried); grind the bridge at depth. Marathon v10.162. /beastmode on K4.

## STREAM-GH — Γ_H rigidity front ([RIG-2] core + [RIG-1] engine landed)
> You are GH, resuming STREAM-GH. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-GH.md` IN FULL (through v10.212). Rule-5 claim + sentinel `beastmode_active.GH`. [RIG-2] core (`aut_endo_eq_one_of_fixes_point`) + [RIG-1] engine (`ForMathlib/UnramifiedEqualizer.lean`) are ratified (axiom-clean mod KM's keystone-pin). **Handshake Q2 RULED → ABEL-FREE:** reply to KM with your `[KEY-KER]` signature in the fibre/finrank form (kernel-size/`mulByHom_finrank`, NOT the endDual/Abel form); re-state the [RIG-2] degree-pin to fibre-finrank if needed. CONTINUE [RIG-1a] (restrict `e.hom.top` to `E[M]` → feed fibre-triviality into UnramifiedEqualizer) → [RIG-1c] (close with `aut_endo_eq_one`) → Γ₁/Γ_H wrappers, CONSUMING KM's keystone as a register-box BB where sorried (do NOT stall on KM's bridge). Marathon v10.162. /beastmode.

## STREAM-OMEGA — the invariant differential ω_{E/S} (ω2 ★ + [E12-A]; on the T-E14 tail)
> You are OMEGA, resuming STREAM-OMEGA. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-OMEGA.md` IN FULL (through v10.212). Rule-5 claim + sentinel `beastmode_active.OMEGA`. **ω2 ★ is DONE** (`InvariantDifferential.lean`, ω_{E/S} invertible; #5866 is NOT a gate — ignore it), and **[E12-A] adapted models** (`basisUnitAt`/`IsAdapted`, KM 2.2.5) landed. CONTINUE the tail: finish E12 → E13 → **ω5 = T-E14, the {±1}/Legendre unblock** — the ★★ that de-sorries `representable_iff:280`, the shared engine Y(N)/Γ₁/Γ_H all wait on (`EllCategory.lean:272` "blocked on T-E-OMEGA" header is stale — only the T-E14 tail remains, which is you). Board the T-E14 unblock LOUDLY (★★). Marathon v10.162. /beastmode.

---

## Parked / done (no order)
- **YN's Y(N) charter** — BEASTMODE-DONE ([YF-ETALE]★ + T-D8-bridge + MASTER wired; in PR-B #5790). Its remaining conjuncts auto-complete when OMEGA lands. The seat is re-tasked to OMEGA above.
- **fable-PIC0's Pic⁰ [NAT]-arc** — parked-with-honor (resume ledger board v10.169-PIC0); resumable if a 5th seat frees.
