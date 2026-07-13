# CURRENT WORK ORDERS — the single place to find every seat's session opener

**This is the findable home for the paste-ready openers.** The coordinator keeps it current each
dispatch. To (re)fire a worker: open a `claude` session **from the worktree**
`/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (except YN/y1 work, which also uses
`/Users/mcu22seu/Documents/GitHub/aintlib-mc-b3`), and paste that seat's opener. Each opener points
to the seat's `inbox/STREAM-*.md` for the full banked state; the board (`tickets.md` Amendments) is
the attribution-of-record.

**Four active seats (as of v10.179, 2026-07-13):** G0, KM, GH, OMEGA. (The former YN seat is
re-tasked to OMEGA — its Y(N) frontier is BEASTMODE-DONE; everything past it waits on the shared
engine OMEGA now builds.)

---

## STREAM-G0 — Γ₀(N) / Hopf–Galois endgame
> You are G0, resuming STREAM-G0. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-G0.md` IN FULL (through v10.178). Rule-5 claim + sentinel `beastmode_active.G0`. RESUME: C3b (E∖G stability — go DIRECT from the preimage predicate) → C3c (the divisor↔section bridge; affineness is mathlib `Proj.isAffineOpen_basicOpen`, build only the bridge; grep `sectionsDivisor` first) → C3d freeness (+ lane-B c4 `E[N]` rank-N²) → C3e/f → C4 glue → **SIGNAL ★★**. Build `RelEffCartierDiv.mapIso` general. Marathon v10.162. /beastmode.

## STREAM-KM — Γ₁ Drinfeld representability
> You are KM, resuming STREAM-KM. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-KM.md` IN FULL (through v10.178). Rule-5 claim + sentinel `beastmode_active.KM`. RESUME: `Moduli/DrinfeldRepresentability.lean` — finish the equiv (invFun via `baseChangeEquiv`/`asSection⁻¹`, then left_inv/right_inv, then naturality) → `gammaOneDrinfeld_rigid` → wire `GammaH:1045 .Representable` via `representable_iff` (ACCEPT its shared sorry — do NOT build the engine; OMEGA is building the gate). = the **Γ₁ rel-rep ★**. No c4 needed. maxHeartbeats 1M + term-mode over pullback.hom_ext. Marathon. /beastmode.

## STREAM-GH — Γ_H quotient problem → GHC1
> You are GH, resuming STREAM-GH. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-GH.md` IN FULL (through v10.177). Rule-5 claim + sentinel `beastmode_active.GH`. RESUME from [couniv-v-a]: couniversal UNIQUENESS (`relKey_of_classifies` at source `quotProb` + tμ″-descent) → the two k̄-geometric clauses → `exists_quotientProblemData` → **GHC1 goes live** → then [GHB6-RING] clears the `f₀_finite_etale` edge. GHB7-0 is settled: ship on β (do NOT open α — mathlib has no relative-Spec-of-invariants). Marathon. /beastmode.

## STREAM-OMEGA — the invariant differential ω_{E/S} (the shared engine gate)
> You are OMEGA, a fresh seat on STREAM-OMEGA (the freed YN seat). Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-OMEGA.md` + the board [T-E-OMEGA] section IN FULL. Rule-5 claim + sentinel `beastmode_active.OMEGA`. Owner un-demoted this — it's the single gate under the SHARED `representable_iff` engine that Y(N)/Γ₁/Γ_H all need. Route R1 is UNGATED (T-W7.1b `pointedIso_exists_variableChange` is proven sorry-free, Comparison.lean:162). FIRST ACT: your own `/develop --decompose` of R1 (ω1 cocycle → ω2 glued invertible `Scheme.Modules` → ω3 basis↔unit = T-A4 torsor → ω4 base change → ω5 {±1}/Legendre = T-E14) in new `EllipticCurve/InvariantDifferential.lean`. Board the T-E14 unblock ★★ (it flips the shared engine). Marathon v10.162. /beastmode.

---

## Parked / done (no order)
- **YN's Y(N) charter** — BEASTMODE-DONE ([YF-ETALE]★ + T-D8-bridge + MASTER wired; in PR-B #5790). Its remaining conjuncts auto-complete when OMEGA lands. The seat is re-tasked to OMEGA above.
- **fable-PIC0's Pic⁰ [NAT]-arc** — parked-with-honor (resume ledger board v10.169-PIC0); resumable if a 5th seat frees.
