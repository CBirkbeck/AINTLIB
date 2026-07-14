# CURRENT WORK ORDERS — the single place to find every seat's session opener

**This is the findable home for the paste-ready openers.** The coordinator keeps it current each
dispatch. To (re)fire a worker: open a `claude` session **from the worktree**
`/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (except YN/y1 work, which also uses
`/Users/mcu22seu/Documents/GitHub/aintlib-mc-b3`), and paste that seat's opener. Each opener points
to the seat's `inbox/STREAM-*.md` for the full banked state; the board (`tickets.md` Amendments) is
the attribution-of-record.

**Four active seats (as of v10.219, 2026-07-14):** GH, KM, OMEGA LIVE; G0 idle (Γ₀ charter COMPLETE,
re-tasked). **THE CRITICAL PATH HAS FUNNELED.** RelRep ✓✓✓ (all three) and **Rigid ✓ (all levels)** —
GH proved `gammaH_rigid_of_orderOf` (general-H, subsuming Γ_H/Γ₁/Γ₀) on top of `gammaBot_rigid` (Y(N)),
so the rigidity side of `representable_iff` is DONE (mod hLN=T-W7.8 parked + hH=KM keystone). **⟹ OMEGA's
T-E14 is now the SINGLE remaining STRUCTURAL gate** — it flips the engine and makes ALL THREE levels
representable at once. **G0** delivered Y₀(N) (`exists_gammaZeroSpace`, concrete Hopf-Galois route) — its
Γ₀ charter is COMPLETE; re-tasked to the E[N] finiteness substrate (BB-QF/BB-FLAT). **KM** at K4 L4-iii
(the keystone's last step — auto-cleans the register-boxes on landing). Boxes: BB-DEG (KM, close),
BB-QF/BB-FLAT (→G0), BB-ELLQUOT (boxed, DR IV.1), L15 (deferred), T-W7.8 (parked).

---

## STREAM-G0 — Γ₀ charter COMPLETE (Y₀(N) delivered) → RE-TASKED to the E[N] finiteness substrate
> You are G0, resuming STREAM-G0. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-G0.md` IN FULL (through v10.219). Rule-5 claim + sentinel `beastmode_active.G0` — **fire ONE G0 session only** (v10.219: two collided on the last dispatch). **Γ₀ CHARTER COMPLETE + ratified** — SIGNAL ★★ (E/G exists, SubgroupQuotient 0-sorries) THEN Y₀(N) (`exists_gammaZeroSpace` NIsogeny:3118, the concrete Hopf-Galois isogeny route). [ELLQUOT-GEOM]×3 ruled a **register-box** (BB-ELLQUOT, DR IV.1 — consume sorried, do NOT chase the geometry). **NEW DISPATCH — the E[N] finiteness substrate** (feeds RelRep across all levels): **(1) BB-QF FIRST** — `mulByHom_locallyQuasiFinite` (Torsion.lean:141, `:= by sorry`): [N] is locally quasi-finite (quasi-finite fibres, the honest content) — your Hopf/isogeny-degree machinery is exactly the right substrate. **(2) THEN scope BB-FLAT** — `mulByHom_flat` (Torsion.lean:147, miracle-flatness) via `/develop --decompose` (design the leaves, don't grind blind). **De-conflicted from KM:** you own quasi-finiteness+flatness (fibre geometry); KM owns BB-DEG degree=N² (division polynomials). Cross-link `mulByHom_isFinite` (:157, consumes BB-QF). Marathon v10.162. /beastmode.

## STREAM-KM — the endomorphism-degree keystone (K4 division-polynomial bridge, at L4-iii)
> You are KM, resuming STREAM-KM. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-KM.md` IN FULL (through v10.219). Rule-5 claim + sentinel `beastmode_active.KM`. Field-level `modelEllipticCurve_mulByHom_finrank=N²` green modulo the L4-core sorry; register-box strategy VALIDATED **twice over** — G0's SIGNAL+Y₀(N), GH's `gammaBot_rigid` AND now `gammaH_rigid_of_orderOf` (general-H) all landed consuming your keystone as boxes. **You have a SECOND consumer now: GH's `hH` pin** on the general-H rigidity — deliver `[KEY-KER] le_endDeg_of_killed_injective` in the **fibre/finrank (Abel-FREE)** form (your own UNIFICATION FINDING is the ruling — `endDeg` via K4 scheme-finrank, NOT via `endDual`/Pic⁰, which is owner-parked; GH replies with the exact signature it consumes). CONTINUE the **K4 division-polynomial bridge** at **L4-iii** (`functionFieldMap` + `Dominant.lean`, finrank↔HasseWeil `mulByInt_degree`) as reusable ForMathlib infra — landing L4-iii auto-cleans BB-DEG across ALL consumers (G0/GH/c4/affineOverEll) at once. **You are NOT the fleet blocker** (OMEGA's T-E14 is the single structural gate); grind the bridge at depth. Marathon v10.162. /beastmode on K4.

## STREAM-GH — general-H rigidity ★★ DELIVERED (rigidity DONE, all levels) → hH / Γ₁ / prep-.Representable
> You are GH, resuming STREAM-GH. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-GH.md` IN FULL (through v10.219). Rule-5 claim + sentinel `beastmode_active.GH`. **★★ general-H rigidity DELIVERED + ratified** — `gammaH_rigid_of_orderOf` (GammaHMaster.lean:985, general-H engine `gammaFullNaive_twist_pow_refl` + the glSmul twist), SUBSUMING Γ_H/Γ₁/Γ₀, on top of `gammaBot_rigid` (Y(N)). **⟹ the rigidity side of `representable_iff` is DONE for ALL levels** (mod hLN=T-W7.8 parked + hH=KM's keystone, both boxes). This is the charter goal. DISPATCH (pick, all real): **(a)** discharge/minimise the `hH` + `hLN` pins on `gammaH_rigid_of_orderOf` (hH is now a KM second-consumer — coordinate the exact fibre/finrank signature); **(b)** the Γ₁ exact-order `.Representable` prep (`fix_absurd` Γ₁ variant → unblocks KM's Drinfeld `.Representable`, which also needs OMEGA's engine); **(c)** prep the `.Representable` assembly for Γ_H so that the instant OMEGA lands T-E14, `gammaH_representable` (:268) closes with no new math. Rigidity is banked — spend the seat widening the `.Representable` frontier. Marathon v10.162. /beastmode.

## STREAM-OMEGA — ω_{E/S} → T-E14 = the SINGLE remaining STRUCTURAL gate on the whole project
> You are OMEGA, resuming STREAM-OMEGA. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-OMEGA.md` IN FULL (through v10.219). Rule-5 claim + sentinel `beastmode_active.OMEGA`. **T-E12 six-sevenths done** (adapted-model theory [E12-A/B/C] + universal (E,ω) + `classifyingMap : Y.base ⟶ M₁` [E12-D], all sorry-free). **★ THE CRITICAL PATH HAS FUNNELED ONTO YOU:** RelRep ✓✓✓ and now **Rigid ✓ for ALL levels** (GH's `gammaH_rigid_of_orderOf` general-H + `gammaBot_rigid`) — so `representable_iff`'s ⇐ needs ONLY **T-E14**, and the instant it lands, **all three levels (Y(N), Γ_H, Γ₁) are representable at once. Nothing else structural stands between here and the headline.** CONTINUE: EllHom upstairs (chart-glue the adapted-model isos over the classifying map) + RepresentableBy packaging → T-E12 → T-E13 (one-liner) → **T-E14 (★★)** — the highest-leverage remaining deliverable in the ENTIRE project. Board the T-E14 unblock LOUDLY (★★). Marathon v10.162; continue.

---

## Parked / done (no order)
- **YN's Y(N) charter** — BEASTMODE-DONE ([YF-ETALE]★ + T-D8-bridge + MASTER wired; in PR-B #5790). Its remaining conjuncts auto-complete when OMEGA lands. The seat is re-tasked to OMEGA above.
- **fable-PIC0's Pic⁰ [NAT]-arc** — parked-with-honor (resume ledger board v10.169-PIC0); resumable if a 5th seat frees.
