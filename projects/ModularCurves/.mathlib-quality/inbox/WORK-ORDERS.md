# CURRENT WORK ORDERS — the single place to find every seat's session opener

**This is the findable home for the paste-ready openers.** The coordinator keeps it current each
dispatch. To (re)fire a worker: open a `claude` session **from the worktree**
`/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (except YN/y1 work, which also uses
`/Users/mcu22seu/Documents/GitHub/aintlib-mc-b3`), and paste that seat's opener. Each opener points
to the seat's `inbox/STREAM-*.md` for the full banked state; the board (`tickets.md` Amendments) is
the attribution-of-record.

**Four active seats (as of v10.192, 2026-07-13):** G0, KM, GH, OMEGA. Live state: **OMEGA** landed
ω_{E/S} sorry-free (ω2 ★) and is on the ω3/ω4/ω5→T-E14 tail; **GH** cleared GHB6 + landed the
[RIG-3] general rigidity bridge and is on [RIG-2]/[RIG-1]; **G0** is in the Hopf C4c-2 glue (steps
4-5); **KM** delivered the Γ₁ rel-rep ★ and is re-chartered to the endomorphism-degree keystone.
Dependency spine: KM's `deg(α−1)`/`endDeg_mulBy=N²` feeds GH's [RIG-2] rigidity (both levels) + G0's
c4 + torsion_rank; OMEGA's ω5=T-E14 flips the shared `representable_iff` engine.

---

## STREAM-G0 — Γ₀(N) / Hopf–Galois endgame (C4c-2 glue)
> You are G0, resuming STREAM-G0. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-G0.md` IN FULL (through v10.192). Rule-5 claim + sentinel `beastmode_active.G0`. RESUME C4c-2: step 3 (`quotientRing_eq_coinvariants` glue=Hopf-on-patches) is ratified sorry-free; do **step 4** (windowHom/imageOpens/saturation/tripleIso — the :343-790 template mirror, consuming the transported per-patch universal property + specEqualizerπ surjectivity) → **step 5** (GlueData :818-910 + quotientπ/pins :969-1869, option-γ (N,hkill)) → C4 glue → **SIGNAL ★★**. NB c4 (E[N] rank-N²) is being pulled to KM's endomorphism-degree keystone — CONSUME `mulByHom_finrank` when it lands rather than re-proving it for C3d. For `range (pullback.fst f g) = f.base ⁻¹' range g.base` use mathlib `AlgebraicGeometry.Scheme.Pullback.range_fst` (hypothesis-free). Marathon v10.162. /beastmode.

## STREAM-KM — the endomorphism-degree keystone (re-chartered; Γ₁ rel-rep ★ delivered)
> You are KM, resuming STREAM-KM. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-KM.md` IN FULL (through v10.192) + board v10.192-§C. Rule-5 claim + sentinel `beastmode_active.KM`. Your Γ₁ rel-rep ★ (`gammaOneDrinfeld_relativelyRepresentable`) is DELIVERED + ratified; rigid is routed to GH's bridge (not yours). **NEW CHARTER — the ENDOMORPHISM-DEGREE KEYSTONE:** the arithmetic root under the whole rigidity front (both levels) + G0's c4 + torsion_rank. FIRST ACT: your own `/develop --decompose` (target `EllipticCurve/EndomorphismDegree.lean` + Torsion.lean BB discharges). SCOPE in order: (i) `mulByHom_finrank`=N² (BB-DEG, Torsion.lean:152) via **`import` HasseWeil `mulByInt_degree`** (Foundation/Basic.lean:727, PROVEN) + the T-B6 fibrewise-degree→finrank bridge; (ii) `mulByHom_locallyQuasiFinite` (BB-QF); (iii) `deg(α−1)` for CM autos (order 3/4/6) — the rigidity root GH's [RIG-2] consumes. NOT BB-FLAT (miracle flatness — separate deeper item). HANDSHAKE the deg(α−1) signature with GH. Makes your own Γ₁ ★ axiom-clean. Marathon v10.162. /beastmode after decompose.

## STREAM-GH — Γ_H rigidity front (GHB6 cleared; [RIG-3] bridge landed)
> You are GH, resuming STREAM-GH. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-GH.md` IN FULL (through v10.192). Rule-5 claim + sentinel `beastmode_active.GH`. GHB6 (`f₀_finite_etale`) is CLEARED, `rigid_of_geom_free` (GammaHMaster:210, Q-general) is PROVEN — it's now the fleet's shared rigidity bridge (KM's Γ₁ instantiates it too). RESUME [RIG-2] → [RIG-1]: state the **[RIG-2] orbit-freeness CORE level-agnostically** (`Aut(E/k̄)` acts freely on exact-order-N points, N≥3; H-condition = thin wrapper). Its arithmetic root `deg(α−1)<N` is **KM's endomorphism-degree keystone — do NOT prove it; CONSUME KM's `deg(α−1)`/`endDeg_mulBy`**. FLAG KM the exact deg(α−1) signature you need. Then [RIG-1] detection → GHC1 fully live. Marathon v10.162. /beastmode.

## STREAM-OMEGA — the invariant differential ω_{E/S} (ω2 ★ landed; on the T-E14 tail)
> You are OMEGA, resuming STREAM-OMEGA. Worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves` (branch dev/modular-curves). Pull, read `projects/ModularCurves/.mathlib-quality/inbox/STREAM-OMEGA.md` IN FULL (through v10.192). Rule-5 claim + sentinel `beastmode_active.OMEGA`. **ω2 ★ is DONE** — `InvariantDifferential.lean` (0 sorries) has ω_{E/S} as an invertible `Scheme.Modules` (built on our `Picard/InvertibleSheaf` base; #5866 is NOT a gate — ignore it). You're at [T-OM-B7-pre]. CONTINUE the tail: ω3 (basis↔unit torsor, T-A4) → ω4 (base change) → **ω5 = T-E14, the {±1}/Legendre unblock** — the ★★ that de-sorries `representable_iff:280`, the shared engine Y(N)/Γ₁/Γ_H all wait on. `EllCategory.lean:272` "blocked on T-E-OMEGA" header is stale (ω exists; only the tail remains — you). Board the T-E14 unblock LOUDLY (★★). Marathon v10.162. /beastmode.

---

## Parked / done (no order)
- **YN's Y(N) charter** — BEASTMODE-DONE ([YF-ETALE]★ + T-D8-bridge + MASTER wired; in PR-B #5790). Its remaining conjuncts auto-complete when OMEGA lands. The seat is re-tasked to OMEGA above.
- **fable-PIC0's Pic⁰ [NAT]-arc** — parked-with-honor (resume ledger board v10.169-PIC0); resumable if a 5th seat frees.
