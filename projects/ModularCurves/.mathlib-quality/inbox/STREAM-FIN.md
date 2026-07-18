# STREAM-FIN — the closer's route book (created v10.320, 2026-07-18, coordinator)

**You hold the entire remaining headline cone** (owner consolidation, 2026-07-18: "finish this
project off — fresh strong worker, the bulk of the remaining work"). This file is your route book;
the board (`tickets.md` Amendments, v10.316→v10.320) is attribution-of-record. **Verify-at-source
before building on anything here** — `git fetch`, grep the census, and fire the capstone script
for ground truth:

    bash projects/ModularCurves/.mathlib-quality/scripts/capstone-receipts.sh

## 0. The verified cone (origin @ bd4b2b2e9, coordinator census 2026-07-18)

| Front | File | Sorries |
|---|---|---|
| F1 | `EllipticCurve/EndomorphismDegree.lean` | 7 — `:202 endDual_comp_self`, `:359 endDeg_comp`, `:429 endDeg_comp_mulBy`, `:435 endTrace_comp_mulBy`, `:453 endTrace_sq_le`, `:459 eq_zero_of_endDeg_eq_zero`, `:469 …fixesTorsion` — **you do NOT grind these** (see the RULING) |
| F2 | `Moduli/Bootstrap.lean` | 1 — `:222 legendreDelta_relativelyRepresentable_finiteEtale` (T-E14-AX2) |
| F3 | `Moduli/EllCategory.lean` | 2 — `:298 representable_iff` ⇐, `:324 representable_iff_rigidNoeth` ⇐ (the headline one) |
| F3 | `Moduli/QuotientProblem.lean` | 2 — `:1022` classical engine, `:1040 representable_of_rigidNoeth_of_torsor` (**THE MOUTH**) |
| F3 | `Moduli/Recollement.lean` `:445` (T-E5f) + gates `ForMathlib/InvariantTorsor.lean` (2 sorry-lines) + `Moduli/EngineDescent.lean` `:646` | ride the ⇐ map |

~125 other sorries are ARCHIVED non-blocking (v10.317-GH classification) — leave them.

## 1. THE RULING you build under (board v10.320 — resolves v10.317-KM's decision point)

**k̄ suffices; T-W7.8 stays PARKED; do NOT build general-S `endDual_comp_self`.** Every headline
consumer of the degree keystone consumes it through ∀-geometric-point pins with quantifier prefix
`∀ (k : Type u) [Field k] [IsAlgClosed k]` — `hbound` @ GammaHMaster:1220/:1259/:1279 +
GammaHClosure:152; `hH` @ GammaHMaster:822/:1064/:1085/:1107. A field is reduced: the arbitrary-base
rigidity lift (KM's L5-general, the T-W7.8 wall) is headline-dead. Prove the keystone AT k̄ ONLY;
after your rewire, re-tag the 7 general-S sorries **[KEY-GEN-PARKED]** (docstring re-tag + board
line; T-W7.8-family spreading-out debt, non-blocking).

## F1 — KEYSTONE-AT-k̄: narrow, discharge `hbound` + `hH`, rewire (the deep front)

**F1.0 — SUSPECT-RIG2 FIRST (board v10.320).** The frozen [RIG-2] `hbound` contract is refutable
as stated (all pointed ε, only `Function.Injective pts`):
- ε = [N+1]: δ = ε−1 = [N] kills any N of the N² points of E[N](k̄) — refutes every N ≥ 4;
- automorphism-restricted, N = 4: ε = [−1], δ = [−2], ker ⊇ E[2] = 4 injective killed points.
Re-derive this yourself (adversarial protocol), then **NARROW the contract to the true shape** the
consumer actually holds — ε an ISO + a point P of exact geometric order N with (ε−1)P = 0 (then
⟨P⟩ ⊆ ker δ since δ is a homomorphism ⟹ N ≤ deg δ ≤ 4 via kernel-bound + Cauchy–Schwarz; the N = 4
equality case forces ε = [−1] ⟹ P = −P ⟹ order ≤ 2, absurd). Re-thread
`gammaOneDrinfeld_fix_absurd` (it holds the iso `e` and the T-D6b exact-order data — "its small
multiples are nonzero"). Statement-layer producer work; BOARD the shape change (receipts 3/6 move).
Run the same review on `hH` against `gammaH_representable_of_orderOf`'s actual side condition on
`H` (hH's ∀γ:H shape is only true when the headliner's orderOf constraint excludes the CM-unit
orders 2/4/6 — read the `_of_orderOf` signature before proving anything).

**F1.1 — targets** (suggested new file `EllipticCurve/KeystoneGeometricPoint.lean`): prove the
(narrowed) hbound statement and the hH statement as standalone theorems over `S = Spec k̄`, then
instantiate at every consumer site and rewire whichever k̄-cores currently consume the sorried
general-S EndomorphismDegree lemmas (trace via the capstone receipts; expected consumption points:
the KM-2.7.2-shaped cores around `aut_endo_eq_one_of_fixes_point` / `gammaOneDrinfeld_fix_absurd`,
GammaHMaster).

**F1.2 — PROVEN substrate (consume, never re-prove):**
- `KernelBound.le_endDeg_of_killed_injective` (sorry-free) — the kernel bound.
- `TorsionDivisibility.exists_eq_one_add_mulBy_comp_of_fixesTorsion_of_isIso` (sorry-free) — KM's
  "ε−1 = gN", modulo the box `[IsIso (E.torsionQuotientToSelf N)]` (**T-G3d-Niso**), which you
  discharge AT k̄ ([N]-quotient iso over a field; engine: `ForMathlib/FinrankComp.lean`
  `finrank_comp`/`isIso_iff_finrank_eq`).
- `endDeg_mulBy = n²` (:211, proven), `endDeg_comp_of_isIntegral` (:292-region, proven),
  `endDeg_one_add` (definitional), `mulByHom_zero_finrank` (:185, proven), the **T-G3a arithmetic
  heart** (:471+, proven — the whole number theory of the rigidity computation).
- GH's `ForMathlib/FinrankDegenerate.lean` (fibre-rank degenerate engine).
- **HasseWeil (IMPORT ONLY, never re-prove):** `hasse_bound` / `degree_quadratic_closed`
  (`HasseWeil.HasseBound.Basic` post-reorg), `DualIsogeny` (`α_dual ∘ α = [deg α]`,
  `HasseWeil.Isogeny.Dual`), `mulByInt_degree`.

**F1.3 — the genuinely NEW pieces (your build):**
1. **L1 fibre dictionary** (the one real bridge): over `S = Spec k̄`, identify repo
   `endDeg`/`endTrace` (scheme-native `Scheme.Hom.finrank` at the zero point) with HasseWeil's
   field-level degree/trace. Anchors banked at the BOTTOM of `decomposition-km-integral.md`
   (§ [CHARTER-K / K2]): `EllipticCurve.baseChange` + the Stage-B scheme↔affine dictionary
   (`modelPointAddEquiv`/`projModelPointsEquiv`). At a field base the pins' statements need no
   base-change step at all — the curve already lives over Spec k̄.
2. **k̄ zero-or-isogeny dichotomy**: a nonzero endo over k̄ is finite flat — feeds the PROVEN
   `endDeg_comp_of_isIntegral` to yield the k̄-instances of :359/:429/:435; the zero case is
   `FinrankDegenerate` + `mulByHom_zero_finrank`.
3. **k̄ trace bound** (:453's k̄-instance): transfer `(tr)² ≤ 4·deg` through the L1 dictionary from
   HasseWeil `hasse_bound`/`degree_quadratic_closed` (that is :453's own documented route).
4. **k̄ definiteness** (:459's k̄-instance): `deg g = 0 ⟹ g = 0` over k̄ (dictionary, or directly
   finrank-0 + FinrankDegenerate). Needed for the Cauchy–Schwarz equality analysis at N = 4.
5. **Assembly** (KM 2.7.2 at k̄, on the NARROWED contract): kernel-bound + quadratic expansion
   (`endDeg_one_add` + the :429/:435 k̄-instances) + trace bound + T-G3a.

**F1 order:** F1.0 narrowing → L1 dictionary → dichotomy → k̄-instances (3)(4) → Niso@k̄ →
assembly → `hH` (same toolbox, finite-order/CM-unit arithmetic) → instantiate + rewire → re-tag
the 7 as [KEY-GEN-PARKED] → **KEYSTONE-k̄-LANDED** (report).

## F2 — Bootstrap:222 (Legendre AX2): COLLISION-GUARDED takeover of CHARTER-G's build

**Guard first, every session:** `ls -la` mtime of `beastmode_active.G0` + `git log
origin/dev/modular-curves --oneline -20 -- projects/ModularCurves` (look for fresh G0 landings on
Sqrt/Legendre/gluing files) + the board. If G0 is live and landing, YIELD this front (work F1/F3)
and coordinate via inbox. If quiet: it is yours.

**Banked build-state (ALL PUSHED, verified):** the funnel is PROVEN
(`legendreDelta_relRep_finiteEtale_of_scaleTorsor`); the affine cover package is PROVEN
(`SqrtUnitCover`: pair/points-iff/finite/étale/over-Spec/sections/twist); glue-1a `sqrtPair_map`,
1b `selfPresentation` + `baseChangeEquiv`, 2a `sqrtPairMapRingHom` PROVEN. OMEGA's `abscissaDiff`
(`Moduli/AbscissaDifference.lean`, axiom-clean) delivers the chart-d data with u²-covariant
transitions (`abscissaDiff_compatible`); `IsLegendreDatum.neg` + `unit_sq_eq_one` pin the fibres
(honestly μ₂). Full detail: `inbox/STREAM-G0.md` + `beastmode_active.G0`.

**Remaining mapped steps (verbatim from G0's sentinel):**
- (2b) the Spec-pullback square: conjugate `CommRingCat.isPushout_tensorProduct` through
  `baseChangeEquiv` + the `sqrtPair_map`-cast, then `isPullback_SpecMap_of_isPushout` (the BB-FLAT
  chart-square pattern).
- (3) the (V,i)-indexed `RelativeGluingData` over `W := fullLevelLocus 2`: index =
  affine-opens-with-atlas-chart-choice; transitions = restriction ∘ `sqrtPairCongr`
  (omegaCocycle-transition); map_comp = cocycle + `algHom_ext`; equifibered = (2b)'s squares;
  `Z₂ := .glued`, toBase-composite; FINITE + ÉTALE via `toBase_preimage_eq_opensRange_ι` +
  `IsZariskiLocalAtTarget`.
- (4) the sections-spec: per-chart `sqrtCoverSectionsEquiv` + sheaf-glue of square roots + the
  b↔u dictionary. NOTE: G0 requested OMEGA's adapted-value refinement (b-adapted ⟹ d's
  b-trivialized value is x_b(Q) − x_b(P); Legendre-datum ⟺ value-1) — NOT landed. Build it
  yourself (OMEGA's note in STREAM-G0.md: "a small layer on `basisUnitAt`") or build around.
- (5) feed the funnel ⟹ `:222` closes → **:222-CLOSED** (report).

## F3 — THE ENGINE GATE (mouth + instantiation wires + recollement)

1. **The mouth** `representable_of_rigidNoeth_of_torsor` (QuotientProblem:1040). Banked route =
   KM pp. 112–116, transcribed in its own docstring. Already PROVEN: `simul_representable`,
   `simulSchemeAction`, the freeness step `simulSchemeAction_free_of_rigidNoeth`, and the T-Q3
   affine quotient (`SchemeAction.quotient`, T-Q5 — AINTLIB's own, no SGA import). Remaining
   gates: `ForMathlib/InvariantTorsor.lean` (the T-Q2 SGA III Exp. V 4.1 interface, 2 sorry-lines)
   + `Moduli/EngineDescent.lean` `:646` (the assembly around it is sorry-free — read its "This
   assembly is sorry-free" note for exactly what it consumes). Close the gates, assemble the
   mouth. Then `:1022` (classical) = corollary by weakening (`hrig.rigidNoeth`) — NEVER a separate
   build. → **MOUTH-CLOSED** (report).
2. **The two TorsorData packages** (the instantiation boundary, ex-O/G work):
   - **T-E15b** (δ = naive level 3, G = GL₂(𝔽₃), over IsUnit 3): `fullLevelLocus` +
     `gammaFullNaiveGlAction` equivariance → `TorsorData`. hQrep/hQaff =
     `naiveLevelThree_representable_by_affine` — PROVEN (the ℤ[1/3] engine, v10.318).
   - **T-E14 package** (δ = Legendre, G = GL₂(ℤ/2) × {±1}, over IsUnit 2): **the action is the
     COUPLED one** (the GL₂-factor re-marks the pair AND re-scales ω — NOT the ambient
     `legendreBootstrapGAction` product; see Bootstrap's T-E14 statement-layer note + ticket
     [T-E14-ACT']). Consumes F2's `:222` on the hQrep side — sequence AFTER F2.
3. **The ⇐-consumption map** (EllCategory:324 — documented VERBATIM in-source): instantiate the
   mouth twice + recollement over D(2) ∪ D(3) = Spec ℤ (`Moduli/Recollement.lean` — its `:445`
   T-E5f sorry rides in). Then `:298` from `:324` (weakening corollary).

## F4 — FINAL WIRING + THE CAPSTONE

- Instantiate the proven `hbound`/`hH` into the closure chain: receipts 3/5/6
  (`gammaOneDrinfeld_rigid_and_representable_of_hbound`, `gammaH_representable_of_orderOf`,
  `gammaOneDrinfeld_representable_prep`) gain unpinned corollaries (one-liners once F1 lands).
- Drive all seven receipts of `scripts/capstone-receipts.sh` to
  `{propext, Classical.choice, Quot.sound}`; extend the script with the unpinned corollaries;
  FIRE it; append the receipts to the board = **THE-HEADLINE** (report; project done).

## What NOT to do
- Do NOT grind the 7 general-S EndomorphismDegree sorries; do NOT un-park T-W7.8.
- Do NOT force T-H6 (SUSPECT-B2, owner-flagged, non-blocking).
- Do NOT touch the ~125 archived stream-WIP sorries.
- External-quiet stands: no mathlib PRs / Zulip / upstream filings (flag-only).

## Mechanics (non-negotiable — from the coordinator handover)
- Rule-5 claim + sentinel `beastmode_active.FIN` (yours; keep FOCUS current each session).
- Board appends via `cat scratch >> tickets.md` ONLY (never Edit — a live commit races an Edit);
  entries `## v10.NNN-FIN (date, STREAM-FIN) — …`; commit `.md` + your `.lean` via exact pathspec.
- Shared worktree + background sync: `git fetch` + `git rev-list --left-right --count
  HEAD...origin/dev/modular-curves` before every commit; `git merge --ff-only` to sync.
- The bar per landing: `lake build` green; ZERO new sorries outside your claimed files (the
  SUSPECT-RIG2 statement-narrowing is boarded, never silent); `#print axioms` = the three
  standard; push, then VERIFY `git ls-remote origin dev/modular-curves`.
- NEVER `2>/dev/null` beside a lake/lean command (guardrail-blocked; use `2>&1`).
- **Report ONLY at: KEYSTONE-k̄-LANDED, :222-CLOSED, MOUTH-CLOSED, THE-HEADLINE.**
