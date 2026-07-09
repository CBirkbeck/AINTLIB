# COORDINATOR HANDOVER — ModularCurves producer fleet
*Written 2026-07-09 by the outgoing coordinator (rate-limit handover). Read this fully,
then read tickets.md §Amendments v10.32 → end. You are the fleet's coordinator, with
owner-delegated authority over dispatches, adjudications, and B2 approvals.*

## THE GOAL (owner, binding)
**Modular curves ASAP**: construct Y₁(N), Y(N), Γ_H as representing objects of the
elliptic-curve moduli problems. Modular forms are SHELVED (ω/T-E-OMEGA demoted to
on-demand). Priority ranking of the planned streams: Y1 > YFULL > GH > NISOG (v10.37).

## HOW THE SYSTEM WORKS
- **The board is the record**: `tickets.md`, append-only Amendments sections at EOF.
  Workers self-number sections too — collisions get letter suffixes (v10.26b). You are at
  ~v10.69+; check the tail before numbering.
- **Append discipline** (races with live workers): write your section to a scratch file,
  `git pull --rebase --autostash`, `cat scratch >> tickets.md`, pathspec-commit ONLY the
  files you own (board/inbox), push with a pull-rebase fallback. NEVER `git add` broadly —
  sibling worktree edits are live WIP.
- **THE INBOX PROTOCOL (v10.69)**: dispatches/redirects/adjudications go to
  `.mathlib-quality/inbox/<worker>.md`, committed+pushed. Workers must pull + read inbox +
  new Amendments at session start and every commit boundary. Reports flow board-ward; you
  POLL the board on each activation. The owner relays nothing routine — their roles are
  session lifecycle, rate limits, and owner decisions.
- **Charter mode (v10.32)**: each worker holds a multi-session charter; they report ONLY
  at named milestones, post-decomposition walls, B2 events, or completion. Respond with
  charters/queues, not micro-tasks. Decisions lead; corrections/cross-links follow.
- **Sentinels**: `.mathlib-quality/beastmode_active.<worker>` = live claim/focus. Stale
  sentinel + finished ticket = dead session. The BARE `beastmode_active` file is
  last-writer-wins garbage — ignore it. Verify claimed blockers against the board before
  endorsing (sentinels go stale; two stale-blocker catches so far).

## BINDING POLICIES (cite by number)
- **v10.8 RR-only**: BB-RR is the ONLY standing assumable. Every sorry needs a
  proof-terminating plan or a registered gate. `/develop --decompose` is the first act of
  any new stream (verbatim source quotes, PDF page = print + 11 for KM).
- **v10.24 slowdown⟹decompose** (a–e): split slow proofs; heavy defs ship opaque
  interfaces same-commit; variable-first transport lemmas; term-built isos (never
  rw-then-exact); "never let unification meet a concrete ring/scheme — hand it a named
  handle". Four-route wall = long past the stop signal.
- **Fresh-session doctrine** (v10.19/23/66): intricate walls/assemblies go to a FRESH
  full-budget session on an explicit boarded plan — never tail-of-session grinding.
  Precedents: faith-infra, C4-HF-ASSEMBLY, T-BE-TAIL.
- **v10.35b EXTERNAL-QUIET**: no Zulip, no mathlib PRs, no upstream filings. Ledger/PR
  drafts/repros stay internal. Mathlib-PR watching is read-only.
- **v10.52 commit-early cadence**: green increments pathspec-committed immediately.
- **Ops under saturation (v10.46/49)**: single-target builds; no sub-delegates; 30-min
  no-build-progress = stop the delegate and bank its analysis; exit 143 = OOM not failure.
  D2 holds NISOG's grind until THEIR load check clears (~70-75 workers = saturated).
- **B2 protocol**: statement wrong ⟹ hard-stop, b2_log.jsonl, owner(-delegate) approves,
  FILE HOLDER executes the change with verbatim quotes same-commit. Two B2s so far:
  T-E5 affineness (executed); T-H4/T-H6 repoint to KM 7.1.2 quotient problem (APPROVED,
  **still awaiting FP4's execution** — GH's corrected wiring waits on it).
- **DS-register rule**: any def-level sorry gets a plan.md register row + pins,
  same commit. Consumers use pins only.
- **Rule 5**: claim on the board BEFORE touching files; first claim wins; adjudications
  land in inboxes.

## FLEET ROSTER + STATE (as of handover)
| Worker | Charter / current | State |
|---|---|---|
| **c5β** | CHARTER-C5B: owns THE ENDGAME solo. Next session first act = [C4-HF-ASSEMBLY] (v10.66: 5-lemma triple-localization spec) → glue → 0c-i → 0c-ii (board-signal fires A's 0h) → 0h → T-W7.12 → **T-W7a** (`abelEnrichment_exists` by rfl) | between runs; sentinel carries plan |
| **fable-P4** | CHARTER-FP4: the KM 4.7 engine. Geometric core COMPLETE; [a5] at 7 blocks, continuing s/r/t conjugation + stitch. Engine = [a5] + T-A3 from axiom-clean. THEN: the B2 repoint of T-H4/H6 (owed!), then the engine's moduli-functor layer | active |
| **beastmode-A** | T-A3 (a→b→c) by adjudication (v10.68); 0h interrupt armed on c5β's 0c-ii signal; then endgame assist via board handshake with c5β | active; WATCH: resumed once without board-sync (near-race) — inbox rule has teeth now |
| **PIC0** | [GAP1-W-MONO]: scaffold done; the ⊗-stability leaf (surj half → inj half, decompose on fork) → LocalizedMonoidal (WAITS until leaf sorry-free) → un-gates P2 Pic program → DS-END0 pins route (a) | active |
| **p2** | CHARTER-P2: κ-bij crux → Hopf laws → L5/L6/L7 → wire `smul_eq_zero_of_factors` → **Milestone 1 BB-DELIGNE DISCHARGED** → falls-sweep → phase 2 = T-C1-KM28 (Weil pairing). p0's G3d comodule crux consumes p2's Hopf layer (v10.50 edge) | active |
| **D2** | STREAM-NISOG claimed; wave M1 (L3 first) HELD on their own load checks; [T-BE-TAIL] registered residual, same policy; B–E banked 99.5% | holding (correct) |
| **fable-FP** | STREAM-FP done ([A711-FP] discharged, étale flipped general-base); stretch: [KM-FMT-FLAT] (theirs), [NISOG-GRASS] (GrassmannianTransition.lean sits UNCOMMITTED in the tree — nudge commit-early) | active |
| **NEW-Y1** | STREAM-Y1 (was P3b3's): vi assembly → Y1-EASY remainder → ATLAS (iii/v open; ii/vi ride [T-B6′-IFACE] pin) | active |
| **NEW-GH** | SmoothDescent's 3 staged leaves → MellWeierstrass cadence cleanup (incl. golf onto A's projModelVCIso_one). GH stream itself is GATE-BOUND (frontier exhausted; T-H4 fully characterized: ⊥ proven, else refuted) | active |
| **p0** (beastmode-B) | rate-limited. On return: inbox has it — gate-flipped GH leaves or [T-G3d-infra] tail (v10.50 ruling: NO formulation bridge; constant-group via FP's results as-is; subgroup-scheme crux from p2's Hopf layer) | dark |
| **P3b3** | rate-limited. On return: reclaim Y1 at a boundary via handshake; étale-cascade resume trigger = T-B6′ dischargeable (⟸ T-W7.36) | dark |

## THE DEPENDENCY PICTURE (what gates what)
- **T-W7a (the group law over every base)** = c5β's chain + nothing else. It un-gates:
  T-B6/T-B6′ → P3b3's étale cascade (BB-DIFF MASTER → torsionπ_etale → hfix leaf →
  **rigidity closes modulo PIC0 pins**) → T-D8-bridge → Y1's ii/vi; FP4's engine [a5]
  consumes T-W7.1b (already done); [U/G] full-faithfulness; A's T-D6b.
- **The engine (exists_ellipticCurveGeom_quotient)** = [a5] (FP4) + T-A3 (A). Then the
  moduli-functor layer (FP4) → T-E5c → Y(N) via route A + Γ_H (post-B2-repoint).
- **The pins (DS-END0, rigidity's tail)** = PIC0's Pic route (a) via GAP1-W-MONO, OR
  p2's Cartier-duality route (b) — two-route edge, never build duality twice (v10.36).
- **Y₁(N) (T-E7)**: leaf pool live (NEW-Y1); needs T-A3 (smoothness) + the T-B6′ pin
  clearing (⟸ T-W7a) + [T-E4-family]; MASTER bridge closes it by one `exact`.

## IMMEDIATELY OPEN ITEMS FOR YOU
1. **Unresolved investigation (I was mid-check)**: `ForMathlib/GaloisDescentModule.lean`
   has ~40 uncommitted working-tree lines adding a geometric [a3-ii] chart-level lemma
   (imports Pullbacks). FP4 reported it as "sibling edits to MY file" — but the content
   is FP4-subject-matter. RESOLVE: ask FP4 (inbox) whether it's their own uncommitted WIP
   (then commit-early applies) or a foreign edit (then identify the writer — rule-5
   violation). Also in the tree: `_ScratchProbe.lean` (stray, delete-after-confirming) and
   `GrassmannianTransition.lean` (fable-FP's, nudge to commit).
2. **FP4 owes the B2 repoint** (T-H4/T-H6 → KM 7.1.2 quotient problem) — queued after
   the engine; GH's corrected wiring waits on it.
3. **c5β's next session** = C4-HF-ASSEMBLY (the user fires it; opener: "Resume CHARTER-C5B
   at [C4-HF-ASSEMBLY] per v10.66").
4. Owner-pending: nothing except deferred external-quiet items (mathlib PRs list,
   Riou Zulip ping, Lean-core repro) — do NOT resurface unless the owner lifts v10.35b.

## YOUR CYCLE (each activation)
pull → read new Amendments + sentinels (+ inboxes-consumed) → absorb reports → decide
(GO/redirect/adjudicate; board wins over sentinels; evidence over assumption) → write a
vN section + inbox replies → pathspec-commit board+inbox → push → tell the owner ONLY:
the summary, milestones, and any genuinely-owner call. Praise honest walls; enforce
fresh-session for intricate assemblies; never let a worker grind past the stop signal.
