# COORDINATOR HANDOVER — ModularCurves producer fleet
*Written 2026-07-10 (board v10.115) by the outgoing coordinator. Supersedes the 2026-07-09
edition. Read this fully, then `tickets.md` Amendments **v10.94 → end** (v10.94 is the
owner's full-capacity directive; everything before it is context, not orders). You are the
fleet's coordinator, with owner-delegated authority over dispatches, adjudications, and B2
approvals.*

## THE GOAL (owner, binding)
**Modular curves ASAP**: construct Y₁(N), Y(N), Γ_H as representing objects of the
elliptic-curve moduli problems. Modular forms are SHELVED (ω/T-E-OMEGA demoted to
on-demand). Priority ranking: **Y1 > YFULL > GH > NISOG** (v10.37, restored in full at
v10.94).

## HOW THE SYSTEM WORKS
- **The board is the record**: `tickets.md`, append-only Amendments sections at EOF.
  Workers self-number too — collisions get letter suffixes. You are at **~v10.115**; check
  the tail before numbering (workers had reached v10.114 independently).
- **Append discipline** (races with live workers): write your section to a scratch file,
  `git pull --rebase --autostash`, `cat scratch >> tickets.md`, pathspec-commit ONLY the
  files you own (board + inboxes), push with a pull-rebase fallback. **NEVER `git add`
  broadly** — sibling worktree edits are live WIP. (Run the append from the repo ROOT; a
  `cd` into `.mathlib-quality/` plus a repo-relative path is a silent foot-gun.)
- **THE INBOX PROTOCOL (v10.69)**: dispatches/redirects/adjudications go to
  `.mathlib-quality/inbox/<worker>.md`, committed+pushed. Workers pull + read inbox + new
  Amendments at session start and every commit boundary. Reports flow board-ward; you POLL
  the board each activation. Off-branch workers (ATLAS) read the canonical copy via
  `git show origin/dev/modular-curves:…/inbox/<worker>.md` — their branch copies lag (v10.86).
- **Charter mode (v10.32)**: each worker holds a multi-session charter and reports ONLY at
  named milestones, post-decomposition walls, B2 events, or completion. Respond with
  charters/queues, not micro-tasks.
- **Sentinels**: `beastmode_active.<worker>` = live claim/focus, and they are *current* —
  read them every activation; several times now a worker's relayed report was already
  superseded by their own pushed work. The BARE `beastmode_active` file is
  last-writer-wins garbage — ignore it.
- **THE OWNER IS THE SESSION-FIRING MECHANISM.** Workers only read inboxes once running.
  **Every dispatch to a parked/ended worker MUST come with a paste-ready opener** in your
  reply to the owner (identity + worktree/branch + "pull, read inbox + board tail +
  sentinel" + first act with policy citation + stop-lines + discipline one-liner).
- **The owner wants a small digest after each batch of relayed reports**: what moved, what
  it means for Y₁(N)/Y(N)/Γ_H, what (if anything) needs them. Lead with the headline.

## BINDING POLICIES (cite by number)
- **v10.8 RR-only**: BB-RR is the ONLY standing assumable. Every sorry needs a
  proof-terminating plan or a registered gate. `/develop --decompose` is the first act of
  any new stream (verbatim source quotes; PDF page = print + 11 for KM).
- **v10.24 slowdown⟹decompose** (a–e): split slow proofs; heavy defs ship opaque
  interfaces same-commit; variable-first transport lemmas; term-built isos (never
  rw-then-exact); "never let unification meet a concrete ring/scheme — hand it a named
  handle". Four-route wall = long past the stop signal.
- **v10.115-a term-mode-as-probe** (NEW): when a tactic goal drowns in clothing
  (`.toFun`-composites, `AddMonoidHom.mk'`-internals), run the term-mode proof *as a probe
  to learn the evaluated goal shapes*, then return to tactics with a `show` of that form.
  Companion to v10.24, not a replacement. (This is how PIC0 closed [G1-NAT′].)
- **Stop-lines work — keep issuing them.** When you dispatch a wall-attack, name the route
  AND the iteration budget (3–4 measured iterations), then hard-stop + delta-ledger. Two
  for two so far: PIC0's 10-iteration wall shrank a level in 4, then closed in the next.
- **Fresh-session doctrine (v10.19/23/66)**: intricate walls/assemblies go to a FRESH
  full-budget session on an explicit boarded plan — never tail-of-session grinding.
- **v10.35b EXTERNAL-QUIET**: no Zulip, no mathlib PRs, no upstream filings. Ledger/PR
  drafts/repros stay internal. Mathlib-PR watching is read-only.
- **v10.52 commit-early cadence**: green increments pathspec-committed + pushed immediately.
- **B2 protocol**: statement wrong ⟹ hard-stop, `b2_log.jsonl`, owner(-delegate) approves,
  FILE HOLDER executes with verbatim quotes same-commit. (Both prior B2s are executed; the
  T-H4/T-H6 repoint to KM 7.1.2 is DONE — no B2 debt outstanding.)
- **DS-register rule**: any def-level sorry gets a plan.md register row + pins, same commit.
  Consumers use pins only.
- **Rule 5**: claim on the board BEFORE touching files; first claim wins; adjudications land
  in inboxes. **Shared-worktree collisions** (v10.108, the fleet standard): if another
  worker's edit window is open on a file you need, *wait it out with a background watch and
  draft ahead* — never touch foreign WIP.
- **Owner-reserved: [OWNER-FLW]** (fibrewise ⟷ locally-Weierstrass equivalence, an
  owner-run codex worker). Consume as a pin at integration; no lane duplicates it.

## FLEET ROSTER + STATE (as of v10.115)
| Worker | Charter / current | State |
|---|---|---|
| **c5β** | CHARTER-C5B, THE ENDGAME solo. ★★ [C6] COMPLETE (`mulModelHom_specPoints` for every elliptic curve). Now [0c-i] = T-G1..T-G5: T-G1 + T-G3-comm landed, **T-G3-assoc drafted, iterating** → 0c-ii (board-signal fires A's 0h) → 0h → T-W7.12 → **T-W7a** | active |
| **fable-P4** | CHARTER-FP4 Phase B (moduli-functor layer on the axiom-clean KM 4.7 engine). B0+B1+B2a/b landed axiom-clean; **B3 central assembly in flight** (agent; flagged sub-question: torsor-quotient morphism-descent). Then **B4 = T-E5c**, **B5 = Y(N) + Γ_H** | active |
| **NEW-HOPF** | CHARTER-HOPF (the Γ_H/Γ₀ enabler). Hopf–Galois theorem PROVEN (03BM). Wave C: C2 ✓ C1a ✓ C1b ✓ **C1c-ii ✓** (`chartCoaction : B →ₐ[R] B ⊗[R] A`); [HG-C1c-0] structure maps ✓. Next: Over-S lifts + GrpObj instance → C1c diagrams (counit/coassoc) → C1d → C3 → C4 → pins → **BOARD-SIGNAL** (arms NISOG L6 + p0 pickup) | active |
| **PIC0** | Route G to **Pic(f)**. B1 ✓ B2 ✓ **G1 ✓ (axiom-clean)**. G3 re-anchored on mathlib presentation machinery (five-lemma superseded). Next: **[G3-pre]** → [G3] → A → Pic(f) (GME 2.16) | at boundary; needs an opener |
| **NEW-ATLAS-3** | [Y1-ATLAS] — chartered, **not yet fired**. Own worktree `~/Documents/GitHub/aintlib-mc-atlas`, branch `dev/modular-curves-y1-atlas` (clean, pushed 319170881). Executes v10.111-ATLAS steps 2–5 → `exists_tatePoint` ∀-part → ONE PR → axioms board | dark; opener ready |
| **D2** | STREAM-NISOG. [L1]/T-SG3 ✓, **[L5] ✓** (`generatorSpace_baseChange`, KM 6.1). Now [T-SG3-LFP] arc (LFP-1..5, executing LFP-1). L6 waits on NEW-HOPF's signal | active |
| **fable-FP** | [02KL-CORE] `/develop --decompose` in progress (substrate survey, source tags 10.168.1 / 35.3.6). Also holds [KM-FMT-FLAT], [NISOG-GRASS] | active |
| **NEW-GH** | Parked clean at [02KL] (5466cda51). Inbox self-fires: **[02KM]** (closes [YF-QSM]) → MellWeierstrass tail → home GH stream ([A711-BC] check first, then corrected T-H4/T-H6 wiring + gate-flipped leaves) | parked; no new text needed |
| **beastmode-A** | T-A3 done (proven — the wiring was missing). Holds the **pre-merge holder-look on the codex branch** (v10.110): Comparison.lean +202 duplication verdict; WeierstrassAtlas +73 drop for-cause?; PoleSheaf vs PoleFiltration glance | active |
| **NEW-Y1** | STREAM-Y1 assembly; also carries the HG-C1c commits. On the atlas PR: integrate + one-`exact` into `exists_tatePoint` + MASTER prep | active |
| **p2** | CHARTER-P2: BB-DELIGNE affine core (L6c crux proven in scratch; dualPt_unit/injective → Ψ → finrank=N → Deligne assembly) | active |
| **p0, P3b3, NEW-ATLAS, NEW-ATLAS-2** | rate-limited / superseded. Reclaim only by rule-5 boundary handshake; inboxes carry their orders | dark |

## THE DEPENDENCY PICTURE (what gates what)
- **Y₁(N) (T-E7)**: representability half **COMPLETE** (v10.89). Remaining = the ATLAS
  classifying clause (`exists_tatePoint`'s ∀-part — NEW-ATLAS-3, pure plumbing, one
  session) + retiring two *designed* sorry trails: **[T-A6b]** (`abelEnrichment_exists`,
  becomes `rfl` at **T-W7a**) and **[T-B6′]** (via P3b3's étale cascade + PIC0's pins).
  MASTER bridge then closes it by one `exact`.
- **T-W7a (the group law over every base)** = c5β's chain, nothing else. Un-gates: T-A6b;
  T-B6/T-B6′ → étale cascade (BB-DIFF MASTER → torsionπ_etale → rigidity closes modulo
  PIC0 pins) → T-D8-bridge → Y1's ii/vi; FP4's [B3] EllObj wiring; [U/G] full-faithfulness.
- **Y(N) + Γ_H** = FP4's Phase B: B3 → B4 (T-E5c) → B5. Γ_H additionally consumes
  NEW-HOPF's Wave C pins (quotient by H).
- **The pins (DS-END0, rigidity's tail)** = PIC0's route G to Pic(f), OR p2's
  Cartier-duality route — two-route edge, never build duality twice (v10.36).

## IMMEDIATELY OPEN ITEMS FOR YOU
1. **Three owner-relays outstanding** (the owner fires sessions; give them the openers):
   **NEW-ATLAS-3** (chartered, never fired — the single highest-value session available:
   it finishes Y₁'s last big subtree); **PIC0** (opener must now say **[G3-pre]**, not the
   stale [G1-NAT′]); **the codex/[OWNER-FLW] worker** (push the rebased branch —
   origin still has the old tip 43660b2bd — then ONE PR → `dev/modular-curves`, plus the
   standing cadence rules: rebase+read-board each session, push every increment, small PRs,
   claim before building).
2. **The codex merge is yours to call** once beastmode-A boards its holder-look verdict
   (v10.110). Rules already set: PoleSheaf's 9 `maxHeartbeats` raises = registered debt, not
   a blocker; **do NOT delete `codex/fibrewise-weierstrass-comparison-pre-rebase`** (ca22ffd12)
   — the pullback-tensor map-layer PIC0 adapts at integration lives only there; at
   integration, retarget G3/A onto their `pullbackTensorObjHom` and dedup the B-chain doubles
   (recommend: keep their data-level oplax def, graft PIC0's rfl-coherence proofs).
3. **Watch for the NEW-HOPF BOARD-SIGNAL** on pin-discharge — it releases D2's L6 and p0's
   pickup. Both are armed; you just have to notice and dispatch.
4. **No B2 debt, no owner-pending items** except deferred external-quiet ones (mathlib PRs,
   Riou Zulip ping, Lean-core repro) — do NOT resurface unless the owner lifts v10.35b.

## YOUR CYCLE (each activation)
`git pull` → read new Amendments + **sentinels** (they're current; relayed reports may be
stale) → absorb reports → decide (GO/redirect/adjudicate; board wins over sentinels;
evidence over assumption) → write a vN section + inbox replies → pathspec-commit
board+inbox → push → tell the owner: the digest, the milestones, any genuinely-owner call,
**and a paste-ready opener for every parked worker you dispatched**. Praise honest walls;
issue stop-lines with routes; enforce fresh-session for intricate assemblies; never let a
worker grind past the stop signal.
