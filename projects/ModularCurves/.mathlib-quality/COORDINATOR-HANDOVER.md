# COORDINATOR HANDOVER — ModularCurves producer fleet
**Rewritten 2026-07-18 (board state v10.318). Read this top-to-bottom before dispatching anything.**

You are the new coordinator of the **ModularCurves producer fleet** on branch `dev/modular-curves`
(worktree `/Users/mcu22seu/Documents/GitHub/aintlib-modular-curves`). Owner = Chris Birkbeck
(c.birkbeck@uea.ac.uk). The owner fires all worker sessions and relays their reports to you; you
verify-at-source, ratify, adjudicate blockers, maintain the append-only board, and dispatch via the
inbox. You do NOT write Lean — you coordinate.

---

## 1. THE GOAL (unchanged since project start)
Three modular-curve levels representable as schemes: **Y(N)=Γ(N)**, **Γ_H**, **Γ₁(N)-Drinfeld** (plus
the integral full-level **T-H8** and **Γ₀** as a direct construction). All engine-routed levels bottom
out at ONE shared engine `representable_iff` / `representable_iff_rigidNoeth` (EllCategory.lean), which
consumes two concrete instantiations in `Moduli/Bootstrap.lean` (the ℤ[1/3] ℰ₃ problem + the Legendre
problem).

## 2. HEADLINE STATE — verified at source 2026-07-18 (do NOT trust this table without re-verifying via `git show origin:<file>`)
- **ℤ[1/3] engine: DONE.** `naiveLevelThree_representable_by_affine` (Bootstrap) is **sorry-free,
  axiom-clean** {propext, Classical.choice, Quot.sound} — OMEGA closed it this batch (RING-DBL
  `two_zsmul_affineSection` → the bridges → `isE3Datum_of_bridges`). CHARTER-O is TERMINAL.
- **Bootstrap = 1 sorry** (`:222`, the Legendre AX2 = G0's :206 lane). That is the ONLY engine-side sorry left.
- **T-D8 dead both halves** (zero boxes on the rel-rep side); **hLN off the headline** (RigidNoeth
  fibre-detection variant, literal KM 4.7 forms parked as `[T-W7.8-L2-PARKED]`).
- **The headline CONE** (GH's receipts-verified minimal blocking set, board v10.317-GH): exactly
  **(a)** KM's keystone set — `endDual_comp_self` + the 5 EndomorphismDegree generals + `fixesTorsion`;
  **(b)** G0's one Bootstrap sorry (:222); **(c)** the shared engine gate — the two `⇐` wires
  (`representable_of_rigidNoeth_of_torsor` mouth is BUILT, QuotientProblem:1032; the instantiation
  wire stops honestly at the TorsorData-equivariance boundary = O/G work) + the engine theorems.
  ~125 other project sorries are archived as non-blocking (NIsogeny, WeilPairing, ForMathlib parks, shells).
- **Capstone is one command:** `bash projects/ModularCurves/.mathlib-quality/scripts/capstone-receipts.sh`
  (GH built it) — fires the 7 headline receipts + the cone-residual census. Run it the moment the cone empties.

## 3. PER-LEVEL REPRESENTABILITY (verify signatures before quoting)
- **Y(N)=Γ(N)** `gammaBot_representable` — real proof via `representable_iff_rigidNoeth.mpr`, **no hLN**.
  Inherits sorryAx only through the engine (Bootstrap :222) + the qpd chain.
- **Γ_H** `gammaH_representable_of_orderOf` — same, plus the explicit `hH` pin (= KM `endDual` keystone).
- **Γ₁-Drinfeld** `gammaOneDrinfeld_representable` (GammaH:1087) — still `:= by sorry`; ingredients banked
  (rigid ✓ mod `hbound` = keystone; rel-rep ✓); final wiring + hbound + engine.
- **T-H8 integral full-level** `gammaFullDrinfeld_representable` (GammaH:1074) — the long pole; rides KM's
  [KM-W0] wave (F3.mp proven over ℤ[1/N]; integral glue is KM's deep background). Rigid conjuncts are
  FREE-RIDERS (`rigid_of_representable`) — the L2 wall never touches T-H8/T-H9.
- **Γ₀** `exists_gammaZeroSpace` (NIsogeny:3290) — the space is CONSTRUCTED (Hopf-Galois route); its
  geometry refinements are boxed by design (BB-ELLQUOT, DR IV.1). Not engine-routed.

## 4. THE FOUR SEATS — charters + current status (charters live in `inbox/WORK-ORDERS.md`)
- **OMEGA (CHARTER-O): TERMINAL** — ℤ[1/3] engine done. Free for re-charter. Strongest at
  affineSection/coordinate/scheme-dictionary + adapted-model/ω work. Natural next: help G0's :206 spec
  layer (the b↔u adapted-value refinement G0 filed), or take a piece of the T-W7.8/endDual question.
- **G0 (CHARTER-G): MID-BUILD on :206** — the μ₂-torsor scheme glue. Done: funnel (proven),
  SqrtUnitCover, sqrtPair_map (1a), selfPresentation+baseChangeEquiv (1b), sqrtPairMapRingHom (2a).
  Remaining (in its sentinel, verbatim): 2b (Spec-pullback square) → 3 (RelativeGluingData → Z₂ finite
  étale) → 4 (sections-spec, consumes OMEGA's b↔u refinement) → 5 (feed funnel → :222 closes = TERMINAL).
  This is the closest-to-done deep item; keep it firing.
- **GH (CHARTER-GH): ARMED** — independent work exhausted (sweep done, ⇐-mouth built, capstone scripted).
  Legitimately waiting; re-fire it on any of {endDual-landed, :206-closed, cone-empty} to run the receipts.
- **KM (CHARTER-K): AT A DECISION POINT** — see §5. K1 done (bridges, consumed by OMEGA). K2
  (`endDual_comp_self`) decomposed into 5 leaves; blocked on a T-W7.8 ruling. L1 (fibre-bridge) is the
  next build regardless of the ruling.

## 5. ★ THE #1 OPEN DECISION — endDual vs T-W7.8 (the new coordinator's first job)
KM found (source-verified, board v10.317-KM): `endDual_comp_self`'s leaf **L5 (rigidity lift)** needs
arbitrary-base rigidity = the same spreading-out as `RigiditySpreadingOut.isMonHom_of_one_comp_eq'_of_finitePresentation`,
which **is the owner-parked T-W7.8** (sorry). Over REDUCED bases L5 is tractable now
(`hom_ext_of_forall_specPoint`); the non-reduced case needs T-W7.8 unparked.

**The ruling hinges on: do endDual's consumers (hH/hbound → the T-H9 capstone) need endDual over
NON-REDUCED bases, or does reduced/geometric-fibre suffice?**
- **Strong prior it's REDUCED-sufficient (verify first):** the headliners were already moved onto
  `RigidNoeth` (fibre-detection — every consumer detects at geometric fibres, where bases are reduced).
  The same logic that let us park T-W7.8 for the headline rigidity should apply to endDual's rigidity
  lift. IF so → KM builds L1–L4 + L5-reduced, K2 closes, **T-W7.8 stays parked.** Very likely the answer;
  have KM or GH (owns the rigidity chain) verify the consumer hypotheses and rule.
- **Second strategic question worth a scope:** is `endDual_comp_self` even necessary? The Weil-pairing
  gate was avoided TWICE (ζ₃-void, combination-clopen). hH/hbound is a kernel-bound at geometric points;
  `le_endDeg_of_killed_injective` (KernelBound) + the now-complete degree theory (`endDeg_mulBy=N²`
  axiom-clean) may deliver it WITHOUT the full Cayley-Hamilton endDual. If a cheaper route exists, the
  five generals + hH/hbound close far faster. **Scope this before committing KM to the 5-leaf endDual build.**

Other pending owner item: **T-H6 SUSPECT-B2** (`gammaH_representable_of_rigid`, GammaHRep:4128 — Rigid⟹
Representable for the orbit presheaf at H≠⊥ is plausibly false; GH boarded the counterexample shape +
b2_log, v10.314). Owner's call; non-blocking for the headline.

## 6. THE HONEST DYNAMICS (why sessions look short — a coordinator cannot fully fix this)
The owner's frustration (2026-07-18: "nobody worked more than 5 mins") is real to look at, but the
mechanics are: **(1)** the milestone-only reporting protocol makes a seat STOP at each named milestone
even mid-charter; **(2)** the endgame has genuinely serialized — the remaining work is 2 deep builds
(endDual, the :206 glue) + real decision points, and hard math doesn't parallelize past its natural
grain; **(3)** this batch OMEGA actually FINISHED the whole ℤ[1/3] engine and KM correctly STOPPED at a
real decision rather than build on parked sorries — both good outcomes that *present* as short sessions.
What a coordinator CAN do: resolve the T-W7.8/endDual decision so KM isn't idle; keep G0's :206 glue
firing (closest to done); hunt cheaper routes (the Weil-avoidance pattern); set owner expectations that
endDual + the integral T-H8 are genuinely multi-session. What a coordinator CANNOT do: make
`endDual_comp_self` a 30-minute job. Consider relaxing milestone-reporting to "report only at
charter-terminal or a real blocker" if the owner wants fewer, longer-looking sessions.

## 7. MECHANICS (how to run the fleet — load-bearing)
- **Board** = `.mathlib-quality/tickets.md` (append-only, ~600KB — read via grep/sed, NEVER whole).
  Coordinator amendments are `## v10.NNN (date, coordinator) — …`. **Append via `cat scratchfile >>
  tickets.md`, NEVER Edit** (a live worker's concurrent commit races an Edit'd append and clobbers it).
  Commit board `.md` ONLY, via atomic pathspec `git add <exact files>`.
- **Dispatch home** = `inbox/WORK-ORDERS.md` (paste-ready openers/charters — the owner fires these).
  Per-seat banked state = `inbox/STREAM-<SEAT>.md` (append pointers via `printf >>`, same anti-race rule).
- **Sentinels** = `beastmode_active.<SEAT>` (a worker's live claim/FOCUS; they go STALE — verify blockers
  against the board + source, never trust a sentinel's "next" line as current truth).
- **VERIFY-AT-SOURCE (the cardinal discipline):** never ratify a worker's claim from its report. `git
  fetch` then `git show origin/dev/modular-curves:<file>` + grep the actual sorry census / theorem bodies.
- **VERIFY PUSHES via `git ls-remote origin dev/modular-curves`**, NOT the worker's "pushed" claim — a
  worker once reported "all pushed" with 10 commits unpushed in the shared local HEAD (protective-push if
  a terminal worker left them: confirm remote-tip is an ancestor of HEAD = clean FF, then push).
- **NEVER `2>/dev/null` next to a lake/lean command** (guardrail-blocked).
- **SHARED worktree** across worker accounts; a background sync fast-forwards it. `git fetch` + check
  `rev-list --left-right --count` before committing; `git merge --ff-only origin/...` to sync (workers'
  dirty .lean files are theirs — don't commit them).

## 8. STANDING DOCTRINES & RULINGS (do not re-litigate)
- **Charter mode + build-ahead (v10.32, re-asserted v10.313):** each seat gets its ENTIRE remaining
  headline contribution as one charter; a cross-seat block ⟹ switch sub-goals, not terminate; build
  consuming sides turnkey. **Force-concentration corollary (v10.316):** when the project serializes onto
  a few deep builds, put the strongest idle seat ON the critical build (transfer works with a banked
  route + collision guard) rather than leaving it to watch.
- **Register-box / DEDUP:** downstream consumers CONSUME a hard lemma sorried and proceed. When ≥2 seats
  converge on shared substrate, RULE one canonical owner + one file (G0's `TorsionCombination` = scheme
  carrier of record; GH's B2 `pair_generates_iff_combos_ne_zero` = generation criterion of record; GH's
  `FinrankDegenerate` = the fibre-rank engine).
- **RigidNoeth (v10.298):** headliners detect rigidity at geometric fibres → hLN off the headline;
  literal forms parked `[T-W7.8-L2-PARKED]` (EGA IV §8, a real mathlib gap).
- **Weil-avoidance pattern:** any "consumes stream C / Weil pairing" gate is SUSPECT — avoided twice
  (NORM ζ₃-void; AX2 combination-clopen). Scope the avoidance before grinding a Weil route.
- **External-quiet (v10.35b):** no mathlib PRs / Zulip / upstream filings; ForMathlib-worthy results
  (`FiniteFlatRigidity`, `FinrankDegenerate`, `finrank_pullback_comp_fst`, RING-DBL) are flag-only.

## 9. IMMEDIATE NEXT ACTIONS for the new coordinator
1. **Rule the endDual/T-W7.8 question (§5)** — almost certainly "reduced suffices, T-W7.8 stays parked";
   verify the consumer hypotheses and unblock KM. Also scope the cheaper-hH/hbound route.
2. **Keep G0 firing on the :206 glue** (2b→3→4→5) — the last engine-side sorry; when it closes, Bootstrap
   is EMPTY and the engine gate is one wire from open.
3. **Re-charter OMEGA** (terminal) — onto G0's :206 spec-layer support (the b↔u refinement) and/or the
   endDual cheaper-route scope.
4. **Hold GH armed** — fire the capstone script on the first cone-empty signal.
5. When the cone (§2) empties: run `capstone-receipts.sh` → the three-level headline.

The finish is close in COUNT (1 Bootstrap sorry + 7 keystone sorries + the wires) but the keystone
sorries are genuinely deep. The single highest-leverage coordinator move right now is resolving §5.
