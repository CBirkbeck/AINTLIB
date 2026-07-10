# INBOX: NEW-ATLAS-3 (takeover of the [Y1-ATLAS] charter, 2026-07-10 — read fully before touching anything)
- [2026-07-10, coordinator, v10.107] You inherit [Y1-ATLAS] at the top-glue, after the
  comparison ENGINE (v10.93), T5 (chart packaging + fibre bridges) and the T6 base-glue
  all landed. Worktree EXISTS: `/Users/mcu22seu/Documents/GitHub/aintlib-mc-atlas`
  (branch `dev/modular-curves-y1-atlas`, clean, pushed through `319170881` — both prior
  owner sessions are rate-limited; REUSE it, do NOT re-clone, do NOT touch other
  worktrees).
  READS (in order): (1) this inbox — canonical copy via
  `git fetch origin && git show origin/dev/modular-curves:projects/ModularCurves/.mathlib-quality/inbox/NEW-ATLAS-3.md`
  (your branch's inbox/board copies LAG — v10.86 protocol; re-read at every commit
  boundary); (2) branch-local `projects/ModularCurves/.mathlib-quality/tickets.md`
  §v10.109-ATLAS → v10.111-ATLAS (park recipe, T5 completion, the pinned top-glue plan);
  (3) `decomposition-y1-assembly.md` §[Y1-ATLAS]; (4) `YOneAtlasClassify.lean`'s
  declarations (4,265 lines; the apparatus is ALL there — read signatures, not proofs).
  DELIVERABLE: v10.111-ATLAS NEXT steps 2–5. Step 1 (`projModelBaseChange_projTateMap` +
  `projTateMap_unfold`, YOneAtlasClassify.lean:4145–4167) is ALREADY LANDED as the tip
  commit — resume at step 2: (2) fibre-restriction of `topMap` agrees across charts
  (`pullbackChartIso_hom_bc` def-chase, then step 1 + ENGINE(b)
  `projTateMap_eq_of_pointedIso` with `fibreModelIso` data); (3) E-cover glue
  (`(chartCover Y).pullbackCover Y.curve.π`-style pieces; overlap O^E ≅ pullback of the
  base-overlap by pasting; refine by the affine cover of the base-overlap pulled back
  along π; morphism-ext over that cover ⟹ `coverTopMap_compat`;
  `Scheme.Cover.glueMorphisms`; `ι_glue` equations); (4) clauses — IsPullback via
  isomorphisms-local-at-target on the comparison into `pullback tateπ gluedBaseMap`
  (per-piece `topMap_isPullback` + `ι_gluedBaseMap`), zero_w + pullSection-marking
  cover-locally (`topMap_zero`/`_marking` + `Scheme.Cover.hom_ext`), assemble
  `EllObj.tateClassifyingHomOfOpenCover`, `pullSection = P` via
  `tateClassifyingHom_pullSection_eq`; (5) T7 uniqueness per the v10.109-ATLAS plan
  (f-induced charts + ENGINE pins + `Cover.hom_ext` on both covers +
  `tateClassifyingHom_existsUnique_of_components`). That closes `exists_tatePoint`'s
  ∀-part — the charter's deliverable.
  BAR (v10.88): own proofs complete; ZERO fresh sorries; NO maxHeartbeats; inherited
  sorryAx LISTED + ATTRIBUTED per decl — [T-A6b] (`abelEnrichment_exists`) and [T-B6′]
  (`geomFibrePointAddEquiv.map_add'`) are the DESIGNED trails, not stop signals;
  everything else `[propext, Classical.choice, Quot.sound]` only.
  REUSE FIRST (v10.89 cost model): the landed glue handles (`test_baseMap_agree`,
  `chartAt`/`chartCover`, `coverBaseMap_compat`, `gluedBaseMap` + `ι_`/`_over`),
  ENGINE(a)/(b), the round-trip API (`tateClassifyingHomOfPullbackMap` + compats),
  `EllObj.homPullbackAlongEquiv` (QuotientProblem.lean), `projModelVCIso_map`
  (ModelVariableChange:564) — CHECK before hand-rolling any hom-rebuild or transport.
  DISCIPLINE: rule-5 claim (branch-board section + sentinel
  `beastmode_active.NEW-ATLAS-3`) BEFORE touching files; v10.24(a–e)
  (decompose-don't-grind, opaque interfaces, term-built isos, named handles); v10.52
  commit-early + PUSH each green increment; v10.35b external-quiet; single-target builds
  from the worktree ROOT (`lake build ModularCurves.ModularCurve.YOneAtlasClassify`);
  LSP is live (lean_goal etc.).
  AT COMPLETION: rebase onto `origin/dev/modular-curves-y1` (the base moves), re-verify,
  ONE PR to `dev/modular-curves-y1`, and board `#print axioms` for the key decls
  (`gluedBaseMap`, the glued top map, the `exists_tatePoint` clauses) with the two-trail
  attribution. Report at completion or a post-decomposition wall ONLY (charter mode).
  v10.94 FULL CAPACITY applies: hygiene stays, credit-frugality relaxed. [OWNER-FLW]
  (fibrewise ⟷ locally-Weierstrass) is owner-reserved — consume as pin, never duplicate.
