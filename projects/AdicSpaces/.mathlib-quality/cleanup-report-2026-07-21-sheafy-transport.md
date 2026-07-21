# /cleanup consolidated report — sheafy-transport campaign files (Phase 7)

Run 2026-07-21 → 2026-07-22 on `dev/adic-spaces`. Baseline `79f069da0` (post-campaign linter
pass); delivered in commits `495e6f746` (Phases 0–6) and `c96827443` (Phases 6.5/6.6).

## Scope and headline numbers

| File | Decls processed | Lines before → after |
|---|---|---|
| RingEquivPresheafTransport.lean | 61 | 1093 → 936 (then +helpers/reflow in 6.5) |
| SheafyRingEquivTransport.lean | 3 | 110 → 99 |
| SheafyCompletionModel.lean | 14 | 223 → 202 |
| SpaRationalSubsetCorrespondence.lean | 15 | 417 → 393 |
| **Total** | **~104 (with sibling relocations)** | **net ≈ −290 lines** |

Every declaration got the full Phase-4 protocol: 24-item audit (HAVE scan with drop-tests,
per-line codepoint LINE-PACKING tables, NAMING / STRUCTURE / INEQUALITY hard gates,
five-method mathlib search, per-hypothesis GENERALISE tables with literature briefs on
public decls), per-rule golf pass (1.1–1.20 / 2.1–2.15 / 3.1–3.7), step-back, per-run
verification builds, and gate tables. Verification was Bash-only (targeted `lake build`
+ `lake env lean` probes) because the LSP was build-locked under worker concurrency.

## Outcomes

- **Statements**: every public name/statement token-identical (whitespace repacks only).
  Campaign-frozen endpoints (T2–T7, C0–C1, 8.2(2) lane) byte-checked.
- **Axioms**: every public decl exactly `{propext, Classical.choice, Quot.sound}`
  (one strict shrink: `ringPlus_map_symm_of_map` dropped `Classical.choice`). No sorryAx.
- **Docstrings**: 10 private docstrings relocated to `--` comments (private decls must not
  carry docstrings); 4 missing public docstrings created; 0 comments deleted (proof-strategy
  prose relocated into proof-body signposts where stripped from docstrings).
- **Instance hygiene**: systematic ballast found and removed by drop-test —
  `letI IsTopologicalRing (Localization.Away …)` was droppable at every carrier site in
  SheafyCompletionModel + 2 sites in the transport file; `haveI IsUniformAddGroup` ballast
  at one site. Load-bearing installs (rightUniformSpace section keys,
  `hasLocLiftPowerBounded_faithful`) preserved everywhere.
- **Proof upgrades**: several proofs moved onto better mathlib API
  (`hu.exists_pow_mem_of_mem_nhds`, `Function.Surjective.preimage_subset_preimage_iff`,
  `IsLocalization.ringHom_ext`-term forms, `Completion.ext'` at the literal target); many
  tactic blocks converted to term mode; the T2 keystone membership iff went 35 → 16 lines
  with its Wedhorn `U ∩ W` shape preserved.
- **Walls honored** (all documented campaign defeq walls): one-call `Homeomorph.piCongr` +
  explicit `(W:=)(Z:=)` families; direct-toFun index equivs; RingEquiv-form equational
  lemmas; term-mode application as the reducibility-wall crossing (a worker *proved* the
  pattern: term application of `ext_of_fields` crosses the unreduced-field defeqs that
  defeat `rw` and `simp`).

## Phase 5a (applied)

- `span_eq_top_of_isOpen_span` relocated upstream into Presheaf.lean;
  `RationalLocData.IsRational.span_eq_top` deduplicated to a 1-line application.
- omit-`DecidableEq` probe on `isLimitSheaf_of_isSheafy`: **rejected with evidence** — its
  three field-suppliers require `DecidableEq A` (synthesis failures at 552–554).

## Phase 5b (renames applied; queue marked consumed)

- `ValuationSpectrum.IsAdic.mapRingEquiv` → `_root_.IsAdic.map_ringEquiv` (unshadows the
  root `IsAdic`; snake-case Prop segment; mathlibable candidate for
  `Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology`).
- `finset_image_symm_image` → `finset_symm_image_image` (old name named the OPPOSITE
  roundtrip direction under mathlib grammar; Finset-level `symm_image_image` is a
  mathlib-PR candidate).

## Phase 6 gates (all green)

Axiom probe files (24 endpoints) clean; FJP directory sorry-free; the five frozen FJP
statement types verbatim-intact; regression endpoints present; umbrella
`lake build '«Adic spaces»'` → 3305 jobs, exit 0.

## Phases 6.5/6.6

simplify: 4 grounded findings applied (two shared proof engines extracted as private
helpers — `locMapOfHom_roundtrip`, `presheafValue_eq_id_of_coeRingHom` — a `let` hoist,
a redundant `show`); 8 ungrounded review findings verified false and discarded.
buzz (1000ms budget): **all four files FAST BOARD** — no per-decl elaboration ≥100ms,
zero `maxHeartbeats` overrides in any file, no deferrals needed.

## Residual notes for the owner / fleet (recorded, deliberately not applied)

1. **`span_image_eq_top_of_ringEquiv`** (transport) duplicates
   `FiniteJet.span_image_eq_top` (FJP/FiniteJetFunctoriality.lean:83) at lower generality;
   probe-verified it survives `[Semiring] + (φ : A →+* B)`. Consolidation = lane:generalise
   ticket (home + import-fanout decision).
2. **`imgDatum_mem_rationalOpen_iff` ↔ `imagePieceDatum_mem_rationalOpen_iff`**
   (RelativePieceKeystone.lean:1009) — consolidation candidate, same shape family.
3. **`[NonarchimedeanRing]` binder family**: the Huber→Nonarch instance chain exists
   (`IsHuberRing.nonarchimedeanAddGroup` + priority-100 `ofNonarchimedeanAddGroup`), so the
   overlappingInstances lints are fixable by binder removal — but that is a section-wide
   public-signature design decision; deferred to the owner. Baseline counts unchanged
   (1 transport, 3 sheafy-transport, 11 completion-model).
4. **Ballast-letI sweep**: the `letI IsTopologicalRing (Localization.Away …)` pattern is
   probably ballast in PresheafIdentification.lean / CompletionModelIndependence.lean too —
   fleet drop-test sweep recommended.
5. **`RingOfIntegralElements.congr`** (AffinoidTransport.lean:140) now has zero in-repo
   consumers (the 6.5-era golf removed the last one); kept as a public P2.12 deliverable.
6. **/decompose-proof flag**: `isSheafy_mapRingEquiv`'s gluing branch is 26 lines (> 10-line
   branch bar); further extraction would invert the campaign decomposition — owner's call.
7. **T3 squares**: `hBsub` is derivable from `h` via
   `rationalOpen_mapRationalRingEquiv_subset_of_subset`; auto-filling it would change the
   public signature — record for any future statement thaw.
8. **/generalise (campaign-level)**: A-side `[IsTateRing A]` in the transport sections is
   inherited from `mapRationalRingEquiv`'s Tate-scoped reconstruction; the literature form
   is arbitrary Huber rings — requires re-architecting the upstream transport def.
9. **Instance-form completion transport**: mathlib's `UniformSpace.Completion.mapRingEquiv`
   is the instance-form analogue of `presheafValueRingEquivOfRingEquiv`; adoptable only
   under an instance-migration campaign (project completions run on def-form uniformities).
10. Vendored mathlib under `projects/AdicSpaces/_blueprint/.lake/` pollutes project-wide
    greps — cleanup-ticket candidate.
