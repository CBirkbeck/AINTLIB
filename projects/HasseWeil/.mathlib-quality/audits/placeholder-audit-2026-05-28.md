# Placeholder audit — 2026-05-28

Full project sweep for "rotten placeholders" (the reviewer's round-6 Q5),
prompted by the discovery that `isogOneSub`/`isogSmulSub`/`oneSubFrobeniusIsog`
pair a correct point-map with a fake `pullback := AlgHom.id`, letting false
theorems (`pointCount = 1`, `q² ≤ 4q`) type-check.

Mechanical guard: `.mathlib-quality/audits/placeholder_guard.sh` (run it in CI;
nonzero exit = a new rotten def / vacuous theorem / custom axiom).

## What "rotten" means

`HasseWeil.Isogeny` stores `pullback` and `toAddMonoidHom` as INDEPENDENT
fields with NO enforced compatibility. `Isogeny.degree` is read off the
`pullback`. A definition is **rotten** if its `pullback` field does not
describe the same geometric morphism as its `toAddMonoidHom` — most often
`pullback := AlgHom.id` paired with a non-identity point map (forcing
`degree = 1`), or `pullback := <other>.pullback`.

## Silverman cross-check (verified against the in-repo PDF, not memory)

`HasseWeil/Silverman-Arithmetic_of_EC.pdf`, GTM 106, 2nd ed.:
- **V.1.1 (Hasse)**: `|#E(F_q) − q − 1| ≤ 2√q`. Proof: `E(F_q) = ker(1 − φ)`;
  `#E(F_q) = #ker(1 − φ) = deg(1 − φ)` via **III.5.5** + **III.4.10(c)**
  ("the importance of knowing 1 − φ is separable"); the degree map is a
  positive-definite quadratic form (**III.6.3**) and `deg φ = q`; conclude
  via the Cauchy–Schwarz **Lemma 1.2**.
- **III.6.3 (Cor. 6.3)**: `deg : Hom(E₁,E₂) → ℤ` is a positive-definite
  quadratic form.
- **III.6.2(e)**: `deg φ̂ = deg φ`. **III.6.2(c)**: `(φ+ψ)^ = φ̂ + ψ̂`
  (dual is additive — the fact the parked qf-nonneg Pic⁰ pivot needs).

**Consequence.** The LIVE chain (`hasse_bound_skeleton` → witness-parametric
assembly → genuine `isogOneSub_negFrobenius`) targets EXACTLY these results.
The DEAD chain's `traceOfFrobenius = q` (from the `AlgHom.id` degree-1 lie)
directly contradicts III.5.5 (`deg(1 − φ) = #E(F_q)`).

## Catalogue

### A. Rotten placeholder DEFINITIONS (6)

| # | Definition | Location | The lie | Status |
|---|---|---|---|---|
| 1 | `isogOneSub α` | Endomorphism.lean:72 | `pullback := AlgHom.id`, point map `id − α` ⇒ degree 1 | Strategy-B delete |
| 2 | `isogSmulSub α r s` | Endomorphism.lean:107 | `pullback := AlgHom.id`, point map `r·α − s` ⇒ degree 1 | Strategy-B delete |
| 3 | `oneSubFrobeniusIsog W` | Frobenius.lean:153 | `= isogOneSub (frobeniusIsog W)` | Strategy-B delete |
| 4 | `mulByInt W 0` branch | Basic.lean:246–248 | `n = 0` branch: `AlgHom.id` pullback + zero point map | GUARDED by `n ≠ 0` everywhere; latent |
| 5 | `dualOfPicZeroPullback` | IsogenyBaseChange.lean:148 | `pullback := α.pullback` (α's comorphism, not α̂'s); degree coincidentally right by III.6.2(e) but pullback is wrong | latent (Pic⁰ machinery) |
| 6 | `dualViaPicZero` | Curves/Miller.lean:1771 | wraps #5 | latent |

Notes:
- #4: every degree theorem carries an explicit `n ≠ 0` / `0 < n` guard, so
  `mulByInt 0`'s fake degree never fires. Still a landmine ("unused fields
  become used later" — reviewer). Point-level zero map should use
  `zsmulAddGroupHom 0` directly.
- #5/#6: companion theorems only consume `.toAddMonoidHom` (genuine conjugate
  dual point map), so no false theorem currently fires; but the object's
  `.pullback`/`.degree` are not the dual's. Used only in the Pic⁰ machinery
  feeding the (parked) qf-nonneg pivot.

### B. Vacuous theorems — substantive name/docstring, statement is `True` (5)

| # | Declaration | Location | Name/doc promises | Actually |
|---|---|---|---|---|
| 7 | `frobenius_pullback_coeff_zero` | FormalGroupCorrespondence.lean:312 | "a_π = 0 (Frobenius purely inseparable)" | `: True := trivial` |
| 8 | `one_sub_frobenius_pullback_coeff_one` | FormalGroupCorrespondence.lean:320 | "a_{1−π} = 1 (separable)" | `: True := trivial` |
| 9 | `liftSomePoint_x` | TranslationOrd.lean:1985 | "underlying x is algebraMap xk" | `: True := trivial` |
| 10 | `aut_of_kernel_construction_fails_without_translation_algebra` | PointFix.lean:648 | documentation-as-theorem | `: True := trivial` |
| 11 | (anonymous `example`) | TranslationEvaluation.lean:73 | "Helper 2's targeted statement (signature only)" | `: True := trivial` |

These are less dangerous than the rotten defs (a `: True` theorem cannot be
`exact`'d where real content is expected — it won't type-check), but the names
mislead and should be either proved for real or renamed/removed.

### C. Verified GENUINE (NOT rotten)

- `Isogeny.id` (Basic.lean:150) — id pullback + id point map + degree 1. ✓
- `CurveMap.id` (Curves/CurveMap.lean:53) — CurveMap has only a pullback. ✓
- `mulByInt W n` for `n ≠ 0` (Basic.lean:245) — genuine `mulByInt_pullbackAlgHom`
  (division polynomials; `mulByInt_pullbackAlgHom` body verified real). ✓
- `frobeniusIsog W` (Frobenius.lean:53) — pullback `f ↦ f^q` (genuine) + id point map. ✓
- `isogOneSub_negFrobenius W hq` (AdditionPullback/Frobenius.lean:2725) — genuine
  `addPullbackAlgHom_negFrobenius` pullback + `id − π` point map. ✓
- `addIsog` / `addPullbackAlgHomPair` (AdditionPullback.lean:1044/1036) — genuine
  addition-formula pullback + `α₁ + α₂` point map. This is the `AddIsogData`-style
  constructor the reviewer recommends. ✓
- `oneSubFrob_isogBaseChange W hq` (WireUpPrep.lean:409) — built via `mkBaseChange`
  from the genuine base-changed `(1−π)` pullback + the genuine geometric `1−Frob`
  point map. BOTH fields are real (degree correct, kernel correct); their mutual
  compatibility is the open `[G1]` residual `oneSubFrob_isogBaseChange_toPointMap_eq`,
  honestly `sorry`'d, NOT assumed. ✓ (witness-parametric pattern)
- `mkBaseChange` (IsogenyBaseChange.lean:57) — neutral constructor: takes both
  fields as arguments, soundness depends on the caller. Not itself rotten. ✓
- `degree_eq_of_finrank_eq` (IsogenyBaseChange.lean:92) — witness-parametric. ✓

## Downstream false statements (from the rotten defs)

- `pointCount_eq` (Frobenius.lean) — `#E(F_q) = 1`. FALSE (y²=x³−x/F₅ has 8 pts).
- `traceOfFrobenius_sq_le` (HasseBound.lean) — `q² ≤ 4q`. FALSE for q ≥ 5.
- `hasse_bound`, `hasse_bound_sq` (HasseBound.lean) — built on the above.
B2 entries logged in `.mathlib-quality/b2_log.jsonl`.

## Remediation (reviewer's Strategy B, agreed)

1. Quarantine/rename the dead theorems (`pointCount_eq`, `traceOfFrobenius_sq_le`,
   `hasse_bound`, `hasse_bound_sq`) so no false statement keeps a plausible name.
2. Add `oneSubFrobeniusPointMap := AddMonoidHom.id − (frobeniusIsog W).toAddMonoidHom`
   (+ a `r·α − s` analogue) for the ~150 point-map-only sites.
3. Migrate point-map-only sites to the bare point map.
4. Replace the ~4 degree/pullback sites with `isogOneSub_negFrobenius W hq`.
5. Delete defs #1–#3 once unreferenced; fix #4 (drop the `n=0` AlgHom.id branch
   or document/guard harder); decide #5/#6 (give the genuine dual pullback or
   demote to a `Raw`/quarantined namespace).
6. Resolve the 5 vacuous theorems (prove for real or remove).
7. Keep `placeholder_guard.sh` in CI so this can never recur.

## Guard status (2026-05-28, pre-cleanup)

`placeholder_guard.sh` currently exits 1, reporting the known baseline:
3 rotten defs (#1, #2, #5) + 5 vacuous theorems. After Strategy B + the
vacuous-theorem cleanup, it should exit 0.

## Strategy-B execution log (2026-05-28)

Build stayed green (3019 jobs) at every step.

- **Step 1** — deleted the false-statement dead chain (no live consumers):
  `traceOfFrobenius_sq_le`, `hasse_bound`, `hasse_bound_sq` (HasseBound.lean);
  `pointCount_eq`, `traceOfFrobenius` (def), `pointCount_eq_sub_trace`
  (Frobenius.lean). Kept the genuine `trace_sq_le_four_mul_deg`,
  `abs_le_two_sqrt_of_sq_le`, `pointCount_eq_of_witness`. Commit `2e3f583`.
- **Step 2a** — deleted orphaned dead files `Hasse/Conditional.lean`,
  `Hasse/CascadeValidation.lean` (imported by nobody; placeholder-bound
  `hasse_bound_target`/`hasse_bound_cascade`). Commit (step 2a).
- **Step 2b** — deleted the closed orphaned CoordHom-RouteB island
  `AdditionPullback/PointMap.lean` → `Hasse/WireUpPrep.lean` →
  `Hasse/Unconditional.lean` (the round-5-retracted dead V.1.3 strategy;
  not in the build graph). The salvageable R-level identities A/B/C +
  KE-level chord identities lived in PointMap.lean — preserved in git
  history (≤ commit `20afcf2`); recover into an in-graph
  `FunctionFieldIdentities` module if a future function-field V.1.3 route
  needs them. Commit (step 2b).
- **Step 2c** — deleted `Hasse/A4FamilyBridge.lean` (closed orphan).

**Safety result.** After Step 1, the BUILT project (HasseWeil.lean root
closure) contains NO false *unconditional* theorems. The two
`degree_quadratic_closed` / `isogSmulSub_degree_quadratic_closed` lemmas
that mention a placeholder degree are **witness-parametric** — their
conclusion follows only from an `h_deg_bridge` hypothesis that is
unsatisfiable for the placeholder, so they cannot prove the false identity
unconditionally. Placeholder-projection code sites: 98 → 71.

- **Step 3a** — deleted the periphery placeholder files (all outside the live
  `hasse_bound_skeleton` dependency, decls unused): `DualIsogeny/RouteA.lean`
  (orphan), `Hasse/GaloisNormal.lean` (orphan), `EC/IsogenyFactor.lean` (only
  the root aggregator imported it) + removed its root import. Build 3019 → 3018.

**Grind boundary reached (2026-05-28).** Nine dead/orphan files deleted total
this session (Conditional, CascadeValidation, PointMap, WireUpPrep,
Unconditional, A4FamilyBridge, RouteA, GaloisNormal, IsogenyFactor). All
safely-removable periphery is gone. The remaining placeholder uses (~200
sites: HoleE ~94, Cascade ~46, PointFix ~21, OpenLemmas ~8, SilvermanIV14 ~7,
Endomorphism ~7 = the defs, DegreeQuadraticForm ~5, PoleDivisorFallback ~4,
Differential ~4, L6Witnesses ~2, Frobenius ~2, AdditionPullback/Frobenius ~2,
PoleDivisor2Tor ~2) are inside the **live-connected qf-nonneg / dual-isogeny
subsystem** that feeds `qf_nonneg_skeleton`: GapSpines genuinely imports and
uses `Verschiebung/QthRootRouteB`, which chains into Cascade → HoleE. In these
files placeholder (`isogSmulSub`, `oneSubFrobeniusIsog`) and genuine
(`*_negFrobenius`, `genuineIsogSmulSub`) uses are intermixed, and most
placeholder uses are witness-parametric (conditional, sound — not false).

Removing the placeholder DEFINITIONS from here requires build-verified
per-file migration (delete dead witness-parametric theorems; rewrite live ones
onto `isogOneSub_negFrobenius` / `genuineIsogSmulSub`; re-prove the few that
exploit the placeholder degree-1 via `unfold`). grep-based dead-code detection
is unreliable at this point (decl-name extraction collides with prose in
docstrings), so this phase must use the Lean build/LSP as the oracle, one file
per commit. It is a sustained effort, best run as a dedicated `/beastmode` pass
with a tickets board (one ticket per file in reverse-import order:
HoleE → Cascade → QthRootRouteB → SilvermanIV14/Differential/PointFix →
DegreeQuadraticForm → finally the defs in Endomorphism/Frobenius).

**Remaining (not yet done).** The three placeholder DEFINITIONS
(`isogOneSub`, `isogSmulSub`, `oneSubFrobeniusIsog`) + `mulByInt 0` branch +
`dualOfPicZeroPullback`/`dualViaPicZero` still exist, used at ~71 in-graph
sites across the live qf-nonneg machinery (HoleE, Verschiebung/Cascade,
DegreeQuadraticForm, SilvermanIV14, Differential) and the V.1.3 machinery
(PointFix, L6Witnesses, PoleDivisor*). These uses are point-map (sound) or
witness-parametric (conditional), so they are not *dangerous*, but the user
wants the definitions physically gone. That is a large, delicate file-by-file
migration (some proofs, e.g. in HoleE, exploit the placeholder's degree-1
semantics via `unfold`, so they need re-proving against genuine isogenies),
and is the next tranche of work. The `oneSubFrobeniusIsog`-→-genuine
relocation is import-feasible (no cycles) but breaks the degree-1-exploiting
proofs, so it is not a clean drop-in.

---

## RESOLVED — placeholder elimination COMPLETE (2026-05-29, steps 3g–3k)

The "next tranche" above was executed in full. Every rotten placeholder is gone;
`lake build HasseWeil` is green (3018 jobs) and `placeholder_guard.sh` PASSES
(CHECK 1 / CHECK 3 / CHECK 4 all empty).

| Item | Resolution |
|---|---|
| #1 `isogOneSub` | DEF DELETED (step 3h). Live sites migrated to `isogOneSub_negFrobenius` (genuine 1−π) / `genuineIsogSmulSub`; the scalar cases `isogOneSub_mulByInt` (=[1−n]) kept (genuine division-poly pullback). |
| #2 `isogSmulSub` | DEF DELETED (step 3h). The dead degree-QF chain that consumed it (HoleE 3 + Differential 4 + SilvermanIV14 7 theorems) deleted; `isogSmulSub_mulByInt` (=[rm−s]) kept (genuine). |
| #3 `oneSubFrobeniusIsog` | DEF DELETED (step 3g, pre-this-arc). |
| #4 `mulByInt 0` | REFRAMED (step 3k), not removable: [0] is not an isogeny, so `Isogeny W W` cannot represent it; the n=0 `AlgHom.id` pullback is an unavoidable total-function junk default (Lean `x/0=0` idiom), guarded by n≠0 everywhere, never relied upon. Dead companion `isogDual_zero_of_comp` deleted. |
| #5 `dualOfPicZeroPullback` | DE-PLACEHOLDERED (step 3j): now takes a genuine `dual_pullback` witness instead of the fake `α.pullback`; `dualViaPicZero` supplies the candidate dual's real `α_dual.pullback`. Point-level theorems untouched. |
| #6 `dualViaPicZero` | resolved with #5. |
| #7,#8 Frobenius pullback-coeff `True` | DELETED (step 3i). Genuine facts live in `OmegaPullbackCoeff`. |
| (3 more vacuous `True`) | DELETED (step 3i): `example` in TranslationEvaluation, `liftSomePoint_x`, `aut_of_kernel_construction_fails_without_translation_algebra`. |
| NEWLY FOUND (audit had missed it) | `dual_additivity_for_one_sub_pi` exhibited a fake `{ pullback := [deg(1−π)].pullback, … }` witness (wrong degree for `1−V`) under a sorry hiding an impossible goal. Replaced with a clean single `sorry` (existence is genuinely true by III.6.2(c)). Surfaced by the hardened guard (step 3k). |

The qf-nonneg core was rewired honestly, not deleted: `HasseOpenLemmaPack`'s
`l8_deg_qf` + `l8z_qf_zero_isogeny` (both stated via the placeholder) collapsed
to one placeholder-free `l8_qf_nonneg : 0 ≤ q·r²−tr·rs+s²`, and `witness_qf_nonneg`
no longer launders through the placeholder's fake degree-1 — it is now a single
honest `sorry` for the genuinely-open Silverman III.6.3 positive-definiteness.

**Guard hardening (never-again).** `placeholder_guard.sh` CHECK 1 now also flags
branch-hidden `then/else/=> AlgHom.id` (allowlisting only the documented
`mulByInt` n=0 default) and treats any `pullback := <x>.pullback` outside
comp/base-change as a violation. This is what surfaced the missed
`dual_additivity_for_one_sub_pi` fake witness.

**Residual (honest, non-rotten).** `l12b_basechange_degree`
(`∃ d, d = α.degree`, proved `⟨α.degree, rfl⟩`) is a content-free but
definitionally-true marker field, honestly documented — not a rotten placeholder
(cannot enable a false theorem). All remaining `sorry`s are genuine open
mathematics (V.1.3, the III.6.3 qf-nonneg, the open lemmas), not placeholder
laundering.
