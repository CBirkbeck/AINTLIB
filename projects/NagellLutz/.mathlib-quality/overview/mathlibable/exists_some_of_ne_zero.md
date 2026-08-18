# /mathlibable report — `LutzNagell.PID.exists_some_of_ne_zero`

> **Note on target.** This report assesses the **PID-track** copy
> `LutzNagell.PID.exists_some_of_ne_zero` at
> `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:60` (the decl named
> in the task). There is an identical **General-track twin**
> `LutzNagell.LutzNagellTheorem.exists_some_of_ne_zero` at `GeneralMain.lean:40`
> (over `curveQ W`/ℤ instead of `curveK R K W`/a PID). Same statement shape, same
> 2-line proof, same verdict. The refactor plan below covers both.

### Baseline (Phase 0)
- lake build:               ⚠ not run (local build stale per task; reasoned from source — file is on green `main`, decl is sorry-free)
- decl `LutzNagell.PID.exists_some_of_ne_zero`: ✓ resolved at `projects/NagellLutz/LutzNagell/LutzNagellTheorem/PIDMain.lean:60`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  The Lutz–Nagell theorem over PIDs and number fields (generalisation from ℤ/ℚ to a char-0 PID `R` with fraction field `K`).

**Qualified-name verification.** Confirmed from source. File opens `namespace LutzNagell` (PIDMain.lean:35) then `namespace PID` (PIDMain.lean:36); the lemma is `lemma exists_some_of_ne_zero` at line 60. Full qualified name: **`LutzNagell.PID.exists_some_of_ne_zero`** — matches the parsed name in the task.

---

### Statement (Phase 1)

`LutzNagell.PID.exists_some_of_ne_zero` states: for a Weierstrass curve `W` over a char-0 PID `R` with fraction field `K`, let `Q` be a nonsingular affine point on the base-changed curve `curveK R K W` (which is `W.map (algebraMap R K)` — an honest base change, **not** a fork of mathlib's `Point`). If `Q ≠ 0` (the group identity / point at infinity), then `Q` is an affine point: there exist coordinates `x, y` and a nonsingularity proof `hns` with `Q = .some hns`.

Mathematically this is the elementary observation that the only point of the elliptic-curve group that is *not* an affine `(x, y)` point is the point at infinity. In Lean terms it is the **forward destructuring** of the two-constructor inductive `WeierstrassCurve.Affine.Point` (`zero | some`): a non-`zero` element is a `some`.

Variables / typeclasses involved (Lean side):
- `R` : char-0 PID + integral domain (`CommRing`, `IsDomain`, `IsPrincipalIdealRing`, `CharZero`) — but **all four are `omit`ted** for this lemma (PIDMain.lean:57–58).
- `K` : field, `Algebra R K`, `IsFractionRing R K`, `DecidableEq K` — `DecidableEq K` and `IsFractionRing` are **`omit`ted** too.
- `W : WeierstrassCurve R`.
- `Q : Affine.Point ((curveK R K W).toAffine)` — a point on the base-changed curve.

Hypotheses (Lean side):
- `hQ : Q ≠ 0` — `Q` is not the identity / point at infinity.

Conclusion (math): `Q` is an affine point `(x, y)` on the curve.
Conclusion (Lean): `∃ x y, ∃ hns : (curveK R K W).toAffine.Nonsingular x y, Q = .some _ _ hns`.

**Proof body** (PIDMain.lean:63–65), verbatim — 3 lines:
```lean
  rcases Q with _ | ⟨_, _, hns⟩
  · exact absurd rfl hQ
  · exact ⟨_, _, hns, rfl⟩
```
Pure inductive case-analysis: `zero` case contradicts `hQ` via `rfl`; `some` case returns the constructor's own fields.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A one-step destructuring helper lemma — not a named theorem, not a new structure, not a `## Main results` entry. (Literature width is EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 3 substantive lines (a `rcases` + two trivial case discharges).
One-liner verdict: **n/a** — kind is `lemma`, not `def`; the 2b def-exemption table does not apply. (The body is nonetheless a trivial tactic destructuring, which feeds the NO-leaning in Phase 7.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                          | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|------------------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "mathlib WeierstrassCurve Affine Point inductive some zero constructor lemma"                  | yes  | `Point` = `zero \| some (h : Nonsingular x y)` inductive | leanprover-community mathlib4_docs; confirms the 2-constructor inductive. No named forward-destructuring lemma surfaced. |
|  2 | WebSearch (general form)         | (covered by #1 doc page) "type of nonsingular points is an inductive: 𝓞 and affine (x,y)"      | yes  | identity = point at infinity `𝓞`; others affine        | The "fact" is just: non-`𝓞` ⟹ affine. Not a theorem with a name; it is the definitional dichotomy. |
|  3 | WebSearch (named-after / aliases)| "elliptic curve point at infinity identity affine point dichotomy" (group-law literature)       | yes  | ITP 2023 group-law paper (Dagstuhl LIPIcs)            | The group-law formalisation treats `𝓞`-vs-affine purely by case analysis; no named lemma for the forward split. |
|  4 | ChatGPT MCP                      | self-contained Q: standard name? + does Bourbaki-style lib name such a destructuring lemma?    | n/a  | (MCP down — Codex exec failed, as task warned)         | Fell back to source evidence in #5–#10, conclusive for a destructuring lemma. |
|  5 | Local references                 | grep `.mathlib-quality/references/` (NagellLutz) for "point"/"infinity"/"some"                  | n/a  | references dir absent for this project                | recorded n/a. |
|  6 | nLab                             | "elliptic curve point at infinity"                                                             | n/a  | abstract group-law context only                       | nLab has no statement of "non-identity ⟹ affine constructor"; below nLab's granularity (a Lean inductive destructuring). |
|  7 | nCatLab                          | —                                                                                              | n/a  | not a categorical concept                              | This is inductive-type case analysis, not a categorical statement. |
|  8 | Stacks Project                   | "Weierstrass equation point at infinity"                                                       | n/a  | Stacks treats elliptic curves scheme-theoretically; no `Point` inductive | The constructor-level dichotomy is a Lean implementation detail, absent from Stacks' scheme language. |
|  9 | MathOverflow / Math.SE           | "elliptic curve only non-affine point is point at infinity"                                     | yes  | folklore/definitional                                  | Universally treated as definitional ("the projective closure adds exactly one point at infinity"); never a *named* result. |
| 10 | recent arXiv (last 5y)           | "formal proof group law Weierstrass curve" (ITP 2023 et al.)                                    | yes  | case analysis on `𝓞`/affine inline                     | Formalisation papers case-split inline; none isolate a named forward lemma. |

### Literature summary (Phase 3)

Concept identified as: the **point-at-infinity / affine-point dichotomy** for the group of points on a Weierstrass curve — "every point other than the identity `𝓞` is an affine point `(x, y)`". In Lean this is precisely the forward destructuring of the inductive `WeierstrassCurve.Affine.Point = zero | some`.
Sources agree on the standard form: yes — it is **definitional / folklore**, never carrying a theorem name. The projective closure of an affine Weierstrass curve adjoins exactly one point at infinity; everything else is affine by construction.
Most general standard form: for any two-constructor "pointed sum" type `⊥ | ι a`, a non-`⊥` element is in the image of `ι`. Mathlib already ships this generically for `Option` (`Option.ne_none_iff_exists`) and `WithBot` (`WithBot.ne_bot_iff_exists`).
Generality dimensions where the literature varies: none meaningful — the content is fixed by the inductive's shape. The only "dimension" is *which carrier* (`Option`/`WithBot`/`Point`/…); the statement is identical modulo the carrier.
Disagreement with the literature: none. The user's Lean form is exactly the definitional dichotomy, specialised to mathlib's `Affine.Point`.

---

### Generality analysis — `LutzNagell.PID.exists_some_of_ne_zero` (Phase 4)

Literature-standard form (from Phase 3): "a non-identity element of `Affine.Point W'` is a `some`", for an arbitrary Weierstrass curve `W'` over *any* base — no PID / fraction-field structure is used.

| # | Parameter / hypothesis                         | Current Lean form                                                          | Literature-standard form                  | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------------------------|----------------------------------------------------------------------------|--------------------------------------------|---------------------|----------------------------------|
| 1 | base ring `R` is a char-0 PID                  | `CommRing R, IsDomain, IsPrincipalIdealRing, CharZero` (all **omitted**)   | any `CommRing` (and even `Nontrivial` not needed) | yes (already done)  | The lemma already `omit`s `IsDomain`/`IsPrincipalIdealRing`/`CharZero`. None are used: `rcases` on the inductive needs nothing. |
| 2 | the curve is the base change `curveK R K W`     | `Affine.Point ((curveK R K W).toAffine)`                                   | `Affine.Point W'` for *any* `W' : Affine R'` | yes                 | `curveK` and the `R→K` setup are irrelevant — the proof never touches the algebra map. The general statement is over an arbitrary curve over an arbitrary base. |
| 3 | `K` field + `IsFractionRing R K` + `DecidableEq K` | `Field K, Algebra R K, IsFractionRing` (latter two / `DecidableEq` **omitted**) | absent entirely                            | yes                 | None of the `K`-side structure is used; the lemma lives over the *target* curve only. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** — it is bolted onto the specific base-changed curve `curveK R K W` and a PID / fraction-field preamble, none of which the proof uses.
Number of weakening opportunities found: 3 (all collapse to "state it for an arbitrary `Affine.Point W'` over an arbitrary base").
Proposed restatement: the maximally general form is a generic `Point.exists_some : Q ≠ 0 → ∃ x y h, Q = .some h` over any base. **Crucially, regeneralising it does not yield a mathlib-worthy lemma**: the general form is the trivial `Option`-style destructuring, which mathlib handles inline (Phase 6). So the narrowness is a symptom of it being a local convenience wrapper, not of a missing general lemma.
Cost of restatement: CHEAP (the same `rcases` proof works verbatim over any base) — but moot, since the verdict is NO-composable.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                                   | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                         | no       | —                      | The preamble is already plain typeclasses; nothing to bundle. |
|  2 | sequences/metric → filters/topology?                                                        | no       | —                      | No analysis here; pure inductive case-split. |
|  3 | construct an object → universal-property class?                                             | no       | —                      | No construction; it reads off an existing constructor. |
|  4 | set-with-closure-predicate → bundled substructure?                                          | no       | —                      | No substructure. |
|  5 | vector-space/field-specific → weaken typeclasses?                                           | no       | —                      | Already maximally weak (uses no algebra). |
|  6 | 1-categorical → higher-categorical?                                                          | no       | —                      | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary algebraic structure?                                      | no       | —                      | No index. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no**. This is a finite inductive destructuring; there is no contemporary mathlib reformulation that improves its organisation. The most "modern" move is simply to *not have the lemma* and inline `rcases`/`obtain` — exactly what mathlib does in its own `Affine/Point.lean` (≈9 inline `rintro (_ | _)` / `rcases` on `Point`).

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma`. No definitional equalities or typeclass-search paths introduced.

---

### Mathlib search-status: `LutzNagell.PID.exists_some_of_ne_zero` (Phase 5)

[A] Lean-Finder       (offline; substituted by direct mathlib-source grep below)      n/a: tool not available locally
[B] Loogle            pattern `Affine.Point _ → ∃ _, _ = Point.some _` (via grep over mathlib source for `∃.*Nonsingular`, `exists_some`, `eq_zero_or_some`, `ne_zero_iff` in EllipticCurve/*)  no hits — no such forward lemma in mathlib
[C] LeanSearch        "nonzero point on elliptic curve is an affine some point" (web-confirmed via mathlib4_docs)   no hit on a named forward lemma; only the inductive itself + `some_ne_zero`
[D] Grep mathlib src  `some_ne_zero | exists_some | eq_zero_or | ne_zero_iff | ∃.*Nonsingular` over `Mathlib/AlgebraicGeometry/EllipticCurve/`   hits: `Affine.Point.some_ne_zero` (the **converse**, Affine/Point.lean:488), and `Jacobian/Projective.equiv_some_of_Z_ne_zero` (a **different** representation: `Z ≠ 0 ⟹ P ≈ [x/z, y/z, 1]`, not the affine inductive)
[E] Name pattern      `exists_some_of_ne_zero`, `Point.exists_some`, `eq_zero_or_some` over mathlib   no hit (these names exist only in the NagellLutz project)

Searched for both:
  - the user's current form (`Q ≠ 0 ⟹ ∃ …, Q = .some …` on `curveK`) — not in mathlib.
  - the literature-standard / general form (same statement over an arbitrary curve/base) — also not in mathlib. Mathlib provides only the converse `some_ne_zero` (Affine/Point.lean:488) and the *generic* `Option.ne_none_iff_exists` / `WithBot.ne_bot_iff_exists` (Order/WithBot.lean:189), neither of which is the `Point`-specific forward lemma.

Concluded: **found the building blocks** — mathlib's `Affine.Point` inductive + its constructors; the converse `WeierstrassCurve.Affine.Point.some_ne_zero`; and the generic analogue `WithBot.ne_bot_iff_exists` / `Option.ne_none_iff_exists`. The exact forward lemma is **not in mathlib**, and mathlib's own convention is to **inline** the case-split (≈9 occurrences in `Affine/Point.lean`). A single `rcases`/`obtain` derives it.

---

### Call sites — `LutzNagell.PID.exists_some_of_ne_zero` (Phase 6.0)

Internal use count: **3** (within PIDMain.lean, the same file, excluding the declaring line 60). These are *same-file* uses; there are **0 external-to-file callers** of the PID copy.
External-to-file callers: 0 files. (The General-track twin `LutzNagell.LutzNagellTheorem.exists_some_of_ne_zero` in GeneralMain.lean:40 is a **separate, duplicated lemma**, used 3× more in the General track — it is *not* a caller of this PID decl.)

| Caller file:line              | Usage pattern (one-line excerpt)                                          |
|-------------------------------|---------------------------------------------------------------------------|
| PIDMain.lean:97               | `obtain ⟨x', y', hns', hQ_eq⟩ := exists_some_of_ne_zero W hQ_ne`          |
| PIDMain.lean:125              | `obtain ⟨x', y', hns', hQ_eq⟩ := exists_some_of_ne_zero W hQ_ne`          |
| PIDMain.lean:364              | `obtain ⟨x', y', hns', h2P_eq⟩ := exists_some_of_ne_zero W h2P_ne`        |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - **Yes — pervasively, inside mathlib itself**: `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean` performs the identical destructuring inline via `rintro (_ | _)` / `rcases … with … | …` in ≈9 places (e.g. lines 489, 514, 535–536) rather than ever extracting a named forward lemma. Decisive: mathlib's own convention is to inline this case-split.

Composability signal: K = 3 *same-file* internal uses, all of the trivial `obtain … := exists_some_of_ne_zero W h` shape. Per the Phase-6 table this is a "wrapper consumers could inline" pattern; combined with mathlib re-deriving it inline → leans **NO-composable-from-mathlib**.

### Composition check (Phase 6)

Can `LutzNagell.PID.exists_some_of_ne_zero` be derived from mathlib in ≤3 chained calls? **Yes — the lemma's own body IS the ≤3-line composition.**

Attempt 1: inline the case-split at each call site.
```lean
-- replacing `obtain ⟨x', y', hns', hQ_eq⟩ := exists_some_of_ne_zero W hQ_ne`
obtain _ | ⟨x', y', hns'⟩ := Q   -- `rcases`/`obtain` on the mathlib inductive
· exact absurd rfl hQ_ne          -- zero case: contradicts the hypothesis
-- some case: x', y', hns' are in scope and `Q = .some hns'` holds by `rfl`
```
  - Mathlib decls used: the `WeierstrassCurve.Affine.Point` inductive eliminator (`rcases`/`Point.rec`); optionally `Affine.Point.some_ne_zero` for the reverse direction (not even needed here).
  - Result: **succeeds** — a single `obtain` (= 1 destructuring "call") plus a one-line `absurd` discharge.
  - Notes: identical to the lemma body; no new mathematics.

Conclusion: **COMPOSABLE** (a 1–2-line `rcases`/`obtain` destructuring of a mathlib inductive). The composition sketch is the lemma body verbatim.

---

## Verdict: `LutzNagell.PID.exists_some_of_ne_zero`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): the fact is the **definitional** point-at-infinity/affine dichotomy — folklore, never a named theorem; mathlib ships the generic analogue only for `Option`/`WithBot`.
- Generality analysis (Phase 4): STRICTLY NARROWER (bolted to `curveK` + an unused PID/fraction-field preamble) — but generalising yields only the trivial `Option`-style destructuring, not a mathlib-worthy lemma. Modern-idiom: none.
- Mathlib search (Phase 5): not in mathlib; mathlib has the **converse** `WeierstrassCurve.Affine.Point.some_ne_zero` and the generic `WithBot.ne_bot_iff_exists` / `Option.ne_none_iff_exists`; mathlib **inlines** this exact case-split in its own `Affine/Point.lean` (≈9×).
- Composition check (Phase 6): COMPOSABLE — a 1–2-line `rcases`/`obtain` on the mathlib `Affine.Point` inductive; the lemma body *is* the composition.

**Rationale:**

This is a textbook NO-composable case. `WeierstrassCurve.Affine.Point` is a two-constructor mathlib inductive (`zero | some`); the lemma says "a non-`zero` point is a `some`", the forward half of the constructor dichotomy. Its proof is three lines of `rcases` + `absurd` + the constructor fields, and it uses **none** of the surrounding PID / fraction-field / base-change machinery (indeed it explicitly `omit`s `IsDomain`, `IsPrincipalIdealRing`, `CharZero`, `IsFractionRing`, `DecidableEq`). Mathlib deliberately does not carry such per-inductive forward-destructuring lemmas: it provides the generic version only for the `Option`-built types (`Option.ne_none_iff_exists`, `WithBot.ne_bot_iff_exists`), and for bespoke inductives like `Affine.Point` it **inlines** the `rcases` / `rintro (_ | _)` at the point of use — which it does about nine times in `Affine/Point.lean` itself. Adding `exists_some_of_ne_zero` to mathlib would duplicate, at curve-specific granularity, a pattern the library intentionally handles by inlining.

The mathlib building blocks are present and sufficient: the `Affine.Point` inductive's eliminator gives the case split, and (if a reverse direction were ever wanted) `Affine.Point.some_ne_zero` is already there. There is no mathematical content to upstream — only a local ergonomic wrapper the project uses to avoid repeating a two-line `obtain`. The right disposition is to keep it as a private project convenience (or inline it), not to send it to mathlib.

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks; the user's form is a ≤2-mathlib-"call" composition (one `rcases`/`obtain` on the `WeierstrassCurve.Affine.Point` inductive, plus an `absurd rfl hQ` for the impossible `zero` case). No new lemma is warranted because mathlib's own elliptic-curve files re-derive precisely this split inline rather than naming it.

Mathlib building blocks:
- `WeierstrassCurve.Affine.Point` (the `zero | some` inductive) and its auto-generated recursor — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:469`.
- `WeierstrassCurve.Affine.Point.some_ne_zero` (the converse, if ever needed) — `Mathlib/AlgebraicGeometry/EllipticCurve/Affine/Point.lean:488`.
- Generic precedent that this is mathlib's chosen granularity: `WithBot.ne_bot_iff_exists` / `Option.ne_none_iff_exists` — `Mathlib/Order/WithBot.lean:189`.

Composition sketch (≤3 lines). At each call site replace
`obtain ⟨x', y', hns', hQ_eq⟩ := exists_some_of_ne_zero W hQ_ne` with:
```lean
obtain _ | ⟨x', y', hns'⟩ := Q
· exact absurd rfl hQ_ne          -- the `zero` case is impossible
-- in the `some` case: x', y', hns' are in scope and `Q = .some hns'` holds by `rfl`
```
(If a call site needs the equation `hQ_eq : Q = .some hns'` as a term, it is `rfl` in the `some` branch.)

Call sites in our project (from Phase 6.0): **K = 3** (PIDMain.lean:97, 125, 364), all same-file.

Refactor plan: at each of those 3 sites, inline the `obtain _ | ⟨x', y', hns'⟩ := Q` destructuring shown above (the surrounding code already binds `x'`, `y'`, `hns'`, and uses `hQ_eq` only as a rewrite that becomes `rfl`/definitional in the `some` branch — verify the implicit/explicit flow of the curve argument `W`, which disappears since the destructuring is on `Q` directly). Then delete `exists_some_of_ne_zero` from PIDMain.lean. **Caveat for the cleaner:** the General-track twin `LutzNagell.LutzNagellTheorem.exists_some_of_ne_zero` (GeneralMain.lean:40, with 3 further call sites — GeneralMain.lean:67, 99 and GeneralDiscriminant.lean:143) is the *same* lemma duplicated. The dedup/cleanup pass should treat both copies identically: either inline both, or — if a single shared helper is preferred over inlining — collapse the two project copies into one `private` helper in `Common/` rather than upstreaming. Either way it does not go to mathlib.

Next action: delete `LutzNagell.PID.exists_some_of_ne_zero` (and dedup the General-track twin) from the project; inline the 1–2-line `obtain` composition at the 3 (+3) call sites. This is an on-`main` `lane:cleanup` dedup/golf task, not a mathlib PR.

---

## Next step

Delete `LutzNagell.PID.exists_some_of_ne_zero` from the project and inline the `obtain _ | ⟨x', y', hns'⟩ := Q` destructuring at its 3 call sites (PIDMain.lean:97, 125, 364); have the cleanup pass dedup the identical General-track twin the same way. Do **not** open a mathlib PR — the building blocks (`Affine.Point` inductive + `some_ne_zero`) are already in mathlib, and mathlib inlines exactly this case-split rather than naming it.
