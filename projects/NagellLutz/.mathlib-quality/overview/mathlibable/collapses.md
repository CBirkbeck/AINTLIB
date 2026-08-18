# /mathlibable report — `collapses`

**VERDICT: BORDERLINE-needs-human — the input is an enumerator false-positive, not a real declaration. No mathlib action.**

Assessed: 2026-06-21. Source read directly (local build stale; irrelevant — the input does not
elaborate because it is not code).

---

## Phase 0 — Doctor (FAILS at 0b: declaration does not resolve)

```
### Baseline (Phase 0)
- lake build:               not run — stale local build; irrelevant (input is not a declaration)
- decl `collapses`:         ✗ DOES NOT RESOLVE — no such declaration exists anywhere in the repo
- parsed qualified name:    LutzNagell.LutzNagellTheorem.collapses  →  does NOT exist
- kind:                     n/a (not a declaration; it is prose inside a doc-comment)
- has sorry:                n/a
- module docstring summary: GeneralMain.lean proves the generalized Lutz–Nagell integrality
                            theorem for nonzero finite-order points on a general integral
                            Weierstrass curve (coords integral, or order 2 with 4x,8y ∈ ℤ).
```

### What is actually at `GeneralMain.lean:147`

Line 147 sits **inside a `/-! … -/` module-documentation comment**, not a declaration. The block
spans lines 144–148:

```
144  /-! ## Short Weierstrass specialization
145
146  For a short Weierstrass curve `y² = x³ + Ax + B`, the order-2 branch of the general
147  theorem collapses to full integrality: `a₁ = a₃ = 0` forces `ψ₂ = 2y`, so order 2
148  gives `y = 0`, and then `x` is a root of the monic `X³ + AX + B ∈ ℤ[X]`. -/
```

The block opens at line 144 (`/-!`) and only closes at line 148 (`… ∈ ℤ[X]`. -/`). Line 147 is the
wrapped continuation of the English sentence *"…the order-2 branch of the general **theorem
collapses** to full integrality…"*. The `/overview` Step-9 enumerator regex (which keys on a line
beginning with `theorem|lemma|def|…` followed by an identifier) matched the two consecutive English
words **"theorem collapses"** and lifted the token after `theorem` (`collapses`) as a declaration
base name. Classic prose-in-a-docstring false-positive — the comment-range guard the skill's B0/B1
notes call for was not applied at the overview→mathlibable hand-off.

### Independent confirmation it is not a real decl (this run)

Declaration-head grep over the whole project tree:

```
grep -rnE "^\s*(@\[[^]]+\]\s+)*(noncomputable\s+)?(private\s+)?(protected\s+)?(public\s+)?\
(theorem|lemma|def|abbrev|structure|inductive|class|instance)\s+collapses\b" projects/ --include="*.lean"
```

returns **exactly one** line — the prose comment at `GeneralMain.lean:147` — and **no** genuine
`theorem`/`lemma`/`def`/`abbrev`/`structure`/`class`/`instance` named `collapses`. The surrounding
real declarations are visible in the same file: the block of helpers, then the doc-comment 144–148,
then the real `/-- … -/` docstring at 150 and the real `theorem lutz_nagell_integrality_short` at
153. The `LutzNagell.LutzNagellTheorem` namespace (opened lines 20–21) contains **no** member
`collapses`. The parsed `LutzNagell.LutzNagellTheorem.collapses` does not exist.

The mathematical content the sentence *narrates* is genuine and **is** formalized — but as a
properly-named theorem six lines below, at `GeneralMain.lean:153`:

```lean
theorem lutz_nagell_integrality_short (A B : ℤ)
    {x y : ℚ} (hpt : (shortCurveQ A B).toAffine.Nonsingular x y)
    (htor : IsOfFinAddOrder (Affine.Point.some _ _ hpt)) :
    (∃ x₀ : ℤ, (x₀ : ℚ) = x) ∧ ∃ y₀ : ℤ, (y₀ : ℚ) = y
```

"collapses" is just English narration of how the short-Weierstrass branch (`a₁ = a₃ = 0 ⟹ ψ₂ = 2y`,
so order 2 ⟹ `y = 0`, so `x` is an integer root of a monic cubic) specializes the general theorem.

### Bonus check — is Lutz–Nagell in mathlib at all?

`grep -rn "Nagell\|LutzNagell\|lutz_nagell" .lake/packages/mathlib/Mathlib/` → **zero hits**. The
Lutz–Nagell theorem (general or short) is not in mathlib in any form. (Recorded for completeness;
not load-bearing for this verdict, since the input is a phantom.)

---

## Phases 1–7 — N/A (no statement exists to assess)

There is nothing to comprehend (Phase 1), no concept to put through the exhaustive literature
protocol (Phase 3), no parameters to compare against a literature-standard form (Phase 4), no
`def`/`class`/`instance` to risk-assess (Phase 4.5), no Lean form to search mathlib for (Phase 5),
and no composition to attempt (Phase 6). Executing any of these would require **inventing** a
statement for a lemma that does not exist — which the skill's gates forbid (Phase 0: *"we read its
full elaborated type, not a sorry-placeholder … If broken, stop."*). The honest output is the
Phase-0 failure.

Per Phase 0c: *"If zero matches → 'Not found in project. Use the qualified name, or check the
spelling. If you meant a mathlib decl, use /generalise instead.'"* — the assessment terminates here.

---

## Verdict: `collapses`

**Category:** BORDERLINE-needs-human

**Rationale:** `collapses` is not a Lean declaration. It is the English word "collapses" inside the
module doc-comment block at `GeneralMain.lean:144–148` ("…the general **theorem collapses** to full
integrality…"), misread as a declaration head by the `/overview` enumerator (it took the identifier
following the prose word "theorem"). No declaration named `collapses`, nor
`LutzNagell.LutzNagellTheorem.collapses`, exists anywhere in the repo. There is no statement,
type, or proof to assess for mathlib inclusion — so no YES/NO bucket can apply; the only honest
verdict is to flag the bad input to a human.

**Numbered questions / actions for the human (≤5):**
1. Drop `collapses` from the mathlibable work-list / `mathlibable_ledger.tsv` — it is a parser
   artifact, not a declaration. (No mathlib action of any kind.)
2. If the intended target is the theorem the sentence describes, it is
   `LutzNagell.LutzNagellTheorem.lutz_nagell_integrality_short` (`GeneralMain.lean:153`) — re-run
   `/mathlibable lutz_nagell_integrality_short`. Note its sibling
   `lutz_nagell_integrality_general` (`GeneralMain.lean:110`) is the BIG person-named theorem
   (Lutz–Nagell) and is the stronger mathlibable candidate of the two; Lutz–Nagell is **absent from
   mathlib** (grep over `Mathlib/` finds nothing), so one of these two — most likely the general
   form — is the genuine upstreaming question hiding behind this phantom.
3. Harden the `/overview` Step-9 enumerator: skip regex matches that fall **inside** `/-! … -/` or
   `/-- … -/` comment ranges, so a docstring word following the English token "theorem" is never
   lifted as a declaration name.

**Next action:** No mathlib action. Remove `collapses` from the work-list (item 1); optionally
re-aim at `lutz_nagell_integrality_short` / `lutz_nagell_integrality_general` (item 2).
