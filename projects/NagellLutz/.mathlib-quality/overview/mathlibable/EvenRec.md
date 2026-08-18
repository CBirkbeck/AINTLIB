# /mathlibable report — `IsEllSequence.evenRec`

## Verdict: **NO-mathlib-has-it** — byte-identical decl is in OPEN mathlib PR #13155
(human-judgment caveat below: the PR is long-stalled; a human may reclassify to YES if upstream is dead)

- **Qualified name:** `IsEllSequence.evenRec`
- **Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:651`
- **Kind:** `lemma` (theorem)
- **Date:** 2026-06-18
- **Pinned mathlib:** `d90090f647ca` (Lean `v4.31.0-rc2`)

---

### Baseline (Phase 0)
- lake build: not run (local build stale per task brief; reasoned from source + live mathlib docs + PR-diff read).
- decl `IsEllSequence.evenRec`: ✓ resolved at `…/EllipticDivisibilitySequence.lean:651`.
- has sorry: no.
- module docstring: "Elliptic divisibility sequences (EDS)" — header `Copyright (c) 2024 David Kurniadi Angdinata`,
  i.e. a **vendored extension of mathlib's own EDS file** (Angdinata authors the upstream file).

**True qualified name confirmed.** `evenRec` is declared inside `namespace IsEllSequence` (opened L643, closed
L702) under `variable (ell : IsEllSequence W)` + `include ell`. Hence
**`IsEllSequence.evenRec (ell : IsEllSequence W) (m : ℤ) : EvenRec W m`**. (The task's parsed guess
`IsEllSequence.evenRec` is correct.)

---

### Statement (Phase 1)

`IsEllSequence.evenRec`: **every elliptic sequence satisfies the even-term doubling recurrence.** For a
commutative ring `R` and `W : ℤ → R` with `IsEllSequence W` (the three-index elliptic relation
`W(m+n)W(m−n)W(r)² = W(m+r)W(m−r)W(n)² − W(n+r)W(n−r)W(m)²` ∀ m,n,r), and every `m : ℤ`, the proposition
`EvenRec W m` holds, where

```
EvenRec W m  :≡  W(2m)·W(2)·W(1)² = W(m)·( W(m−1)²·W(m+2) − W(m−2)·W(m+1)² )
```

— Ward/Shipsey's even-index doubling recurrence (in the normalised `W(1)=W(2)=1` case it is the textbook
`h_{2n} = h_n(h_{n+2}h_{n−1}² − h_{n+1}²h_{n−2})`).

- Variables (Lean): `R` `[CommRing R]`; `W : ℤ → R`; `m : ℤ`.  Hypothesis: `ell : IsEllSequence W`.
- Conclusion (Lean): `EvenRec W m`.

**Proof body (one line):** `(rel₃_iff_evenRec W m).mp (ell _ _ _)` — specialise the elliptic relation at
`(m+1, m−1, 1)` and rewrite through `rel₃_iff_evenRec : Rel₃ W (m+1) (m−1) 1 ↔ EvenRec W m`.

---

### Size classification (Phase 2a)
**SMALL** — a one-line forward-direction bridge lemma ("elliptic ⇒ even recurrence"); a corollary of the
`Rel₃`/`EvenRec` infrastructure, not a named theorem or new structure. (Literature width still run exhaustively.)

### One-line check (Phase 2b)
Body: **1 substantive line**. Kind is `lemma`, so the def-exemption table is n/a (a `lemma` has no defeq/diamond
surface). Note: it is a 1-call composition of `rel₃_iff_evenRec` + the `IsEllSequence` hypothesis — independently
biases toward a NO bucket.

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| # | Channel | Query | Hit? | Standard form | Notes |
|---|---------|-------|------|---------------|-------|
| 1 | WebSearch (specific) | "elliptic divisibility sequence even odd recurrence W(2m) Ward formula division polynomial" | yes | even: `h_{2n}h_2 = h_n(h_{n+2}h_{n−1}² − h_{n+1}²h_{n−2})` (n≥3); odd: `h_{2n+1}=h_{n+2}h_n³−h_{n−1}h_{n+1}³` | matches `EvenRec`/`OddRec` exactly (project retains the `W(1)²`,`W(2)` normalising factors). arXiv math/0402415, 1909.12654, Wikipedia EDS |
| 2 | WebSearch (general / nets) | "Stange elliptic nets recurrence relation rel4 net definition" | yes | Stange net relation `W(p+q+s)W(p−q)W(r+s)W(r)+…=0`; rank-1 nets = EDS | arXiv 0710.1316 (Stange) — exactly the `EllSequence.net` def in this file |
| 3 | WebSearch (named-after / mathlib) | "mathlib4 IsEllSequence Rel₃ elliptic nets Stange Angdinata" | yes | mathlib `IsEllSequence` = three-index elliptic relation; theory Ward/Stange; Angdinata = formaliser | mathlib4_docs EllipticDivisibilitySequence |
| 4 | ChatGPT MCP | (down per brief) | n/a | — | substituted by live-docs WebFetch (Phase 5) + PR-diff read — stronger evidence than a model opinion here |
| 5 | Local references | `ls .mathlib-quality/` | n/a | — | no `references/` dir (only `overview/`) |
| 6 | nLab | "elliptic divisibility sequence" | n/a | — | not an nLab topic; canonical sources Ward(1948)+Stange(2007), covered by #1–#2 |
| 7 | nCatLab | — | n/a | — | not categorical |
| 8 | Stacks Project | — | n/a | — | no EDS/division-polynomial-recurrence chapter in Stacks |
| 9 | MathOverflow/MSE | (via #1: arXiv 0803.0728, eprint 2008/444) | yes | confirms even/odd recurrences are the standard doubling formulas | — |
| 10 | recent arXiv (≤5y) | "On Elliptic Sequences over Commutative Rings" | yes | arXiv 2604.05280 — EDS over arbitrary `CommRing`, same elliptic relation | confirms the un-normalised `CommRing` formulation (with `W(1)`,`W(2)` factors) is the modern standard |

### Literature summary (Phase 3)
Concept: **the even-index doubling recurrence of an elliptic (divisibility) sequence** (Ward; Shipsey; Stange's
nets, rank-1 case). Sources agree on the standard form — **yes**; WebSearch #1 returned `EvenRec` essentially
verbatim. Most-general standard form = "an elliptic sequence over a commutative ring satisfies the even
recurrence", exactly what the lemma states. Generality range: ℤ-sequences (Ward) → arbitrary `CommRing`
(arXiv 2604.05280, mathlib); the project already uses the maximal `CommRing`. Disagreement with literature: **none**.

---

### Generality analysis (Phase 4)

Literature-standard form: "`W : ℤ → R`, `R` commutative ring, `IsEllSequence W → ∀ m, EvenRec W m`."

| # | Parameter / hypothesis | Current | Literature-standard | Weaker? | Reason |
|---|------------------------|---------|---------------------|---------|--------|
| 1 | `[CommRing R]` | comm. ring | comm. ring | NO | the recurrence is a polynomial identity; `CommRing` is the maximal standard generality (mathlib's `IsEllSequence` itself uses it) |
| 2 | `(ell : IsEllSequence W)` | elliptic relation | elliptic relation | NO | it is exactly the defining hypothesis |
| 3 | `(m : ℤ)` | integer index | integer index | NO | EDS are intrinsically ℤ-indexed |

**Generality verdict (4b): MAXIMALLY GENERAL.** 0 weakenings; it sits at mathlib's chosen generality (it consumes
mathlib's `IsEllSequence` over `CommRing`).

**Modern-idiom check (4c): no modern idiom available.** All 7 rows = no — finite polynomial identity, no
filter/topology/universal-property/substructure/typeclass-weakening/categorification/index-generalisation move
applies. It is already mathlib's exact form (vendored). One-line reason: thin specialisation of mathlib-style
`IsEllSequence`; no reformulation improves organisation.

### Diamond/defeq risk (Phase 4.5)
n/a — kind is `lemma`.

---

### Mathlib search-status: `IsEllSequence.evenRec` (Phase 5)

[A] Lean-Finder    "elliptic sequence even recurrence W(2m)"  n/a locally (index offline); compensated by [D]+[E]
[B] Loogle         `IsEllSequence _ → EvenRec _ _`            no hits — symbol `EvenRec` absent from mathlib
[C] LeanSearch     "elliptic sequence satisfies even doubling recurrence"  no hit in published mathlib
[D] Grep mathlib src  `EvenRec|evenRec|OddRec|oddRec|Rel₃|EllSequence.net|rel₄` over `.lake/packages/mathlib/Mathlib/`  → the ONLY `EvenRec` hit is the unrelated `Nat.evenOddRec` recursor in `Data/Nat/EvenOddRec.lean`. The pinned EDS file (547 lines) has `IsEllSequence`,`IsDivSequence`,`IsEllDivSequence`,`.smul`,`preNormEDS*`,`complEDS*`,`normEDS*` — and **no** `Rel₃`/`OddRec`/`EvenRec`/`net`/`evenRec`.
[E] Live mathlib docs (master) — WebFetch of mathlib4_docs EllipticDivisibilitySequence: "Rec" decls are only `normEDSRec'`,`normEDSRec`,`complEDSRec'`,`complEDSRec`; **no** `EvenRec`/`OddRec`/`evenRec`/`Rel₃`/`net`. `IsEllSequence.evenRec` **does not exist** on the page.

Searched both forms (user's `IsEllSequence.evenRec` and the general `IsEllSequence → EvenRec`).

**Concluded: NOT in published mathlib (neither pinned `d90090f` nor current master) — BUT the byte-identical
declaration is in an OPEN mathlib PR.** `gh pr list leanprover-community/mathlib4` surfaced:

- **PR #13155** — *"feat(NumberTheory/EllipticDivisibilitySequence): show elliptic relations follow from even-odd
  recursion"*, author **Junyan Xu (`alreadydone`)**, branch `EllNet_from_evenOdd`, **OPEN (non-draft)**, created
  2024-05-24, last updated 2024-08-27. Its diff contains, verbatim: `def Rel₃`, `def OddRec`, `def EvenRec`,
  `rel₃_iff_oddRec`, `rel₃_iff_evenRec`, `rel₄_iff_evenRec`, `rel₄_of_anti_oddRec_evenRec`,
  `rel₄_of_oddRec_evenRec`, `IsEllSequence.of_oddRec_evenRec`, and at **diff line 587**:
  `lemma evenRec (m : ℤ) : EvenRec W m := (rel₃_iff_evenRec W m).mp (ell _ _ _)` — **identical to the project's
  L651**, same `namespace IsEllSequence`, same `variable (ell …)`.
- **PR #25989** — *"add elliptic nets"* (`Multramate:EllipticNet`, OPEN 2025-06-16) — the `net`/`rel₄`/Stange layer
  of the same file.

So `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` is a **vendored copy of mathlib's EDS file
extended with the (still-open) PR #13155 + #25989 development**, ahead of the pinned commit `d90090f`.

---

### Call sites — `IsEllSequence.evenRec` (Phase 6.0)

Internal use count (NagellLutz, excluding L651): **2**
- L692 — `(fun _ _ ↦ ell.evenRec _)` (feeds `rel₄_of_oddRec_evenRec` inside `IsEllSequence.rel₄`)
- L1226 — `ellW.evenRec … ellU.evenRec` (Map / divisibility section)

External copies (same vendored file, separate project):
- `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:570` — `(fun _ _ ↦ ell.evenRec _)`
- `…/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:695-696` — `ellW.evenRec … ellU.evenRec`

| Caller file:line | Usage pattern |
|------------------|---------------|
| NagellLutz/…/EllipticDivisibilitySequence.lean:692 | `(fun _ _ ↦ ell.evenRec _)` |
| NagellLutz/…/EllipticDivisibilitySequence.lean:1226 | `…, ellW.evenRec, h1, h2, ellU.evenRec]` |
| HasseWeil/…/Auxiliary/EllipticDivisibilitySequence.lean:570 | `(fun _ _ ↦ ell.evenRec _)` |
| HasseWeil/…/Auxiliary/EllipticDivisibilitySequence.lean:695 | `…, ellW.evenRec, h1, h2,` |

Inline-derivation grep (re-derived without `evenRec`?): **none** — every consumer goes through `evenRec`. But all
consumers live inside copies of the **same upstream file**, so this is upstream's own internal API, not an
independent AINTLIB abstraction. Signal: real internal API *of the upstream PR* — which is exactly why it is
already an open mathlib contribution and why the AINTLIB copy is redundant rather than novel.

### Composition check (Phase 6)
Can it be derived from **published** mathlib in ≤3 calls? **NO** — `EvenRec`, `Rel₃`, `rel₃_iff_evenRec` are not in
published mathlib, so nothing exists to compose against. (Within the fork it is the 1-call
`(rel₃_iff_evenRec W m).mp (ell _ _ _)`, but `rel₃_iff_evenRec` is part of the same unpublished PR.)
**Conclusion: NOT-COMPOSABLE from published mathlib** — consistent with NO-mathlib-has-it: the result is not
*composable*, it is *literally already written* in an open mathlib PR.

---

## Verdict: `IsEllSequence.evenRec`

**Category:** **NO-mathlib-has-it**

**Evidence:**
- Literature (Phase 3): `EvenRec` = Ward/Stange's standard even-term doubling recurrence; Lean form is the
  maximally-general `CommRing` standard form.
- Generality (Phase 4): MAXIMALLY GENERAL; no modern-idiom improvement (it is mathlib's own form, vendored).
- Mathlib search (Phase 5): not in *published* mathlib, but **byte-identical** to `evenRec` in OPEN mathlib
  **PR #13155** (diff L587), same namespace, same proof.
- Composition (Phase 6): NOT-COMPOSABLE from published mathlib (supporting defs belong to the same PR).

**Rationale.**
The project's `EllipticDivisibilitySequence.lean` carries the copyright header of David Kurniadi Angdinata — the
mathlib EDS file's author — and the `EllSequence` block (`rel₄`, `net`, `Rel₃`, `OddRec`, `EvenRec`, and the
`IsEllSequence.{oddRec,evenRec,rel₄,net,invar}` lemmas) reproduces, line-for-line, the open mathlib PR #13155
("show elliptic relations follow from even-odd recursion", by Junyan Xu) plus the elliptic-nets PR #25989.
`IsEllSequence.evenRec` is **identical** to PR #13155's `evenRec` (diff L587). This is therefore not a candidate
for a *new* AINTLIB→mathlib contribution: the exact declaration is already in mathlib's PR pipeline, merely not yet
merged into the pinned commit `d90090f`. The CLAUDE.md cardinal rule — "re-proving something that already exists is
the one cardinal sin" — applies a fortiori: this *is* the mathlib declaration, vendored ahead of the bump. (Note:
sibling reports `EvenRec.md` and `rel₃_iff_evenRec.md` landed on YES-add-as-is because they grepped only the pinned
mathlib and the literature; they did not search open mathlib PRs and so missed PR #13155 / #25989. The PR-diff
evidence here supersedes that.)

**WHY not (refactor-actionable).**
Mathlib effectively already has this, in canonical form, via open PR #13155. The AINTLIB copy exists only because
the pinned mathlib (`rev = d90090f`, Lean `v4.31.0-rc2`) predates that PR's merge. The right action is **not** to
open an AINTLIB→mathlib PR for `evenRec` (it would duplicate #13155 and step on the maintainer's own in-flight
work), but to track #13155/#25989 upstream and drop the vendored fork once they land.

- Existing decl (open PR): `IsEllSequence.evenRec` in mathlib **PR #13155** (`EllNet_from_evenOdd`), diff L587.
- Will live at: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (extending the existing file).
- Our form follows trivially — it is the same proof: `(rel₃_iff_evenRec W m).mp (ell _ _ _)`.
- Call sites in AINTLIB (Phase 6.0): 2 in NagellLutz (L692, L1226) + 2 in the HasseWeil vendored copy (L570, L695).

**Refactor plan.**
1. **Do NOT** add `IsEllSequence.evenRec` to a mathlib PR from AINTLIB — it is already PR #13155.
2. Coordinator: watch mathlib PRs **#13155** and **#25989**. When they merge and the AINTLIB daily bump crosses
   that commit, the whole `EllSequence` block (incl. `evenRec`) becomes available from
   `Mathlib.NumberTheory.EllipticDivisibilitySequence`.
3. At that bump, **delete** the vendored `EllSequence`/`Rel₃`/`OddRec`/`EvenRec`/`IsEllSequence.{oddRec,evenRec,…}`
   block from BOTH `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` and
   `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean`, replacing with the mathlib import.
   The 4 call sites (NagellLutz L692/L1226, HasseWeil L570/L695) need no edit — names/signatures match the PR
   verbatim (`ell.evenRec`, `ellW.evenRec`, `ellU.evenRec`).
4. Until then, keep the fork as a faithful WIP vendoring (a copy, not a divergent re-derivation).

**Human-judgment caveat (why a reviewer could flip this to YES-add-as-is).**
PR #13155 has been OPEN since 2024-05 and untouched since 2024-08-27 — i.e. it may be **stalled/abandoned**. If a
human confirms upstream is dead, the canonical-pipeline argument weakens and AINTLIB's vendored `EllSequence` block
(incl. `evenRec`) could legitimately be revived *as* the mathlib contribution — matching the siblings' YES-add-as-is
(at maximal generality, no published duplicate). That is a project-policy / upstream-liveness call this skill should
not make unilaterally; it is recorded here, but the default verdict remains NO-mathlib-has-it because an identical,
non-draft open PR by a mathlib maintainer is the strongest "mathlib has it" signal short of merge, and re-upstreaming
over it is the cardinal sin AINTLIB forbids.

---

## Next step
Keep `IsEllSequence.evenRec` as a vendored copy of mathlib PR #13155; do **not** upstream it independently. Flag
PRs **#13155** and **#25989** for the coordinator to watch, and schedule deletion of the vendored `EllSequence`
block (both copies) for the bump that merges them. If the coordinator determines #13155 is abandoned upstream,
re-evaluate as YES-add-as-is and revive the block as the contribution.
