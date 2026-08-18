# /mathlibable report — `invarDenom_normEDS_two`

## Verdict: NO-mathlib-has-it (it IS vendored mathlib — the EDS-invariant API David Angdinata is upstreaming for the file he maintains)

One-line: `invarDenom_normEDS_two` is the `n = 2` base evaluation of the EDS "invariant
denominator" on the canonical normalised EDS — `invarDenom (normEDS b c d) 1 2 = c · b`.
It belongs to the `EllSequence` / `invarNum` / `invarDenom` / `invar` machinery that the
sibling report `invarDenom.md` already established is a verbatim, Apache-licensed slice of
**David Kurniadi Angdinata's (Multramate's) in-flight rewrite** of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (mathlib PR **#25989**, **OPEN**,
authored by the EDS file's own maintainer). It is not an AINTLIB-original contribution to
upstream — it is mathlib's own pending code, vendored pre-merge. The correct action is to
track/land the upstream PR, dedup the NagellLutz vs HasseWeil copies locally, and let the
daily mathlib bump retire the fork.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — RHS is a trivial ring product, `by simp [invarDenom]`, no elaboration ambiguity)
- decl `invarDenom_normEDS_two`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:980`
- qualified name:           `invarDenom_normEDS_two` — **VERIFIED `_root_`** (no enclosing namespace). It sits in `section NormEDS` (opened line 881) under `open EllSequence` (line 884); `open` does **not** place the decl in `EllSequence`. The two namespaces in the file — `EllSequence` (90–597) and `IsEllSequence` (643–702) — are both closed long before line 980. So the full name is the bare `invarDenom_normEDS_two`. (The parsed-name guess in the task matches.)
- kind:                      `lemma` (Prop), proof `by simp [invarDenom]`
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS): defines IsEllSequence / IsDivSequence / IsEllDivSequence, the Stange elliptic-net machinery (`net`/`rel₄`/`addMulSub`), `preNormEDS`/`normEDS`/`complEDS`, and the sequence invariant (`invarNum`/`invarDenom`/`invar`).

### Statement (Phase 1)

```
lemma invarDenom_normEDS_two : invarDenom (normEDS b c d) 1 2 = c * b := by simp [invarDenom]
```

For the canonical normalised EDS `W = normEDS b c d : ℤ → R` over a commutative ring `R`,
the **invariant denominator** at shift `s = 1`, index `n = 2`, evaluates to `c · b`.

Unfolding: `invarDenom W s n = W(n+s) · W(n) · W(n-s)` (def, line 145). At `s=1, n=2`:

  `invarDenom W 1 2 = W(3) · W(2) · W(1) = normEDS b c d 3 · normEDS b c d 2 · normEDS b c d 1`
                    `= c · b · 1 = c · b`,

using the initial-value simp lemmas `normEDS_three = c`, `normEDS_two = b`, `normEDS_one = 1`.

Variables (Lean side):
- `R : Type*`, `[CommRing R]` — the coefficient ring.
- `b c d : R` — the three free parameters of the canonical normalised EDS (its initial data
  `W(2)=b`, `W(3)=c`, `W(4)=d·b`).

Hypotheses: none.
Conclusion (math): the ring element `c · b`.
Conclusion (Lean): an equality `Prop` in `R`.

**Role.** This is the `n = 2` *base case* feeding the curve-coefficient recovery. Paired
with its sibling `invarNum_normEDS_two : invarNum (normEDS b c d) 1 2 = (d + b^4) · b`
(line 977), it is fed into the invariance identity `invar_normEDS`
(`invarNum s m · invarDenom s n = invarNum s n · invarDenom s m`, line 1473) at `n = 2`
to prove `invar₂_normEDS : invarNum W 1 m · c = invarDenom W 1 m · (d + b^4)` (line 1479/1482)
— i.e. it pins the constant value of the invariant, exhibiting `d + b^4` (the curve's
`b₄`-type coefficient, à la Ward's reverse construction) as the value of the
`invarNum / invarDenom` ratio. So it is genuine, depended-upon API, not a throwaway `#check`.

### Size classification (Phase 2a)

Verdict: SMALL — a one-line evaluation lemma (`invarDenom` of `normEDS` at a fixed small
index), a leaf supporting the genuinely-BIG result `IsEllSequence.invar` / `invar_normEDS`.
Literature width nonetheless run at the wider protocol (the sibling `invarDenom.md` ran
EXHAUSTIVE; this lemma reuses that sweep + adds a PR re-check).

### One-line check (Phase 2b)

Body line count: 1 (`by simp [invarDenom]`).
One-liner verdict: ONE-LINER.

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | no       | it is a proof, not a def; nothing sealed |
| Avoid typeclass diamonds         | no       | no instance involved |
| Mark semantic intent / API name  | yes      | it is the named base case (`s=1,n=2`) of the invariant on `normEDS`; consumed by name in `invar₂_normEDS_of_mem_nonZeroDivisors` (line 1482) — the simp-set entry `invarDenom_normEDS_two` is the API surface |

Conclusion: ONE-LINER WITH-EXEMPTION (semantic-intent / API-name): it is a deliberately-named
specialisation that a downstream proof rewrites with; not inline-able without churning the
`invar₂_normEDS` proof. (Mathlib keeps exactly such `foo_two` / initial-value evaluation
lemmas — cf. `normEDS_two`, `normEDS_three`, `normEDS_four` directly above it.)

### Literature search table

Reuses the sibling `invarDenom.md` EXHAUSTIVE sweep (Ward 1948; Shipsey 2000 thesis;
Stange 0710.1316 / formulary; Akbary–Bleaney–Yazdani; Silverman–Stephens math/0402415;
recent arXiv ≤5y incl. "On Elliptic Sequences over Commutative Rings" 2604.05280, Stange
2025/521, CM net valuations 2512.09601), all confirming the EDS-invariant /
recover-the-curve principle is Ward/Shipsey folklore with **no separately-named object** for
the denominator triple, let alone for its evaluation at a fixed index. New, target-specific
channels for *this* lemma:

| #  | Channel | Query | Hit? | Finding |
|----|---------|-------|------|---------|
| 1  | WebSearch | `mathlib4 PR 25989 elliptic nets invarDenom invarNum normEDS EllSequence` | partial | confirms the EDS-invariant work "has been included in a pull request to Lean's Mathlib in the EllipticDivisibilitySequence.lean file"; released docs page lists only `preNormEDS`/`normEDS`/`complEDS` — **no** `invarNum`/`invarDenom`/`EllSequence`/`invar` |
| 2  | WebSearch | `...EllipticDivisibilitySequence invarDenom_normEDS_two normEDS invariant` | no | no occurrence of the lemma name anywhere on the public web outside this repo; the value-at-2 of the invariant is not a named result in the literature |
| 3  | WebFetch (mathlib4 docs) | released `EllipticDivisibilitySequence.html` contents | yes | present: `preNormEDS'`, `preNormEDS`, `complEDS₂`, `normEDS`, `complEDS`; **absent**: every `invar*`, `EllSequence`, `addMulSub`, `net`, `rel₄` |
| 4  | WebFetch (mathlib PR #25989 /files diff) | does the live PR add `invarDenom_normEDS_two` / `invarDenom` / `EllSequence`? | **renamed** | the **live head** of PR #25989 now uses a **different API** — `IsEllipticNet.atom` / `atomRel` / `rel` — and does **not** contain the `EllSequence` / `invarDenom` / `invarNum` / `invarDenom_normEDS_two` spellings. AINTLIB vendored an **earlier revision** of the same upstreaming effort. (Cf. companion #25990 = "rename".) |
| 5  | `gh pr view 25989` | PR state + author | **OPEN**, author **Multramate (David Kurniadi Angdinata)**, title "feat(NumberTheory/EllipticDivisibilitySequence): add elliptic nets" | the EDS file's own maintainer is actively upstreaming this material |
| 6  | Local references / `refs/NagellLutz/` | `ls` | n/a | neither directory exists |

### Literature summary (Phase 3)

Concept: the **value of the EDS invariant's denominator at the base index** (`s=1, n=2`) for
the canonical normalised EDS — `W(3)·W(2)·W(1) = c·b`. In the literature this is the
denominator term in Ward's/Shipsey's reverse map that recovers a point / curve-coefficient
from a proper EDS `(u₂,u₃,u₄) = (b,c,d·b)`; it is an *auxiliary computation step*, never a
named theorem. Standard form agreement: yes for the underlying recover-the-curve principle;
no named result for the evaluation. Most general standard form: `W(3)·W(2)·W(1)` for `W` the
normalised EDS over any commutative ring — exactly the Lean form. No disagreement with the
literature.

### Generality analysis — `invarDenom_normEDS_two`

Literature-standard form: evaluation of `invarDenom (normEDS b c d) 1 2`; result `c·b`;
`b c d : R`, `R` a commutative ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring (classically integral domain) | NO (already maximal) | RHS `c·b` is a bare ring product; the whole EDS file is developed over `CommRing` and ships ring-hom compat — weakening this leaf alone would desync it from the `normEDS`/`invarDenom` API it specialises |
| 2 | shift/index `s=1, n=2` | the fixed base case | the base case of the recover-the-curve map | NO (specialisation is the point) | this lemma's entire purpose is to be the `n=2` instance feeding `invar_normEDS`; the general statement is `invar_normEDS` itself (already present, line 1473) — there is nothing to "generalise" here without deleting the lemma |
| 3 | sequence | `normEDS b c d` | the canonical normalised EDS | NO | the constant `c·b` is specific to `normEDS`'s initial data; for a general `W` the value is `W(3)·W(2)·W(1)`, which is just `invarDenom W 1 2` unfolded — i.e. the def, not a lemma |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL **for what it is** (a base-case evaluation): it is
already over `CommRing`, and "generalising the indices" would just reproduce the existing
general lemma `invar_normEDS`. Number of sensible weakening opportunities: 0.
Proposed restatement: none. Cost: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Note |
|----|----------|----------|------|
| 1  | bundled hypotheses → typeclasses? | no | no hypotheses |
| 2  | sequences/metric → filters/topology? | no | purely algebraic evaluation |
| 3  | construction → universal property? | no | it is an equation, not a construction |
| 4  | set-with-closure → bundled substructure? | no | — |
| 5  | field-specific → weaken typeclass? | no | already `CommRing` |
| 6  | 1-categorical → higher? | no | not categorical |
| 7  | concrete index → general additive? | no | the *concrete* indices `1,2` ARE the content (base case) |

Modern idiom available: no — it is already in the mathlib idiom, an initial-value evaluation
lemma sitting beside `normEDS_two`/`normEDS_three`/`normEDS_four`, authored by the file's
mathlib maintainer in exactly mathlib's house style.

### Diamond / defeq risk — `invarDenom_normEDS_two`

| # | Risk | Verdict | Rationale |
|---|------|---------|-----------|
| 1 | Typeclass diamond | none | no instance produced/selected |
| 2 | Reducibility leak | none | a `lemma` (Prop), not `@[reducible]` |
| 3 | Non-canonical unfolding | none | proof is a self-contained `simp [invarDenom]` |
| 4 | Instance priority | none | not an instance; not even `@[simp]` |
| 5 | Universe issues | none | `R : Type u`, monomorphic |
| 6 | Coercion ambiguity | none | none |

### Risk verdict (Phase 4.5)

Overall risk: NONE.

### Mathlib search-status: `invarDenom_normEDS_two`

[A] Lean-Finder       n/a (index offline locally) — substituted by live mathlib4 docs fetch (Phase-2b ch.3)
[B] Loogle            type pattern `invarDenom (normEDS ?b ?c ?d) 1 2 = ?c * ?b` is not indexable — `invarDenom`/`normEDS` symbols don't exist in the mathlib index (the symbols themselves are absent from released mathlib)
[C] LeanSearch        "invariant denominator of normalised EDS at two equals c b" — n/a (index offline) — substituted by docs + PR inspection
[D] Grep mathlib src  grepped the **pinned/released** `./.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`: it has `def normEDS` (289), `normEDS_two` (306), `normEDS_dvd_normEDS_two_mul` (326) — but **0 hits** for `invarDenom`, `invarNum`, `EllSequence`, `invar`, or `*_normEDS_two` invariant lemmas. So the invariant layer (incl. this lemma) is **not in released mathlib**.
[E] Name pattern      live `mathlib4_docs/.../EllipticDivisibilitySequence.html`: absent = `invarDenom_normEDS_two`, `invarNum_normEDS_two`, `invarDenom`, `invarNum`, `EllSequence`, `invar`, `addMulSub`, `net`, `rel₄`

Searched for both the specific form (`invarDenom (normEDS …) 1 2 = c*b`) and the general
parent (`invar_normEDS`).

Concluded: **not in mathlib's released master** (docs + pinned on-disk checkout both = 0) —
and **not in the current head** of the upstreaming PR either (the live PR #25989 has since
been **renamed** to the `IsEllipticNet.*` API). The exact spelling `invarDenom_normEDS_two`
in this file is a **snapshot of an earlier revision** of the same maintainer's (Multramate's)
EDS-invariant upstreaming work. The file header confirms provenance:
`Copyright (c) 2024 David Kurniadi Angdinata … Authors: David Kurniadi Angdinata`.

### Call sites — `invarDenom_normEDS_two`

In-file downstream uses: **1** (the load-bearing one) — plus a vendored duplicate:

| Caller (file:line) | Usage |
|--------------------|-------|
| EllipticDivisibilitySequence.lean:1482 | `invar₂_normEDS_of_mem_nonZeroDivisors`: `simp only [invarNum_normEDS_two, invarDenom_normEDS_two]` after `convert invar_normEDS 1 m 2` — i.e. the base case that pins the invariant constant `d + b^4` |
| projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:616–618 | **byte-identical** copy of the same lemma (same vendored PR file); also consumed at HasseWeil line 971 |
| projects/NagellLutz/.../EllipticDivisibilitySequenceOriginal.lean:929 | the staging/`Original` copy of the same vendored file |

External-to-project duplicate: 1 (HasseWeil). The lemma is depended-upon API, never
re-derived ad hoc.

### Composition check (Phase 6)

Can `invarDenom_normEDS_two` be produced by ≤3 mathlib calls?
Syntactically the *proof* is one `simp [invarDenom]` (unfold the def, then the `normEDS`
initial-value simp lemmas `normEDS_one/two/three` fire). But this is the wrong frame: the
proof is short **only because `invarDenom` and `normEDS` already exist** — and `invarDenom`
is **not in released mathlib** (Phase 5, [D]/[E] = 0 hits). So "compose from mathlib" is
impossible: the very symbol `invarDenom` it evaluates is absent upstream; there is nothing in
released mathlib to compose against. The lemma is meaningful only **inside** the vendored
`EllSequence`/`invar` development. Conclusion: NOT-COMPOSABLE from *released* mathlib (its
prerequisite `def invarDenom` lives only in the open/renamed upstream PR + this fork); and
within that development it is the named base case, not an inline-able triviality.

---

## Verdict: `invarDenom_normEDS_two`

**Category:** NO-mathlib-has-it

(Bucket reading: "mathlib has it" = the declaration is part of mathlib's **own** in-flight
EDS-invariant material — authored by the file's maintainer, David Angdinata — that AINTLIB
has **vendored pre-merge**. The released library does not yet expose it, and the live PR has
since been renamed; but it is unambiguously mathlib's code-in-progress, not an AINTLIB
original. This is the strongest possible "do not add as a NEW AINTLIB contribution" signal:
upstreaming is already in flight, by the right person, in the right file. It is **not**
`YES-add-as-is` (nothing new to contribute), **not** `YES-but-generalise-first` (already
maximally general / generalising = the existing `invar_normEDS`), **not**
`NO-composable-from-mathlib` (its prerequisite `invarDenom` is itself absent from released
mathlib, so there is nothing to compose), and **not** `BORDERLINE` (the vendored-PR
provenance is dispositive).)

**Evidence:**
- Provenance: file header credits David Kurniadi Angdinata (Multramate); `gh pr view 25989` → OPEN, author Multramate, "add elliptic nets". Sibling report `invarDenom.md` already established the `EllSequence`/`invarDenom`/`invar` layer as this PR's content; `invarDenom_normEDS_two` is a member of that same layer.
- Literature (Phase 3): the value of the EDS-invariant denominator at the base index is a Ward/Shipsey auxiliary computation; no named result; `CommRing`-general — matches the Lean form.
- Generality (Phase 4): MAXIMALLY GENERAL for a base-case evaluation; "generalise" = the already-present `invar_normEDS`; modern idiom in use; risk NONE.
- Mathlib search (Phase 5): absent from released master (docs + pinned on-disk grep = 0) AND from the current PR head (renamed to `IsEllipticNet.*`); the exact spelling is a snapshot of an earlier revision of the maintainer's upstreaming work.
- Composition (Phase 6): NOT-COMPOSABLE — the prerequisite `def invarDenom` is itself not in released mathlib.

**Rationale.**
`invarDenom_normEDS_two` is not an AINTLIB-original lemma awaiting a mathlibability verdict —
it is part of a **direct, Apache-licensed copy of unmerged mathlib code**. It computes the
base-case value `invarDenom (normEDS b c d) 1 2 = c·b`, the companion to
`invarNum_normEDS_two = (d+b⁴)·b`, and together they are the `n=2` instance that the
invariance identity `invar_normEDS` uses to read off the curve coefficient `d+b⁴` from the
normalised EDS (Ward's/Shipsey's reverse construction). All of this — the `EllSequence`
namespace, `invarNum`, `invarDenom`, `invar`, and these `*_normEDS_two` evaluations — is the
maintainer's own pending upstream material (PR **#25989**, OPEN, by Multramate = David
Angdinata, author of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`), confirmed
absent from released mathlib three ways: the live docs page lists only the old API; a grep of
the pinned on-disk mathlib checkout returns 0 hits for `invarDenom`/`invarNum`/`EllSequence`;
and the project keeps an `EllipticDivisibilitySequenceOriginal.lean` staging copy. A new
wrinkle since `invarDenom.md` was written: the **live head** of PR #25989 has been **renamed**
to an `IsEllipticNet.*` API and no longer uses the `invarDenom`/`EllSequence` spellings — so
the exact name `invarDenom_normEDS_two` is a snapshot of an *earlier* revision of that same
upstreaming effort. Either way the "gap" in mathlib is a PR queue, not a contribution gap.

**WHY not (refactor-actionable):**
Mathlib (merged) does not have it; mathlib's own author is shipping the equivalent material
via open PR #25989; AINTLIB carries a pre-merge snapshot (under names the PR has since
renamed). There is nothing for AINTLIB to upstream — a PR would duplicate / collide with /
contradict the maintainer's own renamed work. The actionable work is entirely local and
downstream of the merge:

  Existing/incoming mathlib material: the EDS-invariant layer (`invarNum`/`invarDenom`/`invar`
    and their `normEDS` evaluations incl. this lemma)
    — in open PR **leanprover-community/mathlib4 #25989** ("add elliptic nets", Multramate),
      destined for `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, **now under the
      renamed `IsEllipticNet.*` API** (cf. companion #25990 = rename).

  AINTLIB call sites of this fork: NagellLutz EDS file (1 in-file use, line 1482; staging copy
    in `…Original.lean:929`) **and** a byte-identical HasseWeil copy
    (`projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:616`, used 971).

  Refactor plan (local, two parts):
   1. **Dedup now**: NagellLutz and HasseWeil both vendor this same `EllSequence` EDS file.
      Factor the shared file into one `Common/` module (or have HasseWeil import NagellLutz's)
      so `invarDenom_normEDS_two` (and the rest) is defined once. Standard AINTLIB
      cross-project dedup → file a `lane:cleanup` issue, not a mathlib PR.
   2. **Retire on merge**: once PR #25989 (+ #25990 rename) lands and the daily bump pulls it
      in, delete the vendored `EllipticDivisibilitySequence.lean` (+ `…Original.lean`) and
      re-point consumers at `Mathlib.NumberTheory.EllipticDivisibilitySequence`. **Heed the
      rename** — the post-merge spelling of this lemma will likely live under the
      `IsEllipticNet.*` API, not `invarDenom_normEDS_two`; track #25989/#25990 to get it right.

  Do NOT open a mathlib PR for `invarDenom_normEDS_two` from AINTLIB: it would race the
  maintainer's own open (and already-renamed) PR.

**Next action:** No mathlib submission. (a) File an AINTLIB `lane:cleanup` dedup ticket to
unify the NagellLutz/HasseWeil copies of the `EllSequence` EDS file into `Common/`.
(b) Track mathlib PRs #25989 / #25990; when they merge and the bump lands, delete the fork and
import `Mathlib.NumberTheory.EllipticDivisibilitySequence` (heeding the `IsEllipticNet.*` rename).
