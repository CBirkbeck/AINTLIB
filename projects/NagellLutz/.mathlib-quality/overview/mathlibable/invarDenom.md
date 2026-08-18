# /mathlibable report — `EllSequence.invarDenom`

## Verdict: NO-mathlib-has-it (it IS unmerged mathlib — open PR #25989 by the file's own author)

One-line: `EllSequence.invarDenom` is a verbatim, Apache-licensed slice of David
Angdinata's (Multramate's) in-flight rewrite of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
(mathlib PR **#25989 "add elliptic nets"**, currently **open**). It is not an AINTLIB
contribution to evaluate for upstreaming — it is mathlib code that has not landed yet.
The correct action is to track/land the upstream PR, dedup the NagellLutz vs HasseWeil
copies locally, and let the daily mathlib bump remove the fork once #25989 merges.

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task; reasoned from source — type is a trivial product of ring elements, no elaboration ambiguity)
- decl `EllSequence.invarDenom`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:145`
- qualified name:           `EllSequence.invarDenom` (inside `namespace EllSequence`, opened at line 90) — VERIFIED
- kind:                      `def`
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS): defines IsEllSequence/IsDivSequence/IsEllDivSequence, the Stange elliptic-net machinery (`net`/`rel₄`), `preNormEDS`/`normEDS`/`complEDS`, and the sequence invariant.

### Statement (Phase 1)

`EllSequence.invarDenom` is a **definition**. For a sequence `W : ℤ → R` over a
commutative ring `R` and integers `s, n`, it is the product

  `invarDenom W s n  =  W(n + s) · W(n) · W(n - s)`.

It is the **denominator** of the "invariant of an elliptic sequence": the companion
`invarNum W s n = (W(n+2s)·W(n-s)² + W(n+s)²·W(n-2s))·W(s)² + W(n)³·W(2s)²` and
`invarDenom` satisfy the cross-multiplication identity
`invarNum s m · invarDenom s n = invarNum s n · invarDenom s m`
(theorem `EllSequence.invar_of_net`, line 149; and `IsEllSequence.invar`, line 699),
i.e. the ratio `invarNum s n / invarDenom s n` is **independent of `n`**. This invariant is
the algebraic device by which an elliptic-curve coefficient is recovered from the
sequence (in the `normEDS` case, lines 1480–1499 tie it to `d + b^4`, i.e. the curve's
`b₄`/`a`-coefficient à la Ward's reverse construction of a point on the curve).

Variables (Lean side):
- `R : Type*`, `[CommRing R]` — the coefficient ring.
- `W : ℤ → R` — the elliptic sequence (explicit `variable`, bound before line 145).
- `s n : ℤ` — the shift `s` and the index `n`.

Hypotheses: none (it is a pure algebraic expression; ellipticity of `W` is required only
by the *theorems about* `invarDenom`, not by the def).

Conclusion (math): the ring element `W(n+s)·W(n)·W(n-s)`.
Conclusion (Lean): `R` (a `def`, not a `Prop`).

### Size classification (Phase 2a)

Verdict: SMALL — a one-line auxiliary `def` (a product of three sequence terms),
supporting the genuinely-BIG result `IsEllSequence.invar`. (Literature width run
EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`W (n + s) * W n * W (n - s)`).
One-liner verdict: ONE-LINER.

| Exemption                         | Applies? | Evidence |
|-----------------------------------|----------|----------|
| Avoid defeq abuse                | no       | sealed only incidentally; proofs unfold it freely via `simp [invarDenom]` |
| Avoid typeclass diamonds         | no       | no instance resolution involved — it is a plain element of `R` |
| Mark semantic intent / API name  | yes      | the name + docstring ("denominator of an invariant") is the API surface: `invar`, `map_invarDenom`, `invarDenom_normEDS_two`, `invarDenom_eq_redInvarDenom_mul` all reference it by name (19 in-file uses) |

Conclusion: ONE-LINER WITH-EXEMPTION (semantic-intent / API-name). It anchors a
whole lemma family; it is not inline-able without churning that API.

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1  | WebSearch (specific form) | EDS invariant `W(n+s)W(n)W(n-s)` constant independent of n, Stange elliptic nets | partial | the EDS recurrence `W_{m+n}W_{m-n}=W_{n+1}W_{n-1}W_m²−W_{m+1}W_{m-1}W_n²`; the *denominator triple* appears as an auxiliary, not as a named object | Ward 1948; Stange 0710.1316; Stange formulary edsformulary.pdf |
| 2  | WebSearch (general form) | Stange elliptic nets / division polynomials / Ward sequence — invariant net polynomial | yes | Ward's theorem: every EDS is `W_n = λ^{n²−1} Ψ_n(x,y)`; nets generalise EDS; net polynomials (Akbary–Bleaney–Yazdani; Stange symmetries 1408.6623) | the invariant recovers curve data, consistent with `invar` |
| 3  | WebSearch (named-after / Shipsey) | Shipsey thesis recover x-coordinate of elliptic curve from `W(n+1)W(n-1)` | yes | Ward's reverse map: a proper EDS `(u₂,u₃,u₄)` yields a point `(x,y)`; `x` is a ratio whose denominator is the `W_{n±1}W_n` triple | Shipsey 2000 thesis; Silverman/Stephens "sign of an EDS" math/0402415 |
| 4  | ChatGPT MCP | self-contained Q on whether `W(n+s)W(n)W(n-s)` is named + its generality | n/a — DOWN | — | Codex MCP errored (stdin failure); fallbacks used (web + direct mathlib PR/source inspection) |
| 5  | Local references | `ls projects/NagellLutz/.mathlib-quality/references/` and `refs/NagellLutz/` | n/a | — | neither directory exists |
| 6  | nLab | "elliptic divisibility sequence" / "elliptic net" | n/a | nLab has no dedicated EDS/elliptic-net page; concept is arithmetic-geometry, not categorical | recorded n/a |
| 7  | nCatLab | — | n/a | not a categorical concept | — |
| 8  | Stacks Project | "elliptic divisibility sequence" | n/a | Stacks has no EDS material (it is scheme-theoretic foundations, not EDS arithmetic) | recorded n/a |
| 9  | MathOverflow / MSE | EDS invariant / recover curve from sequence | partial | confirms the `invarNum/invarDenom` ratio = curve-coefficient idea is folklore from Ward | no canonical *name* for the denominator |
| 10 | recent arXiv (≤5y) | Stange "Division polynomials for arbitrary isogenies" 2025/521; CM net valuations 2512.09601 | yes | net-polynomial framework; denominator triples appear as auxiliaries throughout | reinforces: auxiliary expression, not a headline named object |
| 11 | **mathlib PR tracker (decisive)** | mathlib4 PRs with "EllipticDivisibilitySequence" in title | **yes** | **PR #25989 (open) "add elliptic nets" by Multramate** introduces `EllSequence`/`net`/`rel₄`/`invarNum`/`invarDenom`/`invar`; companion #25990 (rename, open draft), #13155 (alreadydone, open) | this decl is that PR's code, pre-merge |

### Literature summary (Phase 3)

Concept identified as: the **denominator of the EDS "invariant"** — the triple product
`W(n+s)·W(n)·W(n-s)`, the `s`-shifted generalisation of Ward's `W_{n+1}·W_n·W_{n-1}`
that appears as the denominator when recovering the `x`-coordinate / a curve coefficient
from an elliptic divisibility sequence (Ward 1948; Shipsey 2000; Stange 2007).
Sources agree on the standard form: yes for the *underlying recurrence and the
recover-the-curve principle*; **no named object** for the denominator triple itself — it
is universally treated as an auxiliary algebraic expression.
Most general standard form: `W(n+s)·W(n)·W(n-s)` for `W` valued in any commutative ring
(the EDS theory is stated over arbitrary commutative rings / integral domains).
Generality dimensions where the literature varies:
  - coefficient domain: ℤ (classical Ward) → integral domain → arbitrary commutative ring (modern/mathlib) — most general is comm ring, which is exactly the Lean form.
  - rank: rank-1 (EDS) → rank-n (Stange elliptic nets) — but the *denominator-triple* lives at rank 1, matching this def.
Disagreement with the literature: none.

### Generality analysis — `EllSequence.invarDenom`

Literature-standard form: `W(n+s)·W(n)·W(n-s)`, `W : ℤ → R`, `R` a commutative ring.

| # | Parameter / hypothesis | Current Lean form | Literature-standard | Weaker form exists? | Reason |
|---|------------------------|-------------------|---------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring (classically integral domain) | NO (already maximal) | the def is a product of three ring elements; needs only `Mul`, but the *whole EDS file* is developed over `CommRing` and ships ring-hom compat (`map_invarDenom`); weakening this one def below the file's `CommRing` would fragment the API for zero gain |
| 2 | `W : ℤ → R` | sequence indexed by ℤ | sequence indexed by ℤ | NO | the EDS invariant is inherently a ℤ-indexed-sequence notion; rank-n nets are a *different* (already-separate) object in the same file |
| 3 | `s n : ℤ` | integer shift + index | integer shift + index | NO | indices are ℤ by definition of the sequence |

### Generality verdict (Phase 4b)

The current form is: MAXIMALLY GENERAL (it matches the literature-standard form exactly,
at the modern `CommRing` generality mathlib uses for the whole EDS file).
Number of weakening opportunities found: 0 that are sensible (the `Mul`-only weakening of
row 1 is rejected — it would desync this def from its own file's `CommRing` API).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Reformulation | Downstream |
|----|----------|----------|---------------|------------|
| 1  | bundled hypotheses → typeclasses? | no | the def has no hypotheses to bundle | — |
| 2  | sequences/metric → filters/topology? | no | purely algebraic; no limit/topology | — |
| 3  | construction → universal-property class? | no | it is a concrete ring element, not a constructed object with a UMP | — |
| 4  | set-with-closure → bundled substructure? | no | not a set | — |
| 5  | vector-space/field-specific → weaken typeclass? | no | already at `CommRing`; see Phase 4b row 1 | — |
| 6  | 1-categorical → higher-categorical? | no | not categorical | — |
| 7  | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | ℤ-indexing is essential to the EDS notion (already generalised to rank-n nets as a separate object in the same file) | — |

Modern idiom available: no. It is already in the contemporary mathlib idiom — a `def`
over `CommRing`, with a sibling `map_invarDenom` ring-hom-naturality lemma, exactly the
shape mathlib's EDS file uses for `preNormEDS`/`normEDS`. (Indeed it IS the mathlib idiom:
it was authored by the file's mathlib maintainer.)

### Diamond / defeq risk — `EllSequence.invarDenom`

| # | Risk | Verdict | Rationale |
|---|------|---------|-----------|
| 1 | Typeclass diamond | none | no instance is produced or selected; it is a function returning an element of `R` |
| 2 | Reducibility leak | none | not `@[reducible]`; body is a plain product, semireducible is fine |
| 3 | Non-canonical unfolding | low | proofs unfold via explicit `simp [invarDenom]` / `rw [invarDenom]`; no surprising auto-unfolding (it is sealed by default) |
| 4 | Instance priority collision | none | not an instance |
| 5 | Universe-polymorphism issues | none | `R : Type u` mono-universe; no forced annotations |
| 6 | Coercion ambiguity | none | no `CoeFun`/`CoeSort` |

### Risk verdict (Phase 4.5)

Overall risk: NONE.
Top risks: none.

### Mathlib search-status: `EllSequence.invarDenom`

[A] Lean-Finder       n/a (index offline locally) — substituted by live mathlib4 docs fetch
[B] Loogle            type pattern `(ℤ → ?R) → ℤ → ℤ → ?R` is far too generic to be useful; the discriminating term is the *name* — not in the mathlib index
[C] LeanSearch        "denominator of elliptic divisibility sequence invariant" — n/a (index offline) — substituted by docs + PR tracker
[D] Grep mathlib src  grepped `invarDenom|invarNum|namespace EllSequence|def net|def addMulSub` across **every** mathlib checkout on disk (incl. mathlib4 master @ a02d59b, 2026-05-27, and the project's pinned d90090f): **0 hits everywhere**
[E] Name pattern      live `mathlib4_docs/.../EllipticDivisibilitySequence.html`: present = `IsEllSequence`, `preNormEDS`, `normEDS`, `complEDS`, map-lemmas; **absent** = `invarNum`, `invarDenom`, `addMulSub`, `net`, `rel₄`, `Rel₃`, `EllSequence` namespace, `invar`

Searched for both the current form and the literature-standard form.

Concluded: **not in mathlib's released master** — BUT it is the verbatim content of
**open mathlib PR #25989** ("feat(NumberTheory/EllipticDivisibilitySequence): add elliptic
nets", author Multramate = David Angdinata, the EDS file's own maintainer). The
declaration, its namespace, and its whole lemma family are already authored and PR'd
upstream; they simply have not been merged. The file header here is
`Copyright (c) 2024 David Kurniadi Angdinata … Authors: David Kurniadi Angdinata`,
i.e. AINTLIB vendored the unmerged PR file directly.

### Call sites — `EllSequence.invarDenom`

Internal use count (NagellLutz, outside the declaring file): 0.
In-file downstream uses: **19** (the declaring file is itself the whole EDS development).
External-to-project duplicate: 1 — HasseWeil has a byte-identical copy.

| Caller (file:line) | Usage pattern |
|--------------------|---------------|
| EllipticDivisibilitySequence.lean:149 | `invar_of_net`: `invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m` |
| EllipticDivisibilitySequence.lean:699 | `IsEllSequence.invar` (the headline invariant theorem) |
| EllipticDivisibilitySequence.lean:980 | `invarDenom_normEDS_two : invarDenom (normEDS b c d) 1 2 = c * b` |
| EllipticDivisibilitySequence.lean:1175 | `map_invarDenom` (ring-hom naturality) |
| EllipticDivisibilitySequence.lean:1383 | `invarDenom_eq_redInvarDenom_mul` (feeds Nagell–Lutz reduction) |
| EllipticDivisibilitySequence.lean:1474–1499 | `invar_normEDS` / `invar₂_normEDS` — relate invariant to `d + b^4` (recover curve coeff) |
| projects/HasseWeil/.../EllipticDivisibilitySequence.lean:89 | byte-identical `def invarDenom` in the same `EllSequence` namespace (vendored copy of the same PR) |

Inline-derivation grep: none — every use goes through the named def. The triple product
is never re-derived ad hoc, confirming it is real, depended-upon API (just not *new* API).

### Composition check (Phase 6)

Can `EllSequence.invarDenom` be derived from mathlib in ≤3 calls?
It is a `def`, not a proposition, so "composition" means: is there a mathlib object this is
a trivial wrapper around? No — mathlib's *released* EDS file has no invariant machinery at
all (`invarNum`/`invar` absent), so there is nothing to wrap. The `def` is trivially
`W (n+s) * W n * W (n-s)`, but its *value* is the named API anchor for `invar`,
`map_invarDenom`, and the `normEDS` invariant chain. Inlining the product at the 19 sites
would destroy that API and the matching upstream PR structure.
Conclusion: NOT-COMPOSABLE (in the sense that matters — there is no mathlib primitive to
inline against; and even syntactically inlining the product would gratuitously fork from
PR #25989's API).

---

## Verdict: `EllSequence.invarDenom`

**Category:** NO-mathlib-has-it

(Bucket reading: "mathlib has it" = the identical declaration is already authored and
carried by an **open** mathlib PR (#25989) written by the file's own mathlib maintainer.
This is the strongest possible "do not add as a new AINTLIB contribution" signal: the
upstreaming is already in flight, by the right person, in the right file. It is not
`YES-add-as-is` (nothing new to contribute — it is literally mathlib's own pending code),
not a generalise case (already maximally general / already the mathlib idiom), and not
`BORDERLINE` (no judgment call remains — the upstream provenance is dispositive).)

**Evidence:**
- Literature (Phase 3): denominator of the EDS invariant (Ward/Shipsey/Stange); auxiliary expression, no separate name; `CommRing`-general — matches the Lean form.
- Generality (Phase 4): MAXIMALLY GENERAL; modern idiom already in use; risk NONE.
- Mathlib search (Phase 5): absent from released master (docs + every on-disk checkout = 0), but present verbatim in **open PR #25989 by Multramate** — the file's maintainer.
- Composition (Phase 6): NOT-COMPOSABLE — no mathlib primitive to inline against; it is an API anchor for 19 in-file uses.

**Rationale.**
`EllSequence.invarDenom` is not an AINTLIB-original definition awaiting a mathlibability
verdict — it is a **direct, Apache-licensed copy of unmerged mathlib code**. The file
header credits David Kurniadi Angdinata (GitHub: Multramate), who is the author of
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` and of the open PR **#25989
"add elliptic nets"** that introduces exactly this `EllSequence` namespace together with
`net`, `rel₄`, `addMulSub`, `invarNum`, `invarDenom`, and the `invar` invariant theorem.
The companion PRs **#25990** (rename, open draft) and **#13155** (alreadydone, open)
complete the same rewrite stack. None of this is in released mathlib yet — confirmed three
independent ways: the live `mathlib4_docs` page lists only the old API; a grep across every
mathlib checkout on this machine (including master at `a02d59b`, 2026-05-27, and the
project's pinned `d90090f`) returns zero hits for `invarDenom`/`EllSequence`/`net`; and the
project even keeps an `EllipticDivisibilitySequenceOriginal.lean` staging copy. The "gap"
in mathlib is therefore not a gap to fill with a *new* contribution — it is a PR queue.

**WHY not (refactor-actionable):**
Mathlib (in its merged form) does not yet have it, but **mathlib's own author is already
shipping it** via open PR #25989; AINTLIB is carrying a pre-merge snapshot. There is
nothing for AINTLIB to upstream — doing so would duplicate / collide with #25989. The
actionable work is entirely *local* and *downstream of the merge*:

  Existing/incoming mathlib decl: `EllSequence.invarDenom`
    — in open PR **leanprover-community/mathlib4 #25989** ("add elliptic nets", Multramate),
      destined for `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.
  Our form follows in 0 lines: it is the same source text (modulo two proof-tactic tweaks
    elsewhere in the file — the `invarDenom` *def* is identical).

  AINTLIB call sites of this fork: the NagellLutz EDS file (19 in-file uses) **and** a
  byte-identical HasseWeil copy (`projects/HasseWeil/.../EllipticDivisibilitySequence.lean:89`).

  Refactor plan (local, two parts):
   1. **Dedup now**: NagellLutz and HasseWeil both vendor this same `EllSequence` namespace.
      Factor the shared EDS-rewrite file into one `Common/` module (or have HasseWeil import
      NagellLutz's) so `invarDenom` is defined once, not twice. This is a standard AINTLIB
      cleanup (cross-project dedup) — file it as a `lane:cleanup` issue, not a mathlib PR.
   2. **Retire on merge**: once PR #25989 (+ #25990 rename, #13155) lands upstream and the
      daily mathlib bump pulls it in, delete the vendored
      `EllipticDivisibilitySequence.lean` fork (and `…Original.lean`) and re-point all
      consumers at `Mathlib.NumberTheory.EllipticDivisibilitySequence`. Watch for the
      #25990 *rename* — `invarDenom` may land under a different final name; track the PR
      to get the post-merge spelling right.

  Do NOT open a mathlib PR for `invarDenom` from AINTLIB: it would race the maintainer's
  own open PR.

**Next action:** No mathlib submission. (a) File an AINTLIB `lane:cleanup` dedup ticket to
unify the NagellLutz/HasseWeil copies of the `EllSequence` EDS file into `Common/`.
(b) Track mathlib PRs #25989 / #25990 / #13155; when they merge and the bump lands, delete
the fork and import `Mathlib.NumberTheory.EllipticDivisibilitySequence` (heeding any rename).
