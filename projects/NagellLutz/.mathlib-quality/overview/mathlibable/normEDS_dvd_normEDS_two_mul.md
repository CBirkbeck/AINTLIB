# /mathlibable report — `normEDS_dvd_normEDS_two_mul`

**Verdict: `NO-mathlib-has-it`** — the lemma is **byte-identical** to one already
present in the very mathlib commit this repo pins (`09b373db6e24`,
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:326`). The project file is
a stale fork of that mathlib file.

---

### Baseline (Phase 0)

- lake build:               not run (build stale, per task note); reasoning from source + the pinned mathlib tree on disk. Decl elaborates trivially (one-line term-mode `⟨_, _⟩`).
- decl `normEDS_dvd_normEDS_two_mul`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:930`
- kind:                      lemma (theorem)
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences" — defines EDS and constructs normalised EDSs from initial terms (verbatim copy of mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`, same Apache header, same author David Kurniadi Angdinata).

**Qualified name (VERIFIED).** The decl sits in `section NormEDS` (opened L881).
The only `namespace` in scope earlier (`EllSequence`, L90) was closed at L597. So
there is **no enclosing namespace**: the fully-qualified name is the root-level
`normEDS_dvd_normEDS_two_mul`. (Identical situation in pinned mathlib: `section
NormEDS`, no namespace.)

---

### Statement (Phase 1)

`normEDS_dvd_normEDS_two_mul` states: for the canonical normalised elliptic
divisibility sequence `W = normEDS b c d : ℤ → R` over a commutative ring `R`
(with initial data `b, c, d : R`), and any `k : ℤ`,

> `W(k) ∣ W(2k)`.

This is the `n = 2` instance of the defining *divisibility* property of an EDS: a
normalised EDS is a divisibility sequence, so `W(m) ∣ W(n)` whenever `m ∣ n`; here
`k ∣ 2k`. The witness is the explicit "2-complement" `complEDS₂ b c d k`, via
`normEDS_mul_complEDS₂ : W(k) * complEDS₂ b c d k = W(2k)`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring (most general sensible ring for the recurrence).
- `(b c d : R)` — the initial data of the normalised EDS.
- `(k : ℤ)` — the index.

Hypotheses: none.

Conclusion (math): `W(k) ∣ W(2k)`, where `W = normEDS b c d`.
Conclusion (Lean): `normEDS b c d k ∣ normEDS b c d (2 * k)`.

Proof body (verbatim):
```lean
⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩
```
i.e. the divisor witness is `complEDS₂ b c d k`, certified by the symmetrised
multiplication lemma `normEDS_mul_complEDS₂`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line corollary (`n = 2` specialisation of the EDS divisibility
property), packaging an existing product identity (`normEDS_mul_complEDS₂`) as a
`Dvd`. Not a new structure, not a named theorem, not a `## Main statements` entry.

(Note: literature width was run EXHAUSTIVE regardless — see Phase 3.)

### One-line check (Phase 2b)

Body line count: 1 substantive line. Kind is **lemma**, not `def`/`abbrev`/
`structure` — so the one-liner def-exemption machinery does **not** apply. A
one-line *lemma* is a normal, expected mathlib shape (a corollary). No exemption
analysis needed; this is not a one-line *definition*.

Conclusion: n/a — declaration kind is `lemma`.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                 | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "elliptic divisibility sequence W(k) divides W(2k) division polynomial Ward" | yes  | EDS is a divisibility sequence: `m ∣ n ⟹ W_m ∣ W_n` | Wikipedia "Elliptic divisibility sequence"; Ward 1948 |
|  2 | WebSearch (general form)         | (same query covered the general `m∣n ⟹ W_m∣W_n` law)                  | yes  | general divisibility property; `k∣2k` is the `n=2` case | "this divisibility property … is the reason the sequences are called divisibility sequences" |
|  3 | WebSearch (named-after / aliases)| EDS / Ward / division polynomials Ψ_n divisibility                     | yes  | division polynomials `Ψ_n`, `W_n = λ^{n²-1}Ψ_n`        | classical; Silverman/Stange literature |
|  4 | ChatGPT MCP                      | n/a — MCP down per task note; substituted by reading mathlib's own docstring (L243: "witnesses `W(k) ∣ W(2 * k)`"), which is itself the canonical statement | n/a  | mathlib docstring states the exact property            | the authoritative formulation is in-tree (see Phase 5) |
|  5 | Local references                 | `.mathlib-quality/references/` for "divisibility" / EDS               | n/a  | references dir not consulted (not required — mathlib has the exact decl) | the standard-form question is settled by the in-tree decl itself |
|  6 | nLab                             | "elliptic divisibility sequence"                                      | n/a  | nLab has no dedicated EDS page; concept is classical NT, not categorical | recorded n/a |
|  7 | nCatLab (if categorical)         | —                                                                     | n/a  | not a categorical concept                              | recorded n/a |
|  8 | Stacks Project (if alg geom)     | —                                                                     | n/a  | Stacks does not cover EDS / division-polynomial recurrences | recorded n/a |
|  9 | MathOverflow / Math.SE           | EDS divisibility property                                             | yes  | folklore: EDS ⟹ divisibility sequence (Ward)           | covered by #1 results (arXiv math/0404412, 1108.3051) |
| 10 | recent arXiv (last 5 yr)         | division polynomials / EDS divisibility (Stange 2025, etc.)           | yes  | reaffirms `n∣m ⟹ W_n∣W_m`                              | eprint.iacr 2025/521; arXiv 2310.01013 |

### Literature summary (Phase 3)

Concept identified as: the **divisibility property of (normalised) elliptic
divisibility sequences** — specifically the `n = 2` case `W(k) ∣ W(2k)`.
Sources agree on the standard form: **yes** — `m ∣ n ⟹ W_m ∣ W_n` is the defining
divisibility property (Ward 1948), and `k ∣ 2k` is its smallest nontrivial
instance. Mathlib packages the explicit witness `complEDS₂` for the `n=2` case and
the general `complEDS` for the `n` case.
Most general standard form: `IsDivSequence W` for a normalised EDS, i.e. `m ∣ n ⟹
W m ∣ W n`. This decl is the convenient `n=2` corollary used in `normEDS_even` and
downstream.
Disagreement with the literature: none.

---

### Generality analysis — `normEDS_dvd_normEDS_two_mul`

Literature-standard form (from Phase 3): `m ∣ n ⟹ W m ∣ W n` for a normalised EDS;
the `n=2` instance is exactly the present statement.

| # | Parameter / hypothesis | Current Lean form     | Literature-standard form         | Weaker form exists? | Reason |
|---|------------------------|-----------------------|-----------------------------------|---------------------|--------|
| 1 | `[CommRing R]`        | commutative ring      | commutative ring (the EDS recurrence needs a comm ring) | NO | `normEDS`/`preNormEDS` and the product identity live over `CommRing R`; this is already the mathlib-standard generality for the whole EDS API |
| 2 | `(b c d : R)`         | arbitrary initial data| arbitrary initial data            | NO | already fully general |
| 3 | `(k : ℤ)`             | integer index         | integer index                     | NO | EDS are ℤ-indexed by definition |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (it matches the mathlib-standard
generality of the EDS API exactly — it *is* the mathlib decl).
Number of weakening opportunities found: 0.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Notes |
|----|----------|----------|-------|
|  1 | bundled hyps → typeclasses? | no | nothing to bundle; the inputs are ring + data + index. |
|  2 | sequences/metric → filters/topology? | no | pure algebraic divisibility identity; no limits. |
|  3 | construction → universal property? | no | it's a `Dvd` witness, not a construction. |
|  4 | set+closure → bundled substructure? | no | n/a. |
|  5 | vector-space/field-specific → weaken typeclass? | no | already `CommRing`. |
|  6 | 1-categorical → higher-categorical? | no | n/a. |
|  7 | concrete index → general algebra? | no | `ℤ`-indexing is intrinsic to EDS; the general `m∣n` law (which mathlib could also expose) is a *different* lemma, not a reformulation of this one. |

Modern idiom available: **no**. This is a finite algebraic divisibility corollary;
there is no contemporary reformulation that improves organisation. Moot regardless
(Phase 5).

---

### Diamond / defeq risk — `normEDS_dvd_normEDS_two_mul`

n/a — declaration kind is `lemma` (no definitional equalities or instance-search
paths introduced).

---

### Mathlib search-status: `normEDS_dvd_normEDS_two_mul`

[A] Lean-Finder      n/a (index offline) — substituted by direct source read of pinned mathlib
[B] Loogle           pattern `normEDS _ _ _ _ ∣ normEDS _ _ _ (2 * _)` — **HIT** in pinned mathlib source (index tool offline; confirmed by grep on the pinned tree)
[C] LeanSearch       "normEDS divides normEDS two mul" — n/a (offline); confirmed by source read
[D] **Grep mathlib src** terms `normEDS_dvd_normEDS_two_mul`, `complEDS₂`, `normEDS_mul_complEDS₂` — **HIT**
[E] Name pattern     `normEDS_dvd_normEDS_two_mul` — **HIT**, exact name

Searched for both the user's current form and the general `IsDivSequence` form.

**Concluded: found in mathlib as `normEDS_dvd_normEDS_two_mul`; IDENTICAL form
(byte-for-byte, same statement AND same proof).**

Decisive evidence — the repo's **own pinned mathlib** contains it:

- File: `/Users/mcu22seu/Documents/GitHub/aintlib-main/.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:326`
- Pinned commit: `09b373db6e24` (per `lakefile.toml` rev), `git log -1` → `09b373db6e247a35cfa5e44578c09a20e7c97271`, dated 2026-06-21.
- The lemma in mathlib:
  ```lean
  lemma normEDS_dvd_normEDS_two_mul (k : ℤ) : normEDS b c d k ∣ normEDS b c d (2 * k) :=
    ⟨complEDS₂ .., (normEDS_mul_complEDS₂ ..).symm⟩
  ```
- `diff` of the project block (L925–931) against the mathlib block (L321–327)
  reported **IDENTICAL (no diff)**. Both sit in `section NormEDS`, no namespace.
- Its dependencies are likewise already in mathlib at the same generality:
  - `complEDS₂` (def) — mathlib L246, docstring "the 2-complement sequence … that witnesses `W(k) ∣ W(2 * k)` … `W(k) * Wᶜ₂(k) = W(2 * k)`".
  - `normEDS_mul_complEDS₂` — mathlib L321.
  - The broader `complEDS` / `complEDS_even` / `complEDS_odd` API (general `n`) — mathlib L392–545.

The project file (`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean`,
1672 lines) is a **superset fork** of the 547-line mathlib file; the first ~half is
a verbatim copy (same Apache header, same author) that includes this lemma. Mathlib
has since absorbed exactly this content, so the fork is now redundant for this decl.

---

### Call sites — `normEDS_dvd_normEDS_two_mul`

Internal use count: **0** (no occurrence anywhere in the repo outside the declaring
line — `grep -rn "normEDS_dvd_normEDS_two_mul"` across all `.lean` returns only
L930, the declaration itself).
External-to-file callers: 0.

| Caller file:line | Usage pattern |
|------------------|---------------|
| (none)           | —             |

Inline-derivation grep: the *product* identity `normEDS_mul_complEDS₂` and the
general `normEDS_mul_complEDS` ARE used heavily (L948, L1342, L1349, L1354, L1397–
1440) to build divisibility witnesses — but they go through the product/`complEDS`
lemmas directly, never through this `∣`-wrapper. So even within the fork this
specific `Dvd`-packaging lemma is dead. (Consistent with it being inherited
verbatim from upstream rather than something the project actively relies on.)

K = 0 internal uses + the equivalent witness re-derived inline elsewhere → strong
NO signal. Combined with Phase 5 (mathlib already has the exact decl), the verdict
is unambiguous.

---

### Composition check (Phase 6)

Can `normEDS_dvd_normEDS_two_mul` be derived from mathlib in ≤3 chained calls?

Attempt 1: `⟨complEDS₂ b c d k, (normEDS_mul_complEDS₂ b c d k).symm⟩`
  - Mathlib decls used: `complEDS₂`, `normEDS_mul_complEDS₂` (both already in mathlib).
  - Result: **succeeds** — this is literally the upstream proof; one anonymous-constructor + `.symm`.
  - But this is moot: mathlib already exposes the assembled lemma under this exact name, so there is nothing to inline — call sites should use the mathlib decl directly.

Conclusion: the decl is **already in mathlib verbatim** (NO-mathlib-has-it dominates;
the composition would only matter if mathlib lacked the named lemma, which it does not).

---

## Verdict: `normEDS_dvd_normEDS_two_mul`

**Category: `NO-mathlib-has-it`**

**Evidence:**
- Literature search (Phase 3): standard divisibility property of EDS (Ward 1948); `k∣2k` is the `n=2` case. Form is canonical.
- Generality analysis (Phase 4): MAXIMALLY GENERAL; no modern-idiom move.
- Mathlib search (Phase 5): **found in mathlib as `normEDS_dvd_normEDS_two_mul`; byte-identical statement and proof**, in the repo's own pinned mathlib `09b373db6e24`.
- Composition check (Phase 6): trivially the upstream proof; moot.

**Rationale:**

This declaration is not merely *covered* by mathlib — it **is** a mathlib
declaration. The project's `EllipticDivisibilitySequence.lean` is a forked,
extended copy of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (identical
copyright header and author, David Kurniadi Angdinata). At some point mathlib
absorbed the `complEDS₂` / `normEDS_mul_complEDS₂` / `normEDS_dvd_normEDS_two_mul`
block, and the repo's *currently pinned* mathlib commit (`09b373db6e24`, dated
2026-06-21) contains `normEDS_dvd_normEDS_two_mul` at line 326 with a `diff` of
**zero** against the project's lines 925–931. There is no generality gap, no
formulation gap, and nothing to upstream: it is already upstream.

The lemma also has **zero call sites** in the project (the active code uses the
underlying product lemma `normEDS_mul_complEDS₂` and the general `normEDS_mul_complEDS`
instead), reinforcing that this `Dvd`-wrapper is inherited dead weight in the fork
rather than a load-bearing project result.

**WHY not (refactor-actionable):**
Mathlib already has the exact decl — same name, same statement, same proof, at the
same generality (`CommRing R`, `b c d : R`, `k : ℤ`). Our form does not even
*follow from* a mathlib lemma in ≤1 line; it is literally the same lemma. The fork
copy is redundant.

Existing mathlib decl:  `normEDS_dvd_normEDS_two_mul`
Located at:             `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:326`
                        (in this repo: `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:326`, pinned commit `09b373db6e24`)
Our form follows in ≤1 line (it is the same statement):
```lean
example (b c d : R) (k : ℤ) : normEDS b c d k ∣ normEDS b c d (2 * k) :=
  normEDS_dvd_normEDS_two_mul k          -- the mathlib lemma
```
Call sites in our project (from Phase 6.0): **K = 0**.

Refactor plan:
1. This is part of a whole-file dedup, not a single-decl fix. The project file
   `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean` duplicates the
   first ~half of mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
   verbatim (lines through ~969 mirror mathlib lines through ~339). The correct
   cleanup is to **delete the duplicated upstream block** and `import
   Mathlib.NumberTheory.EllipticDivisibilitySequence` instead, keeping only the
   genuinely-new material the fork adds beyond mathlib (e.g. the `EllSequence.transf`
   / `Rel₄OfValid` / `Perm` machinery, `universalNormEDS`, `invarNum`, and whatever
   `complEDS`-track results post-date the pin).
2. For `normEDS_dvd_normEDS_two_mul` specifically: since K = 0 call sites, simply
   **remove the duplicated lemma** — nothing references it. No call-site rewrites
   needed.
3. Because the whole forked prefix is the issue, this decl should be handled as one
   line item in a file-level "re-sync fork against pinned mathlib" cleanup ticket on
   `main`, not as an isolated edit.

**Next action:** delete `normEDS_dvd_normEDS_two_mul` (and the surrounding verbatim
upstream block) from the project file; replace with an import of
`Mathlib.NumberTheory.EllipticDivisibilitySequence`. Track this under a file-level
"de-fork / re-sync against pinned mathlib" cleanup ticket, since the same applies to
all the duplicated upstream decls in this file (`complEDS₂`, `normEDS_mul_complEDS₂`,
`normEDS_even`, `normEDS_odd`, `preNormEDS*`, etc.).

---

## Next step

Delete the lemma (it is already in the repo's pinned mathlib, byte-identical, with
zero project call sites) as part of a file-level fork re-sync; import
`Mathlib.NumberTheory.EllipticDivisibilitySequence` rather than re-declaring it.

---

### Sources (Phase 3 literature)
- [Elliptic divisibility sequence — Wikipedia](https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence)
- [Divisibility sequence — Grokipedia](https://grokipedia.com/page/divisibility_sequence)
- [p-adic properties of division polynomials and EDS (arXiv math/0404412)](https://arxiv.org/pdf/math/0404412)
- [Integral points on elliptic curves and explicit valuations of division polynomials (arXiv 1108.3051)](https://arxiv.org/pdf/1108.3051)
- [Division polynomials for arbitrary isogenies, Stange (eprint 2025/521)](https://eprint.iacr.org/2025/521.pdf)
