# /mathlibable report — `EllSequence.compl'`

**Verdict: YES-but-generalise-first**

mathlib already contains the *special case* of this definition (`complEDS'`, hardwired to a normalised
EDS), authored by the same person who wrote this project file. The value of `compl'` is precisely the
**abstraction** of `complEDS'` over its two defining sequences — and that abstraction is what lets the
project prove the general divisibility witness `W(m) ∣ W(n·m)` for an **arbitrary** elliptic sequence,
which mathlib does *not* prove. So the correct action is to upstream `compl'` as a *generalisation of
mathlib's existing `complEDS'`*, not to add it as a fresh parallel definition.

- **Declaration:** `EllSequence.compl'`
- **Source:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1086`
- **Date:** 2026-06-21 (full 10-phase re-assessment; supersedes the 2026-06-18 Step-9 triage note)

---

## Baseline (Phase 0)

- lake build:               ⚠ stale (local build is stale per task context; reasoned from source — the
                            decl is part of the same author's vendored fork of the mathlib EDS file and
                            elaborates in the committed tree)
- decl `EllSequence.compl'`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1086`
- kind:                      `def` (well-founded recursion on `ℕ`, `R`-valued)
- has sorry:                 no
- module docstring summary:  EDS / division-polynomial machinery for the Nagell–Lutz theorem; this file
                            is a fork/rewrite of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
                            by the same author (identical copyright: David Kurniadi Angdinata, 2024).

Qualified name verified: base name `compl'`, inside `namespace EllSequence` (opened at line 1079),
under file-level `variable {R : Type u} [CommRing R]` and section `variable (W₁ compl₂ : ℤ → R) (m : ℤ)`.
⇒ **`EllSequence.compl'`** with signature `(W₁ compl₂ : ℤ → R) (m : ℤ) : ℕ → R`.

---

## Statement (Phase 1)

```lean
/-- Given two sequences representing `W(m)/W(1)` and `W(2m)/W(m)` respectively,
we construct the sequence representing `W(n*m)/W(m)` in a division-free way. -/
def compl' : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => letI k := n / 2 + 1
    have : k < n + 2 := by omega
    if hn : Even n
      then compl₂ (k * m) * compl' k
      else
        have : k + 1 < n + 2 := by
          have := (Nat.not_even_iff_odd.mp hn).pos; omega
        W₁ ((k + 1) * m + 1) * W₁ ((k + 1) * m - 1) * compl' k ^ 2
      - W₁ (k * m + 1) * W₁ (k * m - 1) * compl' (k + 1) ^ 2
```

**Prose.** Given an elliptic (divisibility) sequence `W : ℤ → R` over a commutative ring `R`, `compl'`
constructs the **complement sequence** whose `n`-th term is `W(n·m)/W(m)` — the cofactor witnessing the
classical EDS divisibility `W(m) ∣ W(n·m)` (Ward, 1948) — built by a strong recursion on `n` that uses
**no ring division**, so it is well defined over an arbitrary commutative ring. Crucially it is
parametrised over **two abstract input sequences**:
- `W₁ : ℤ → R`, representing the normalisation `W(·)/W(1)`, and
- `compl₂ : ℤ → R`, representing the 2-complement `W(2·)/W(·)`.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the value ring (commutative ring; mathematical role: coefficient ring).
- `(W₁ compl₂ : ℤ → R)` — the two abstract defining sequences (the load-bearing abstraction).
- `(m : ℤ)` — the base index `m` in `W(n·m)/W(m)`.

Conclusion (math): the sequence `n ↦ W(n·m)/W(m)`, division-free.
Conclusion (Lean): `n/a — definition` (`ℕ → R`); extended to `ℤ` by `compl` (line 1099) via the sign,
and specialised to a normalised EDS by `complEDS b c d m := compl (normEDS b c d) (compl₂EDS b c d) m`.

---

## Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is a named `def` of a recognised mathematical device (the EDS "complement"/quotient sequence)
and the recursion core on which the project's central divisibility theorem `W(m) ∣ W(n·m)` rests.
(Literature width was EXHAUSTIVE regardless.)

## One-line check (Phase 2b)

Body line count: ~9 substantive lines (a two-branch well-founded recursion with two recursive calls).
One-liner verdict: **MULTI-LINE** — exemption table not required.

---

## Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                 | Hit? | Standard form found                                          | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------|------|--------------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | EDS `W(m)∣W(nm)` division-free recurrence "complement sequence"                        | yes  | division-free recurrences for EDS over rings                 | arXiv 2102.07573, Stange formulary; no *named* standalone "complement sequence" object in the literature |
|  2 | WebSearch (general form)         | EDS over commutative ring, `W_m∣W_n`, Ward                                             | yes  | `m∣n ⟹ W(m)∣W(n)` for **arbitrary** EDS; over arbitrary comm. ring | Ward 1948; arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings" — purely-algebraic, any-ring treatment |
|  3 | WebSearch (named-after/aliases)  | division polynomials ψ_m∣ψ_n; elliptic nets; quotient `W(nm)/W(m)`                     | yes  | `Ψ_{nm} = (Ψ_n∘[m])·Ψ_m^{n²}`; net/quotient devices          | Wikipedia "Division polynomials"; Stange "Elliptic nets and elliptic curves" (0710.1316) |
|  4 | ChatGPT MCP                      | (a) recursion-identity reading; (b) generality of `W(m)∣W(nm)`                         | n/a  | —                                                            | MCP unavailable: Codex backend errored on stdin (env issue, per task brief). Substituted by WebFetch of the Wikipedia source (row 9) + direct side-by-side source reading (Phase 5) |
|  5 | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/`                                | n/a  | (directory absent)                                           | no per-project `references/` dir exists — recorded n/a |
|  6 | nLab                             | "elliptic divisibility sequence"                                                       | yes  | `w_{m+n}w_{m-n} = w_{m+1}w_{m-1}w_n² - w_{n+1}w_{n-1}w_m²`, with `n∣m ⟹ u_n∣u_m` | EDS as Ward recursion; divisibility is a defining property of *every* EDS |
|  7 | nCatLab (if categorical)         | —                                                                                     | n/a  | —                                                            | not a categorical concept |
|  8 | Stacks Project (if alg geom)     | —                                                                                     | n/a  | —                                                            | Stacks has no EDS / division-polynomial-sequence entry |
|  9 | MathOverflow / Wikipedia source  | WebFetch en.wikipedia.org/wiki/Elliptic_divisibility_sequence — divisibility property  | yes  | "An EDS is a divisibility sequence: `m∣n ⟹ W_m∣W_n`"; "fundamental characteristic of all EDS" | confirms ARBITRARY-EDS generality; classical over ℤ, normalised by `W₁=1` |
| 10 | recent arXiv (last 5 years)      | EDS over commutative rings; elliptic nets valuations (2024–2025)                       | yes  | any-commutative-ring EDS divisibility                        | 2604.05280 (2026), 2512.09601 (2025) — modern any-ring framing |

### Literature summary (Phase 3)

Concept identified as: the **complement / quotient sequence** of an EDS — the cofactor `W(n·m)/W(m)`
witnessing `W(m) ∣ W(n·m)`. The divisibility `m ∣ n ⟹ W(m) ∣ W(n)` is one of the two *defining*
properties of an elliptic divisibility sequence (Ward 1948).
Sources agree on the standard form: **yes** — the divisibility property holds for an **arbitrary** EDS
(Wikipedia "fundamental characteristic of all EDS"; nLab; Ward), and the modern treatment states/proves
it over an **arbitrary commutative ring** (arXiv 2604.05280), exactly the division-free setting this def
targets.
Most general standard form: for *any* elliptic (divisibility) sequence `W : ℤ → R` over a commutative
ring, `W(m) ∣ W(n·m)`, with a division-free cofactor witness.
Generality dimensions where the literature varies:
  - Coefficient domain: classical ℤ  →  modern **arbitrary commutative ring** (the latter is the
    current standard; matches `[CommRing R]`).
  - Which sequence: division-polynomial sequence of a fixed curve  →  the **general EDS** `W`
    (the general form is the literature standard).
Disagreement with the literature: none. Note that the literature gives the *theorem* and the cofactor
*device*; it does not enshrine a *standalone named definition* "the complement sequence" — that naming
is formalisation-specific (mathlib's `complEDS'` / this project's `compl'`).

---

## Generality analysis — `EllSequence.compl'`

Literature-standard form (from Phase 3): a division-free cofactor for `W(m) ∣ W(n·m)` for an
**arbitrary** EDS `W` over a commutative ring.

| # | Parameter / hypothesis        | Current Lean form                            | Literature-standard form                | Weaker/abstracter form exists? | Reason |
|---|-------------------------------|----------------------------------------------|-----------------------------------------|--------------------------------|--------|
| 1 | `[CommRing R]`               | commutative ring                              | commutative ring (division-free)        | NO                             | already the modern any-ring generality; the whole point of the division-free recursion |
| 2 | `(W₁ : ℤ → R)`               | **abstract** sequence `≈ W(·)/W(1)`           | the general EDS's normalisation         | already maximally abstract     | mathlib's `complEDS'` hardwires this to `normEDS b c d`; abstracting it IS the generalisation |
| 3 | `(compl₂ : ℤ → R)`           | **abstract** 2-complement `≈ W(2·)/W(·)`      | the general EDS's 2-complement          | already maximally abstract     | mathlib's `complEDS'` hardwires this to `complEDS₂ b c d`; abstracting it IS the generalisation |
| 4 | `(m : ℤ)`                    | integer base index                            | integer base index                      | NO                             | already fully general |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** as a standalone object (it is already the abstract,
any-commutative-ring form — strictly *more* general than mathlib's `complEDS'`).
Number of weakening opportunities on `compl'` itself: 0.

**But relative to mathlib this is STRICTLY MORE GENERAL THAN the existing decl `complEDS'`**, and that
is what drives the verdict: the right contribution is to *replace* mathlib's specialised `complEDS'`
with this abstract `compl'`, recovering `complEDS'` as the instantiation
`compl (normEDS b c d) (complEDS₂ b c d) k`. So the verdict is **YES-but-generalise-first** with reason
LITERATURE-WEAKENING (the user's abstract form is the literature-standard generality; mathlib currently
ships only the specialisation).

Proposed restatement (mathlib-side): keep `compl'`/`compl` abstract over `(W₁ compl₂ : ℤ → R)`; redefine
mathlib's `complEDS' b c d k n := compl (normEDS b c d) (complEDS₂ b c d) k n` (and likewise `complEDS`),
then re-derive the existing `complEDS'_even/odd`, `complEDS_*`, `complEDSRec'/Rec`, `map_complEDS'` from
the abstract API; **and add the missing general witness theorem** (below).

Cost of restatement: **MODERATE** — the recursion and its `_even/_odd`/`map` lemmas transfer mechanically
(the project already proves the abstract versions: `compl_ofNat`, `compl_neg`, `EllSequence.map_compl'`);
the genuinely new content (the general divisibility identity) is already proven in the project and would
transfer. EXPENSIVE only if one re-derives every downstream `normEDS`-specific lemma — but those follow
by instantiation. (Cost does not downgrade the verdict.)

### Modern-idiom check (Phase 4c)

| #  | Question                                                                 | Applies? | Proposed reformulation | Mathlib downstream |
|----|--------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preamble → typeclass/instance?                          | no       | — | the abstract sequences `W₁, compl₂` are genuine data (function arguments), not a structure to bundle; `IsEllSequence` already exists as the predicate |
|  2 | sequences/metric → filters/topology?                                     | no       | — | finite algebraic recursion; no limiting notion |
|  3 | construct an object → universal-property class?                          | no       | — | this *is* the explicit construction; no universal property at play |
|  4 | set+closure-predicate → bundled substructure?                           | no       | — | not a substructure |
|  5 | vector-space/field-specific → weaken typeclass?                          | no       | — | already `[CommRing R]`, the right level (division-free) |
|  6 | 1-categorical → higher-categorical?                                      | no       | — | n/a |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive structure?                  | no       | — | the index is intrinsically ℤ/ℕ (the EDS recurrence lives on ℤ) |

**Concrete-via-abstract (the key signal).** The relevant move here is *exactly* the
parametrise-the-concrete-input idiom: `compl'` is `complEDS'` with its two concrete defining sequences
promoted to free arguments. The proof of the project's central theorem
`IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` (line 1296) unfolds `compl'` and inducts on
its recursion using only the **abstract characterisations** `h₁ : ∀ m, W 1 * W₁ m = W m` and
`h₂ : ∀ m, W m * compl₂ m = W (2*m)` — it never touches a specific EDS. That is precisely why the
abstraction is load-bearing rather than cosmetic, and why this is a genuine generalisation, not flavour.

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**, but it coincides with the literature-weakening already identified
(abstracting `normEDS`/`complEDS₂` into `W₁`/`compl₂`). Reason it is a real improvement, not cosmetics:
it is the *only* form under which the general divisibility theorem `W(m) ∣ W(n·m)` for an arbitrary
`IsEllSequence W` can be (and is) stated and proven — see Phase 5/6.

---

## Diamond / defeq risk — `EllSequence.compl'` (Phase 4.5)

| # | Risk                          | Verdict | Evidence / rationale                                                                 |
|---|-------------------------------|---------|--------------------------------------------------------------------------------------|
| 1 | Typeclass diamond            | none    | no new instance; `[CommRing R]` is an ordinary hypothesis, no instance emitted |
| 2 | Reducibility leak            | none    | plain `def` (no `@[reducible]`); a well-founded recursion — sealed, unfolds only via its `_even/_odd` equation lemmas |
| 3 | Non-canonical unfolding      | low     | well-founded recursion; like mathlib's `complEDS'`, raw `compl'` does not `rfl`-unfold — consumers use the projected `compl'_even/odd` lemmas (the project provides these as `complEDS_even/odd` etc.) |
| 4 | Instance priority collision  | n/a     | not an instance |
| 5 | Universe-polymorphism issues | none    | `R : Type u` only; values in `R`, index in `ℕ`/`ℤ` — no extra universe forced |
| 6 | Coercion ambiguity           | none    | no `CoeFun`/`CoeSort` |

### Risk verdict (Phase 4.5)

Overall risk: **LOW**. Mirrors mathlib's existing `complEDS'` exactly (same recursion shape, already in
mathlib without issue). No HIGH rows.

---

## Mathlib search-status: `EllSequence.compl'`

Pinned mathlib: `lakefile.toml` → mathlib (toolchain `v4.32.0-rc1`); relevant file
`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines, same author).

[A] Lean-Finder       n/a: AI index tool not available in this environment (recorded per protocol).
[B] Loogle            n/a: `lean_loogle` not surfaced as a tool here. Substituted by exhaustive direct
                      grep of the pinned mathlib tree (method D), which is authoritative since the exact
                      pinned source is on disk.
[C] LeanSearch        n/a: `lean_leansearch` not surfaced as a tool here. Substituted by D.
[D] Grep mathlib src  Searched all of `.lake/packages/mathlib/Mathlib/`:
                       - `namespace EllSequence` → **0 hits** (exists only in this project).
                       - `complEDS'` → **1 file**, `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:392`.
                       - abstract `(compl₂ : ℤ → R)`-style complement → **0 hits** (the `compl₂ ` hits in
                         mathlib are unrelated: SesquilinearForm / TensorProduct).
                       - general witness identity `… = normEDS b c d (n * k)` → **0 hits** (mathlib does
                         NOT prove `W(k)∣W(nk)` in general; only the `n=2` case `normEDS_mul_complEDS₂`,
                         `normEDS_dvd_normEDS_two_mul`).
[E] Name pattern      `compl` family in mathlib EDS file = `complEDS₂`, `complEDS'`, `complEDS`,
                      `complEDSRec'/Rec`, `map_complEDS₂/'`/`map_complEDS` — all **hardwired to
                      `normEDS b c d` / `complEDS₂ b c d`** via the section `variable (b c d k)`. No
                      abstractly-parametrised variant anywhere.

Searched for both:
  - the user's abstract form `(W₁, compl₂)` → not in mathlib.
  - the literature-standard general form (general EDS witness) → the *theorem* is not in mathlib at all;
    the *def* exists only as the `normEDS`-specialised `complEDS'`.

Concluded: **found a partial match — mathlib has `complEDS'`
(`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:392`), which is the
`normEDS b c d` / `complEDS₂ b c d`-specialised case of `compl'`; the abstract generalisation, and the
general divisibility witness it enables, are NOT in mathlib.**

### Recursion-identity verification (read both sources side-by-side)

mathlib `complEDS'` (line 392, section vars `b c d k`):
```lean
| (n + 2) => let m := n / 2 + 1
    if hn : Even n then complEDS' m * complEDS₂ b c d (m * k) else
      complEDS' m ^ 2 * normEDS b c d ((m + 1) * k + 1) * normEDS b c d ((m + 1) * k - 1) -
        complEDS' (m + 1) ^ 2 * normEDS b c d (m * k + 1) * normEDS b c d (m * k - 1)
```
project `compl'` (line 1086), under `normEDS ↔ W₁`, `complEDS₂ ↔ compl₂`, `k ↔ m`:
- even branch: `complEDS' m * complEDS₂ (m*k)`  ≡  `compl₂ (k*m) * compl' k`  ✓ (commuted product)
- odd branch:  `complEDS' m² · normEDS((m+1)k±1) − complEDS'(m+1)² · normEDS(mk±1)`
            ≡  `W₁((k+1)m±1)·compl' k² − W₁(km±1)·compl'(k+1)²`  ✓
The two recursive bodies are the **same recursion**; `compl'` = `complEDS'` with the two concrete
sequences abstracted. (Verified by direct reading; ChatGPT MCP cross-check was unavailable.)

---

## Composition check (Phase 6)

### Call sites — `EllSequence.compl'`

Internal use count (within the project, excluding the `def` body lines 1086–1096): **K ≥ 6**
External-to-file callers: **0** (it is the recursion primitive; external consumers use the wrappers
`compl` / `complEDS` / `complEDS`).

| Caller (same file):line | Usage pattern (excerpt) |
|-------------------------|--------------------------|
| `…:1099` `EllSequence.compl` | `n.sign * compl' W₁ compl₂ m n.natAbs` (the ℤ-extension) |
| `…:1101–1102` `compl_ofNat` | `compl W₁ compl₂ m n = compl' W₁ compl₂ m n` |
| `…:1140–1145` `EllSequence.map_compl'` | `f (compl' …) = compl' (f∘W₁) (f∘compl₂) m n` |
| `…:1302,1304` `IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` | unfolds `compl'` and inducts on its recursion (the payoff theorem) |
| `…:1413,1416,1419` `redInvarDenom`/`complEDS` simp lemmas | `simp [redInvarDenom, complEDS, compl', compl]` |

Inline-derivation grep (re-derived elsewhere without using `compl'`?): **(none)** — it is the unique
recursion core; consumers reference it, none bypass it.

⇒ Real, load-bearing API (K ≥ 6, no inline re-derivation) → composability signal points **YES**.

### Composition check

Can `compl'` be derived from mathlib in ≤3 chained calls? **No.**

Attempt 1: instantiate mathlib's `complEDS'` at `(W₁, compl₂) := (normEDS, complEDS₂)`.
  - Result: **fails** — gives only the `normEDS`-special case; cannot recover the abstract `(W₁, compl₂)`
    object (you cannot un-specialise a definition by calling it).
Attempt 2: obtain the general witness `W(m)·compl … = W(n·m)` for arbitrary `IsEllSequence W` from
mathlib lemmas about `complEDS'`.
  - Result: **fails** — mathlib proves no such general identity (only `normEDS_mul_complEDS₂`, the `n=2`
    case). The project proves it by a multi-branch strong induction over the `compl'` recursion using
    `h₁`/`h₂` (lines 1296–1320) — dozens of lines, not a 1–3-call composition.

Conclusion: **NOT-COMPOSABLE.**

---

## Verdict: `EllSequence.compl'`

**Category:** YES-but-generalise-first  (reason: LITERATURE-WEAKENING / concrete-via-abstract)

**Evidence:**
- Literature search (Phase 3): `W(m)∣W(n·m)` is a defining property of an **arbitrary** EDS (Ward;
  Wikipedia; nLab), stated over an **arbitrary commutative ring** in the modern treatment (arXiv
  2604.05280). The general form is the literature standard.
- Generality analysis (Phase 4): `compl'` is the maximally-general (abstract, any-`CommRing`) form; it
  is **strictly more general than mathlib's `complEDS'`**, which hardwires `normEDS`/`complEDS₂`.
- Mathlib search (Phase 5): partial match — `complEDS'` (`…/EllipticDivisibilitySequence.lean:392`) is
  the specialisation; the abstract form and the general witness theorem are **absent** from mathlib.
- Composition check (Phase 6): NOT-COMPOSABLE (you cannot un-specialise a def; the general identity is a
  multi-line induction mathlib does not have).

**Rationale.**
mathlib's `complEDS'` and this project's `compl'` are the *same recursion* — verified by reading both
bodies side by side (even branch `complEDS' m * complEDS₂(m·k)` ≡ `compl₂(k·m) * compl' k`; odd branch
identical up to the `normEDS↔W₁`, `complEDS₂↔compl₂`, `k↔m` renaming). The only difference is that
`complEDS'` bakes in the two concrete sequences `normEDS b c d` and `complEDS₂ b c d`, whereas `compl'`
takes them as abstract parameters `W₁, compl₂ : ℤ → R`. This abstraction is **load-bearing, not
cosmetic**: the project's central result
`IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` (line 1296) proves
`W(m) · compl W₁ compl₂ m n = W(n·m)` — i.e. the divisibility witness `W(m) ∣ W(n·m)` — for an
**arbitrary** `IsEllSequence W` whose first two terms are non-zero-divisors, by inducting on the `compl'`
recursion using only the abstract laws `W 1 · W₁ m = W m` and `W m · compl₂ m = W(2m)`. mathlib cannot
even state this in its current form, and in fact **mathlib never proves the general witness identity at
all** — it defines `complEDS'`, proves its `_even`/`_odd`/`map` equations, but stops at the `n = 2`
divisibility (`normEDS_mul_complEDS₂`). So the project is not duplicating mathlib; it is supplying the
generalisation that unlocks the theorem the definition was named to witness.

Because the right action touches an existing mathlib declaration's name/API surface (`complEDS'` →
generalise to `compl'`, recover `complEDS'` as the `normEDS`/`complEDS₂` instantiation) rather than
adding a fresh parallel def, the bucket is **YES-but-generalise-first**, not YES-add-as-is. It is *not*
BORDERLINE: the mathematics is unambiguous — mathlib has the strict specialisation, the literature
standard is the general form, and the general form is what proves the headline divisibility.

**Reason for the generalisation:** LITERATURE-WEAKENING — Phase 4 found mathlib's `complEDS'` strictly
narrower than the literature-standard "arbitrary EDS over a commutative ring" form; the user's abstract
`compl'` is exactly that standard form. (Equivalently, the Phase-4c concrete-via-abstract idiom: promote
the two concrete defining sequences of `complEDS'` to free arguments.)

**Proposed restatement (mathlib-side):**
```lean
namespace EllSequence
/-- The complement sequence `n ↦ W(n·m)/W(m)` for an EDS with normalisation `W₁ ≈ W(·)/W(1)`
and 2-complement `compl₂ ≈ W(2·)/W(·)`, built division-free. -/
def compl' (W₁ compl₂ : ℤ → R) (m : ℤ) : ℕ → R := …   -- (this project's body, verbatim)
def compl  (W₁ compl₂ : ℤ → R) (m : ℤ) (n : ℤ) : R := n.sign * compl' W₁ compl₂ m n.natAbs
end EllSequence

-- recover mathlib's existing decls as instantiations:
def complEDS' (b c d k : R/ℤ) (n : ℕ) : R := EllSequence.compl' (normEDS b c d) (complEDS₂ b c d) k n
def complEDS  (b c d k : …)       (n : ℤ) : R := EllSequence.compl  (normEDS b c d) (complEDS₂ b c d) k n

-- the genuinely new theorem (project lines 1287–1320), the headline content:
theorem IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors
    {W : ℤ → R} (ell : IsEllSequence W) (W₁ compl₂ : ℤ → R)
    (h₁ : ∀ m, W 1 * W₁ m = W m) (h₂ : ∀ m, W m * compl₂ m = W (2 * m))
    (m n : ℤ) (mem : W m ∈ nonZeroDivisors R) :
    W m * EllSequence.compl W₁ compl₂ m n = W (n * m) := by
  sorry  -- transfers from the project's existing proof
```
Estimated cost of regeneralisation: **MODERATE** (the `_even`/`_odd`/`map` lemmas and the witness theorem
are already proven in the project against the abstract form; the `normEDS`-specific corollaries follow by
instantiation). Cost does **not** downgrade the verdict.

**Mathlib downstream this enables:**
- The general EDS divisibility `W(m) ∣ W(n·m)` for any `IsEllSequence W` — currently absent from mathlib
  despite `IsEllSequence`, `IsDivSequence` and `complEDS'` all already living there. This closes the gap
  between mathlib's `IsDivSequence`/`IsEllSequence` predicates (which *assert* `m∣n ⟹ W m ∣ W n`) and a
  *constructive witness* for it on the canonical `n·m` axis.
- `normEDS k ∣ normEDS (n·k)` for the normalised EDS, as a one-line instantiation (the project's
  `normEDS_mul_complEDS`, line 1338) — a strict strengthening of mathlib's `n=2`-only
  `normEDS_dvd_normEDS_two_mul`.
- A single abstract `compl`/`compl'` API (with `compl_ofNat`, `compl_neg`, `map_compl'`) from which
  mathlib's existing `complEDS'_even/odd`, `complEDS_*`, `map_complEDS'` specialise — less duplicated
  surface.

**Next action:** run `/generalise EllSequence.compl'` (tensioning against both the literature-standard
general-EDS form and mathlib's existing `complEDS'`), landing it as a **refactor PR** to
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` that (i) generalises `complEDS'` to the abstract
`compl'`, (ii) re-derives the existing `complEDS'`/`complEDS` API by instantiation, and (iii) adds the
general divisibility witness theorem. Because it changes a mathlib decl's API surface and is by the same
author, coordinate the refactor with the upstream author / a `Mathlib/NumberTheory` reviewer.

---

## Next step

Run `/generalise EllSequence.compl'`, then open a refactor PR to
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` generalising `complEDS'` to the abstract
`compl'` and adding the general `W(m) ∣ W(n·m)` witness theorem; recover the existing `complEDS'`/
`complEDS` API by instantiation. Coordinate with the upstream author (same person) / a NumberTheory
reviewer since it touches mathlib's existing API surface.
