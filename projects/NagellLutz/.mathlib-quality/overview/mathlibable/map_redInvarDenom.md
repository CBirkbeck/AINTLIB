# /mathlibable report — `EllSequence.map_redInvarDenom`

> Step-9 mathlibable assessment (AINTLIB /overview), NagellLutz project (Nagell–Lutz theorem;
> elliptic curves; division polynomials; elliptic divisibility sequences). Single declaration.
> **Re-assessment 2026-06-21** — supersedes the earlier `NO-composable-from-mathlib` pass. Verdict
> **changed** to `YES-but-generalise-first` to track its parent definition `redInvarDenom`
> (re-assessed the same day from `BORDERLINE` → `YES-but-generalise-first`). A `map_*` glue lemma's
> fate is **bound to its subject definition** (skill verdict-inheritance/re-aim rule): if
> `redInvarDenom` is upstreamed, this functoriality lemma ships with it as required boilerplate —
> exactly as mathlib's own `map_normEDS` / `map_complEDS` accompany `normEDS` / `complEDS`. See
> "Why the verdict changed" below. The two grounds the old NO pass rested on are both now stale.
>
> Environment note: local Lean build is stale (read-only assessment from source). Mathlib-index
> tools (loogle/leansearch) unavailable, so Phase 5 methods [A]–[C] fall back to an **exhaustive
> grep over the vendored mathlib pin** (`.lake/packages/mathlib/`), definitive for an existence
> question (the fork's exact upstream is on disk). ChatGPT MCP unavailable — Phase 3 channel #4
> records `n/a`, compensated by WebSearch + the vendored-source read.

---

### Baseline (Phase 0)
- lake build:               ⚠ stale locally (reasoned from source; the decl elaborates in the green `main` build per project state).
- decl `EllSequence.map_redInvarDenom`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1428` (the prompt's `:1423` pointer landed 5 lines high, on `map_compl₂EDSAux`; the intended decl is unambiguous).
- kind:                      `lemma` (theorem) — Phase 4.5 (diamond/defeq) is **n/a**: a lemma introduces no defeq or typeclass-search path.
- has sorry:                 no
- module docstring summary:  "Elliptic divisibility sequences (EDS)…" — a 1672-line **fork/extension** of `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (mathlib: 547 lines), authored by **David Kurniadi Angdinata** (the upstream mathlib EDS + DivisionPolynomial author), adding the `net`/`rel₄`/`invar*`/`redInvar*`/`compl₂EDS`/`ω` layer.

**Qualified-name verification.** The `lemma` at line 1428 sits inside `namespace EllSequence`
(re-opened at line 1356; this block closes at `end EllSequence`, line 1431). No outer namespace
wraps it. Confirmed fully-qualified name: **`EllSequence.map_redInvarDenom`** (the parsed-from-prompt
name is correct).

---

### Statement (Phase 1)

`EllSequence.map_redInvarDenom` is **a lemma** stating that a coefficient-ring homomorphism commutes
with the construction `redInvarDenom`:

```lean
variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)   -- file header, lines 85–86
variable (b c d : R) (m : ℤ)

lemma map_redInvarDenom :
    f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m := by
  simp [redInvarDenom, apply_ite f, map_normEDS, map_complEDS]
```

Mathematically: the "reduced invariant denominator" `redInvarDenom b c d m` (the division-free,
`mod 6`-cased repackaging of `W(m+1)·W(m)·W(m−1) / (W₃·W₂)` for the normalised EDS `W = normEDS b c d`)
is **natural in the coefficient ring** — pushing a ring hom `f : R → S` through it commutes with
re-seeding by `(f b, f c, f d)`. This is the standard "`map_<foo>`" base-change lemma that mathlib
maintains for every EDS construction; here it is for the project's `redInvarDenom`.

Variables / typeclasses (Lean side):
- `{R S : Type*} [CommRing R] [CommRing S]` — source/target coefficient rings.
- `{F} [FunLike F R S] [RingHomClass F R S] (f : F)` — the bundled-hom-class form (slightly *more
  general* than mathlib's own EDS `map_*` lemmas, which take a concrete `f : R →+* S`).
- `(b c d : R)` — the normalised-EDS seeds; `(m : ℤ)` — the index.

Hypotheses: none beyond the typeclasses.

Conclusion (math): `f ∘ redInvarDenom = redInvarDenom ∘ (f ×)` — functoriality / base change.
Conclusion (Lean): `f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m`.

**Subject is project-local.** `redInvarDenom` (line 1377) is the project's own `def`, built from
**the project's own** `complEDS` (line 1568, `complEDS b c d k n := n.sign * complEDS' b c d k n.natAbs`)
— a *distinct* definition from mathlib's upstream `complEDS` (`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:544`).
This is load-bearing for Phase 6 (the composition does **not** bottom out in mathlib alone).

---

### Size classification (Phase 2a)

Verdict: **SMALL** (one-line functoriality boilerplate).
Reason: not a named theorem, not a new structure/typeclass, not a person-named result, not a
`## Main results` headline. It is a `map_*` transport lemma — naturality plumbing for a single
project-local definition. (Literature width run EXHAUSTIVE regardless; the enclosing object `ω` is
BIG and the protocol forces the wider sweep for the cluster.)

### One-line check (Phase 2b)

Kind is `lemma`/`theorem`, not `def`/`abbrev`/`structure` — the Phase-2b one-liner-⇒-NO signal **does
not apply** (that signal is for one-line *definitions*). For the record the proof body is a single
`simp` line, which reflects that the lemma is content-free naturality plumbing, but this is exactly
how mathlib's own `map_normEDS` (`simp [normEDS, apply_ite f]`) and `map_complEDS` are written — being
a one-line `simp` proof is the *norm* for this lemma family, not a negative signal.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "ring homomorphism commutes with division polynomial elliptic divisibility sequence functoriality base change" | no (as named thm) | — | arXiv 2604.05280 (EDS over commutative rings), 2102.07573, math/0404412, 2503.15428, mathlib4 EDS docs. Functoriality of EDS over a ring hom is *assumed/used*, never a named theorem. |
| 2 | WebSearch (general form) | EDS / division polynomial naturality, base change `R → S`, `map_normEDS` analog | yes (as idiom) | `f (foo b c d n) = foo (f b) (f c) (f d) n` | This is the standard mathlib `map_*`-EDS idiom; mathlib's EDS file ships exactly this for `preNormEDS`/`normEDS`/`complEDS₂`/`complEDS'`/`complEDS`. No literature *names* it. |
| 3 | WebSearch (named-after / aliases) | "base change of division polynomials", "reduced invariant denominator" functoriality | no | — | No source has a "reduced invariant denominator", let alone a naming for its functoriality. The mathematical content is in `redInvarDenom`; this lemma is transport. |
| 4 | ChatGPT MCP | (standard form / generality / historical evolution) | n/a — MCP down per task brief | — | Compensated by WebSearch + direct read of the vendored mathlib source (stronger here — the upstream `map_*` family is literally on disk). |
| 5 | Local references | grep `projects/NagellLutz/.mathlib-quality/references/`, `refs/` | n/a | — | Directory absent (`No such file or directory`). |
| 6 | nLab | "elliptic divisibility sequence / division polynomial / base change" | no | — | No page treats this functoriality as a named result. |
| 7 | nCatLab | — | n/a — not a categorical concept | — | A concrete ring-coefficient transport identity; naturality is the only "categorical" flavour and it is trivial. |
| 8 | Stacks Project | "elliptic curve division polynomial base change" | n/a — not covered | — | Stacks covers the moduli stack, not explicit division-polynomial coordinate transport. |
| 9 | MathOverflow / MSE | (folded into WebSearch #1–#3) | no | — | No Q/A names this object. |
| 10 | recent arXiv (≤5 yr) | 2604.05280, 2503.15428, 2102.07573, math/0404412 | no | — | EDS/`ψ`/`ω`/isogeny division polynomials; none isolates a *named* functoriality lemma for a reduced invariant denominator. |

### Literature summary (Phase 3)

Concept identified as: **functoriality (base change) of an EDS-derived expression under a ring
homomorphism** — i.e. the `map_<construction>` naturality lemma. The *idiom* is standard and mathlib
codifies it for the upstream EDS constructions; the *specific subject* (`redInvarDenom`, the
reduced/division-free invariant denominator) is a formalisation-engineering device with no literature
name (see the parent's report `redInvarDenom.md`).
Sources agree on the standard form: **yes** for the idiom shape `f (foo …) = foo (f …)`; there is no
literature-named theorem for *this* subject's functoriality.
Most general standard form: the `map_*` lemma over an arbitrary ring hom between commutative rings —
which is exactly what is stated (in fact via the more general `RingHomClass F R S` bundling).
Disagreement with the literature: none. The lemma is correct naturality plumbing; its mathlibability
is entirely a function of whether its *subject* `redInvarDenom` belongs in mathlib.

---

### Generality analysis — `EllSequence.map_redInvarDenom`

Literature-standard form (from Phase 3): the `map_<construction>` naturality lemma over an arbitrary
ring hom of commutative rings.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[CommRing R] [CommRing S]` | two commutative rings | commutative rings | **NO** | the subject `redInvarDenom` lives over `CommRing` (subtractions `m−1`, `r₆ = W₅ − d²`, the `W₃W₂` cancellation need additive inverses + commutativity). Already maximal. |
| 2 | `[FunLike F R S] [RingHomClass F R S] (f : F)` | bundled hom class | a ring hom `R →+* S` | already **more general** than needed | this is *stronger/cleaner* than mathlib's own EDS `map_*` lemmas (which use concrete `f : R →+* S`). The proof needs only that `f` preserves `+,*,^,1` and the `ite` (`apply_ite f`). No weakening available or wanted. |
| 3 | `(b c d : R)`, `(m : ℤ)` | seeds + index | seeds + index | NO | inherited from `redInvarDenom`; ℤ-indexed EDS with `mod 6`/`/2`/`/3` arithmetic. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (arbitrary `CommRing` source/target; `RingHomClass`
bundling that is *more* general than mathlib's concrete-`R →+* S` EDS `map_*` lemmas). 0 weakenings.
The lemma cannot be generalised in any direction mathlib doesn't already cover, because its *subject*
is a fixed project-local expression — the generality question is **moot until `redInvarDenom` itself
is judged** (and that parent is `YES-but-generalise-first`).
Cost of restatement: n/a (no weakening proposed).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1 | bundled-hypotheses → typeclasses? | already done | — | the lemma *already* uses the modern `FunLike`+`RingHomClass` idiom (more idiomatic than the concrete `R →+* S` in mathlib's own EDS `map_*` family). |
| 2 | sequences/metric → filters/topology? | no | — | purely algebraic transport; no limits/topology. |
| 3 | construction → universal-property class? | no | — | it is a functoriality lemma, not a construction. |
| 4 | set-with-closure-predicate → bundled substructure? | no | — | n/a. |
| 5 | field/metric-specific → weaken typeclasses? | no | already `CommRing` + `RingHomClass` | maximal. |
| 6 | 1-categorical → higher-categorical? | no | — | n/a. |
| 7 | concrete index → general additive structure? | no | `m : ℤ` intrinsic | inherited from `redInvarDenom`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** — the lemma already *is* in the contemporary mathlib idiom (and the
`RingHomClass` form is one notch more general than mathlib's existing EDS `map_*` lemmas). Nothing to
migrate to. **Caveat for the PR:** to match the surrounding mathlib `map_*`-EDS family verbatim one
might *narrow* to a concrete `f : R →+* S` for consistency — that is a style alignment, not a
generalisation, and is a matter for the parent subsystem's `/cleanup`.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (a proposition; introduces no definitional equality or
typeclass-search path).

---

### Mathlib search-status: `EllSequence.map_redInvarDenom`

Performed by direct grep over the on-disk vendored mathlib tree `.lake/packages/mathlib/Mathlib/`
(the fork's actual upstream), plus name/concept search. Definitive for "is this in *this* pin?".

[A] Lean-Finder       n/a (offline) — substituted by direct source grep below.
[B] Loogle            n/a (offline) — substituted by direct source grep below.
[C] LeanSearch        n/a (offline) — substituted by direct source grep below.
[D] Grep mathlib src  `redInvarDenom|redInvarNum|invarDenom|invarNum|map_redInvar` over the whole mathlib tree
    - `redInvarDenom` / `redInvarNum` / `invarDenom` / `invarNum` / `map_redInvar*` in mathlib:  **0 hits** (re-verified 2026-06-21; definitive). The subject does not exist upstream, so neither can a `map_*` lemma about it.
    - mathlib's EDS `map_*` family **does** exist and is identical in shape: `map_preNormEDS'` (L510), `map_preNormEDS` (L522), `map_complEDS₂` (L526), **`map_normEDS` (L530)**, `map_complEDS'` (L534), **`map_complEDS` (L544)** — all `f (foo b c d n) = foo (f b) (f c) (f d) n`. This is precisely the idiom this lemma instantiates.
[E] Name pattern      mathlib EDS def/lemma list contains **no** `invar*`/`redInvar*` family at all; the whole invariant/reduced-invariant layer is the project's extension.

Searched for both:
  - the user's current form (`map_redInvarDenom`) — **not in mathlib** (subject absent);
  - the enclosing idiom (`map_normEDS`/`map_complEDS`) — **in mathlib**, identical shape, accompanying their respective defs.

Concluded: **not in mathlib**, and cannot be until its subject `redInvarDenom` is. Mathlib *does*
maintain the exact accompanying-`map_*` pattern — which is precisely why, *if* `redInvarDenom` is
upstreamed, this lemma rides along as the standard companion (not as an independent contribution).
(Intra-AINTLIB: `map_redInvarDenom` is **duplicated** — see Call sites.)

---

### Call sites — `EllSequence.map_redInvarDenom`

Internal-to-project (NagellLutz, excluding the declaring file):

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1513` | `simpa only [map_redInvarNum, map_mul, map_add, map_pow, map_redInvarDenom, aeval_X] using this` — inside `redInvar_normEDS` (the `aeval`/universal-ring transport step) |
| `NagellLutz/LutzNagell/DivisionPolynomialOmega.lean:112` | `simp_rw [ω, ← coe_mapRingHom, map_add, map_sub, map_mul, map_redInvarDenom, map_compl₂EDSAux, …]` — building `W.ω` / `map_ω` (ring-hom transport of the Y-coordinate division polynomial) |

Cross-project (same Lake workspace — genuine `import` consumers):

| Caller file:line | Usage pattern |
|------------------|----------------|
| `HasseWeil/.../Auxiliary/DivisionPolynomial.lean:138` | `simp_rw [ω, ← coe_mapRingHom, …, ← map_redInvarDenom, …]` — the twin-track `ω` transport, consuming the **flipped** orientation via `←` |

Intra-repo **duplicates** (the dominant cleanup signal, not a mathlib hit):
  - `HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:935` — verbatim lemma, **equation flipped** (`redInvarDenom (f b) (f c) (f d) m = f (redInvarDenom b c d m)`), proof `simp only [redInvarDenom, ← map_normEDS, ← map_complEDS, …]` (the project-local `map_*`). Consumed as `← map_redInvarDenom` at `DivisionPolynomial.lean:138`.
  - `NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:1334` — the pre-fork baseline copy.
  - Related name skew flagged in `map_ω.md`: `compl₂EDSAux` (NagellLutz) vs `complEDSAux₂` (HasseWeil).

Inline-derivation grep: the equivalent transport is **not** re-derived inline elsewhere — every
consumer goes through `map_redInvarDenom` (in one orientation or the other). The multiple
*definitions* are the project's forked-track duplication, not a bypass.

**Signal:** K ≥ 2 internal + cross-project uses, no inline bypass → it is **real, depended-upon API**
(part of the `map_ω` transport chain for the Y-coordinate division polynomial). Not dead code; not a
one-liner-without-consumers. The "keep + ship with parent" signal, with an intra-repo dedup to do
first.

### Composition check (Phase 6)

Can `EllSequence.map_redInvarDenom` be reproduced from **mathlib** in ≤3 chained calls (so it could
be inlined at call sites and deleted)?

Attempt 1: `simp [redInvarDenom, apply_ite f, map_normEDS, map_complEDS]` (the actual proof).
  - `apply_ite f`, `map_mul`/`map_pow`/`map_sub` — mathlib (structural). ✓
  - `map_normEDS` — exists in mathlib (L530) **and** is re-declared in the project (L1134); either works here. ✓ (mathlib-available)
  - `map_complEDS` — this is the **project's** `map_complEDS` (L1156), about the **project's** `complEDS` (L1568), which is **NOT** mathlib's `complEDS`. Mathlib's `map_complEDS` (L544) is about a *different* `complEDS`. ✗ **(not mathlib)**
  - `redInvarDenom` (the `simp`-unfolded subject) — project-local `def`, absent from mathlib. ✗ **(not mathlib)**
  - Result: **fails as a mathlib-only composition.** Two of the ingredients (`redInvarDenom` itself, and the project's `complEDS` via the project's `map_complEDS`) are project-local. You cannot inline this at a call site using mathlib alone — there is no mathlib `redInvarDenom` to transport, and the project's `complEDS` is a distinct object from the upstream one.

Conclusion: **NOT-COMPOSABLE from mathlib.** The earlier `NO-composable-from-mathlib` pass mis-read
the `map_complEDS`/`map_normEDS` in the proof as *mathlib's*; they resolve (for `complEDS`) to the
*project's* re-declarations about the *project's* `complEDS`. The lemma is therefore **bound to its
project-local subject**, not an inline-able mathlib composition. Its correct disposition is to ride
with `redInvarDenom` when that parent is upstreamed (where it becomes the standard companion `map_*`
lemma, alongside mathlib's pattern), not to be inlined and deleted.

---

## Why the verdict changed (earlier `NO-composable-from-mathlib` → `YES-but-generalise-first`)

The earlier pass landed **NO-composable-from-mathlib** on two grounds, **both now stale**:

1. *"Its proof is a ≤3-call composition of mathlib's `apply_ite` + `map_normEDS` + `map_complEDS`."*
   **Stale / inaccurate.** The `map_complEDS` it invokes is the **project's own** (L1156), about the
   **project's own** `complEDS` (L1568) — a *different* definition from mathlib's `complEDS` (L544).
   And `redInvarDenom` itself is project-local. So the proof is **not** a mathlib-only composition;
   it cannot be inlined at call sites from mathlib (Phase 6: NOT-COMPOSABLE). The premise of the
   NO-composable bucket (the building blocks are all in mathlib, inline + delete) is false.

2. *"Let its fate follow `redInvarDenom`'s — if that def is ever upstreamed, this `map_` lemma goes
   with it as boilerplate."* This is exactly right — and `redInvarDenom`'s fate **has now been
   decided**: the parent was re-assessed the same day (2026-06-21) from `BORDERLINE` to
   **`YES-but-generalise-first`** (it is the integral **leading term of `ωₙ`**, an explicit mathlib
   TODO at `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean:71,83`; author is
   the mathlib EDS author). By the lemma's own stated logic, it now inherits `YES-but-generalise-first`.

The skill's **verdict-inheritance / re-aim rule** is dispositive: a `map_*` glue lemma whose
statement is *about* a parent def already assessed in the cluster inherits the parent's verdict.
Mathlib itself demonstrates the convention — `map_normEDS`, `map_complEDS`, `map_preNormEDS`, … are
shipped *with* their defs, never as independent contributions and never inlined away. So
`map_redInvarDenom` is `YES-but-generalise-first`, riding with `redInvarDenom`, after the intra-repo
dedup.

---

## Verdict: `EllSequence.map_redInvarDenom`

**Category:** `YES-but-generalise-first`

> Bucket nuance: the lemma's *own* statement is already maximally general (Phase 4b: MAXIMALLY
> GENERAL; Phase 4c: already the modern `RingHomClass` idiom — in fact one notch more general than
> mathlib's existing EDS `map_*` lemmas). It is **not** an independent mathlib candidate: it is
> required functoriality boilerplate for the project-local `redInvarDenom`, with **no content of its
> own**. It inherits its parent's bucket. "Generalise first" here = "ship as the companion `map_*`
> lemma inside the parent `redInvarDenom`/division-free-`ω` subsystem upstreaming (named/located to
> mathlib conventions, after the intra-repo dedup)", **not** as a standalone PR and **not** inlined
> away — exactly as mathlib ships `map_normEDS` with `normEDS`.

**Evidence:**
- Literature search (Phase 3): functoriality of EDS/division-polynomial constructions over a ring hom is standard *plumbing* (mathlib codifies the `map_*`-EDS idiom; arXiv 2604.05280 / 2102.07573 / 2503.15428 use base change freely), but **no source names** "`f` commutes with the reduced invariant denominator" as a theorem — the content lives in `redInvarDenom`, not here.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — `[CommRing R] [CommRing S]` + `RingHomClass F R S` (more general than mathlib's concrete-`R →+* S` EDS `map_*`); 0 weakenings; already the modern idiom. Generality is moot independently of the subject.
- Mathlib search (Phase 5): **not in mathlib** (subject `redInvarDenom`/`invar*` absent), and cannot be until the subject is; mathlib *does* maintain the identical accompanying-`map_*` pattern (`map_normEDS` L530, `map_complEDS` L544), which is exactly the slot this lemma fills for `redInvarDenom`.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** — the proof's `map_complEDS` and the unfolded `redInvarDenom` are *project-local* (the project's `complEDS` at L1568 ≠ mathlib's `complEDS` at L544); it cannot be inlined at call sites from mathlib. Call-sites: real cross-project API in the `map_ω` transport chain; intra-repo **duplicated** (HasseWeil L935, orientation-flipped).

**Rationale.**
`map_redInvarDenom` carries no independent mathematical content: it is the canonical
`map_<construction>` naturality lemma for the project-local definition `redInvarDenom`. Whether it
belongs in mathlib is therefore **entirely** a function of whether `redInvarDenom` does — and that
parent was re-assessed (same cluster, 2026-06-21) to `YES-but-generalise-first`, because
`redInvarDenom` is the integral leading term of the **`ωₙ` division polynomial** that
`Mathlib/.../DivisionPolynomial/Basic.lean` explicitly flags as an open TODO (lines 71, 83), and the
file's author is the mathlib EDS author. Mathlib's own EDS file demonstrates the disposition: every
construction (`normEDS`, `preNormEDS`, `complEDS`, `complEDS₂`, …) ships with its `map_*` companion;
those companions are never standalone PRs and never inlined away. So when `redInvarDenom` is
upstreamed, `map_redInvarDenom` ships *with* it as the standard companion. It inherits
`YES-but-generalise-first`.

This is a **correction** of the earlier `NO-composable-from-mathlib` verdict, on two grounds. First,
that verdict's composition premise is inaccurate: the `map_complEDS` in the proof is the *project's*
(about the project's `complEDS`, a distinct object from mathlib's), and `redInvarDenom` is
project-local — so the lemma is **not** an inline-able ≤3-mathlib-call composition (Phase 6:
NOT-COMPOSABLE), and the NO-composable bucket's "inline at call sites and delete" action is not
available. Second, that verdict explicitly deferred to `redInvarDenom`'s fate ("if that def is ever
upstreamed, this `map_` lemma goes with it") — and that fate is now `YES-but-generalise-first`.

**Reason for the generalisation:** `MODERN-IDIOM`-adjacent **packaging/grain** (inherited), not a
weakening of this lemma's own hypotheses (already maximal). The "more general object" to ship is the
parent `redInvarDenom`/division-free-`ω` subsystem; `map_redInvarDenom` is its required companion
functoriality lemma.

**Proposed restatement.** No change to `map_redInvarDenom`'s statement or proof is needed on its own
terms; it is already mathlib-shaped (arguably *over*-general — see the style caveat). The
"restatement" is *contextual* — present it alongside its subject inside the `redInvarDenom`/`ω`
cluster, as the companion `map_*` lemma, the way mathlib pairs `map_normEDS` with `normEDS`:

```lean
namespace EllSequence
variable {R : Type*} [CommRing R] (b c d : R) (m : ℤ)

/-- `W(m+1)·W(m)·W(m−1) / (W₃·W₂)` for a normalised EDS, division-free (mod-6 case split). -/
def redInvarDenom : R := …

section Map
variable {S : Type*} [CommRing S] (f : R →+* S)   -- (style: align to the concrete-hom form mathlib's EDS map_* family uses)

@[simp] lemma map_redInvarDenom :
    f (redInvarDenom b c d m) = redInvarDenom (f b) (f c) (f d) m := by
  simp [redInvarDenom, apply_ite f, map_normEDS, map_complEDS]
end Map
end EllSequence
```

Estimated cost of regeneralisation: **CHEAP** for this lemma (verbatim; an optional `RingHomClass →
R →+* S` narrowing for family-consistency and an `@[simp]` tag to match mathlib's `map_*`-EDS lemmas
are the only style touch-ups). The real work is assembling the *surrounding* subsystem — that is the
parent decls' cost, not this leaf's. Cost does **not** downgrade the verdict.

**Mathlib downstream this enables (inherited from the parent):**
- Ships as the companion functoriality lemma for `redInvarDenom`, which is on the critical path for
  the **`ωₙ` TODO** in `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` — the
  bivariate ω-division polynomial, division-free over a commutative ring. Base-change of `ωₙ` under a
  ring hom (already used in the AINTLIB `map_ω` chain) is built directly on this lemma.
- Completes mathlib's `map_*`-EDS family for the invariant/reduced-invariant layer that the upstream
  EDS file currently lacks.

**Next action:** treat `map_redInvarDenom` as the **companion `map_*` lemma of `redInvarDenom`**, not
a standalone candidate and **not** an inline-and-delete target. Concretely: (1) first resolve the
**intra-AINTLIB duplication** — reconcile the NagellLutz↔HasseWeil orientation (`f (redInvarDenom …)
= redInvarDenom (f …)` vs the flipped form at `HasseWeil/.../EllipticDivisibilitySequence.lean:935`)
and the `compl₂EDSAux`/`complEDSAux₂` name skew, leaving one canonical copy; (2) confirm the
upstreaming plan with the file's author (D. K. Angdinata) — the parent subsystem is plausibly already
mathlib-bound; (3) ship it inside the `redInvarDenom`/`compl₂EDS`/`invar`/`ω` upstreaming bundle
(jointly with `map_redInvarNum`), `@[simp]`-tagged and optionally narrowed to a concrete `R →+* S` to
match mathlib's EDS `map_*` family, in one `feat(NumberTheory/AlgebraicGeometry)` PR.

---

## Next step

Ship `EllSequence.map_redInvarDenom` as the companion functoriality (`map_*`) lemma of its subject
`redInvarDenom`, inside the division-free-`ω` subsystem upstreaming (jointly with `map_redInvarNum`,
coordinating with the mathlib `ωₙ` TODO and the file's mathlib author) — not as a standalone PR and
not inlined away. First deduplicate the orientation-flipped HasseWeil copy (L935) and the
`compl₂EDSAux`/`complEDSAux₂` name skew so one canonical copy is the PR source.

---

### Sources
- On Elliptic Sequences over Commutative Rings — https://arxiv.org/pdf/2604.05280
- A recurrence relation for elliptic divisibility sequences — https://arxiv.org/pdf/2102.07573
- p-adic properties of division polynomials and elliptic divisibility sequences — https://arxiv.org/pdf/math/0404412
- Division polynomials for arbitrary isogenies — https://arxiv.org/pdf/2503.15428
- Mathlib.NumberTheory.EllipticDivisibilitySequence (docs) — https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
- mathlib (vendored pin): `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (`map_*`-EDS family, L510–L544); `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean` (ωₙ TODO, lines 30/71/83)
- Sibling reports: `redInvarDenom.md` (parent, `YES-but-generalise-first`), `map_redInvarNum.md`, `map_ω.md` (same `.mathlib-quality/overview/mathlibable/` dir)
