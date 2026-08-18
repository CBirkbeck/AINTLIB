# /mathlibable report — `EllSequence.compl`

> Step-9 mathlibable assessment (NagellLutz project — Nagell–Lutz / elliptic
> divisibility sequences). Run manually (ChatGPT MCP down; lean index MCP not
> exposed in this env) — reasoned from source + a full read of the upstream
> mathlib EDS file (`.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`,
> 548 lines), which this project forks.
>
> (Overwrites an earlier 2026-06-18 assessment; same conclusion, refreshed evidence.)

---

### Baseline (Phase 0)
- lake build:               not run (env build stale — task-permitted; reasoning from source)
- decl `EllSequence.compl`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1099`
- kind:                     `def` (one-liner)
- has sorry:                no
- module docstring summary: Expanded **fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence` (same author D.K. Angdinata, same Ward reference); adds the EDS divisibility-witness theory mathlib only TODO-promises.

**Qualified name VERIFIED:** the decl is inside `namespace EllSequence`
(opened line 1079), so the fully-qualified name is **`EllSequence.compl`**.
(Base name `compl`; used unqualified within the namespace. Note line 1099 is the
`def`; surrounding code spans 1083–1112.)

---

### Statement (Phase 1)

```lean
namespace EllSequence
variable (W₁ compl₂ : ℤ → R) (m : ℤ)

/-- Given two sequences representing `W(m)/W(1)` and `W(2m)/W(m)` respectively,
we construct the sequence representing `W(n*m)/W(m)` in a division-free way. -/
def compl' : ℕ → R
  | 0 => 0
  | 1 => 1
  | (n + 2) => letI k := n / 2 + 1; …   -- division-free quartic recursion

/-- `W(n*m)/W(m)` with `n : ℤ`. -/
def compl (n : ℤ) : R := n.sign * compl' W₁ compl₂ m n.natAbs
```

`EllSequence.compl` is the **integer-indexed complement (quotient) sequence** of
an elliptic divisibility sequence. Given a base index `m` and two auxiliary
sequences `W₁ ≈ W(·)/W(1)` and `compl₂ ≈ W(2·)/W(·)`, it extends the
ℕ-indexed division-free recursion `compl'` to all of ℤ via the standard sign
trick `compl(n) = sign(n) · compl'(|n|)`. Mathematically it is intended to be
`W(n·m)/W(m)`, computed without ring division, so that multiplying by `W(m)`
recovers `W(n·m)` and witnesses the classical divisibility `W(m) ∣ W(n·m)`.

Variables / typeclasses (Lean side):
- `{R : Type*} [CommRing R]` — ambient commutative ring (Ward's setting at modern generality).
- `(W₁ compl₂ : ℤ → R)` — **abstract** auxiliary sequences (NOT tied to `normEDS`).
- `(m : ℤ)` — base index whose multiples are taken.
- `(n : ℤ)` — the multiplier.

Conclusion (math): the integer-indexed quotient sequence `n ↦ W(n·m)/W(m)`, division-free.
Conclusion (Lean): `R` (a `def`, not a proposition).

**Raison d'être.** `compl` exists to state and prove
`IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` (line 1296): for
any elliptic sequence `W` whose first two terms are non-zero-divisors,
`W m * compl W₁ compl₂ m n = W (n*m)`. The project then **re-specialises** at
line 1110, `complEDS b c d m := compl (normEDS b c d) (compl₂EDS b c d) m`,
recovering exactly mathlib's `complEDS`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (structurally load-bearing)
Reason: a helper `def` (the ℤ-extension of a recursion), not a named theorem and
not a new structure — but the engine for a main lemma of the file (general
divisibility witness). "Small def, big purpose."

### One-line check (Phase 2b)

Body line count: **1 substantive line** (`n.sign * compl' W₁ compl₂ m n.natAbs`).
One-liner verdict: **ONE-LINER**.

| Exemption                        | Applies? | Evidence |
|----------------------------------|----------|----------|
| Avoid defeq abuse                | partial  | Sign-extension stays sealed; consumers go through `compl_ofNat`/`compl_neg`. The witness proof rewrites with `EllSequence.compl` + `Int.sign_eq_one_of_pos` (lines 1301–1303), not raw unfolding. |
| Avoid typeclass diamonds         | no       | No instance involved. |
| Mark semantic intent / API name  | yes      | Named + docstringed (`W(n*m)/W(m)`); it anchors `complEDS` (1110) and `map_compl` (1152). **Exactly mirrors mathlib's own one-liner `complEDS (n : ℤ) : R := n.sign * complEDS' b c d k n.natAbs`** (mathlib EDS file:427), shipped by mathlib for the same reason. |

Conclusion: **ONE-LINER WITH-EXEMPTION** (the same API-anchor exemption mathlib
already grants its parallel `complEDS`/`preNormEDS` sign-extension one-liners).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1  | WebSearch (specific) | EDS complement `W(nk)/W(k)` division-free recursion Ward | partial | only Mathlib doc + Wikipedia phrase "complement sequence" | The phrase "complement sequence … witnesses `W(k) ∣ W(n·k)`" traces to the **Mathlib docstring itself**, not a classical source. |
| 2  | WebSearch (general)  | EDS `W(k)` divides `W(nk)` divisibility proof | yes | `gcd(W_m,W_n)=W_{gcd}` ⇒ `W_n ∣ W_{nm}` (classical Ward 1948) | Standard PROOFS use p-adic valuations / formal groups (Silverman, Stange), **not** an explicit division-free recursive witness. |
| 3  | WebSearch (named/alias) | Ward memoir EDS quotient sequence; Stange elliptic nets | yes | Ward 1948 *Memoir on EDS*, Amer. J. Math. 70(1), 31–74; Stange elliptic nets | Ward's coherence proof uses σ-function quotients; no "complement-quotient recursion" object is named. |
| 4  | ChatGPT MCP | standard-form + generality of abstract `(W₁,compl₂)` complement | **n/a** | — | MCP down in this env (Codex exec failed) — task-noted fallback; drawn from 1–3, 9, 10 + full mathlib source read. |
| 5  | Local references | grep `.mathlib-quality/references/` | **n/a** | — | Project has no `references/` dir. |
| 6  | nLab | EDS / elliptic net | no article | — | No dedicated EDS/complement-sequence page. |
| 7  | nCatLab (categorical) | — | **n/a** | — | Not categorical. |
| 8  | Stacks Project (alg geom) | — | **n/a** | — | Not a scheme-theoretic concept (sequence/recursion). |
| 9  | MathOverflow / MSE | EDS divisibility / quotient sequence generality | yes | reaffirms divisibility classical; proofs via formal groups | No abstract-`(W₁,compl₂)` object surfaced. |
| 10 | recent arXiv (≤5 yr) | elliptic sequences over commutative rings; quotient `W(nk)/W(k)` | yes | **Xu, "On Elliptic Sequences over Commutative Rings", arXiv:2604.05280** — algebraic EDS over a commutative ring via "elliptic relations" | The modern commutative-ring program this project aligns with; proves EDS facts algebraically but does **not** name a "complement quotient sequence over an abstract sequence pair". |

### Literature summary (Phase 3)

Concept identified as: the **complement / quotient sequence `W(n·k)/W(k)`** of an
EDS — i.e. the witness for `W(k) ∣ W(n·k)` (Ward 1948).
Sources agree on the standard form: **the divisibility property is classical and
universal**; the *division-free recursive witness* and the *abstract
`(W₁,compl₂)`-indexed* formulation are **not** named literature objects — the
"complement sequence" terminology originates in mathlib's own docstrings.
Most general standard form: "for an EDS `W` over a commutative ring,
`W(k) ∣ W(n·k)`" — a *property*, classically proved via p-adic valuations /
formal groups, not via an explicit quotient-sequence `def`.
Generality dimensions the literature varies on:
  - coefficient domain: ℤ (Ward) → arbitrary commutative ring (Xu 2026, mathlib);
    the project sits at the most general end (`[CommRing R]`).
  - base object: concrete `normEDS` (mathlib) → **abstract elliptic sequence**
    (this project) — a generality dimension the literature does **not** track as
    a named object.
Disagreement with literature: none — but the specific construct (division-free
quotient recursion over an abstract sequence pair) is a **formalisation-driven**
object, not a textbook one; best read as a proof engine, with the textbook
content being the divisibility property it witnesses.

---

### Generality analysis — `EllSequence.compl`

Target (Phase 3): the property `W(k) ∣ W(n·k)` over a commutative ring; the
canonical object mathlib already ships is the concrete `complEDS` for `normEDS`.

| # | Parameter / hypothesis | Current Lean form | Concrete-mathlib `complEDS` | More general here? | Reason |
|---|------------------------|-------------------|-----------------------------|--------------------|--------|
| 1 | `[CommRing R]`         | commutative ring  | commutative ring            | same | Already maximal (matches mathlib + Xu 2026). |
| 2 | base sequence          | **abstract `W₁, compl₂ : ℤ → R`** | concrete `normEDS`, `compl₂EDS` | **YES — strictly more general** | Project's `complEDS := compl (normEDS) (compl₂EDS) m` (1110) is a *specialisation* of `compl`. `compl` abstracts the two auxiliaries mathlib hard-codes. |
| 3 | index `n`              | `ℤ` (sign-extended)| `ℤ` | same | Same `n.sign · (·).natAbs` extension as mathlib. |

**Direction of generality (key finding):** `EllSequence.compl` is **strictly MORE
general than** mathlib's `complEDS` — mathlib's decl is recovered as a one-line
specialisation of the project's. This is the *inverse* of the usual
NO-mathlib-has-it pattern. Here the project has the general form; mathlib has the
specialisation.

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (more general than mathlib's
`complEDS`; coefficient generality already `[CommRing R]`).
Number of weakening opportunities found: **0** (it *is* the generalisation).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Reformulation | Downstream |
|---|----------|----------|---------------|-----------|
| 1 | bundled-hyp → typeclass? | no | `W₁,compl₂` are genuinely arbitrary function inputs, not a structure to classify | — |
| 2 | sequences → filters? | no | finite algebraic recursion; no limit/topology | — |
| 3 | construction → universal property? | borderline | one could characterise "the complement" by `W m * compl = W(n·m)` instead of the explicit recursion — but the division-free recursion is the point (computability, no ring division) | would lose computability |
| 4 | set+closure → bundled substructure? | no | n/a | — |
| 5 | field/metric → ring/module weakening? | no (already `[CommRing R]`) | already weak | — |
| 6 | 1-categorical → higher? | no | n/a | — |
| 7 | concrete index → general monoid? | no | index is essentially `ℤ` (sign trick) | — |

Modern-idiom verdict: **no** strong modernisation move. The abstract
`(W₁,compl₂)` form *is* the contemporary generalisation; trading the explicit
recursion for a universal-property characterisation would sacrifice the
division-free computability that motivates the construction.

---

### Diamond / defeq risk — `EllSequence.compl` (Phase 4.5)

| # | Risk | Verdict | Rationale |
|---|------|---------|-----------|
| 1 | Typeclass diamond | none | No instance; plain `def` returning `R`. |
| 2 | Reducibility leak | low | Not `@[reducible]`; sign-extension sealed; consumers go through `compl_ofNat`/`compl_neg`. Same posture as mathlib's `complEDS`/`preNormEDS`. |
| 3 | Non-canonical unfolding | low | `simp [EllSequence.compl]` used deliberately at base cases (1301–1302); no surprising global unfolding. |
| 4 | Instance priority collision | n/a | Not an instance. |
| 5 | Universe issues | none | Lives in `R : Type u`; no forced annotation beyond `complEDS`. |
| 6 | Coercion ambiguity | none | No `CoeFun`/`CoeSort`. |

### Risk verdict (Phase 4.5): **NONE/LOW** (mirrors mathlib's existing,
accepted `complEDS` one-liner). No HIGH rows.

---

### Mathlib search-status: `EllSequence.compl`

[A] Lean-Finder       — n/a: index MCP not exposed in this env.
[B] Loogle            — n/a: index MCP not exposed in this env.
[C] LeanSearch        — n/a: index MCP not exposed in this env.
[D] Grep mathlib src  `def compl`, `W₁ compl₂`, `n.sign * compl`, `dvd…normEDS` over `.lake/packages/mathlib/Mathlib/` → **concrete complement family only** (`complEDS₂`:246, `complEDS'`:392, `complEDS`:427, recursors). **No abstract `(W₁,compl₂)` complement anywhere.** The only `W₁ compl₂` hits are unrelated `MorphismProperty` category theory.
[E] Name pattern      `def compl…` in `Mathlib/NumberTheory/` → `complEDS*` (concrete) + `completed*Zeta` (unrelated). The abstract `compl` name is unique to this project (repo grep: only `…NagellLutz/…:1099`).

Searched for both:
  - user's current form (abstract `(W₁,compl₂)` complement) → **not in mathlib**;
  - literature-standard form (the property `W(k) ∣ W(n·k)`, and concrete
    `complEDS`) → **mathlib has the concrete `complEDS` *def* (file:427) but NOT
    the general divisibility-witness *theorem***. Mathlib proves only the `n = 2`
    case `normEDS_dvd_normEDS_two_mul` (file:326); there is **no**
    `normEDS_mul_complEDS` / general `normEDS k ∣ normEDS (n*k)`.

Concluded: **mathlib has a strictly-LESS-general concrete cousin (`complEDS`,
qualified `_root_.complEDS`) but does NOT have this abstract `compl`, and does
NOT have the general divisibility witness the abstract `compl` is built to
prove.** The full upstream EDS file was read end-to-end; the concept lives in
exactly one mathlib file, so methods D+E are exhaustive for it.

---

### Call sites — `EllSequence.compl`

Internal use count: **8** within the declaring file (lines 1101, 1106, 1110,
1153, 1297, 1301, 1302, 1303, 1326) — all in
`EllipticDivisibilitySequence.lean`.
External-to-file callers: **0** distinct files. Downstream-library callers: **0**.

| Caller line | Usage |
|-------------|-------|
| :1101 | `compl_ofNat` glue lemma (`compl … n = compl' … n`) |
| :1106 | `compl_neg` glue lemma |
| :1110 | `complEDS := compl (normEDS b c d) (compl₂EDS b c d) m` — re-specialisation to mathlib's object |
| :1153 | `EllSequence.map_compl` (ring-hom naturality) |
| :1297 | `IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors` — the divisibility-witness theorem (reason to exist) |
| :1301–1303 | unfolding inside that theorem's proof |
| :1326 | `normEDS_mul_complEDS_of_mem` bridges back to `complEDS` |

Inline-derivation grep: none (no consumer re-derives `W(n·m)/W(m)` bypassing `compl`).

**What this tells us:** classic "engine def" pattern — `K = 8` internal uses but
**all in one file, 0 external, 0 downstream**. Not dead code; private scaffolding
immediately re-specialised to `complEDS`. With no *external* consumer, its value
to mathlib rides entirely on whether mathlib wants the *abstract* engine, or only
the concrete `complEDS` plus a directly-proved divisibility lemma.

---

### Composition check (Phase 6)

Can `EllSequence.compl` be obtained from mathlib in ≤3 calls?

Attempt 1: specialise mathlib's `complEDS`? — `complEDS b c d k n` *is*
`compl (normEDS b c d) (compl₂EDS b c d) k n`, i.e. mathlib gives the
`W₁ = normEDS`, `compl₂ = compl₂EDS` **instance** of `compl`. But the abstract
`compl` over *arbitrary* `W₁, compl₂` cannot be recovered from concrete
`complEDS` — you cannot un-specialise. **Fails** (wrong direction).

Attempt 2: build the abstract recursion from mathlib primitives? — The body is a
bespoke well-founded division-free quartic recursion on ℕ, then a sign-extension.
No mathlib primitive yields this recursion; it must be defined.
`Int.sign`/`Int.natAbs` give only the trivial outer wrapper, not `compl'`.
**Fails.**

Conclusion: **NOT-COMPOSABLE** (mathlib's `complEDS` *down*-specialises from
`compl`, not a route to it).

---

## Verdict: `EllSequence.compl`

**Category:** **BORDERLINE-needs-human**

**Evidence:**
- Literature search (Phase 3): the property `W(k) ∣ W(n·k)` is classical (Ward
  1948); the *division-free quotient-sequence witness* and the *abstract
  `(W₁,compl₂)`-indexed* formulation are **formalisation-driven**, not named
  literature objects ("complement sequence" is mathlib's own coinage).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — strictly MORE general
  than mathlib's `complEDS` (which is a one-line specialisation of it).
- Mathlib search (Phase 5): abstract `compl` **not in mathlib**; concrete
  `complEDS` *is* (file:427); the **general divisibility witness it enables is
  NOT** (mathlib has only the `n=2` case, file:326).
- Composition check (Phase 6): **NOT-COMPOSABLE**.

**Rationale.**
`EllSequence.compl` is not "already in mathlib" — it is a **strict
generalisation of** mathlib's `complEDS`, abstracting the two auxiliary
sequences (`normEDS`, `compl₂EDS`) mathlib hard-codes into arbitrary inputs
`W₁, compl₂`. That generalisation is *purposeful*: it is exactly what lets the
project prove `W m * compl W₁ compl₂ m n = W (n·m)` for an **abstract** elliptic
sequence, and thence the general divisibility `W(k) ∣ W(n·k)` — filling a gap
mathlib's own docstring only TODO-promises ("witnesses `W(k) ∣ W(n·k)`") and
currently discharges only for `n = 2`. So there is real, upstream-relevant
mathematical content nearby, correctly and maximally general. That pushes *away*
from every NO bucket and away from YES-but-generalise-first (nothing to weaken —
it is already the generalisation).

What stops a clean **YES-add-as-is** is a genuine taste/policy judgment the skill
should not make alone: the *definition itself* is a **one-line proof-scaffolding
object** with zero external consumers, immediately re-specialised back to
mathlib's existing `complEDS`. A working mathematician's "natural object" here is
`complEDS` for `normEDS` (mathlib already has it); the abstract
`(W₁,compl₂)`-indexed `compl` exists chiefly to make the divisibility-witness
*induction* go through. Mathlib could reasonably want **either** (a) this
abstract `compl` upstreamed as the canonical engine, with `complEDS` redefined as
its specialisation and new `normEDS_mul_complEDS` / `normEDS_dvd …` lemmas; **or**
(b) just the missing *theorem* (`normEDS k ∣ normEDS (n*k)` and
`normEDS_mul_complEDS`) proved directly against the existing concrete `complEDS`,
keeping the abstract scaffolding out of the public API. Both are defensible; the
choice is mathlib-maintainer taste about whether the abstract generality earns a
public name. Hence BORDERLINE. (Not a cost-driven downgrade — the abstract form
already exists and builds; the open question is API-surface taste, a legitimate
BORDERLINE trigger.)

**Numbered questions for the user / mathlib reviewer (≤5):**

1. Does mathlib want the **abstract** complement `compl (W₁ compl₂ : ℤ → R)`
   upstreamed as the canonical object (with `complEDS` redefined as
   `compl (normEDS …) (compl₂EDS …)`), or only the **concrete** `complEDS` it
   already has?
2. Either way, the clearly-mathlib-worthy item is the **missing theorem**:
   `normEDS b c d k ∣ normEDS b c d (n*k)` and
   `normEDS b c d m * complEDS b c d m n = normEDS b c d (n*m)` (mathlib has only
   the `n=2` case `normEDS_dvd_normEDS_two_mul`). Should the upstreaming target
   **that lemma** as the deliverable (which then dictates whether the abstract
   `compl` is needed as scaffolding)?
3. Is proving the divisibility witness for a **general** elliptic sequence `W`
   (the abstract route, via
   `IsEllSequence.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors`) wanted in
   mathlib, or is the `normEDS`-only statement sufficient — i.e. is the
   abstraction's *theorem* in scope, not just its *def*?
4. If only the concrete result is wanted (Q1/Q3 = "concrete"), are you content to
   **delete** the standalone `EllSequence.compl`/`compl'` defs upstream and
   inline the recursion into `complEDS'`'s divisibility proof, keeping the
   abstract engine project-local?

**Next action:** user/maintainer answers Q1–Q4. If "abstract `compl` wanted as
the canonical engine + general divisibility witness in scope" → resolves to
**YES-add-as-is** (location
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`; PR grouped with
`compl'`, the `complEDS` redefinition, and the new `normEDS_mul_complEDS` /
`normEDS_dvd …` lemmas; pre-PR `/generalise` + `/cleanup`). If "concrete
`complEDS` is the public object, prove the divisibility lemma directly against
it" → the abstract `compl` stays project-local scaffolding (effectively
NO-composable / NO-mathlib-has-it for the *def*, while the *theorem* is the real
YES contribution).

---

## Next step

User/maintainer answers questions 1–4 above; re-run `/mathlibable
EllSequence.compl` (or commit directly) once the API-surface decision is made.
The high-value, non-borderline takeaway regardless of that decision: **mathlib is
missing the general EDS divisibility witness `normEDS k ∣ normEDS (n*k)` (only
`n=2` exists)** — that lemma is worth upstreaming; whether the abstract `compl`
rides along is the borderline call.
