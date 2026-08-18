# `/mathlibable` report — `PadicLFunctions.extLog_neg`

Mode A (single declaration), full 10-phase workflow with the exhaustive 9-channel
literature search.

**Final verdict: `YES-but-generalise-first`.** `extLog_neg` is the sign-invariance
law `log_p(−x) = log_p(x)` of the extended (Iwasawa-branch) p-adic logarithm — the
specialisation to `μ_2 = {±1}` of the standard, literature-confirmed fact that *the
extended `log_p` kills every root of unity* (its kernel is exactly `{p^r·ζ : r∈ℚ, ζ a
root of unity}`). It is genuinely missing from mathlib (which has **no** nonarchimedean
logarithm of any kind — directly verified: no `padicLog`/`extLog`, no Exp/Log file under
`NumberTheory/Padics/`), it is not a short mathlib composition (its building blocks
`extLog`, `extLog_mul`, `extLog_eq_zero_of_pow_eq_one` are all project-local and absent
from mathlib), and it is real, load-bearing API (2 external call lines in
`ValuesAtOne.lean`, driving the `(−1)^m`-invariance induction and the `extLog(ε^c−1) =
extLog(1−ε^c)` sign fix in the residue/L-value computation). It is **not**
`YES-add-as-is` only because it inherits the *base-field* narrowing already flagged for
its parent `extLog`/`extLog_mul` and base `padicLog` (all `YES-but-generalise-first`):
it is stated over a `ℚ_[p]`-algebra rather than an arbitrary complete nonarchimedean
**char-0** field, so the verdict gate forces `YES-but-generalise-first`. The
generalisation is the *same single move* that re-aims the entire `padicLog`/`extLog`
cluster; the modern-idiom target makes `extLog_neg` a free **kernel lemma** of the
extended log bundled as a `MonoidHom` (any torsion element maps to `0`).

---

### Baseline (Phase 0)

- lake build:               **not re-run; reasoned from source** (per task BUILD NOTE — the build is stale/slow on this checkout; the declaration and its entire dependency chain were read directly from source, exactly as the skill's Phase-0 fallback allows). `ExtLog.lean` is on `main` (which the project asserts always builds), was last touched by a committed cleanup, and contains **0 `sorry`/`admit`** (grep `\b(sorry|admit)\b` over the file → none). Every consumer of `extLog_neg` (`ValuesAtOne.lean:1099` inside `extLog_neg_one_pow_mul`, and `ValuesAtOne.lean:1757`) elaborates against the theorem as written.
- decl `PadicLFunctions.extLog_neg`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:434`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The extended (Iwasawa-branch) p-adic logarithm (RJW §6, decomposition W6a)" — extends `padicLog` to rational-valuation elements `x` with `x^m = p^k·y` (`y` in the exp ball) by `extLog x := m⁻¹·padicLog y` (junk `0` off-domain; Iwasawa's branch `log_p(p)=0`); cross-references Washington, *Cyclotomic Fields*, §5.1. The target is the file's stated **"W6a-a10 (continued): `log_p(x) = log_p(−x)` (RJW's final step, TeX 2150)."**

---

### Statement (Phase 1)

`PadicLFunctions.extLog_neg` is **a theorem** stating the **sign-invariance** of the
extended p-adic logarithm:

> Let `L` be a complete ultrametric normed field that is a normed `ℚ_[p]`-algebra
> (e.g. `ℚ_[p]`, finite extensions, `ℂ_[p]`). If `x` lies in the *rational-valuation
> domain* of the extended logarithm — i.e. `x^m = p^k·y` for some `m > 0`, `k ∈ ℤ`, and
> `y` in the (translated) exponential ball — then the extended Iwasawa logarithm is
> **invariant under negation**: `extLog(−x) = extLog(x)`.

This is the specialisation to `−1` of the literature's headline kernel fact: the
extended `log_p` is a group homomorphism `K^× → (K,+)` whose kernel is exactly
`{p^r·ζ : r∈ℚ, ζ a root of unity}`. Since `−1` is a (2nd) root of unity, `extLog(−1) =
0`, and by additivity `extLog(−x) = extLog(−1) + extLog(x) = extLog(x)`. The Lean proof
is exactly this: it proves `−1 ∈ ExtLogDomain` (witness `(−1)² = 1 = p^0·1`), applies
`extLog_mul` to `−x = (−1)·x`, and kills the `extLog(−1)` term via
`extLog_eq_zero_of_pow_eq_one` (`(−1)² = 1`).

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [Fact p.Prime]` — the residue prime; scalars live in `ℚ_[p]` through `extLog`/`padicLog`.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a complete ultrametric (nonarchimedean) normed field that is a normed `ℚ_[p]`-algebra. `CharZero` is **not** stated (it is implied by the `ℚ_[p]`-algebra structure).

Hypotheses (Lean side):
- `(hx : ExtLogDomain p x)` — `x` is in the rational-valuation domain `∃ m k y, 0 < m ∧ x^m = p^k·y ∧ InExpBall p (y−1)`. Needed so `x` is an honest argument of `extLog` (off-domain `extLog = 0` is junk; `extLog_mul` requires `x` in domain).

Conclusion (math): `log_p(−x) = log_p(x)` — the `μ_2 ⊂ μ_∞` kernel / sign-invariance of the extended Iwasawa logarithm.
Conclusion (Lean): `extLog p (-x) = extLog p x`.

Underlying definitions / lemmas (read from source):
- `extLog p x` (`ExtLog.lean:286`) — `m⁻¹ • padicLog y` for a `Classical.choice` witness, junk `0` off-domain.
- `ExtLogDomain p x` (`ExtLog.lean:278`) — `∃ m k y, 0<m ∧ x^m = p^k·y ∧ InExpBall p (y−1)`.
- Proof inputs: `extLog_mul` (`:357`, additivity on the domain), `extLog_eq_zero_of_pow_eq_one` (`:427`, roots of unity ↦ `0`), `neg_one_sq`, `inExpBall_one_sub_one` (`:346`).

---

### Size classification (Phase 2a)

Verdict: **SMALL** (borderline).
Reason: it is a one-step corollary of two named laws (`extLog_mul` + `extLog_eq_zero_of_pow_eq_one`) — the specialisation of the kernel/torsion property of the extended `log_p` to `μ_2 = {±1}`. It is *not* a person-named theorem and *not* a headline construction; it is a derived sign-invariance lemma. (It is mathematically the `−1`-instance of a deeper, universally-stated fact — "log kills all roots of unity" — but as a standalone declaration it is a small corollary.) The closely-related `extLog_prod`/`extLog_mul` are the structural laws; `extLog_neg` rides on them.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is narrative framing only — and was run EXHAUSTIVE here.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-line check **n/a / skipped**.
The proof body is ~4 lines of genuine mathematics (establish `−1 ∈ ExtLogDomain` via
`(−1)²=1`, rewrite `−x = (−1)·x`, apply `extLog_mul`, kill `extLog(−1)` via the
roots-of-unity lemma), not a definitional one-liner.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form — `log(−x)=log x` / roots of unity in kernel) | `p-adic logarithm roots of unity kernel log(-x) = log(x) Iwasawa extended` | **yes** | "The p-adic logarithm is a homomorphism whose kernel is the subgroup of `C_p^×` generated by all roots of unity and all roots of `p`"; extension via `log(p^n(1+x)) := log(1+x)`, `log p = 0` | Surfaced MIT 18.785 PS10, arXiv:1907.06437, arXiv:math/0512015, the AAC papers (2410.20934). The kernel contains **all** roots of unity ⇒ `−1` ∈ kernel ⇒ `log(−x)=log x`. |
| 2 | WebSearch (general form — kernel/uniqueness/homomorphism) | `p-adic logarithm vanishes on roots of unity log_p(zeta)=0 kernel torsion` | **yes** | "the kernel of the p-adic logarithm consists of the p-power roots of unity"; "the kernel of the logarithm map is the torsion subgroup of roots of unity"; `log_p(ζ)=0` for roots of unity ζ is "a standard foundational fact" | K. Conrad/Jack Thorne notes, Gupta REU, Gross/p-adic Stark notes. Confirms the homomorphism kills all torsion ⇒ the `−1` case is `extLog_neg`. |
| 3 | WebSearch (named-after / sign-invariance phrasing) | `p-adic logarithm "log(-x)" equals "log(x)" sign invariance roots of unity in kernel` | **yes (kernel form)** | "log_p(s) = 0 iff `s` is a rational power of `p` times a root of unity"; "log_p(xy) = log_p(x) + log_p(y)"; extend by `log_p(p)=log_p(w)=0`, `w` any root of unity | planetmath, C. Dion report, K. Conrad. (The fast-model summary's aside that "−1 is typically not a root of unity p-adically" is **wrong** — `−1` is a 2nd root of unity in any field of char ≠ 2; the Lean proof uses exactly `(−1)²=1`. The kernel-contains-all-roots-of-unity statement, present in every source, is decisive.) |
| 4 | ChatGPT MCP | (intended: standard form of `log_p(−x)=log_p x`; is "log kills roots of unity / kernel = `p^ℚ·μ_∞`" the standard statement; at what generality; historical evolution) | **n/a** | — | No ChatGPT/OpenAI MCP tool configured in this sandbox (only Asana/Atlassian/etc. proxy servers are surfaced; consistent with the sibling `extLog`/`extLog_mul`/`padicLog` reports). **Compensated** by the primary-source Wikipedia `WebFetch` (row 11) giving the verbatim kernel + homomorphism statement, plus the in-repo Washington-cited docstring and the three WebSearch generality levels. Intent met. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/`; `ls refs/PadicLFunctions/`; `ls <--refs arg>` | **n/a** | (no references dir; no `refs/` symlink) | Both absent on this `main` checkout (`references/` does not exist; `refs/` is dev-branch-only). The `--refs` arg points at the plugin's generic skill references (which on this 0.50.0 cache do not even contain `mathlibable-verdicts.md`), not project-source PDFs. The module docstring cites RJW §6 / Thm 6.1(ii) / TeX 2150 and Washington §5.1. Sibling reports (`extLog.md`, `extLog_mul.md`) consulted as in-repo prior art. |
| 6 | nLab | `nLab p-adic logarithm kernel roots of unity homomorphism C_p` | **partial** | nLab "p-adic number" / "p-adic Hodge theory": the p-adic exponential has an inverse, the p-adic logarithm; homomorphism `log_p(xy)=log_p x + log_p y`; extend to `C_p^×` by `log_p(p)=log_p(w)=0`, `w` any root of unity | nLab has no dedicated "Iwasawa logarithm" / "sign-invariance of log" page; the kernel-is-roots-of-unity content is the p-adic-number entry plus the analysis references (rows 1–3, 11). |
| 7 | nCatLab (categorical) | (same as nLab) | **n/a** | — | Not a higher-categorical concept; `extLog_neg` is an algebraic identity (`=`) of an analytic function — no universal-property formulation to look up. (Its only categorical shadow: it is a *kernel membership* fact, i.e. `−1` in `ker` of the bundled hom — a downstream packaging, see Phase 4c.) |
| 8 | Stacks Project (alg geom) | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic concept; `log_p(−x)=log_p x` for field elements does not appear in Stacks. |
| 9 | MathOverflow / Math.StackExchange | (covered by rows 1–3; MO/MSE/lecture-note threads surfaced — Matt Baker's blog, Bayreuth/Stoll notes) | **yes** | consensus: extend by `log p = 0`, `log(p^r ζ z)=log z`, getting a **homomorphism** `C_p^× → C_p` with kernel `p^ℚ·μ_∞`; every root of unity (so `−1`) maps to `0` | No disagreement; the kernel-contains-all-torsion fact is stated on the *whole* `C_p^×`, never restricted to a `ℚ_p`-algebra. |
| 10 | recent arXiv (≤5 yr) | (rows 1–2) | **yes** | arXiv:1907.06437 (2023), arXiv:1904.09850, arXiv:2410.20934 (2024, AAC congruences): `log_p: 1+𝔪_K → 𝔪_K` is a homomorphism; the kernel/torsion facts are taken for granted in computing the *image* | Active modern use of exactly this extended `log_p` with `log p=0`; the `log(ζ)=0` (hence `log(−x)=log x`) fact is foundational, used silently. |
| 11 | Wikipedia primary fetch | `WebFetch en.wikipedia.org/wiki/P-adic_exponential_function` | **yes** | **verbatim**: "The roots of the Iwasawa logarithm `log_p(z)` are exactly the elements of `C_p` of the form `p^r·ζ` where `r` is a rational number and `ζ` is a root of unity"; "`log_p(zw) = log_p z + log_p w`"; extend by `log_p(p)=0` | This is exactly the kernel fact specialised by `extLog_neg`: `−1 = p^0·(−1)` with `−1` a root of unity ⇒ `−1` is a root of `log_p` ⇒ `log_p(−1)=0` ⇒, by additivity, `log_p(−x)=log_p x`. Stated over `C_p`, **not** restricted to `ℚ_p`. |

The protocol passed: WebSearch ran **3 distinct generality levels** (rows 1–3: the
`log(−x)=log x`/roots-of-unity form, the kernel/torsion form, the sign-invariance/`log_p(ζ)=0`
form) plus arXiv (10) and a primary fetch (11); local refs checked (absent, n/a with reason);
nLab checked (6, partial); Stacks/nCatLab/MathOverflow each adjudicated (8/7/9). ChatGPT MCP is
genuinely unavailable in this sandbox — recorded n/a with the compensating primary-source
Wikipedia fetch (row 11) carrying the verbatim standard form.

### Literature summary (Phase 3)

Concept identified as: **the sign-invariance / `μ_2`-kernel fact `log_p(−x) = log_p(x)` of
the extended Iwasawa logarithm** — the `−1`-instance of the universal statement that *the
extended `log_p` is a homomorphism whose kernel is `{p^r·ζ : r∈ℚ, ζ a root of unity}`*, i.e.
it kills every root of unity (`log_p(ζ)=0`).
Sources agree on the standard form: **yes, unanimously** — Wikipedia (verbatim kernel
statement), MIT 18.785, K. Conrad/Jack Thorne/Stoll notes, planetmath, World Scientific, the
modern arXiv principal-units/AAC papers all state that the extended `log_p` is a group
homomorphism `K^× → (K,+)` killing all roots of unity (kernel `p^ℚ·μ_∞`); hence
`log_p(−1)=0` and `log_p(−x) = log_p(−1)+log_p(x) = log_p(x)`. The "`−1` is not a p-adic root
of unity" aside in one fast-model summary is incorrect (`−1` is a 2nd root of unity in any
field of char ≠ 2; `p` odd here via the project's running `Fact p.Prime`) and contradicted by
the explicit kernel statements in every primary source.
Most general standard form: for **any complete nonarchimedean field `K` of characteristic 0**
(`ℚ_p`, finite/infinite extensions, `ℂ_p`), `extLog(−x) = extLog x` for every `x ∈ K^×`
(equivalently `−1 ∈ ker(extLog)`). It does **not** require a `ℚ_[p]`-algebra structure — only
`CharZero` (so `m⁻¹` and the `1/n` inside `padicLog` make sense).
Generality dimensions where the literature varies:
  - **Base ring**: `ℚ_p ⊂` finite extensions `⊂ ℂ_p ⊂` arbitrary complete nonarchimedean
    char-0 field. The literature standard is `ℂ_p` / "complete nonarchimedean field"; the
    Lean `[NormedAlgebra ℚ_[p] L]` is the **same** inherited artefact flagged for `padicLog`/
    `extLog`/`extLog_mul`.
  - **Domain of the hypothesis**: the literature states the kernel/sign fact on **all of `K^×`**
    (over `ℂ_p`, vacuously every nonzero element); the Lean form restricts to `ExtLogDomain p x`,
    which is the *natural domain of `extLog`* (off it `extLog=0` is junk and `extLog_mul` fails),
    so it is **not** an additional narrowing beyond where the function is meaningfully defined.
Disagreement with the literature: none on content — the Lean form is **correct** and stated on
the natural domain; its only narrowing relative to standard is the inherited **base-field**
`ℚ_[p]`-algebra assumption (and the exp-ball domain choice carried by `ExtLogDomain`/`padicLog`)
— see Phase 4.

---

### Generality analysis — `PadicLFunctions.extLog_neg`

Literature-standard form (from Phase 3): `extLog(−x) = extLog x` for **all** `x ∈ K^×` of a
complete nonarchimedean **char-0** field `K` (the `−1 ∈ ker(extLog)` instance of the
kernel-is-roots-of-unity property); equivalently a `map`-of-a-torsion-element kernel lemma for
the bundled `MonoidHom K^× → (K,+)`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] L]` (and, through `extLog`/`padicLog`, the scalars `m⁻¹, 1/(n+1) ∈ ℚ_[p]`) | `L` is a normed `ℚ_[p]`-algebra | `K` is a `CharZero` complete nonarchimedean field; `m⁻¹ ∈ K` directly | **yes** | The sign-invariance never asks the base field to be a `ℚ_[p]`-algebra — only that the underlying `extLog`/`padicLog` make sense (`CharZero`). The literature states the kernel fact over `ℂ_p` and arbitrary complete nonarchimedean char-0 fields. This is the **same** inherited artefact as `extLog` row 1 / `extLog_mul` row 1 / `padicLog` row 1. |
| 2 | `[IsUltrametricDist L]` + `[CompleteSpace L]` + `[NormedField L]` | complete ultrametric normed field | complete nonarchimedean field | **NO** | Genuinely needed by the building blocks (`extLog_mul`, the well-definedness of `extLog`, `padicLog` summability) — all use ultrametric norm facts. Correct hypothesis cluster. |
| 3 | `(hx : ExtLogDomain p x)` | `x` in the rational-valuation domain with the near-1 factor in the **exp** ball | `x ∈ K^×` (on `ℂ_p`: vacuous — all nonzero; in general the natural domain of `extLog`) | **partial (inherited, not introduced here)** | The hypothesis correctly restricts to where `extLog` is meaningfully defined and `extLog_mul` applies (off-domain `extLog=0` is junk; the sign fact is asserted of `extLog`, which is only meaningful in-domain). The one inherited narrowing is *inside* `ExtLogDomain` (near-1 factor on the exp ball `‖y−1‖^{p−1}<p⁻¹` rather than the full log ball `‖y−1‖<1`) — the same gap flagged for `padicLog`/`extLog`, widened as part of the `extLog` generalisation, **not** a separate `extLog_neg` move. (Note: `extLog_neg` *itself* proves `−1 ∈ ExtLogDomain` internally, so the only domain hypothesis is on `x`.) |
| 4 | the **shape** of the law (a bare `=` between two `extLog`s) | a standalone sign-invariance equation | the same equation *as* a kernel-membership fact: `−1 ∈ ker(extLog)` for the bundled `MonoidHom (domain subgroup ≤ Kˣ) → (K,+)`, i.e. a corollary of "`extLog` kills `μ_∞`" | **partial (modern-idiom)** | The equation matches the literature exactly. What the literature additionally packages — and what a mathlib version would want — is the *general* "`extLog ζ = 0` for `ζ^n = 1`" kernel lemma (`extLog_eq_zero_of_pow_eq_one`, already in the file) plus, in the bundled form, "torsion ⊆ kernel"; `extLog_neg` is then the `n=2`, `ζ=−1` instance. See Phase 4c rows 3–4. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.**
Number of weakening opportunities found: **K = 1** genuine base-generality weakening
(row 1: drop `[NormedAlgebra ℚ_[p] L]` for `[CharZero K]`). Row 2 is already optimal;
row 3's narrowing is *inherited* from `ExtLogDomain`/`padicLog` (widened as part of
generalising `extLog`, not independently here); row 4 is a Phase-4c idiom point.

Proposed restatement (the literature-standard target, riding on the generalised
`extLog`/`extLog_mul`/`padicLog`):

```lean
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- Sign-invariance of the extended (Iwasawa-branch) p-adic logarithm:
`extLog (-x) = extLog x` (the `μ_2 ⊂ μ_∞` kernel fact). -/
theorem extLog_neg {p : ℕ} [Fact p.Prime] {x : K} (hx : ExtLogDomain p x) :
    extLog p (-x) = extLog p x := …
```

i.e. the *only* change from the current statement is the base-field typeclass cluster
(`[NormedAlgebra ℚ_[p] L]` → `[CharZero K]`). This sits **directly on top of** the generalised
`extLog`, `extLog_mul`, and `extLog_eq_zero_of_pow_eq_one` already proposed in the sibling
reports — `extLog_neg` **cannot be generalised independently**, since it is proven *through*
`extLog_mul` + `extLog_eq_zero_of_pow_eq_one` and is an identity *about* `extLog`.

Cost of restatement: **MODERATE** — the statement is a near-mechanical typeclass rewrite, and
the proof body itself is trivially stable (it only calls `extLog_mul`, `extLog_eq_zero_of_pow_eq_one`,
`neg_one_sq`, `inExpBall_one_sub_one`), but it is *sequenced behind* generalising `padicLog` →
`extLog` → `extLog_mul` (its prerequisites must first sit on the `CharZero`-field setting).
EXPENSIVE/MODERATE does **not** downgrade the verdict — it informs sequencing.

→ STRICTLY NARROWER ⇒ Phase 7 considers **YES-but-generalise-first** prominently. Also runs 4c.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let `L` be a foo" preamble → typeclass? | partial | already typeclass-based; the only change is `NormedAlgebra ℚ_[p] L` → `CharZero K` (row 1 of 4a) | composes with all of mathlib's `CharZero` nonarchimedean-field API, not only `ℚ_[p]`-algebras |
| 2 | sequences/metric → filters/topological? | no | the statement is an algebraic identity (`=`); the `tsum` inside `padicLog` already uses mathlib's filter-based `Summable`/`tsum`. Nothing sequence/metric to filter-ise. | n/a |
| 3 | construct object → universal-property / bundled-morphism class? | **yes** | bundle the extended log as a `MonoidHom (domain subgroup ≤ Kˣ) → (Additive K)` (per the parent `extLog`/`extLog_mul` Phase 4c). Then `extLog_neg` is a **kernel lemma**: `−1` is torsion (`(−1)²=1`), and `extLog` kills torsion (the `map`-of-a-root-of-unity-is-`0` fact), so `extLog (−1) = 0` and `extLog (−x) = extLog x` follows from `map_mul`. | `extLog_neg`, `extLog_eq_zero_of_pow_eq_one`, and the whole `μ_∞`-kernel become consequences of "torsion ⊆ ker(MonoidHom)"/`map_mul`/`map_pow` — free from mathlib's `MonoidHom`/`Subgroup` API instead of bespoke re-proofs |
| 4 | set-with-closure-pred → bundled substructure? | partial | same as the parent: `ExtLogDomain` is the subgroup `p^ℤ·(1+B) ≤ Lˣ` written as a `Prop`; once bundled, `extLog_neg` is the `−1`-instance of the kernel containing `μ_∞ ≤` that subgroup | `Subgroup` lattice + kernel API; `extLog_neg` as `(−1 : ker extLog)` |
| 5 | vector-space/field-specific → weaken to module/ring? | partial | same as row 1: weaken `ℚ_[p]`-algebra to `CharZero` field | uniform `extLog_neg` over `ℚ_p`, finite extensions, `ℂ_p` |
| 6 | 1-categorical → higher-categorical? | no | not categorical | n/a |
| 7 | concrete index ℕ/ℤ/ℝ → general structure? | no | the only "index" is the literal `−1` / exponent `2` in `(−1)²=1`; intrinsic to the `μ_2` statement | n/a |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — two real, same-direction improvements (consistent with the
parent `extLog`/`extLog_mul` Phase 4c).
  - **Base-generality (primary, = Phase 4b):** the `CharZero` complete-nonarchimedean-field form,
    dropping the `ℚ_[p]`-algebra assumption. The sign-invariance of the missing nonarchimedean
    extended logarithm holds over all such fields, not just `ℚ_p`-algebras.
  - **Bundled-kernel (secondary):** once `extLog` is bundled as a `MonoidHom`/`AddMonoidHom` with
    `extLog_mul = map_mul` and the torsion-kernel fact, `extLog_neg` is *not a freestanding lemma*
    but the `ζ=−1` instance of "`extLog` kills roots of unity" — itself a consequence of `map_pow`
    + "the only `n`-th root of `0` … " over the codomain, or just `extLog_eq_zero_of_pow_eq_one`
    bundled as `map`-of-torsion. The literature characterises the extended `log_p` precisely *by*
    its kernel `p^ℚ·μ_∞`; bundling makes `extLog_neg` fall out of that characterisation.
  - Cost: CHEAP for the base-generality rewrite (modulo first generalising `padicLog`/`extLog`/
    `extLog_mul`); MODERATE for the bundling (needs the `ExtLogDomain`-is-a-`Subgroup` upgrade +
    the torsion-kernel packaging, which `extLog_eq_zero_of_pow_eq_one` + `ExtLogDomain.mul`
    already half-supply).
  - Mathlib downstream this enables: composes with mathlib's `CharZero`/nonarchimedean-field API
    and, if bundled, the entire `MonoidHom`/`Subgroup`/kernel ecosystem — `extLog_neg` and the
    `μ_∞` kernel become free consequences of `map_mul`/`map_pow` and "torsion ⊆ ker", subsuming
    `ℚ_p`, finite extensions, `ℂ_p` in one statement.
  - Real mathematical improvement (not just "looks cooler"): the sign-invariance *is* a corollary
    of the kernel fact the literature defines the extension by; over arbitrary complete
    nonarchimedean char-0 fields, and bundled, it stops being a bespoke `ℚ_[p]`-algebra lemma and
    becomes the `−1`-instance of the extended log's characterising kernel.

Phase 4c reinforces Phase 4b: the right mathlib target is the `CharZero`-field form (ideally the
`−1`-instance of the bundled hom's torsion-kernel), built atop the generalised
`extLog`/`extLog_mul`/`padicLog` — **not** the `ℚ_[p]`-algebra freestanding lemma. Since Phase 4b
already found the form STRICTLY NARROWER, the verdict is `YES-but-generalise-first` regardless.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** No definitional equalities or typeclass-search paths are
introduced. (The objects it rests on get their own Phase-4.5 assessments when they are targets:
`extLog` was assessed `YES-but-generalise-first` with overall risk NONE/LOW; `ExtLogDomain` is a
`Prop`-valued predicate; `extLog_mul`/`extLog_eq_zero_of_pow_eq_one` are theorems.)

---

### Mathlib search-status: `PadicLFunctions.extLog_neg`

[A] Lean-Finder       — **n/a**: Lean-Finder MCP not available in this environment. Compensated by exhaustive source grep (D) + name enumeration (E) over the actual pinned mathlib.
[B] Loogle            type-patterns `?f (-?x) = ?f ?x` (negation-invariance of a unary function) and `padicLog`/`extLog`-shaped — **n/a**: `lean_loogle` MCP not available; substituted by source grep (D). The `f(-x)=f(x)` pattern in the `log` family returns only the **archimedean** `Real.log_neg_eq_log` (see [D]); no nonarchimedean/p-adic instance.
[C] LeanSearch        "p-adic logarithm of negation equals logarithm", "extended Iwasawa logarithm sign invariant", "nonarchimedean log of -x equals log x", "p-adic log kills roots of unity" — **n/a**: `lean_leansearch` MCP not available; substituted by the literature channels (Phase 3) + source grep.
[D] Grep mathlib src  **executed in full** on `.lake/packages/mathlib/`:
  - `def +(padicLog|padicExp)`, `nonarchimedean.*log`, `ultrametric.*log`, `iwasawa.*log` → **no p-adic/nonarchimedean log of any kind** (the only `nonarchimedean` hits are the *topological-group* classes `NonarchimedeanGroup`/`NonarchimedeanRing`, unrelated).
  - `ls Mathlib/NumberTheory/Padics/` → `AddChar, Complex, HeightOneSpectrum, Hensel, MahlerBasis, PadicIntegers, PadicNorm, PadicNumbers, PadicVal, ProperSpace, RingHoms, ValuativeRel, WithVal` — **no Exp/Log file at all**.
  - `log_neg_eq_log` (the *shape* `log(-x)=log x`) → **`Real.log_neg_eq_log`** at `Analysis/SpecialFunctions/Log/Basic.lean:120`: `log (-x) = log x := by rw [← log_abs x, ← log_abs (-x), abs_neg]`. **Archimedean**; proven via `log = log |·|` — a *completely different* mechanism (the real log is even because it is `log ∘ abs`), not the kernel-of-roots-of-unity additivity argument. No `Complex`/nonarchimedean analog of the *negation* law beyond the real one.
[E] Name pattern      enumerated every `log`/`*_neg`/`*_neg_eq` in the `log` family: archimedean `Real.log_neg_eq_log`, `Real.log_neg`, `Complex.log` (no `log_neg_eq_log` — `Complex.log` is *not* even), `ENNReal`/`EReal` logs; discrete `Nat.log`/`Int.log`; formal `PowerSeries.log`. **No p-adic/nonarchimedean `log` exists**, hence no negation-invariance for one.

Searched for both:
  - the user's current form (`extLog(−x)=extLog x` over an ultrametric `ℚ_[p]`-algebra, on `ExtLogDomain`): **not in mathlib**.
  - the literature-standard form (sign-invariance / `−1`-in-kernel of the extended Iwasawa log over a complete nonarchimedean char-0 field / `ℂ_p`, on all of `K^×`, ideally as a bundled-hom kernel fact): **not in mathlib**.

Closest existing mathlib objects (all confirmed *not* the same):
  - `Real.log_neg_eq_log` (`Analysis/SpecialFunctions/Log/Basic.lean:120`) — the **archimedean** `log(−x)=log x`. Same *shape*, but a different function (real log) proven a different way (`log ∘ abs` is even). Confirms the shape is mathlib-idiomatic; the p-adic instance is absent.
  - `NormedSpace.exp` + `exp_add_of_mem_ball` (`Analysis/Normed/Algebra/Exponential.lean`) — analytic exp, no companion `log`, archimedean radius. Cannot phrase `extLog`.
  - `PowerSeries.log` (`RingTheory/PowerSeries/Log.lean`) — the **formal** log series; no convergence, no evaluation, no sign-invariance of an evaluated function.

Concluded: **not in mathlib** (all available methods exhausted — source grep run **in full** for both the user's form and the literature-standard form, directly confirming no `padicLog`/`extLog` and no Exp/Log file under `NumberTheory/Padics/`; the entire `log`-family `*_neg`/`log`-def inventory enumerated; semantic MCP tools genuinely unavailable and recorded n/a). Mathlib has **no nonarchimedean / p-adic analytic logarithm of any kind**, hence no sign-invariance law for one — and a fortiori no extended (Iwasawa-branch) version. Consistent with the sibling `extLog.md`, `extLog_mul.md`, `padicLog.md` (all "not in mathlib"). `extLog_neg` is the sign-invariance of an object three steps out (the `−1`-kernel of the off-ball extension of an already-missing `padicLog`), so it is triply absent.

---

### Call sites — `PadicLFunctions.extLog_neg`

Internal use count: **2 genuine `extLog_neg` applications** (within the `PadicLFunctions`
project, NOT counting the declaring statement or docstring mentions), both in **1 external
file** (`ValuesAtOne.lean`).
External-to-file callers: **1 distinct file** (`ValuesAtOne.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `ValuesAtOne.lean:1099` | `extLog_neg p hdom, ih` — the `insert`/induction step of `extLog_neg_one_pow_mul` (`extLog((−1)^m·x) = extLog x`), i.e. the `μ_2`-power invariance lifting `extLog_neg` to all `(−1)^m`. This in turn drives the `±1`-invariance used in the `μ_p`-collapse (`ValuesAtOne.lean:1161`). |
| `ValuesAtOne.lean:1757` | `rw [show (1:K) − ε^c = −(ε^c − 1) from by ring, extLog_neg p hdom]` — the sign fix `extLog(ε^c − 1) = extLog(1 − ε^c)` in the residue/p-adic-L-value computation (matching the orientation of the log-of-`1−ε^c` factor in RJW Thm 6.1(ii)). |

Inline-derivation grep (was `extLog(−x)=extLog x` re-derived without calling `extLog_neg`?):
  - **Within `PadicLFunctions`: none.** No site re-derives sign-invariance by hand via
    `extLog_mul` + the `extLog(−1)=0` step; both consumers route through `extLog_neg`.
  - **Cross-project:** no other `extLog`/extended-log exists in the repo
    (`grep extLog projects/ --exclude PadicLFunctions` → empty), so no duplicate `extLog_neg`.

Call-sites signal: **K = 2 genuine uses (both external, in `ValuesAtOne.lean`), with no
inline re-derivation → real, consumed API** (it is the base case of the `(−1)^m`-invariance
induction `extLog_neg_one_pow_mul` and a load-bearing sign fix in the L-value computation).
Per the Phase-6.0.1 table this is between "K ≥ 3 ⇒ YES" and "K = 1 ⇒ lean NO"; at K = 2 with
no bypass it is genuine consumed API, reinforcing a YES-* lean (the verdict is anyway driven by
the inherited generality narrowing, not the call count).

---

### Composition check (Phase 6)

Can `PadicLFunctions.extLog_neg` be derived from mathlib in ≤3 chained calls?

Attempt 1: some mathlib `log_neg`/negation-invariance lemma applied to `extLog`.
  - Mathlib decls used: `Real.log_neg_eq_log`.
  - Result: **fails** — `Real.log_neg_eq_log` is about the *real* log (proven via `log = log∘abs`); there is no mathlib `extLog`/`padicLog` to apply it to, and no nonarchimedean negation law. Not a composition.

Attempt 2: build it from a bundled-hom `map`/kernel lemma over mathlib's `MonoidHom` API.
  - Mathlib decls used: `map_mul`, `map_pow`, some "torsion ↦ identity" lemma.
  - Result: **fails** — there is no mathlib `extLog` bundled as a `MonoidHom` (no nonarchimedean log exists to bundle); the bundling is itself the *proposed* (not yet existing) generalisation. Not a current composition.

Attempt 3: assemble `extLog_neg` from the repo's own primitives in ≤3 mathlib calls.
  - Result: **fails as a *mathlib* composition.** The proof is `extLog(−x) = extLog((−1)·x) = extLog(−1) + extLog x` (via `extLog_mul`) `= 0 + extLog x` (via `extLog_eq_zero_of_pow_eq_one` on `(−1)²=1`) `= extLog x`. This is short (≤3 *project* steps), but **every** primitive — `extLog`, `extLog_mul`, `extLog_eq_zero_of_pow_eq_one`, `ExtLogDomain`, `InExpBall` — is project-local and **absent from mathlib**. A "composition" that bottoms out entirely in mathlib-missing definitions is not a mathlib composition; it is a corollary *within the project's own (to-be-upstreamed) API*.

Conclusion: **NOT-COMPOSABLE (from mathlib).** Although `extLog_neg` is a short corollary of
`extLog_mul` + the roots-of-unity-kernel lemma *inside the project*, those building blocks are
not in mathlib (mathlib has no nonarchimedean log at all). It cannot be inlined at call sites
as a 1–3 mathlib-call glue. Within the package, it is a natural small lemma to ship alongside
`extLog_mul`/`extLog_eq_zero_of_pow_eq_one`.

---

## Verdict: `PadicLFunctions.extLog_neg`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): `extLog(−x) = extLog x` is the `−1`-instance of the
  **kernel-is-roots-of-unity** property of the extended Iwasawa logarithm — every source
  (Wikipedia verbatim: "the roots of `log_p` are exactly `p^r·ζ`, `ζ` a root of unity"; MIT
  18.785, K. Conrad, planetmath, the AAC/principal-units arXiv papers) states the extended
  `log_p` is a homomorphism killing all roots of unity. `−1` is a 2nd root of unity ⇒
  `log_p(−1)=0` ⇒ `log_p(−x)=log_p x`. Stated over `ℂ_p` / complete nonarchimedean char-0
  fields, **not** restricted to `ℚ_p`-algebras.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 1 base-generality
  weakening (drop `[NormedAlgebra ℚ_[p] L]` for `[CharZero K]`), inherited from
  `extLog`/`extLog_mul`/`padicLog`. The `ExtLogDomain p x` hypothesis is the natural domain
  (not an extra narrowing); the exp-ball-vs-log-ball point is inherited. Phase 4c agrees and
  adds the bundled-hom torsion-kernel idiom.
- Mathlib search (Phase 5): **not in mathlib** under either form. Directly confirmed: no
  `padicLog`/`extLog`, no Exp/Log file under `NumberTheory/Padics/`, no nonarchimedean log.
  The closest object, `Real.log_neg_eq_log`, is the *archimedean* shape proven a different way
  (`log∘abs`), confirming the shape is mathlib-idiomatic while the nonarchimedean instance is
  absent.
- Composition check (Phase 6): **NOT-COMPOSABLE (from mathlib)** — a short corollary of
  `extLog_mul` + `extLog_eq_zero_of_pow_eq_one`, but every building block is project-local and
  missing from mathlib.

**Rationale (1–2 paragraphs):**

`extLog_neg` is the **sign-invariance law `log_p(−x) = log_p(x)`** of the extended
(Iwasawa-branch) p-adic logarithm — the `μ_2 = {±1}` instance of the property the literature
defines the extension by: the extended `log_p` is a group homomorphism `K^× → (K,+)` whose
kernel is exactly `{p^r·ζ : r∈ℚ, ζ a root of unity}` (Wikipedia verbatim, MIT 18.785, K.
Conrad/Jack Thorne, planetmath, World Scientific, the modern arXiv principal-units/AAC papers
— unanimous). Since `−1` is a 2nd root of unity, `log_p(−1) = 0`, and additivity gives
`log_p(−x) = log_p(−1) + log_p(x) = log_p(x)` — which is exactly the Lean proof (prove `−1 ∈
ExtLogDomain` via `(−1)²=1`, rewrite `−x = (−1)·x`, apply `extLog_mul`, kill `extLog(−1)` via
`extLog_eq_zero_of_pow_eq_one`). Mathlib has **no nonarchimedean logarithm of any kind**
(directly verified: no `padicLog`/`extLog`, no Exp/Log file under `NumberTheory/Padics/`; the
only negation-invariance in the `log` family is the *archimedean* `Real.log_neg_eq_log`, proven
via `log∘abs` — a different function and a different mechanism), so it has neither `extLog` nor
its sign-invariance. The lemma is real, consumed API: 2 external applications in
`ValuesAtOne.lean` — the base case of the `(−1)^m`-invariance induction
`extLog_neg_one_pow_mul` (feeding the `μ_p`-collapse) and a load-bearing sign fix in the
residue/p-adic-L-value computation — with no inline re-derivation. Phase 6 confirms
NOT-COMPOSABLE from mathlib: although it is a short corollary *within the project's own API*,
every building block (`extLog`, `extLog_mul`, `extLog_eq_zero_of_pow_eq_one`) is project-local
and absent from mathlib.

The verdict is **not** `YES-add-as-is` because Phase 4b found the Lean form **strictly narrower
than the literature standard**, on the very same base-field axis already flagged for its parent
`extLog`/`extLog_mul` and base `padicLog` (all `YES-but-generalise-first`): it gratuitously
assumes `[NormedAlgebra ℚ_[p] L]`, whereas the sign-invariance/kernel fact of the extended
Iwasawa log needs only a complete nonarchimedean **char-0** field — the literature states it
over `ℂ_p` and arbitrary such fields, never restricting to `ℚ_p`-algebras. (The `ExtLogDomain p
x` hypothesis is *not* an additional narrowing: it faithfully restricts to the domain on which
`extLog` is even defined and `extLog_mul` applies, and over `ℂ_p` is vacuous, recovering the
literature's "all of `K^×`" form.) Crucially, `extLog_neg` is proven *through* `extLog_mul` +
`extLog_eq_zero_of_pow_eq_one` and is an identity *about* `extLog`, so it **cannot be
generalised independently** — it must ride on the `extLog`/`extLog_mul`/`padicLog`
generalisation. Per the skill's verdict gate, a known weakening forces
`YES-but-generalise-first`, not `YES-add-as-is`; and cost (MODERATE, sequenced behind the
cluster generalisation) is explicitly **not** a downgrade factor. This is **not**
`NO-composable-from-mathlib` either: the composition bottoms out in mathlib-missing primitives,
so it is not a mathlib-call glue — it ships *with* the package, not inlined.

**Reason for the generalisation:**
  - **LITERATURE-WEAKENING (primary):** Phase 4b found the user's form strictly narrower than
    the literature-standard form — the redundant `ℚ_[p]`-algebra assumption (the kernel/sign
    fact holds over any complete nonarchimedean char-0 field; the literature states it over
    `ℂ_p`).
  - **MODERN-IDIOM (secondary, same direction):** Phase 4c — once the extended log is bundled as
    a `MonoidHom (domain subgroup ≤ Kˣ) → (K,+)` (per the parent `extLog`/`extLog_mul` reports),
    `extLog_neg` is the `ζ=−1` instance of "the extended log kills roots of unity" (the kernel
    `p^ℚ·μ_∞` the literature characterises it by), itself a consequence of `map_mul`/`map_pow`
    + the torsion-kernel fact — not a freestanding bespoke lemma.

  Proposed restatement:
  ```lean
  variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

  /-- Sign-invariance of the extended (Iwasawa-branch) p-adic logarithm:
  `extLog (-x) = extLog x` (the `μ_2 ⊂ μ_∞` kernel fact). -/
  theorem extLog_neg {p : ℕ} [Fact p.Prime] {x : K} (hx : ExtLogDomain p x) :
      extLog p (-x) = extLog p x := by
    sorry  -- proof is stable: extLog_mul + extLog_eq_zero_of_pow_eq_one (both generalised)
  ```
  (the only change from the current statement is `[NormedAlgebra ℚ_[p] L]` → `[CharZero K]`);
  ideally re-derived as the `ζ=−1` kernel instance of the bundled `extLog : (domain subgroup of
  Kˣ) →* (Additive K)` per Phase 4c rows 3–4.

  Estimated cost of regeneralisation: **MODERATE** — the statement is a near-mechanical typeclass
  rewrite and the proof body is trivially stable, but it is *sequenced behind* generalising
  `padicLog` → `extLog` → `extLog_mul` → `extLog_eq_zero_of_pow_eq_one` (its prerequisites must
  first sit on the `CharZero`-field setting). EXPENSIVE/MODERATE does **not** downgrade the
  verdict.

  Mathlib downstream this enables:
  - the single general `extLog_neg` serves `ℚ_p`, finite extensions, and `ℂ_p` uniformly as the
    sign-invariance of the canonical extended Iwasawa logarithm;
  - if bundled, `extLog_neg` becomes a free consequence of `map_mul`/`map_pow` + "torsion ⊆
    ker" from mathlib's `MonoidHom`/`Subgroup` API, alongside the full `μ_∞` kernel — instead of
    a bespoke re-proof;
  - it (with `extLog_eq_zero_of_pow_eq_one`) gives mathlib the `roots-of-unity ⊆ ker(log_p)`
    half of "the unique homomorphic extension of `log_p` with `log_p(p)=0`" — facts downstream
    p-adic L-function / Iwasawa-theory work (this project's `ValuesAtOne.lean`) repeatedly needs.

  Proposed mathlib location (post-generalisation): ship **together with** the generalised
  `padicLog`/`extLog`/`extLog_mul`/`extLog_eq_zero_of_pow_eq_one` (and `padicExp`/`InExpBall`) as
  one coherent "p-adic exponential and logarithm" contribution — e.g.
  `Mathlib/NumberTheory/Padics/Logarithm.lean` (new), with `extLog_neg` as the sign-invariance /
  `μ_2`-kernel of the extended branch (or a free `map_pow`/kernel consequence of the bundled
  `Padic.iwasawaLog`). **PR grouping (required):** do **not** upstream `extLog_neg` in isolation —
  it ships with `padicLog`, `padicLog_mul`, `extLog`, `extLog_mul`, `extLog_eq_zero_of_pow_eq_one`,
  `extLog_prod` as one package.

  Pre-PR checklist before opening:
    - [ ] `/generalise PadicLFunctions.extLog_neg` — confirm the `CharZero`-field restatement (and,
          ideally, the bundled-hom kernel derivation), after first generalising `padicLog` → `extLog`
          → `extLog_mul` → `extLog_eq_zero_of_pow_eq_one` (its prerequisites).
    - [ ] `/cleanup projects/PadicLFunctions/PadicLFunctions/ExtLog.lean extLog_neg` — full audit + diff gates.
    - [ ] Pick a mathlib reviewer from `Mathlib/NumberTheory/Padics/` recent commits; announce the
          p-adic-exp/log package on the `#mathlib4` Zulip.

  Next action: **run `/generalise PadicLFunctions.extLog_neg`** (it will tension against both the
  literature-standard kernel/sign form from Phase 3 and the modern-idiom bundled-hom torsion-kernel
  form from Phase 4c) — **after** first generalising `padicLog`, `extLog`, `extLog_mul`, and
  `extLog_eq_zero_of_pow_eq_one` (its prerequisites; see `padicLog.md`, `extLog.md`, `extLog_mul.md`).
  Then `/cleanup` `ExtLog.lean` and open the mathlib PR grouping the whole p-adic exponential/logarithm
  core as one coherent contribution.

---

## Next step

Run `/generalise PadicLFunctions.extLog_neg` to restate it over a complete nonarchimedean
`CharZero` field `K` (dropping `[NormedAlgebra ℚ_[p] L]`), and ideally re-derive it as the
`ζ=−1` instance of the extended log's torsion kernel once `extLog` is bundled as the `MonoidHom
(domain subgroup of Kˣ) → (K,+)` whose kernel is `p^ℚ·μ_∞` the literature characterises `log_p`
by. This is **sequenced behind** generalising `padicLog` → `extLog` → `extLog_mul` →
`extLog_eq_zero_of_pow_eq_one` (`extLog_neg` is proven through `extLog_mul` +
`extLog_eq_zero_of_pow_eq_one` and is an identity about `extLog`). Then `/cleanup` `ExtLog.lean`
and open a single mathlib PR grouping the whole p-adic exponential/logarithm core (`padicExp` +
`padicLog` + `padicLog_mul` + `extLog` + `extLog_mul` + `extLog_eq_zero_of_pow_eq_one` +
`extLog_neg` + `extLog_prod` + `InExpBall`), with the bundled-homomorphism kernel facts as the
canonical home for "`log_p` kills roots of unity".
