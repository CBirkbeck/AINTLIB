# `/mathlibable` report — `PadicLFunctions.pZpExp_coe`

**Final verdict: `BORDERLINE-needs-human`.** The *mathematical content* of `pZpExp_coe`
is a genuine, classical fact mathlib is missing — **for odd `p`, the `p`-adic exponential is
integral on `pℤ_p`** (it maps `pℤ_p` into `1 + pℤ_p`; equivalently `‖exp x‖ ≤ 1` there). But
the lemma as written is the **defining/branch-selection equation of a project-local junk-total
construction** `pZpExp` (a `dif`-on-`‖·‖≤1` packaging of `padicExp`, junk value `1`), and its
mathlib-worthiness is entirely contingent on a *form* decision the skill cannot ground in the
evidence alone: should mathlib have the `ℤ_p`-valued *junk-total restriction* at all, or only
the integrality lemma `‖exp x‖ ≤ 1` / `exp x ∈ 1+𝔪` *about* `NormedSpace.exp` (at the
generality of a complete nonarchimedean local field), from which any restriction is derived? The
parent `pZpExp` has **no report yet**, so this cannot be resolved by inheritance. Four numbered
questions are posed in Phase 7.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` stale/slow here; Phase 0 fallback used: read the decl + dependency closure directly).
- decl `PadicLFunctions.pZpExp_coe`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1046`
- kind:                      `theorem`
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp`/`log` on the ball `‖x‖ < p^{−1/(p−1)}` of a complete nonarchimedean normed `ℚ_[p]`-algebra field; for odd `p` the ball contains `pℤ_p`; realises `x^s := exp(s·log x)` and agrees with `PadicInt.onePAdicPow`.

---

### Statement (Phase 1)

`PadicLFunctions.pZpExp_coe` is a **theorem** asserting the defining equation of the junk-total
integral exponential `pZpExp` on the prime ideal `pℤ_p`:

> For an odd prime `p` and `x ∈ pℤ_p`, the `ℤ_p`-valued integral exponential `pZpExp p x`,
> pushed back to `ℚ_p`, equals the analytic `p`-adic exponential `exp(x) = ∑ xⁿ/n!`:
> `((pZpExp p x : ℤ_[p]) : ℚ_[p]) = padicExp p (x : ℚ_[p])`.

Mathematically this is the bookkeeping half of the classical fact that **`exp` is integral on
`pℤ_p` for odd `p`** — i.e. `exp` maps `pℤ_p` into `1 + pℤ_p ⊆ ℤ_p^×`. The parent definition

```lean
noncomputable def pZpExp (x : ℤ_[p]) : ℤ_[p] :=
  if h : ‖padicExp p ((x : ℚ_[p]))‖ ≤ 1 then ⟨padicExp p ((x : ℚ_[p])), h⟩ else 1
```

is a *junk-total* (everywhere-defined) `ℤ_p`-valued function: when `exp(x)` happens to be
integral it returns the genuine value as an element of `ℤ_p`; otherwise it returns the junk
value `1`. `pZpExp_coe` proves that on `pℤ_p` the integrality side-condition `‖exp x‖ ≤ 1`
holds, so the `dif` takes its true branch and `pZpExp` carries the true `exp`.

The proof is **not** glue (`rfl`/`Iff.rfl`): it establishes `‖exp x‖ ≤ 1` by a genuine
ultrametric argument — `‖exp x − 1‖ = ‖x‖` on the ball (`norm_padicExp_sub_one`), `‖x‖ ≤ 1` on
`pℤ_p`, then `‖exp x‖ = ‖1 + (exp x − 1)‖ ≤ max(1, ‖x‖) ≤ 1` via
`IsUltrametricDist.norm_add_le_max` — and only then selects the branch with `rw [pZpExp, dif_pos hle]`.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the residue characteristic.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`
  is in scope file-wide, but **this theorem `omit`s `[NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]`** — its statement and proof live entirely over `ℚ_[p]`/`ℤ_[p]` (the `L`-instance of `padicExp` is used at `L = ℚ_[p]`). So `pZpExp_coe` is, mathematically, **fixed to `ℚ_p`/`ℤ_p`** — it is not stated for a general nonarchimedean extension.

Hypotheses (Lean side):
- `(hp2 : p ≠ 2)` — odd prime. **This is the load-bearing hypothesis:** it is exactly what places `pℤ_p` strictly inside the exp convergence ball `‖x‖ < p^{−1/(p−1)}` (for `p = 2`, `pℤ_2 = 2ℤ_2` is *not* inside the ball, and `exp` need not be integral there — one needs `4ℤ_2`).
- `{x : ℤ_[p]}`, `(hx : x ∈ Ideal.span {(p : ℤ_[p])})` — `x ∈ pℤ_p`.

Conclusion (math): on `pℤ_p` (odd `p`) the junk-total `pZpExp` realises the true analytic `exp` — equivalently `exp` is integral on `pℤ_p`.

Conclusion (Lean): `((pZpExp p x : ℤ_[p]) : ℚ_[p]) = padicExp p ((x : ℚ_[p]))`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG shadow).
Reason: `pZpExp_coe` itself is a helper/defining-equation lemma — it is the "true-branch selector"
for the def `pZpExp`. It is *not* a `## Main results` headline (the headline is RJW Lem 5.14:
`x^s := exp(s·log x)` agreeing with `onePAdicPow`, proved later at
`padicExp_smul_padicLog_eq_onePAdicPow`). However, the *content* it encodes — exp integral on
`pℤ_p` — is a classical named fact (BIG-shadow), so the literature width below is genuinely
EXHAUSTIVE and not pro-forma.

(Literature width is EXHAUSTIVE regardless of this classification.)

### One-line check (Phase 2b)

Body line count: ~12 substantive lines (a `have hle : ‖…‖ ≤ 1` proved by a `calc` through the
ultrametric inequality, then `rw [pZpExp, dif_pos hle]`).
One-liner verdict: **n/a — kind is `theorem`, not `def`.** (For completeness: even if it were a
def, it is multi-line, so no one-liner penalty applies.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic exponential maps pZ_p into 1+pZ_p integral odd prime exp converges principal units" | yes | "for odd primes `p`, `exp: pℤ_p → 1+pℤ_p`; `exp∘log = id` on `1+pℤ_p`, `log∘exp = id` on `pℤ_p`"; "image of exp is the ball of valuative radius `1/(p−1)` around 1" | Jack Thorne (Cambridge) p-adic analysis notes; M-L. Hsieh L3 notes; K. Conrad notes. The integrality `exp(pℤ_p) ⊆ 1+pℤ_p` is exactly the content of `pZpExp_coe`. |
| 2 | WebSearch (general / isomorphism form) | "p-adic exponential isomorphism exp: pZ_p -> 1+pZ_p logarithm log: 1+pZ_p -> pZ_p odd p" | yes | "for odd `p > 2`, `exp` and `log` are inverse isomorphisms between the additive group `pℤ_p` and the multiplicative group `1+pℤ_p`"; "`log(1+pⁿℤ_p) ⊆ pⁿℤ_p`" | Wikipedia *P-adic exponential function*; PlanetMath; David Vogan (MIT) *Exponential and logarithm in p-adic fields*; uchicago REU (Gupta). Standard form is the **bundled iso**, not a junk-total branch. |
| 3 | WebSearch (named-after / aliases / p=2 caveat) | "p-adic exp restriction to ring of integers well-defined integral exp_p(x) in Z_p Cassels local fields chapter 12" | yes | "the natural `exp(x)=∑xⁿ/n!` is **not** well-defined on all of `ℤ_p`; instead `E_p(x):=exp(px)` (and `E_2(x):=exp(4x)`) is well-defined on `ℤ_p`" | Mariano (arXiv 1408.0900) p-adic exponential ring; properties cited to Cassels, *Local Fields* Ch. 12 (the file's own citation). Confirms the `p=2`→`4ℤ_2` caveat that motivates the `hp2` hypothesis. |
| 4 | WebSearch (maximal-generality / local-field form) | "exponential nonarchimedean local field maps maximal ideal into units of integers complete discrete valuation ring" | partial | the standard local-field setup `𝒪={‖·‖≤1}`, `𝔪={‖·‖<1}`, `𝒪^×={‖·‖=1}` is the natural home; exp on `𝔪` for `e<p−1` lands in `1+𝔪` | search surfaced the DVR/local-field framing (Williams–Wuthrich, Tomczak Cambridge LF notes) but not a single packaged lemma — the general-local-field statement of "exp integral on `𝔪`" is folklore, stated per-text. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` symlink | n/a | (no `references/` dir; no `refs/` symlink) | Recorded n/a — both absent. The file's own docstring citations (RJW Lem 5.14, Cassels §12, Washington §5.1) substitute. |
| 6 | nLab | WebFetch `ncatlab.org/nlab/show/p-adic+exponential` (per sibling `padicExp.md`: HTTP 404) | n/a | no dedicated nLab page | nLab has no standalone "p-adic exponential" entry; the integrality fact is a p-adic-analysis result, not categorical. |
| 7 | nCatLab (categorical) | (same as 6) | n/a | not a categorical concept | A branch-selection equation for a power-series special function; no universal-property formulation. |
| 8 | Stacks Project | — | n/a | not an algebraic-geometry concept | The integral p-adic exp is analytic number theory; outside Stacks' scheme-theoretic scope. |
| 9 | MathOverflow / Math.SE | (covered by WebSearch channels 1–3, which surfaced lecture notes + MO/MSE consensus) | yes | consensus: `exp: pℤ_p ≅ 1+pℤ_p` for odd `p`; `exp(x)` integral with `‖exp x‖ = 1` on `pℤ_p` | No disagreement on the underlying fact. |
| 10 | recent arXiv (≤5 yrs) | "Hensel minimality, p-adic exponentiation and Tate uniformization" (2602.16433); "p-adic exponential ring…" (1408.0900) | yes | same classical object; `E_p(x)=exp(px)` integral on `ℤ_p`; iso `pℤ_p ≅ 1+pℤ_p` | Modern papers use the identical fact; none reformulate the junk-total branch encoding (that is a formalization device, not a math object). |

Protocol pass: WebSearch ran **4** queries at four generality levels (specific `exp(pℤ_p)⊆1+pℤ_p`,
the bundled iso, the named/Cassels form with the `p=2` caveat, and the general-local-field form);
local refs checked (n/a, absent); nLab/nCatLab/Stacks recorded n/a with reasons; MO/MSE and arXiv
each hit.

**Channel deviations from the 9-channel ideal (disclosed):** the **ChatGPT MCP** channel is
recorded **n/a — MCP server not configured in this environment** (no `chatgpt`/`codex` tool is
exposed; `/mathlib-quality:setup-chatgpt` was never run here). To compensate, WebSearch was run at
**four** distinct generality levels (one above the required ≥3) plus a WebFetch of the primary
source, and the sibling `padicExp.md` report's MCP findings on the same exponential object are
cross-referenced. Likewise **Loogle / LeanSearch / Lean-Finder MCP tools are unavailable**, so
Phase 5 leans on the decisive grep-over-mathlib-source method [D] + name-pattern [E].

### Literature summary (Phase 3)

Concept identified as: **integrality of the `p`-adic exponential on `pℤ_p`** — equivalently the
exp/log isomorphism `exp: pℤ_p ≅ 1+pℤ_p` for odd `p`. `pZpExp_coe` is the "exp lands in `ℤ_p`"
half (its companions `pZpExp_sub_one_mem`, `padicExp_smul_padicLog_eq_onePAdicPow` carry the rest).
Sources agree on the standard form: **yes** — and they agree it is naturally a **bundled map**
`pℤ_p → 1+pℤ_p` (often a group isomorphism), *not* a junk-total `dif`-branch construction.
Most general standard form: on a complete nonarchimedean field/DVR `(𝒪, 𝔪)` with absolute
ramification small enough (`e < p−1`; for `ℚ_p` this is `p` odd), `exp` maps `𝔪` into `1+𝔪 ⊆ 𝒪^×`,
and `exp: 𝔪 ≅ 1+𝔪`. Specialised to `ℚ_p`: `exp: pℤ_p ≅ 1+pℤ_p`, odd `p`.
Generality dimensions where the literature varies:
  - **Base field**: textbooks state it over `ℚ_p` (the project's setting), but the maximal-generality
    form is an arbitrary complete nonarchimedean local field / DVR with `e < p−1`. The project's
    lemma is **fixed to `ℚ_p`** (it `omit`s the general-`L` instances), so it is *strictly narrower*
    than the literature's natural home even though the file's `padicExp` itself is `L`-general.
  - **Packaging**: bundled map / `MonoidHom` / iso (literature default) vs. junk-total `dif`-on-norm
    restriction with junk value `1` (the project's Lean device). The latter is a formalization
    convenience, not a literature object.
  - **`p=2` caveat**: universally noted — `exp` is integral on `4ℤ_2`, not `2ℤ_2`. The `hp2`
    hypothesis matches.
Disagreement with the literature: **none on the fact**; the divergence is purely in *form*
(junk-total restriction vs. bundled map, `ℚ_p`-fixed vs. general local field).

If the literature search had returned nothing this would bias toward NO/BORDERLINE — but it
returned a clear, classical fact, so the BORDERLINE here is *form*-driven, not absence-driven.

---

### Generality analysis — `PadicLFunctions.pZpExp_coe`

Literature-standard form (from Phase 3): `exp: 𝔪 → 1+𝔪` (integral on the maximal ideal) on a
complete nonarchimedean DVR/local field with `e < p−1`; for `ℚ_p`, `exp(pℤ_p) ⊆ 1+pℤ_p`, odd `p`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | base field fixed to `ℚ_[p]`/`ℤ_[p]` (theorem `omit`s general `L`) | `ℚ_p`/`ℤ_p` only | complete nonarchimedean local field / DVR `(𝒪,𝔪)`, `e<p−1` | **yes** | The *content* (exp integral on `𝔪`) holds for any such field; the project's `padicExp`/`norm_padicExp_sub_one`/`InExpBall` are already `L`-general, so the integrality bound `‖exp x‖ ≤ 1` could be stated over general `L` with `‖x‖ ≤ 1`. The `ℚ_p`-fixing is a *narrowing*, driven by the chosen `ℤ_p`-valued packaging. |
| 2 | `(hp2 : p ≠ 2)` | odd `p` | `e < p−1` (⇔ `p` odd for `ℚ_p`) | NO (for `ℚ_p`) | Genuinely necessary: `pℤ_2` is outside the convergence ball; the right `ℤ_2` statement uses `4ℤ_2`. Not a removable hypothesis — it is the correct one for `ℚ_p`. |
| 3 | `(hx : x ∈ Ideal.span {p})` | `x ∈ pℤ_p` | `x ∈ 𝔪` (here `pℤ_p`) / more generally `‖x‖ ≤ p⁻¹` | partially | The proof only needs `‖x‖ ≤ p⁻¹` (used via `coe_norm_le_inv_of_mem_span` then `‖x‖ ≤ 1`). Stating via the norm bound rather than ideal membership is a mild generalisation, but `x ∈ pℤ_p` is the idiomatic/standard packaging. |
| 4 | target type `ℤ_[p]` (the `pZpExp` value) + junk-total `dif` encoding | junk-total restriction, junk value `1` | bundled `exp: pℤ_p → 1+pℤ_p` (or integrality *lemma* `‖exp x‖ ≤ 1`) | **yes — different form entirely** | The junk-total `dif`-on-norm construction is a Lean device. The literature object is the bundled map; mathlib would more idiomatically state the *integrality lemma* about `NormedSpace.exp` and derive any restriction. `pZpExp_coe` is the glue tying the device to `padicExp`. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.**
Number of weakening opportunities found: **3** (base field `ℚ_p` → general nonarchimedean local
field; ideal-membership → norm bound; and most importantly the junk-total `ℤ_p`-restriction →
either a bundled map or a plain integrality lemma about the general exponential).
Proposed restatement: see Phase 4c (the right target is the *modern-idiom* reformulation, since the
"narrowing" here is inseparable from the *packaging* choice — the literature form is a bundled map /
an integrality lemma, not a more-general junk-total `dif`).
Cost of restatement: **MODERATE** — the underlying integrality bound `‖exp x‖ ≤ 1` is already
proved inside `pZpExp_coe`'s body over `L`-general primitives, so extracting it as a standalone
`norm_padicExp_le_one` (general `L`, `‖x‖ ≤ p⁻¹`) is cheap; re-packaging the *restriction* as a
bundled map and re-deriving the def-equation is moderate. (Per the skill, cost does not by itself
change the bucket.)

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" → typeclasses? | partially | re-aim the *content* at general `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` (the file's own variables, which this theorem currently `omit`s) — i.e. state the integrality bound over `L`, not just `ℚ_p` | every nonarchimedean extension of `ℚ_p` (`C_p`, finite extensions) gets exp-integrality for free |
| 2 | sequences/metric → filters/topological? | no | the proof is already norm/ultrametric-inequality based, no sequences | — |
| 3 | construct an object → universal-property class? | no (but see 4) | the iso `pℤ_p ≅ 1+pℤ_p` is a structure, not a universal property | — |
| 4 | set-with-closure-predicate → **bundled (sub)structure / bundled map**? | **yes** | replace the junk-total `pZpExp : ℤ_p → ℤ_p` + its `_coe` equation by either (a) a bundled **integrality lemma** `theorem norm_padicExp_le_one (hx : ‖x‖ ≤ (p:ℝ)⁻¹) : ‖padicExp p x‖ ≤ 1` about `NormedSpace.exp` (general `L`), from which `ℤ_p`-restrictions follow; or (b) a bundled map `padicExpUnit : pℤ_p →* (1+pℤ_p)` / the `exp ≅ log` `MulEquiv` | (a) composes with all of `PadicInt`'s `‖·‖≤1 ↔ mem 𝒪` API and `NormedSpace.exp`'s ecosystem; (b) gives the principal-units iso usable across cyclotomic / Iwasawa-theory developments |
| 5 | vector-space/field-specific → weaken typeclasses? | partially | (same as #1: the `ℚ_p`-fixing is removable for the integrality content) | scalar-restriction lemmas, full `NormedSpace.exp` API |
| 6 | 1-categorical → higher-categorical? | no | — | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → general algebraic structure? | no | the `p`/`ℤ_p` here are intrinsic to the object | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes.**
- Proposed mathlib-idiomatic restatement(s):
  ```lean
  -- (a) the integrality LEMMA the literature actually cares about, general L, no junk-total def:
  theorem norm_padicExp_le_one {L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L]
      [IsUltrametricDist L] [CompleteSpace L] {x : L} (hx : ‖x‖ ≤ (p : ℝ)⁻¹) :
      ‖padicExp p x‖ ≤ 1 := …   -- exactly the `hle` already proved inside pZpExp_coe, generalised
  -- (b) OR the bundled principal-units map / iso (specialised to ℚ_p):
  noncomputable def padicExpPrincipal (hp2 : p ≠ 2) :
      Ideal.span {(p : ℤ_[p])} →+ (… 1 + pℤ_p, ·*· …) := …
  ```
- Cost: MODERATE (lemma (a) is essentially free — its proof is already inside `pZpExp_coe`).
- Mathlib downstream this enables: lemma (a) is the reusable atom (exp-integrality on the ball) that
  composes with `PadicInt`'s `norm_le_one ↔ ∈ 𝒪` API and `NormedSpace.exp`; the bundled map (b) is
  the principal-units iso used throughout cyclotomic-field / Iwasawa-theory work.
- Real mathematical improvement (not just "looks cooler"): the **junk-total `dif`-on-norm encoding
  with junk value `1` is a formalization device with no literature counterpart**; the integrality
  *lemma* (a) is the actual theorem mathematicians state and reuse, and it composes far more widely
  than a `ℤ_p`-fixed restriction-plus-defining-equation pair.

Because Phase 4b is STRICTLY NARROWER **and** Phase 4c finds a real modern-idiom reformulation, the
naive reading points at `YES-but-generalise-first`. **But** the "generalise" target is not a
mechanical weakening of *this* statement — it is a *change of object* (drop the junk-total def;
ship an integrality lemma about `NormedSpace.exp`, or a bundled map). Whether mathlib wants the
`ℤ_p`-valued restriction *at all*, and in which of the two forms, is a library-policy / taste call.
That is precisely the BORDERLINE trigger (Phase 7).

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`** (not `def`/`class`/`instance`). No definitional equalities
or typeclass-search paths are introduced by `pZpExp_coe` itself. (The diamond/defeq surface lives on
the *parent def* `pZpExp`, which is out of scope for this lemma's report and has no report yet.)

---

### Mathlib search-status: `PadicLFunctions.pZpExp_coe`

[A] Lean-Finder       n/a — MCP tool not available in this environment.
[B] Loogle            n/a — MCP tool not available in this environment.
[C] LeanSearch        n/a — MCP tool not available in this environment.
[D] Grep mathlib src  decisive — `grep -rinE` over `.lake/packages/mathlib/Mathlib`:
      • `exp.*PadicInt | PadicInt.*exp` → **no p-adic exp on `PadicInt`** (only a `MahlerBasis.lean` docstring mentioning `Δ`).
      • `NumberTheory/Padics/` `\bexp\b|\blog\b` → only `WithZero.exp`/`log` (the **valuation monoid** maps, unrelated); **no `p`-adic exponential or logarithm exists in mathlib at all**.
      • `if ‖…‖ ≤ 1 then ⟨…⟩` (the junk-total integral-restriction pattern) → **no hits**.
      • `exp_coe | log_coe | exp.*: ℤ_[` (a coe-of-restricted-exp defining equation) → **no hits**.
      • `norm_exp | ‖…exp…‖ | isometry.*exp` → only `Real`/`Complex`/CStar (`norm_exp_sub_one_sub_id_le` is `Real`/`Complex`); **nothing nonarchimedean**, in particular no `‖exp x‖ ≤ 1` integrality lemma.
[E] Name pattern      grep for `padicExp`, `pZpExp`, `expPadic`, integral-exp names across mathlib → **no hits**; the name and the object are project-local. (Sibling fact: `padicExp` itself = `NormedSpace.exp` specialised — but the **integral `ℤ_p`-valued** form `pZpExp` and its `_coe` equation are absent.)

Searched for both:
  - the user's current form (`(pZpExp x : ℚ_p) = exp x`, i.e. the `dif`-true-branch defining equation), and
  - the literature-standard form (the integrality lemma `‖exp x‖ ≤ 1` / `exp x ∈ 1+𝔪`, and the bundled iso `exp: pℤ_p ≅ 1+pℤ_p`).

Concluded: **not in mathlib (grep [D] + name-pattern [E] exhausted, for both the user's form and the
literature-standard integrality lemma / bundled iso).** Mathlib has neither the junk-total `pZpExp`,
nor an integral exp on `PadicInt`, nor any `‖exp x‖ ≤ 1` nonarchimedean integrality result, nor the
`pℤ_p ≅ 1+pℤ_p` exp/log isomorphism. (The MCP search channels A/C were unavailable; the grep methods
are conclusive for an *absence* result — a present decl would have shown in the source grep.)

---

### Call sites — `PadicLFunctions.pZpExp_coe`

Internal use count (within the project, **not** counting the declaring file): **3** (all in `ResidueZeta.lean`).
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`).
Within-declaring-file uses (`PadicExp.lean`, excluding the def line): **4** (lines 1066, 1120, 1125, 1156).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ResidueZeta.lean:112 | `pZpExp_coe p hp2 htℓmem,` (inside a `rw […]`) |
| ResidueZeta.lean:256 | `pZpExp_coe p hp2 hmem]` (closing a `rw […]`) |
| ResidueZeta.lean:1729 | `rw [pZpExp_coe p hp2 (Ideal.zero_mem _), PadicInt.coe_zero, padicExp_zero, PadicInt.coe_one]` |
| PadicExp.lean:1066 (in-file) | `… pZpExp_coe p hp2 hx,` — used to prove `pZpExp_sub_one_mem` |
| PadicExp.lean:1120 (in-file) | `fun t => pZpExp_coe p hp2 (hargmem t)` — inside `padicExp_smul_padicLog_eq_onePAdicPow` |
| PadicExp.lean:1125 (in-file) | `rw [zero_mul, …, pZpExp_coe p hp2 (Ideal.zero_mem _), …]` |
| PadicExp.lean:1156 (in-file) | `rw [one_mul, hℓ, pZpExp_coe p hp2 hℓmem, pZpLog_coe p hp2 hx]` |

Inline-derivation grep: the `(pZpExp x : ℚ_p) = exp x` equation is **not** re-derived inline
anywhere — every consumer routes through `pZpExp_coe`. It is the single defining equation that makes
`pZpExp` usable (you cannot work with the junk-total def without it).

Call-sites signal: `K = 3` external + 4 internal ⇒ **real, load-bearing API** *for the project's own
`pZpExp` ecosystem*. Per the skill's table this leans toward a YES bucket **were the object itself
mathlib-bound** — but the object is the project-local junk-total `pZpExp`, whose mathlib form is the
open question. So the call sites confirm the lemma is *not* dead code / a bypassed wrapper; they do
**not** by themselves resolve whether the underlying *construction* belongs in mathlib.

### Composition check (Phase 6)

Can `pZpExp_coe` be derived from mathlib in ≤3 chained calls? — **No.**

Attempt 1 (treat it as a `dif_pos` after a one-line side condition):
```lean
-- rw [pZpExp, dif_pos ?hle]   -- but ?hle : ‖padicExp p x‖ ≤ 1 is itself the theorem's content
```
  - Mathlib decls used: none directly — `pZpExp` is project-local, and the side condition `‖exp x‖ ≤ 1` is the substance.
  - Result: **fails as a composition** — the `dif_pos` step is one line, but discharging `‖exp x‖ ≤ 1` requires the project's `norm_padicExp_sub_one` (= the nonarchimedean isometry, itself a mathlib gap) + `coe_norm_le_inv_of_mem_span` + `IsUltrametricDist.norm_add_le_max`. That is a genuine ~6-line proof through project-specific lemmas, not a 1–3 mathlib-call chain.
  - Notes: even the *atomic* fact `‖exp x‖ ≤ 1` is **not** in mathlib (Phase 5 [D]); there is no mathlib building block to compose.

Attempt 2 (via mathlib `NormedSpace.exp` integrality): no such lemma exists (`norm_exp_*` is
`Real`/`Complex` only). Fails.

Conclusion: **NOT-COMPOSABLE.** The lemma depends on a nonarchimedean integrality bound that mathlib
does not provide, glued to a project-local junk-total def. This rules out `NO-composable-from-mathlib`.

---

## Verdict: `PadicLFunctions.pZpExp_coe`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the underlying fact — **exp integral on `pℤ_p` for odd `p`; the iso
  `exp: pℤ_p ≅ 1+pℤ_p`** — is classical and unanimous (Wikipedia, PlanetMath, Vogan/MIT, Thorne,
  K. Conrad, Cassels §12, arXiv 1408.0900/2602.16433). The literature's form is a **bundled map /
  integrality lemma**, *not* a junk-total `dif`-branch, and it lives most naturally over a general
  nonarchimedean local field, not `ℚ_p`-fixed.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — `ℚ_p`-fixed (the theorem
  `omit`s the file's general-`L` instances) and packaged as a junk-total `ℤ_p`-restriction. Phase 4c:
  a real modern-idiom reformulation exists (integrality lemma about `NormedSpace.exp`, general `L`;
  or a bundled `pℤ_p ≅ 1+pℤ_p`).
- Mathlib search (Phase 5): **not in mathlib** under either the user's form or the literature integrality
  lemma / bundled iso — mathlib has *no* `p`-adic exp/log at all, and *no* nonarchimedean `‖exp x‖ ≤ 1`.
- Composition check (Phase 6): **NOT-COMPOSABLE** (the side condition `‖exp x‖ ≤ 1` is itself a mathlib
  gap; the proof routes through project-specific isometry lemmas).

**Rationale.**
`pZpExp_coe` is not a self-standing theorem one would PR in isolation: it is the **defining/branch-selection
equation of the project-local junk-total construction `pZpExp`** (an everywhere-defined `ℤ_p`-valued exp
with junk value `1`). Its mathlib-worthiness is therefore *derivative* of `pZpExp`'s — and `pZpExp` has
no `/mathlibable` report yet, so the def-first inheritance rule cannot resolve it here. The evidence does
establish two firm negatives: this is **not** `NO-mathlib-has-it` (mathlib has neither the object nor any
equivalent integral exp / `‖exp x‖ ≤ 1` lemma — Phase 5 grep is conclusive) and **not**
`NO-composable-from-mathlib` (the proof depends on the nonarchimedean isometry `‖exp x − 1‖ = ‖x‖`, itself
absent from mathlib — Phase 6). The *content* is a genuine, classical mathlib gap worth upstreaming.

What blocks a clean YES is a **form/policy judgment the skill cannot ground in the evidence**: the
literature object is a **bundled map / iso** `exp: pℤ_p ≅ 1+pℤ_p` (or simply the integrality *lemma*
`‖exp x‖ ≤ 1` about the *general* `NormedSpace.exp`), whereas `pZpExp_coe` is the glue equation for a
**junk-total `dif`-on-norm restriction that has no literature counterpart** and is **fixed to `ℚ_p`** even
though every primitive it uses (`padicExp`, `norm_padicExp_sub_one`, `InExpBall`) is already `L`-general.
Per the verdict reference, when Phase 4 is STRICTLY NARROWER *and* Phase 4c offers a real modern-idiom
reformulation, the candidate is `YES-but-generalise-first` — **but only if the generalisation is a
restatement of the same object.** Here it is a *change of object* (drop the junk-total def; ship an
integrality lemma or a bundled map), and whether mathlib wants the `ℤ_p`-valued restriction at all, in
which form, and at which generality is a library-taste call. That is the textbook BORDERLINE trigger
(cf. case 5 in `mathlibable-verdicts.md`: real content, project-specific bookkeeping form, form decision
left to the human). Note the strongest concrete upstreaming target the search surfaced is **not**
`pZpExp_coe` itself but the **integrality lemma `‖padicExp p x‖ ≤ 1` for `‖x‖ ≤ p⁻¹`, stated over general
`L` about `NormedSpace.exp`** — that atom is already proved verbatim inside `pZpExp_coe`'s body (`hle`),
is maximally general, composes widely, and would be a clean `YES`; `pZpExp_coe` is then a 1-line corollary
of it plus `dif_pos`.

**Numbered questions (≤5):**

1. **Should mathlib carry the `ℤ_p`-valued junk-total integral exponential `pZpExp` at all**, or only
   the *integrality lemma* `‖padicExp x‖ ≤ 1` (general `L`) about `NormedSpace.exp`, deriving any
   `ℤ_p`-restriction at the call site? (If "only the lemma", `pZpExp_coe` becomes a project-internal
   corollary — *not* a mathlib target — and the lemma to upstream is `norm_padicExp_le_one`.)
2. If mathlib *does* want the restriction, should it be the **bundled map / iso** `exp: pℤ_p ≅ 1+pℤ_p`
   (a `MulEquiv`/`MonoidHom`, the literature form) rather than a junk-total `dif`-on-norm `def` with
   junk value `1`? (A bundled map composes with the principal-units API; a junk-total def needs a
   defining equation like `pZpExp_coe` precisely *because* it is junk-total.)
3. Should the contribution be **`ℚ_p`-specific or general nonarchimedean local field**? The content
   holds for any complete nonarchimedean extension with `e < p−1`, and the project's primitives are
   already `L`-general — `pZpExp_coe` is the one place that re-narrows to `ℚ_p`. Mathlib's "most general
   form" rule pushes toward the general-`L` integrality lemma.
4. Is `pZpExp` (hence `pZpExp_coe`) intended as **public API for downstream developments** (cyclotomic
   fields, Iwasawa theory, `onePAdicPow`), or is it **internal scaffolding** for *this* project's RJW
   Lem 5.14 / `padicExp_smul_padicLog_eq_onePAdicPow`? (Its only external consumer is `ResidueZeta.lean`,
   the project's own residue-zeta computation — suggesting internal scaffolding, which would argue for
   keeping it project-local and upstreaming only the general integrality lemma.)

**Next action:** user answers questions 1–4; then re-run `/mathlibable PadicLFunctions.pZpExp_coe`
(and, recommended, first run `/mathlibable PadicLFunctions.pZpExp` on the parent def so the
def-first inheritance can settle the form). Likely outcomes:
  - Q1 "only the lemma" / Q4 "internal scaffolding" → `pZpExp_coe` itself: **drop from mathlib
    consideration** (project-internal corollary); instead extract and upstream
    `norm_padicExp_le_one` (general `L`) — a clean **`YES-add-as-is`** about `NormedSpace.exp`,
    targeting `Mathlib/Analysis/Normed/Algebra/Exponential.lean` (or a new nonarchimedean file).
  - Q2 "bundled map" + Q3 "general field" → re-run targeting the bundled `exp: 𝔪 ≅ 1+𝔪`; verdict
    likely `YES-but-generalise-first` with the bundled-map restatement, `pZpExp_coe` subsumed as the
    map's value-equation.

---

## Next step

User answers the four numbered questions above (start with Q1 + Q4 — they decide whether `pZpExp_coe`
is a mathlib target at all). Recommended: first run `/mathlibable PadicLFunctions.pZpExp` on the parent
def so this lemma can inherit the def's settled form. Regardless of the answers, the search surfaced one
unambiguous, maximally-general upstreaming target already proved inside this lemma's body — the
integrality bound `‖padicExp p x‖ ≤ 1` for `‖x‖ ≤ p⁻¹` over general `L` — which should be extracted as
`norm_padicExp_le_one` and is a clean `YES-add-as-is` candidate about `NormedSpace.exp` (mathlib has no
nonarchimedean exp-integrality lemma).
