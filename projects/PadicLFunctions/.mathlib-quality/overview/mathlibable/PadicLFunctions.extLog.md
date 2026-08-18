# `/mathlibable` report — `PadicLFunctions.extLog`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

**Final verdict: `YES-but-generalise-first`.** `extLog` is the *Iwasawa logarithm
extended to the rational-valuation domain* via the branch choice `log_p(p) = 0`
— a canonical, literature-standard object (Wikipedia, MIT 18.785, Iwasawa, Washington
§5.1) that mathlib lacks entirely (mathlib has **no** nonarchimedean/analytic logarithm
of any kind). It is genuinely missing and genuinely used (50 call lines across two files),
so it is a real contribution — **but** the Lean form is strictly narrower than the literature
standard on the same axes as its base `padicLog`: a redundant `[NormedAlgebra ℚ_[p] L]`
assumption and a domain keyed to the small exp ball rather than the standard log ball. Per the
verdict gate, a known weakening forces `YES-but-generalise-first` over `YES-add-as-is`.

---

### Baseline (Phase 0)

- lake build:               build **not re-run** (stale/slow per task BUILD NOTE); reasoned from source — `ExtLog.lean` is committed-clean, contains **0 `sorry`/`admit`**, and the entire surrounding API (`extLog_witness_smul_eq`, `extLog_eq_of_witness`, `extLog_eq_padicLog`, `extLog_mul`, plus the 50 call sites in `ResidueZeta.lean`/`ValuesAtOne.lean`) elaborates against the def as written.
- decl `PadicLFunctions.extLog`:   ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:286`
- kind:                      `def` (`noncomputable def`, under `open Classical in`; **not** `@[reducible]`, sealed)
- has sorry:                 no
- module docstring summary:  "The extended (Iwasawa-branch) p-adic logarithm (RJW §6, decomposition W6a)" — extends `padicLog` to rational-valuation elements `x` with `x^m = p^k·y`, `y` in the exp ball, by `extLog x := m⁻¹·padicLog y` (junk `0` off-domain; Iwasawa's branch `log_p(p) = 0`); cross-references Washington, *Cyclotomic Fields*, §5.1.

---

### Statement (Phase 1)

`PadicLFunctions.extLog` is **a definition of the Iwasawa-branch p-adic logarithm,
extended off its convergence ball to the rational-valuation domain**:

> Let `L` be a complete ultrametric normed field that is a normed `ℚ_[p]`-algebra
> (e.g. `ℚ_[p]`, finite extensions, `ℂ_[p]`). For `x ∈ L` lying in the
> *rational-valuation domain* — i.e. there exist `m > 0`, `k ∈ ℤ`, `y ∈ L` with
> `x^m = p^k · y` and `y` in the (translated) exponential ball `‖y−1‖^{p−1} < p⁻¹` —
> set `extLog x := m⁻¹ · log_p y`, where `log_p = padicLog` is the convergent
> logarithm series and `m⁻¹` is taken in `ℚ_[p]` and scalar-multiplied in. The
> definition is **junk-total**: it returns `0` off the domain, and the value is
> independent of the chosen witness (`extLog_witness_smul_eq`). This is exactly
> Iwasawa's extension of `log_p` to all of `K^×` under the noncanonical branch
> choice `log_p(p) = 0`: write `x = p^r·ζ·z` (equivalently `x^m = p^k·y`) and define
> `extLog(x) = log_p(z) = m⁻¹ log_p(y)`.

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [Fact p.Prime]` — the prime; the rational scalar `m⁻¹` is taken in `ℚ_[p]`.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a complete ultrametric (nonarchimedean) normed field that is a normed `ℚ_[p]`-algebra.

Hypotheses (Lean side): none on the def itself (junk-total via the `if h : ExtLogDomain p x` dite). The witness data `(m, k, y)` is selected by `Classical.choice` from the domain proof; meaning is carried by `ExtLogDomain p x`.

Conclusion (math): the extended (Iwasawa-branch) p-adic logarithm of `x`.
Conclusion (Lean): `L` (kind is `def`).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: introduces a **named mathematical object** (the *extended* / *Iwasawa-branch*
p-adic logarithm, `log_p` on all of `K^×`), is the headline construction of the file
(module docstring: "The extended (Iwasawa-branch) p-adic logarithm"; decomposition R6
cluster W6a), and is a named classical analytic object ("Iwasawa logarithm", the
`log_p(p)=0` extension) essentially guaranteed to be in the literature.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is narrative framing only.)

### One-line check (Phase 2b)

Body line count: **4 substantive lines** — a `dite` on `ExtLogDomain p x` whose
`then` branch selects the witness data via `Classical.choice` (`h.choose`,
`h.choose_spec.choose_spec.choose`) and forms `(h.choose : ℚ_[p])⁻¹ • padicLog p (…)`,
with `else 0`.
One-liner verdict: **MULTI-LINE** — this is *not* a one-line definition. The body
performs genuine choice-extraction over the existential `ExtLogDomain` and a
junk-total branch; it is materially more than a single substantive expression.

The Phase-2b one-liner gate does not apply. (For completeness: the def is sealed,
non-`@[reducible]`, and `padicLog`'s own Phase-2b exemptions — sealed `tsum`, real
API surface — apply a fortiori here.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `Iwasawa p-adic logarithm extended to all of C_p^× log_p(p)=0 branch definition` | **yes** | "Following Iwasawa, log is extended… by arbitrarily defining `log p = 0`, and for `x ∈ m`, `n ∈ ℤ`, `log(p^n(1+x)) := log(1+x)`… For `x ∈ C_p^×` with `x^n ∈ G`, define `log(x) := (1/n) log(x^n)`." | This is the **verbatim** construction the Lean def implements (`extLog x = m⁻¹·padicLog y`, `x^m = p^k·y`). Surfaced MIT 18.785 PSet10; arXiv `math/0512015` "A Note on a result of Iwasawa"; arXiv:1907.06437; en-academic "p-adic exponential function". Kernel = `p^a·ζ`, `a ∈ ℚ`, `ζ` a root of unity. |
| 2 | WebSearch (general form) | `p-adic logarithm unique extension homomorphism K^× log_p(p)=0 Iwasawa branch principal units` | **yes** | "logp(1+x) converges for all `x ∈ m_K`… `Iwasawa's p-adic log can be normalized so that log(p)=0`"; the extension is a continuous **group homomorphism** on principal units / `K^×` | ResearchGate "On the image of p-adic logarithm on principal units"; arXiv:1904.09850, arXiv:1907.06437, arXiv:2601.18187. The extended log is standard across Iwasawa theory; `log_p : 1+m_K^r → m_K^r` iso for `r > e/(p−1)`. |
| 3 | WebSearch (named-after / aliases) | `Washington Introduction Cyclotomic Fields p-adic logarithm extension log_p p = 0 chapter 5` | **yes (name confirmed)** | confirms the object is the "Iwasawa logarithm", `log_p(p)=0` choice; covered in Washington *Cyclotomic Fields* (Iwasawa `Z_p`-extensions chapters) and Coates–Sujatha | Washington GTM 83 (the file's cited source §5.1); Coates–Sujatha *Cyclotomic Fields and Zeta Values*; Ferrero–Washington. The book content itself is paywalled but the name + branch choice are corroborated. |
| 4 | ChatGPT MCP | (MCP unavailable in this environment) | n/a | — | No `.mcp.json` / ChatGPT MCP configured in this sandbox (consistent with the sibling `padicLog`/`padicExp` reports). **Compensated** by a primary-source `WebFetch` of Wikipedia (row 11) giving the verbatim extension formula, plus the in-repo Washington-cited docstring. The standard-form + generality + historical-evolution question is answered by rows 1–3, 9, 11. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/`; `ls refs/PadicLFunctions/` | n/a | (no references dir; no `refs/` symlink) | Both absent — recorded n/a per protocol. The module docstring itself cites RJW §6 / Thm 6.1(ii) and Washington §5.1. Sibling reports under `.mathlib-quality/overview/mathlibable/` (esp. `PadicLFunctions.padicLog.md`) were consulted as in-repo prior art. |
| 6 | nLab | `nLab p-adic logarithm exponential nonarchimedean` | partial | nLab "p-adic number": "the p-adic exponential… has an inverse function, named the p-adic logarithm"; series converges `\|x−1\|_p<1` | nLab has no *dedicated* "Iwasawa logarithm / extended log" page; the relevant content is the p-adic-number entry + the analysis references (rows 1–2, 9, 11). |
| 7 | nCatLab (categorical) | (same as nLab) | n/a | — | Not a categorical concept; the extended log is an analytic function on a normed field — no universal-property formulation to look up. |
| 8 | Stacks Project (alg geom) | — | n/a | — | Not an algebraic-geometry / scheme-theoretic concept; the (extended) p-adic log is analytic number theory, outside Stacks' scope. |
| 9 | MathOverflow / Math.StackExchange | (covered by the WebSearch sweep; rows 1–2 surfaced MO/MIT/lecture-note treatments) | yes | consensus: extend by `log p = 0`, `log(p^r ζ z) = log z`, get a homomorphism `C_p^× → C_p`; kernel `p^ℚ·μ_∞` | No disagreement on the standard extended form across the surfaced notes; the branch choice `log_p(p)=0` is universally flagged as the (noncanonical but standard) Iwasawa normalisation. |
| 10 | recent arXiv (≤5 yr) | (rows 1–2) | yes | arXiv:2601.18187 (2026) "On the Image of the p-adic Logarithm on Annuli of Principal Units"; arXiv:1907.06437 (2023); Ankeny–Artin–Chowla papers (2024) | Active modern use of exactly this `log_p` (with the `log p = 0` normalisation) — the extended Iwasawa logarithm is current, not historical-only. |
| 11 | Wikipedia primary fetch | `WebFetch en.wikipedia.org/wiki/P-adic_exponential_function` | **yes** | verbatim: "`w = p^r·ζ·z` with `r` a rational number, `ζ` a root of unity, and `\|z − 1\|_p < 1`", set `log_p(w) = log_p(z)`; under "`log_p(p) = 0`" this is a **group homomorphism** `C_p^× → C_p`; kernel = `{p^r·ζ}`; "different choices [of factoring `p^r`] differ only by multiplication by a root of unity, absorbed into `ζ`." | This is precisely `extLog`: the Lean witness `x^m = p^k·y` is the rational-valuation rewriting of `x = p^r·ζ·z` (clearing the rational `r` by the `m`-th power), and `extLog x = m⁻¹ log_p y = log_p z`. Stated over `C_p`, **not** restricted to `ℚ_p`. |

The protocol passed: WebSearch ran 3 distinct generality levels (rows 1–3) plus
arXiv (10) and a primary fetch (11); local refs checked (absent, n/a); nLab checked
(6, partial); Stacks/nCatLab/MathOverflow each adjudicated (8/7/9). ChatGPT MCP is
genuinely unavailable in this sandbox — recorded n/a with the compensating
primary-source Wikipedia fetch (row 11) carrying the verbatim standard form.

### Literature summary (Phase 3)

Concept identified as: the **Iwasawa logarithm `log_p` extended to all of `K^×`
(the rational-valuation domain)** under the branch choice `log_p(p) = 0`.
Sources agree on the standard form: **yes** — extend the convergent `log_p` (on
`‖x−1‖<1`) to `K^×` by writing `w = p^r·ζ·z` (`r ∈ ℚ`, `ζ` a root of unity,
`‖z−1‖<1`) and setting `log_p(w) := log_p(z)`, with the normalisation `log_p(p) = 0`
(and `log_p(ζ) = 0`). Operationally, for `x` with `x^m = p^k·y` (`y` near 1),
`log_p(x) = m⁻¹ log_p(y)` — **exactly** the Lean `extLog`. Wikipedia, MIT 18.785,
arXiv `math/0512015`, Washington/Coates–Sujatha all agree.
Most general standard form: the function on all of `K^×` for **any complete
nonarchimedean field of characteristic 0** containing `ℚ_p` (`ℚ_p`, finite/infinite
extensions, `ℂ_p`); it is a **group homomorphism** `K^× → K` (additivity, the Lean
`extLog_mul`), with kernel `p^ℚ·μ_∞`.
Generality dimensions where the literature varies:
  - **Base ring**: `ℚ_p ⊂` finite extensions `⊂ ℂ_p ⊂` arbitrary complete
    nonarchimedean char-0 field. The literature standard is `ℂ_p` / "complete
    nonarchimedean field"; it does **not** require a `ℚ_[p]`-algebra structure —
    only `CharZero` (so `m⁻¹` and the coefficients `1/n` in the underlying
    `padicLog` make sense). The Lean `[NormedAlgebra ℚ_[p] L]` is an artefact of the
    project living over `ℚ_[p]`.
  - **The "near-1" region used by the witness**: the literature uses the *full log
    convergence ball* `‖z−1‖ < 1`; the Lean `ExtLogDomain` keys the witness `y` to
    the strictly-smaller *exponential ball* `‖y−1‖^{p−1} < p⁻¹` (= `InExpBall`).
    Both define the same total function on its natural domain (the project proves
    `extLog = padicLog` on the exp ball, and `ValuesAtOne.lean` extends agreement to
    the full `‖x−1‖<1` ball), but the *standard* domain hypothesis is the larger ball.
Disagreement with the literature: the Lean form is **correct** but **narrower than
standard on the same two axes as `padicLog`** (redundant `ℚ_[p]`-algebra assumption;
witness domain on the exp ball rather than the full log ball) — see Phase 4.

---

### Generality analysis — `PadicLFunctions.extLog`

Literature-standard form (from Phase 3): the Iwasawa `log_p` extended to `K^×` on a
**complete nonarchimedean field `K` of characteristic 0** (or `⊇ ℚ_p`), via
`x = p^r·ζ·z` (`‖z−1‖<1`) ↦ `log_p(z)`, normalisation `log_p(p)=0`, a group homomorphism.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] L]` + the scalar `(m : ℚ_[p])⁻¹` (and, through `padicLog`, the `1/(n+1) ∈ ℚ_[p]`) | `L` is a normed `ℚ_[p]`-algebra; `m⁻¹` lives in `ℚ_[p]`, scalar-multiplied in | `K` is a `CharZero` complete nonarchimedean field; `m⁻¹ ∈ K` directly | **yes** | The extended log never asks the base field to be a `ℚ_[p]`-algebra — only that `m⁻¹` (and `1/n` inside `log_p`) make sense (`CharZero`/`Algebra ℚ`). The literature states it over `ℂ_p` and arbitrary complete nonarchimedean char-0 fields. The `• ` through `ℚ_[p]` is an inherited artefact (identical to `padicLog` row 1 of its own Phase 4). |
| 2 | `[IsUltrametricDist L]` + `[CompleteSpace L]` | complete ultrametric normed field | complete nonarchimedean field | NO | Genuinely needed: the underlying `padicLog`'s summability is the nonarchimedean `cofinite → 0` criterion, and the well-definedness proof (`extLog_witness_smul_eq`) uses ultrametric norm facts (`norm_eq_one_of_inExpBall_sub_one`, `zpow_right_injective₀` on `‖p‖`). This is the right hypothesis. |
| 3 | witness domain `ExtLogDomain p x` (`∃ m k y, … ∧ InExpBall p (y−1)`, i.e. `‖y−1‖^{p−1} < p⁻¹`) | the *exponential* ball for the near-1 factor `y` | the *full log* ball `‖z−1‖<1` | **yes (mild)** | The standard extension factors `x = p^r·ζ·z` with `z` in the **full** log convergence ball `‖z−1‖<1`, which is strictly larger than the exp ball. The def evaluates the same on its natural domain, and the project itself already proves `extLog = padicLog` on the full `‖x−1‖<1` ball (`ValuesAtOne.lean` T618). The narrowness is in the *domain predicate `ExtLogDomain`* (and hence which `x` are "in domain"), not the formula — but it is the same exp-ball-vs-log-ball gap flagged for `padicLog`. |
| 4 | the **shape** of the extension (witness `x^m = p^k·y` vs. the homomorphism characterisation) | concrete witness/`Classical.choice` construction | the same concrete construction *plus* the homomorphism characterisation `log_p : K^× → K`, `log_p(p)=0`, kernel `p^ℚ μ_∞` | partial | The construction matches the literature exactly. What the literature additionally packages — and what a mathlib version would want — is the **bundled homomorphism** view (`extLog` as a monoid hom `Lˣ → L` on the domain, with `extLog_mul` as `map_mul`). This is a modern-idiom point, not a base-generality weakening; see Phase 4c row 3. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: K = 2 genuine base-generality weakenings
(rows 1, 3; row 2 is already optimal, row 4 is a Phase-4c idiom point).

Proposed restatement (the literature-standard target):

```lean
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- The domain of the extended (Iwasawa-branch) logarithm: `x^m = p^k·y` with
`y` in the FULL log convergence ball `‖y−1‖ < 1`. -/
def ExtLogDomain (p : ℕ) (x : K) : Prop :=
  ∃ (m : ℕ) (k : ℤ) (y : K), 0 < m ∧ x ^ m = (p : K) ^ k * y ∧ ‖y - 1‖ < 1

open Classical in
/-- The Iwasawa-branch p-adic logarithm extended to the rational-valuation domain,
junk-total (`log_p p = 0`): `extLog x = m⁻¹ • log_p y` for a witness `x^m = p^k·y`. -/
noncomputable def extLog (p : ℕ) (x : K) : K :=
  if h : ExtLogDomain p x then (h.choose : K)⁻¹ • padicLog p h.choose_spec.choose_spec.choose
  else 0
```

i.e. drop `[NormedAlgebra ℚ_[p] L]` for `[CharZero K]`, take `m⁻¹ ∈ K`, and (optionally)
widen `ExtLogDomain`'s near-1 factor to the full log ball `‖y−1‖<1`. This sits **directly on top
of** the generalised `padicLog` already proposed in the sibling `padicLog.md` report — `extLog`
cannot be generalised independently of `padicLog`, since it is `m⁻¹ • padicLog y`.

Cost of restatement: **MODERATE** — the def is a near-mechanical rewrite (`• ` over `ℚ_[p]` → `• ` in `K`; drop the algebra assumption), but it is *blocked on* first generalising `padicLog` (cost MODERATE there), and re-proving `extLog_witness_smul_eq`/`extLog_mul` on the wider domain is real (the current proofs key off `InExpBall`/exp-ball facts). EXPENSIVE/MODERATE does **not** downgrade the verdict — it informs sequencing.

If STRICTLY NARROWER → Phase 7 considers **YES-but-generalise-first** prominently.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let `L` be a foo" preamble → typeclass? | partial | already typeclass-based; the only change is `NormedAlgebra ℚ_[p] L` → `CharZero K` (row 1 of 4a) | composes with all of mathlib's `CharZero` nonarchimedean-field API, not only `ℚ_[p]`-algebras |
| 2 | sequences/metric → filters/topological? | no | the underlying `padicLog` is already `tsum`/filter-based; `ExtLogDomain` is an existential over algebra, not a sequence/metric notion | n/a |
| 3 | construct object → universal-property / bundled-morphism class? | **yes (mild)** | the literature packages the extended log as a **group homomorphism** `log_p : K^× → K` (`log_p(p)=0`, kernel `p^ℚ·μ_∞`); a mathlib version would bundle it as a `MonoidHom` on the domain subgroup (with `extLog_mul` = `map_mul`, `extLog 1 = 0` = `map_one`) | the `MonoidHom`/additive-character API — `MonoidHom.comp`, kernel/range lemmas, the whole bundled-morphism ecosystem — and the cleaner statement of `extLog_mul`/`extLog_eq_padicLog` as structure-map lemmas |
| 4 | set-with-closure-pred → bundled substructure? | partial | `ExtLogDomain` is exactly "the subgroup `p^ℤ·(1+B)` of `Lˣ`" written as a `Prop`; mathlib idiom would make it a `Subgroup Lˣ` (it *is* closed under `*` — `extLog_mul` proves the domain is multiplicatively closed) | `Subgroup` lattice API; the extended log as a hom *out of* that subgroup |
| 5 | vector-space/field-specific → weaken to module/ring? | partial | same as row 1: weaken `ℚ_[p]`-algebra to `CharZero` field. (A Banach-algebra `log(1+·)` generalisation exists but is a *separate, larger* object, as noted for `padicLog`.) | uniform `log_p` over `ℚ_p`, finite extensions, `ℂ_p` |
| 6 | 1-categorical → higher-categorical? | no | not categorical | n/a |
| 7 | concrete index ℕ/ℤ/ℝ → general structure? | no | the witness exponents `m : ℕ`, `k : ℤ` are intrinsic (powers / valuations), already at the right index types | n/a |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — two real, same-direction improvements.
  - **Base-generality (primary, = Phase 4b):** the `CharZero` complete-nonarchimedean-field form, dropping the `ℚ_[p]`-algebra assumption (`m⁻¹ ∈ K`). This is the missing nonarchimedean analytic logarithm extended to `K^×`, the partner to a generalised `padicLog`.
  - **Bundled-morphism (secondary):** package the extended log as a `MonoidHom` from the domain subgroup `p^ℤ·(1+B) ≤ Lˣ` to `(L, +)`, with `extLog_mul` becoming `map_mul`. The literature's headline statement *is* "`log_p` is the unique continuous homomorphism `K^× → K` with `log_p(p)=0`"; the bundled form captures that.
  - Cost: CHEAP for the base-generality def rewrite (modulo first generalising `padicLog`); MODERATE for the `MonoidHom`-bundling (needs the domain-is-a-subgroup proof, which `extLog_mul` already half-supplies).
  - Mathlib downstream this enables: composes with mathlib's `CharZero`/nonarchimedean-field API and (if bundled) the entire `MonoidHom`/`Subgroup` ecosystem; subsumes `ℚ_p`, finite extensions, and `ℂ_p` in one definition; gives the canonical home for "the unique homomorphic extension of `log_p` with `log_p(p)=0`".
  - Real mathematical improvement (not just "looks cooler"): removes the gratuitous `ℚ_[p]`-algebra restriction so the *one* extended Iwasawa logarithm serves all complete nonarchimedean char-0 fields, and (optionally) states it as the homomorphism the literature actually characterises it by.

Phase 4c reinforces Phase 4b: the right mathlib target is the `CharZero`-field form
(ideally bundled as a `MonoidHom`), built atop the generalised `padicLog` — **not** the
`ℚ_[p]`-algebra form. Since Phase 4b already found the form STRICTLY NARROWER, the verdict is
`YES-but-generalise-first` regardless.

---

### Diamond / defeq risk — `PadicLFunctions.extLog`

(`def`, so Phase 4.5 runs. Probes reasoned from source — build not re-run per task note.)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | `extLog` returns a bare element of `L`; it anchors no instance and appears in no instance head. No typeclass-search path is steered by it. |
| 2 | Reducibility leak | **none** | Plain `noncomputable def`, **not** `@[reducible]`. The body is a `dite` over a `Classical.choice` extraction (non-trivial); sealing it is correct. Downstream unfolds via the API lemmas (`extLog_eq_of_witness`, `extLog_eq_padicLog`), not by `rfl`. |
| 3 | Non-canonical unfolding | **low** | The `if h : ExtLogDomain p x` is a `dite` on a `Classical`-decidable `Prop`; `simp`/`rfl` will not reduce it spontaneously (`ExtLogDomain` is an opaque existential). The only safe-value lemmas are the explicit equational API; no surprising reduction. The `Classical` decidability instance is local (`open Classical in`), the mathlib-standard way to write a junk-total `dite` — no instance leaks past the def. |
| 4 | Instance priority collision | **n/a** | Not an `instance`. |
| 5 | Universe-polymorphism issues | **none** | `L : Type*` and the result is `L`; no universe annotation forced; no polymorphic call-site breakage. |
| 6 | Coercion ambiguity | **none** | No `CoeFun`/`CoeSort`; `extLog` is an ordinary function `L → L`, not a bundled coercible type. (If the Phase-4c `MonoidHom`-bundling is adopted later, a `FunLike` coercion *would* be introduced — but that is the standard bundled-hom coercion, not a competing/ambiguous one.) |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW**
Top risks: none HIGH.
Recommended mitigations: none required. (A sealed, non-reducible junk-total `dite`
over a `Classical`-decidable existential is exactly the mathlib-safe pattern for an
extended/branch special function. The `open Classical in` scoping keeps the
decidability instance from leaking.)

---

### Mathlib search-status: `PadicLFunctions.extLog`

[A] Lean-Finder       — n/a: Lean-Finder MCP not available in this environment.
[B] Loogle            `(_ : ℚ_[_]) → ℚ_[_]` extended-log-shaped; `_⁻¹ • padicLog _` — n/a: `lean_loogle` MCP not available; substituted by exhaustive source grep (D) over the actual pinned mathlib.
[C] LeanSearch        "Iwasawa logarithm extended to whole field", "p-adic logarithm of element with rational valuation", "logarithm log_p(p)=0 branch" — n/a: `lean_leansearch` MCP not available; substituted by the literature channels (Phase 3) + source grep.
[D] Grep mathlib src  `p.?adic.*log`, `nonarchimedean.*log`, `ultrametric.*log`, `iwasawa.*log`, `extend.*log`, `branch.*log`, `valuation.*log`, `def [a-zA-Z]*[Ll]og`, every `def .*log`/`def .*Log` under `Analysis/`, `RingTheory/PowerSeries/Log.lean` — **executed in full** on `.lake/packages/mathlib/`.
[E] Name pattern      enumerated **every** `log` def in mathlib: `Real.log`, `Complex.log`, `ENNReal.log` (archimedean); `Nat.log`/`Int.log`/`Ordinal.log`/`Submonoid.log` (discrete/integer); `PowerSeries.log`/`logOf` (formal); `ContinuousFunctionalCalculus…log = cfc Real.log` (archimedean CFC); `VonMangoldt.log`, `posLog`, `negMulLog` (real). The p-adic-area "log" hits (`padicValNat_le_nat_log`, `Nat.log p n`) are the **integer** `Nat.log`, unrelated.

Searched for both:
  - the user's current form (extended Iwasawa log over an ultrametric `ℚ_[p]`-algebra, witness domain): **not in mathlib**.
  - the literature-standard form (extended Iwasawa log over a complete nonarchimedean char-0 field / `ℂ_p`, witness on the full log ball): **not in mathlib**.

Closest existing mathlib objects (all confirmed *not* the same):
  - `NormedSpace.exp` (`Mathlib/Analysis/Normed/Algebra/Exponential.lean`) — the analytic exponential, but radius `∞` (archimedean) and has **no companion `log`** at all, let alone an extended/branch one. Not relevant to the nonarchimedean log.
  - `PowerSeries.log` / `logOf` (`Mathlib/RingTheory/PowerSeries/Log.lean`) — the **formal** logarithm series; no convergence, no analytic evaluation, and certainly no extension off the unit ball. The repo's `padicLog` *evaluates* this; `extLog` then *extends the evaluated* function — both steps are missing from mathlib.
  - `Real.log`/`Complex.log`/`ContinuousFunctionalCalculus.log` — archimedean; the CFC `log` is `cfc Real.log` over a real/complex spectrum, unrelated to the p-adic regime.

Concluded: **not in mathlib** (all available methods exhausted: source grep run in full for both the user's form and the literature-standard form, and the *entire* mathlib `log`-def inventory enumerated; semantic MCP search tools genuinely unavailable and recorded n/a). Mathlib has **no nonarchimedean / p-adic analytic logarithm of any kind**, and a fortiori no *extended* (Iwasawa-branch, `log_p(p)=0`) logarithm. This is consistent with the sibling `padicLog.md` (`not in mathlib`) — and `extLog` is one construction *further* out (the off-ball extension), so it is doubly absent.

---

### Call sites — `PadicLFunctions.extLog`

Internal use count: **50 bare `extLog p` call lines** across **2 distinct files**
(within the `PadicLFunctions` project, excluding the declaring file `ExtLog.lean`).
External-to-file callers: **2 distinct files**.

| Caller file:line (representative) | Usage pattern (one-line excerpt) |
|-----------------------------------|-----------------------------------|
| `PadicLFunctions/ResidueZeta.lean:470` | `PowerSeries.C (-(extLog p ((a : K))))` — constant coefficient of the residue series |
| `PadicLFunctions/ResidueZeta.lean:1554` | `have hWitness : extLog p ((a : K)) = …` — Fermat-witness computation of `extLog` |
| `PadicLFunctions/ResidueZeta.lean:1625` | `extLog p ((a : K)) = algebraMap ℚ_[p] K (extLog p ((a : ℚ_[p])))` — base-change of `extLog` |
| `PadicLFunctions/ResidueZeta.lean:1739` | `extLog p ((m : ℚ_[p])) …` — `extLog ω = 0` for roots of unity (the `log_p(ζ)=0` fact) |
| `PadicLFunctions/ValuesAtOne.lean:48` | `if n = 0 then extLog p (u - 1) …` — coeff 0 of the log series is `extLog(u−1)` |
| `PadicLFunctions/ValuesAtOne.lean:1090` | `extLog p ((-1 : K)^m * x) = extLog p x` — `±1`-invariance (the `μ_∞` kernel) |
| `PadicLFunctions/ValuesAtOne.lean:1129` | `∑ i : Fin p, extLog p (ξ^i·ε^c − 1) = extLog p (ε^{pc} − 1)` — the `μ_p`-collapse |
| `PadicLFunctions/ValuesAtOne.lean:1225` | `∑ c, θ⁻¹(c)·extLog p (ε^{pc} − 1) = θ(p)·∑ c, θ⁻¹(c)·extLog p (ε^c − 1)` — the `c↦pc` clearing |

Inline-derivation grep (was `m⁻¹·padicLog(witness)` re-derived without calling `extLog`?):
  - **Within `PadicLFunctions`: none.** The single near-match (`ResidueZeta.lean:1555`,
    `(p−1)⁻¹ • padicLog p ((a:K)^(p−1))`) is the *witness* side of `extLog_eq_of_witness`
    — it is the canonical way to *compute* `extLog p (a:K)` (the surrounding `hWitness`
    binds it to `extLog`), i.e. it goes *through* the API, not around it.
  - **Cross-project:** no other `extLog`/extended-log definition exists in the repo
    (`grep extLog projects/ --exclude PadicLFunctions` → empty). The
    `BernoulliRegular.FLT37.PadicL.padicLog` duplicate flagged in `padicLog.md` is the
    *unextended* log (different object); it does **not** duplicate `extLog`.

Call-sites signal: **K = 50 ≫ 3, across 2 external files, with no inline
re-derivation → a real, load-bearing API; consumers depend on it → strong YES-* lean.**

---

### Composition check (Phase 6)

Can `PadicLFunctions.extLog` be derived from mathlib in ≤3 chained calls?

Attempt 1: `fun x => (witness‑m x)⁻¹ • PowerSeries.eval … (PowerSeries.log) (y−1)` — combine a witness extractor with a formal-log evaluation.
  - Mathlib decls used: `PowerSeries.log` (formal only).
  - Result: **fails** — there is (i) no mathlib analytic evaluation summing `PowerSeries.log` in a complete nonarchimedean field (already the missing content for `padicLog`), and (ii) no mathlib machinery to *extend* such a function off the unit ball via the `x^m = p^k·y` factoring. Not a composition.

Attempt 2: reuse some mathlib `log`/`exp` inverse on `K^×`.
  - Mathlib decls used: `NormedSpace.exp` / `Real.log` / `Complex.log` / `PowerSeries.logOf`.
  - Result: **fails** — `NormedSpace.exp` is archimedean and has no log; the real/complex/CFC logs are archimedean; the formal `PowerSeries` logs do not evaluate. None extends to `K^×` in the nonarchimedean regime.

Attempt 3: assemble `extLog` from the repo's own `padicLog` in ≤3 calls.
  - Result: **fails as a *mathlib* composition** — even granting `padicLog`, building `extLog` requires (a) the `Classical.choice` extraction of a witness `(m,k,y)` from `ExtLogDomain`, and (b) the *well-definedness theorem* `extLog_witness_smul_eq` (a ~20-line proof matching `p`-valuations across two witnesses) to know the value is witness-independent. That is genuine new mathematical content, not a 1–3 mathlib-call glue. (And `padicLog` itself is not in mathlib.)

Conclusion: **NOT-COMPOSABLE.** The off-ball *extension* of the p-adic logarithm — witness selection plus the well-definedness proof — is genuinely new content on top of an already-missing `padicLog`; it is not a short mathlib composition.

---

## Verdict: `PadicLFunctions.extLog`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the **Iwasawa logarithm extended to `K^×` (rational-valuation domain)** under the branch choice `log_p(p)=0`; standard construction `x = p^r·ζ·z ↦ log_p(z)`, operationally `log_p(x) = m⁻¹ log_p(y)` for `x^m = p^k·y` — a **verbatim** match to the Lean `extLog`. Canonical across Wikipedia, MIT 18.785, arXiv `math/0512015`/2601.18187, Washington/Coates–Sujatha. Stated over `ℂ_p` / complete nonarchimedean char-0 fields, **not** restricted to `ℚ_p`-algebras.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 2 base-generality weakenings (drop `NormedAlgebra ℚ_[p]` for `CharZero`, `m⁻¹ ∈ K`; widen the witness domain to the full log ball `‖y−1‖<1`), inherited from `padicLog`. Phase 4c agrees and adds an optional `MonoidHom`-bundling idiom.
- Mathlib search (Phase 5): **not in mathlib** under either form; the *entire* mathlib `log`-def inventory is archimedean / discrete / formal — there is **no** nonarchimedean analytic log, and a fortiori no extended Iwasawa log.
- Composition check (Phase 6): **NOT-COMPOSABLE** — witness selection + the well-definedness theorem on top of an already-missing `padicLog` is genuinely new content.

**Rationale (1–2 paragraphs):**

`extLog` is a genuinely missing, classical, heavily-used object: it is the **Iwasawa
logarithm extended to all of `K^×`** under the standard branch normalisation `log_p(p)=0`
— the unique continuous homomorphic extension of the convergent `log_p`, realised
exactly as the literature does it (`x = p^r·ζ·z ↦ log_p z`, i.e. `extLog x = m⁻¹ log_p y`
for `x^m = p^k·y`). Wikipedia, the MIT 18.785 problem set, arXiv `math/0512015`, and the
2026 annuli paper all give precisely this construction. Mathlib has **no nonarchimedean
logarithm of any kind** (only archimedean `Real`/`Complex`/CFC logs, discrete `Nat`/`Int`
logs, and the formal `PowerSeries.log`), so it has neither the convergent `log_p` nor its
off-ball extension. The project supplies the full ecosystem around `extLog` —
well-definedness (`extLog_witness_smul_eq`), agreement with `padicLog` on the ball
(`extLog_eq_padicLog`), additivity/homomorphism (`extLog_mul`), and the
roots-of-unity/`μ_p` kernel laws — with **50 call lines across `ResidueZeta.lean` and
`ValuesAtOne.lean`** and no inline re-derivation. That is a real API and a genuine
contribution, NOT a wrapper or a short composition (Phase 6 NOT-COMPOSABLE: the witness
selection plus the ~20-line well-definedness proof is real content, on top of an
already-missing `padicLog`).

The verdict is **not** `YES-add-as-is` because Phase 4b found the Lean form **strictly
narrower than the literature standard**, on the very same axes already flagged for its
base object `padicLog` (whose sibling verdict is likewise `YES-but-generalise-first`):
(1) it gratuitously assumes `[NormedAlgebra ℚ_[p] L]` and takes `m⁻¹` (and, through
`padicLog`, the `1/n`) in `ℚ_[p]`, whereas the extended Iwasawa log needs only a complete
nonarchimedean **char-0** field — the literature states it over `ℂ_p` and arbitrary such
fields, never restricting to `ℚ_p`-algebras; and (2) its witness domain `ExtLogDomain`
keys the near-1 factor `y` to the *exponential* ball `‖y−1‖^{p−1}<p⁻¹` rather than the
*full* log convergence ball `‖y−1‖<1` the standard factoring uses (and which the project
itself reaches in `ValuesAtOne.lean`). Crucially, `extLog = m⁻¹ • padicLog y` is *built
directly on* `padicLog`, so it **cannot be generalised independently** — it must ride on
the `padicLog` generalisation. Per the skill's gate, a known weakening forces
`YES-but-generalise-first`, not `YES-add-as-is`; and cost (MODERATE, and sequenced behind
the `padicLog` generalisation) is explicitly **not** a downgrade factor.

**Reason for the generalisation:**
  - **LITERATURE-WEAKENING (primary):** Phase 4b found the user's form strictly narrower
    than the literature-standard form — redundant `ℚ_[p]`-algebra assumption and a witness
    domain on the exp ball rather than the standard log ball.
  - **MODERN-IDIOM (secondary, same direction):** Phase 4c — the `CharZero`
    complete-nonarchimedean-field form is the mathlib-idiomatic target (the missing
    nonarchimedean partner to a generalised `padicLog`), and the extended log is canonically
    a **`MonoidHom` `K^× → K`** (`log_p(p)=0`), which a mathlib version should bundle
    (`extLog_mul` = `map_mul`).

  Proposed restatement:
  ```lean
  variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

  /-- The domain of the extended logarithm: `x^m = p^k·y` with `y` in the FULL
  log convergence ball `‖y−1‖ < 1`. -/
  def ExtLogDomain (p : ℕ) (x : K) : Prop :=
    ∃ (m : ℕ) (k : ℤ) (y : K), 0 < m ∧ x ^ m = (p : K) ^ k * y ∧ ‖y - 1‖ < 1

  open Classical in
  /-- The Iwasawa-branch p-adic logarithm extended to the rational-valuation
  domain (`log_p p = 0`), junk-total: `extLog x = m⁻¹ • log_p y` for `x^m = p^k·y`. -/
  noncomputable def extLog (p : ℕ) (x : K) : K :=
    if h : ExtLogDomain p x then (h.choose : K)⁻¹ • padicLog p h.choose_spec.choose_spec.choose
    else 0
  ```
  (optionally re-packaged as `extLog : (domain subgroup of Kˣ) →* (K, +)` per Phase 4c row 3).

  Estimated cost of regeneralisation: **MODERATE** — the def rewrite is mechanical, but it is
  *sequenced behind* the `padicLog` generalisation (`extLog` is `m⁻¹ • padicLog y`) and
  re-proving `extLog_witness_smul_eq`/`extLog_mul` on the wider `CharZero`-field / full-log-ball
  setting is real work. EXPENSIVE/MODERATE does **not** downgrade the verdict.

  Mathlib downstream this enables:
  - the single general `extLog` serves `ℚ_p`, finite extensions, and `ℂ_p` uniformly as the
    canonical *extended* Iwasawa logarithm — the off-ball companion to the generalised `padicLog`;
  - it composes with mathlib's `CharZero`/nonarchimedean-field API and, if bundled, with the
    whole `MonoidHom`/`Subgroup` ecosystem (the literature's "unique continuous homomorphism
    `K^× → K` with `log_p(p)=0`" becomes a first-class bundled object);
  - it gives mathlib the canonical home for `log_p(p)=0`, the `μ_∞` kernel, and additivity on
    `K^×` — facts currently re-proved project-locally (`extLog_mul`, the `extLog ω = 0` lemma,
    the `μ_p`-collapse) that downstream p-adic L-function / Iwasawa-theory work repeatedly needs.

  Proposed mathlib location (post-generalisation): ship **together with** the generalised
  `padicLog` (and `padicExp`/`InExpBall`) as one coherent "p-adic exponential and logarithm"
  contribution — e.g. `Mathlib/NumberTheory/Padics/Logarithm.lean` (new), with `extLog` (or a
  better mathlib name such as `padicLogExtend` / the bundled `Padic.iwasawaLog`) as the extended
  branch.

  Next action: **run `/generalise PadicLFunctions.extLog`** (it will tension against both the
  literature-standard form from Phase 3 and the modern-idiom form from Phase 4c) — **after**
  first generalising `padicLog` (its prerequisite; see `padicLog.md`'s next-action). Then
  `/cleanup projects/PadicLFunctions/PadicLFunctions/ExtLog.lean extLog` and open the mathlib
  PR grouping `padicExp` + `padicLog` + `extLog` + `InExpBall`.

---

## Next step

Run `/generalise PadicLFunctions.extLog` to restate it over a complete nonarchimedean
`CharZero` field `K` (dropping `[NormedAlgebra ℚ_[p] L]`, taking `m⁻¹ ∈ K`), widening
`ExtLogDomain`'s near-1 factor to the full log ball `‖y−1‖<1`, and ideally bundling it as
the `MonoidHom` `K^× → K` with `log_p(p)=0` that the literature characterises. This is
**sequenced behind** the `padicLog` generalisation (`extLog = m⁻¹ • padicLog y` rides on it).
Then `/cleanup` `ExtLog.lean` and open a mathlib PR grouping `padicExp` + `padicLog` +
`extLog` + `InExpBall` as one coherent "p-adic exponential and logarithm" contribution.
