# `/mathlibable` report — `PadicLFunctions.extLog_mul`

Mode A (single declaration), full 10-phase workflow with the exhaustive 9-channel
literature search.

**Final verdict: `YES-but-generalise-first`.** `extLog_mul` is the **additivity /
homomorphism law of the extended (Iwasawa-branch) p-adic logarithm** —
`log_p(xy) = log_p x + log_p y` — which the literature names as *the* defining
property of the extended `log_p` ("log : C_p^× → C_p is the **unique group
homomorphism** with log_p(p)=0", kernel `p^ℚ·μ_∞`). It is genuinely missing from
mathlib (which has **no** nonarchimedean logarithm of any kind), is not composable
(its building blocks — `extLog`, `padicLog`, `padicLog_mul`, the witness machinery —
are all project-local and absent from mathlib), and is real, load-bearing API
(3 external call lines + the backbone of `extLog_prod` and `extLog_neg`). It is **not**
`YES-add-as-is` only because it inherits the *base-field* narrowing already flagged for
its parent `extLog` and base `padicLog`: it is stated over a `ℚ_[p]`-algebra rather than
an arbitrary complete nonarchimedean **char-0** field, so the verdict gate forces
`YES-but-generalise-first`. The generalisation is the same single move that re-aims the
whole `padicLog`/`extLog` cluster, and the modern-idiom target is to bundle it as the
`map_mul`/`map_add` of a `MonoidHom (domain subgroup of Lˣ) → (L,+)` — exactly the
object the literature characterises `log_p` as.

---

### Baseline (Phase 0)

- lake build:               **not re-run; reasoned from source** (per task BUILD NOTE — the build is stale/slow on this checkout; the declaration and its entire dependency chain were read directly from source, exactly as the skill's Phase-0 fallback allows). `ExtLog.lean` is on `main` (which the project asserts always builds), was last touched by a committed `cleanup` (`0729ce7 cleanup: golf PadicLFunctions/ExtLog.lean (#15) (#275)`), and contains **0 `sorry`/`admit`** (grep `\b(sorry|admit)\b` over the file → none). Every consumer of `extLog_mul` (`extLog_prod`, `extLog_neg`, `ResidueZeta.lean:1766`, `ValuesAtOne.lean:1080`) elaborates against the theorem as written.
- decl `PadicLFunctions.extLog_mul`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:357`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  "The extended (Iwasawa-branch) p-adic logarithm (RJW §6, decomposition W6a)" — extends `padicLog` to rational-valuation elements `x` with `x^m = p^k·y` (`y` in the exp ball) by `extLog x := m⁻¹·padicLog y` (junk `0` off-domain; Iwasawa's branch `log_p(p)=0`); cross-references Washington, *Cyclotomic Fields*, §5.1. The target is the file's stated **"W6a-a9: additivity on the domain."**

---

### Statement (Phase 1)

`PadicLFunctions.extLog_mul` is **a theorem** stating the **additivity (homomorphism)
law** of the extended p-adic logarithm:

> Let `L` be a complete ultrametric normed field that is a normed `ℚ_[p]`-algebra
> (e.g. `ℚ_[p]`, finite extensions, `ℂ_[p]`). If `x` and `y` both lie in the
> *rational-valuation domain* of the extended logarithm — i.e. each admits a witness
> `x^m = p^k·a` with `a` in the (translated) exponential ball, and likewise
> `y^{m'} = p^{k'}·b` — then the extended Iwasawa logarithm is **additive over the
> product**: `extLog(x·y) = extLog(x) + extLog(y)`.

This is exactly the literature's headline characterisation of the Iwasawa logarithm:
`log_p` extended to `K^×` (via `log_p(p)=0`) is the **unique continuous group
homomorphism** `K^× → (K,+)`, so `log_p(xy) = log_p x + log_p y`. The proof forms a
*product witness* `(x·y)^{m·m'} = p^{k m' + k' m}·(a^{m'}·b^m)`, evaluates all three
`extLog`s via `extLog_eq_of_witness`, and reduces to `padicLog`'s own multiplicativity
on the exp ball (`padicLog_mul` + `padicLog_pow`) followed by `ℚ_[p]`-scalar algebra.

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [Fact p.Prime]` — the residue prime; the rational scalars `m⁻¹, m'⁻¹` are taken in `ℚ_[p]`.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — a complete ultrametric (nonarchimedean) normed field that is a normed `ℚ_[p]`-algebra. `CharZero` is **not** stated (it is implied by the `ℚ_[p]`-algebra structure).

Hypotheses (Lean side):
- `(hx : ExtLogDomain p x)` — `x` is in the rational-valuation domain `∃ m k a, 0 < m ∧ x^m = p^k·a ∧ InExpBall p (a−1)`.
- `(hy : ExtLogDomain p y)` — same for `y`.

Conclusion (math): `log_p(x·y) = log_p(x) + log_p(y)` on the rational-valuation domain — the homomorphism law of the extended Iwasawa logarithm.
Conclusion (Lean): `extLog p (x * y) = extLog p x + extLog p y`.

Underlying definitions / lemmas (read from source):
- `extLog p x` (`ExtLog.lean:286`) — `m⁻¹ • padicLog y` for a `Classical.choice` witness, junk `0` off-domain.
- `ExtLogDomain p x` (`ExtLog.lean:278`) — `∃ m k y, 0<m ∧ x^m = p^k·y ∧ InExpBall p (y−1)`; **the natural domain of `extLog`**, proven multiplicatively closed by `ExtLogDomain.mul` (`ExtLog.lean:386`).
- `InExpBall p x` (`PadicExp.lean:65`) — `‖x‖^{p−1} < (p:ℝ)⁻¹`, the exp ball (⊊ unit ball).
- Proof inputs: `extLog_eq_of_witness` (`:335`, every witness computes `extLog`), `padicLog_mul` (`:973`, exp-ball multiplicativity), `padicLog_pow` (`:79`), `mul_mem_expBall`/`pow_mem_expBall` (ball closure). The product-witness identity is the same construction as `ExtLogDomain.mul`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline; recorded BIG).
Reason: it is a **named structural identity** — the homomorphism / additivity law of a
transcendental function (`log_p`) that mathlib lacks entirely, and a "guaranteed in the
literature" classical fact (the literature *defines* the extended `log_p` by this exact
property). It is not a person-named theorem, and it is a derived law of the headline def
`extLog` rather than a standalone main result, hence borderline — but the homomorphism
property is the canonical characterisation of the object, so BIG is the honest call.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is narrative framing only.)

### One-line check (Phase 2b)

Kind is `theorem`, not a `def`/`abbrev`/`structure`. One-line check **n/a / skipped**.
The proof body is ~24 lines of genuine mathematics (product-witness construction +
three-`extLog` evaluation + `padicLog`-reduction + `ℚ_[p]`-scalar algebra), not a
one-liner.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form — additivity/hom) | `Iwasawa p-adic logarithm group homomorphism additivity log(xy)=log(x)+log(y) extended whole multiplicative group C_p log_p(p)=0` | **yes** | "log: C_p^× → C is a **homomorphism** whose kernel is the subgroup of C_p^× generated by all roots of unity and all roots of p"; "log(p^n(1+x)) := log(1+x)… for x with x^n ∈ G, log(x):=(1/n)log(x^n)" | The Lean `extLog_mul` is *precisely* this homomorphism property. Surfaced MIT 18.785 PS10, AWS 2018 problems, arXiv:1907.06437, Iwasawa-theory survey PDFs. The additivity is the **defining** property of the extension. |
| 2 | WebSearch (general form — uniqueness/kernel) | `p-adic logarithm unique continuous homomorphism C_p^times to C_p log_p(p)=0 extension kernel roots of unity` | **yes** | "log_p : Q*_p → (Q_p,+) is the **unique group homomorphism** with log_p(p)=0 that extends the homomorphism log_p : 1+pZ_p → Q_p"; kernel = roots of unity together with roots of p | Confirms: the extension is *characterised* by being a homomorphism (the additivity) plus `log_p(p)=0`. Kober/Stoll Bayreuth notes, K. Conrad, MIT PS10. So `extLog_mul` is the half of that characterisation mathlib would headline. |
| 3 | WebSearch (named-after / textbook) | `nLab p-adic logarithm exponential homomorphism convergence "p-adic logarithm" log(xy) additive non-archimedean field` | **yes** | "the power series for the p-adic logarithm converges for x in C_p with \|x\|_p<1 and defines log_p(z) for \|z−1\|_p<1 satisfying the usual property **log_p(zw)=log_p z+log_p w**"; "log_p can be **extended to all of C_p^×** by imposing that it continues to satisfy this last property and setting log_p(p)=0" | World Scientific *Value Distribution in p-adic Analysis* §25, MIT `exp.pdf`, ResearchGate "On the image of p-adic logarithm on principal units". The extension is *built to preserve additivity* — `extLog_mul` is that preserved law. |
| 4 | ChatGPT MCP | (intended: standard form of the extended-log additivity, at what generality the homomorphism law is stated, exp-ball vs unit-ball vs whole `C_p^×`, historical evolution) | **n/a** | — | No ChatGPT/OpenAI MCP tool configured in this sandbox (only Asana/Atlassian/etc. proxy servers surfaced; consistent with the sibling `extLog`/`padicLog`/`padicLog_mul` reports). **Compensated** by the primary-source Wikipedia `WebFetch` (row 11) giving the verbatim "holds on the entire multiplicative group C_p^×" statement, plus the in-repo Washington-cited docstring and the three WebSearch generality levels. Intent met. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/`; `ls refs/PadicLFunctions/` | **n/a** | (no references dir; no `refs/` symlink) | Both absent on this `main` checkout (`references/` does not exist; `refs/` is dev-branch-only). The `--refs` arg points at the plugin's generic skill references, not project-source PDFs. The module docstring cites RJW §6 / Thm 6.1(ii) and Washington §5.1. Sibling reports (`extLog.md`, `padicLog_mul.md`) consulted as in-repo prior art. |
| 6 | nLab | `nLab p-adic logarithm` (via row-3 sweep) | **partial** | nLab "p-adic number": "the p-adic exponential has an inverse, named the p-adic logarithm"; series converges `\|x−1\|<1`; an iso of additive/multiplicative groups on the matched balls | nLab has no dedicated "Iwasawa logarithm" / extended-log page; the additivity-as-homomorphism content is the p-adic-number entry plus the analysis references (rows 1–3, 11). |
| 7 | nCatLab (categorical) | (same as nLab) | **n/a** | — | Not a higher-categorical concept; `extLog_mul` is an algebraic identity (`=`) of an analytic function — no universal-property formulation to look up. (The only categorical shadow is the multiplicative-formal-group `M(x,y)=x+y+xy`, a downstream packaging, noted for `padicLog_mul`.) |
| 8 | Stacks Project (alg geom) | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic concept; `log_p(xy)=log_p x+log_p y` for field elements does not appear in Stacks. |
| 9 | MathOverflow / Math.StackExchange | (covered by rows 1–3; MO/MSE/lecture-note threads surfaced) | **yes** | consensus: extend by `log p = 0`, `log(p^r ζ z)=log z`, getting a **homomorphism** `C_p^× → C_p`; the additivity is the standard, used-everywhere fact; kernel `p^ℚ·μ_∞` | No disagreement: the additivity is universally stated on the *whole* `C_p^×`, never restricted to a `ℚ_p`-algebra. |
| 10 | recent arXiv (≤5 yr) | (rows 1–2) | **yes** | arXiv:1907.06437 (2023) & ResearchGate 2025 "On the image of p-adic logarithm on principal units": `log_p: 1+𝔪_K → 𝔪_K` is a **homomorphism**, iso on `1+𝔪_K^r`; Ankeny–Artin–Chowla congruences (arXiv:2410.20934, 2024) use exactly this `log_p` | Active modern use of the additivity of exactly this extended `log_p` (`log p=0` normalisation). The open problems concern its *image*, taking the homomorphism property — i.e. `extLog_mul` — for granted. |
| 11 | Wikipedia primary fetch | `WebFetch en.wikipedia.org/wiki/P-adic_exponential_function` | **yes** | **verbatim**: "log_p(zw) = log_p z + log_p w holds for nonzero elements in **C_p**"; "The multiplicative property holds on the **entire multiplicative group C_p^×**"; extend via `w = p^r·ζ·z` ↦ `log_p(z)`; kernel = `{p^r·ζ : r∈ℚ, ζ root of unity}` | This is exactly `extLog_mul`: the additivity stated over all of `C_p^×` (not restricted to `ℚ_p`), with the extension built precisely to preserve it. The Lean hypotheses `ExtLogDomain p x/y` are the in-domain restriction; on `C_p` every nonzero element is in domain (see Phase 4). |

The protocol passed: WebSearch ran **3 distinct generality levels** (rows 1–3: the
additivity/hom form, the uniqueness/kernel form, the textbook/named form) plus arXiv (10)
and a primary fetch (11); local refs checked (absent, n/a with reason); nLab checked (6,
partial); Stacks/nCatLab/MathOverflow each adjudicated (8/7/9). ChatGPT MCP is genuinely
unavailable in this sandbox — recorded n/a with the compensating primary-source Wikipedia
fetch (row 11) carrying the verbatim standard form.

### Literature summary (Phase 3)

Concept identified as: **the additivity / homomorphism law of the Iwasawa logarithm
`log_p` extended to `K^×`** — i.e. `log_p(xy) = log_p x + log_p y`, the property that
*characterises* the extension (together with `log_p(p)=0`).
Sources agree on the standard form: **yes, unanimously** — Wikipedia, MIT 18.785,
K. Conrad / Stoll notes, World Scientific, arXiv:1907.06437/2410.20934 all state that the
extended `log_p` is a **group homomorphism** `K^× → (K,+)`, so `log_p(xy)=log_p x+log_p y`
holds on the **whole** multiplicative group; the extension off `‖z−1‖<1` is *defined* by
requiring this additivity to persist. Kernel `p^ℚ·μ_∞`.
Most general standard form: for **any complete nonarchimedean field `K` of characteristic 0**
(`ℚ_p`, finite/infinite extensions, `ℂ_p`), `extLog : K^× → (K,+)` is a group homomorphism;
`extLog(xy)=extLog x+extLog y` for all `x,y ∈ K^×`. It does **not** require a
`ℚ_[p]`-algebra structure — only `CharZero` (so `m⁻¹` and the `1/n` inside `padicLog` make
sense).
Generality dimensions where the literature varies:
  - **Base ring**: `ℚ_p ⊂` finite extensions `⊂ ℂ_p ⊂` arbitrary complete nonarchimedean
    char-0 field. The literature standard is `ℂ_p` / "complete nonarchimedean field"; the
    Lean `[NormedAlgebra ℚ_[p] L]` is an artefact of the project living over `ℚ_[p]` (the
    *same* axis flagged for `padicLog` and `extLog`).
  - **Domain of the hypotheses**: the literature states additivity on **all of `K^×`**; the
    Lean form restricts to `ExtLogDomain p x ∧ ExtLogDomain p y`. But `ExtLogDomain` is the
    *natural domain of `extLog` itself* (off it, `extLog = 0` is junk), and over `ℂ_p` every
    nonzero element is in domain (rational-valuation factoring `x = p^r·ζ·z` holds for all
    of `C_p^×`). So the in-domain hypotheses are **not** an additional narrowing beyond the
    domain `extLog` is meaningfully defined on — they faithfully encode "x, y are honest
    arguments of `log_p`". The narrowing baked into `ExtLogDomain` (exp ball vs full log
    ball for the near-1 factor) is inherited from `extLog`/`padicLog`, not introduced here.
Disagreement with the literature: the Lean form is **correct** and stated on the natural
domain; its only narrowing relative to standard is the inherited **base-field**
`ℚ_[p]`-algebra assumption (and the exp-ball domain choice carried by `ExtLogDomain`/
`padicLog`) — see Phase 4.

---

### Generality analysis — `PadicLFunctions.extLog_mul`

Literature-standard form (from Phase 3): `extLog(xy) = extLog x + extLog y` for **all**
`x,y ∈ K^×` of a complete nonarchimedean **char-0** field `K` (the homomorphism law of the
extended Iwasawa logarithm); equivalently the `map_mul`/`map_add` of the bundled
`MonoidHom K^× → (K,+)`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] L]` + the scalars `m⁻¹, m'⁻¹ ∈ ℚ_[p]` (and, through `padicLog`, the `1/(n+1) ∈ ℚ_[p]`) | `L` is a normed `ℚ_[p]`-algebra | `K` is a `CharZero` complete nonarchimedean field; `m⁻¹ ∈ K` directly | **yes** | The additivity never asks the base field to be a `ℚ_[p]`-algebra — only that `m⁻¹` (and `1/n` in `padicLog`) make sense (`CharZero`/`Algebra ℚ`). The literature states it over `ℂ_p` and arbitrary complete nonarchimedean char-0 fields. This is the **same** inherited artefact as `extLog` row 1 / `padicLog` row 1. |
| 2 | `[IsUltrametricDist L]` + `[CompleteSpace L]` + `[NormedField L]` | complete ultrametric normed field | complete nonarchimedean field | **NO** | Genuinely needed: `padicLog`'s summability is the nonarchimedean `cofinite → 0` criterion, and the well-definedness / exp-ball facts feeding the proof (`extLog_witness_smul_eq`, `padicLog_mul`, `mul_mem_expBall`) use ultrametric norm facts. Correct hypothesis cluster. |
| 3 | `(hx : ExtLogDomain p x)`, `(hy : ExtLogDomain p y)` | `x, y` in the rational-valuation domain with the near-1 factor in the **exp** ball | `x, y ∈ K^×` (on `ℂ_p`: vacuous — all nonzero elements; in general the natural domain of `extLog`) | **partial (inherited, not introduced here)** | The hypotheses correctly restrict to where `extLog` is meaningfully defined (off-domain `extLog=0` is junk; additivity *cannot* hold off-domain). They are **not** a narrowing of the *additivity statement* beyond the domain of the function. The one inherited narrowing is *inside* `ExtLogDomain`: the near-1 factor is keyed to the exp ball `‖a−1‖^{p−1}<p⁻¹` rather than the full log ball `‖a−1‖<1` (the same exp-ball-vs-log-ball gap flagged for `padicLog`/`extLog`). Widening this is part of the `extLog` generalisation, not a separate `extLog_mul` move. |
| 4 | the **shape** of the law (a bare `=` between three `extLog`s) | a standalone additivity equation | the same equation *plus* the bundled-morphism view: `extLog_mul` = `map_mul` of `MonoidHom (domain subgroup of Lˣ) → (L,+)` | **partial (modern-idiom)** | The equation matches the literature exactly. What the literature additionally packages — and what a mathlib version would want — is `extLog_mul` as the structure-map law of a bundled hom (the domain `ExtLogDomain` *is* a subgroup of `Lˣ`, which `ExtLogDomain.mul` already half-proves). See Phase 4c row 3/4. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD.**
Number of weakening opportunities found: **K = 1** genuine base-generality weakening
(row 1: drop `[NormedAlgebra ℚ_[p] L]` for `[CharZero K]`, take `m⁻¹ ∈ K`). Row 2 is
already optimal; row 3's narrowing is *inherited* from `ExtLogDomain`/`padicLog` (widened
as part of generalising `extLog`, not independently here); row 4 is a Phase-4c idiom point.

Proposed restatement (the literature-standard target, riding on the generalised
`extLog`/`padicLog`):

```lean
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

/-- Additivity of the extended (Iwasawa-branch) p-adic logarithm on its (rational-
valuation) domain: `extLog (x*y) = extLog x + extLog y`. The homomorphism law of `log_p`. -/
theorem extLog_mul {p : ℕ} [Fact p.Prime] {x y : K}
    (hx : ExtLogDomain p x) (hy : ExtLogDomain p y) :
    extLog p (x * y) = extLog p x + extLog p y := …
```

i.e. the *only* change from the current statement is the base-field typeclass cluster
(`[NormedAlgebra ℚ_[p] L]` → `[CharZero K]`, `m⁻¹ ∈ K`). This sits **directly on top of**
the generalised `extLog` and `padicLog` already proposed in the sibling reports — `extLog_mul`
**cannot be generalised independently**, since it is an identity *about* `extLog` and is proven
*through* `padicLog_mul`/`padicLog_pow`.

Cost of restatement: **MODERATE** — the statement is a near-mechanical typeclass rewrite, but
it is *sequenced behind* generalising `padicLog` (cost MODERATE) and `extLog` (the proof calls
`extLog_eq_of_witness`, `padicLog_mul`, `padicLog_pow`, all of which must first be on the
`CharZero`-field setting). Re-running the `ℚ_[p]`-scalar algebra step (`Nat.cast_smul_eq_nsmul`,
`field_simp`) in a general `CharZero` field is straightforward once `m⁻¹ ∈ K`. EXPENSIVE/MODERATE
does **not** downgrade the verdict — it informs sequencing.

→ STRICTLY NARROWER ⇒ Phase 7 considers **YES-but-generalise-first** prominently. Also runs 4c.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let `L` be a foo" preamble → typeclass? | partial | already typeclass-based; the only change is `NormedAlgebra ℚ_[p] L` → `CharZero K` (row 1 of 4a) | composes with all of mathlib's `CharZero` nonarchimedean-field API, not only `ℚ_[p]`-algebras |
| 2 | sequences/metric → filters/topological? | no | the statement is an algebraic identity (`=`); the `tsum` inside `padicLog` already uses mathlib's filter-based `Summable`/`tsum`. No sequence/metric notion in the statement to filter-ise. | n/a |
| 3 | construct object → universal-property / bundled-morphism class? | **yes** | the literature characterises the extended `log_p` as the **unique continuous group homomorphism** `K^× → (K,+)` with `log_p(p)=0`; `extLog_mul` is precisely its `map_mul`/`map_add`. A mathlib version would bundle `extLog` as a `MonoidHom (domain subgroup ≤ Kˣ) → (Additive K)` (or an `AddMonoidHom` to `(K,+)`), and `extLog_mul` becomes `map_mul`, `extLog 1 = 0` becomes `map_one`. | the entire `MonoidHom`/`AddMonoidHom` ecosystem — `map_pow` (= `extLog_pow`), `map_prod` (= `extLog_prod`), kernel/range lemmas, `MonoidHom.comp`; `extLog_mul` stops being a bespoke lemma and becomes the structure field. |
| 4 | set-with-closure-pred → bundled substructure? | **yes** | `ExtLogDomain` is exactly "the subgroup `p^ℤ·(1+B)` of `Lˣ`" written as a `Prop`; `ExtLogDomain.mul` (`ExtLog.lean:386`) already proves it is closed under `*` — i.e. it *is* a sub-monoid/group. The mathlib idiom would make it a `Subgroup Lˣ`. | `Subgroup` lattice API; `extLog` as a hom *out of* that subgroup, with `extLog_mul` as the hom's `map_mul`. |
| 5 | vector-space/field-specific → weaken to module/ring? | partial | same as row 1: weaken `ℚ_[p]`-algebra to `CharZero` field. (A Banach-algebra `log(1+·)` homomorphism is a *separate, larger* object, as noted for `padicLog`.) | uniform `extLog_mul` over `ℚ_p`, finite extensions, `ℂ_p`. |
| 6 | 1-categorical → higher-categorical? | no | not categorical | n/a |
| 7 | concrete index ℕ/ℤ/ℝ → general structure? | no | the witness exponents `m, m' : ℕ`, `k, k' : ℤ` are intrinsic (powers / valuations), already at the right index types | n/a |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — two real, same-direction improvements (consistent with the
parent `extLog`'s Phase 4c).
  - **Base-generality (primary, = Phase 4b):** the `CharZero` complete-nonarchimedean-field form,
    dropping the `ℚ_[p]`-algebra assumption (`m⁻¹ ∈ K`). The additivity of the missing
    nonarchimedean extended logarithm should hold over all such fields, not just `ℚ_p`-algebras.
  - **Bundled-morphism (secondary):** `extLog_mul` is the `map_mul` of the extended log viewed as a
    `MonoidHom`/`AddMonoidHom` from the domain subgroup `p^ℤ·(1+B) ≤ Lˣ` to `(L,+)`. The literature's
    headline statement *is* "`log_p` is the unique continuous homomorphism `K^× → K` with
    `log_p(p)=0`"; bundling makes `extLog_mul` the structure field rather than a freestanding lemma.
  - Cost: CHEAP for the base-generality rewrite (modulo first generalising `padicLog`/`extLog`);
    MODERATE for the `MonoidHom`-bundling (needs the `ExtLogDomain`-is-a-`Subgroup` upgrade, which
    `ExtLogDomain.mul` already half-supplies).
  - Mathlib downstream this enables: composes with mathlib's `CharZero`/nonarchimedean-field API and,
    if bundled, the entire `MonoidHom`/`AddMonoidHom`/`Subgroup` ecosystem — `map_pow` (= `extLog_pow`),
    `map_prod` (= `extLog_prod`), kernel lemmas (= the `μ_∞`/`p^ℚ` kernel), all for free; subsumes
    `ℚ_p`, finite extensions, `ℂ_p` in one law.
  - Real mathematical improvement (not just "looks cooler"): the additivity *is* the property the
    literature defines the extension by; stating it as a bundled-hom structure field over arbitrary
    complete nonarchimedean char-0 fields gives mathlib the canonical home for "the unique homomorphic
    extension of `log_p` with `log_p(p)=0`" — and `extLog_prod`/`extLog_neg`/`extLog_pow` become
    `map_prod`/kernel/`map_pow` instead of bespoke re-proofs.

Phase 4c reinforces Phase 4b: the right mathlib target is the `CharZero`-field form (ideally the
`map_mul` of a bundled `MonoidHom`), built atop the generalised `extLog`/`padicLog` — **not** the
`ℚ_[p]`-algebra freestanding lemma. Since Phase 4b already found the form STRICTLY NARROWER, the
verdict is `YES-but-generalise-first` regardless.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** No definitional equalities or typeclass-search paths are
introduced. (The objects it rests on get their own Phase-4.5 assessments when they are targets:
`extLog` was assessed `YES-but-generalise-first` with overall risk NONE/LOW; `ExtLogDomain` is a
`Prop`-valued predicate, verdict `NO-composable-from-mathlib`; `padicLog` `YES-but-generalise-first`.)

---

### Mathlib search-status: `PadicLFunctions.extLog_mul`

[A] Lean-Finder       — **n/a**: Lean-Finder MCP not available in this environment. Compensated by exhaustive source grep (D) + name enumeration (E) over the actual pinned mathlib.
[B] Loogle            type-patterns `?f (?x * ?y) = ?f ?x + ?f ?y` (additive-hom-over-product) and `padicLog`/`extLog`-shaped — **n/a**: `lean_loogle` MCP not available; substituted by source grep (D). The additive-hom-over-product pattern returns only archimedean `Real.log_mul`/`Complex.log`/`ENNReal.log_mul_add` and discrete `Nat.log`/`WithZero.log`/`Submonoid.log` — none nonarchimedean/p-adic.
[C] LeanSearch        "p-adic logarithm of a product is the sum", "extended Iwasawa logarithm additive", "nonarchimedean log homomorphism log_p(p)=0" — **n/a**: `lean_leansearch` MCP not available; substituted by the literature channels (Phase 3) + source grep.
[D] Grep mathlib src  **executed in full** on `.lake/packages/mathlib/`: every `theorem .*log_mul`/`.*log_add`/`_mul.*= .*log.*+ .*log`; `padicLog`, `p_?adic.*log`, `nonarchimedean.*log`, `ultrametric.*log`, `iwasawa`; `exp_log`/`log_exp` outside `Real`/`Complex`; `NumberTheory/Padics/` directory listing. **Findings:** every `log_mul` is archimedean (`Real.log_mul` `Analysis/.../Log/Basic.lean:132`, `Complex.log_mul_ofReal`, `ENNReal.log_mul_add`, `Real.logb_mul`) or discrete/algebraic (`Nat.log_mul_base`, `Ordinal.add_log_le_log_mul`, `Submonoid.log_mul`, `WithZero.log_mul`); `NumberTheory/Padics/` has **no Exp/Log file at all**; the only `exp_log`/`log_exp` hits are `Real`/`Complex`/CStar-CFC. **No p-adic / nonarchimedean evaluated logarithm, and a fortiori no additivity law for one.** |
[E] Name pattern      enumerated **every** `*_mul` log-additivity and every `log` def/hom in mathlib: archimedean (`Real`/`Complex`/`ENNReal`/`EReal`, incl. `ENNReal.logHomeomorph`, `Complex.expHom`), discrete (`Nat`/`Int`/`Ordinal`/`Submonoid`/`WithZero`), formal (`PowerSeries.log`). The p-adic-area "log" hits (`padicValNat_le_nat_log`) are the **integer** `Nat.log`, unrelated. No bundled `log`-as-`MonoidHom`/`AddMonoidHom` on a nonarchimedean/valued field exists.

Searched for both:
  - the user's current form (additivity of the extended Iwasawa log over an ultrametric `ℚ_[p]`-algebra, on `ExtLogDomain`): **not in mathlib**.
  - the literature-standard form (additivity / homomorphism of the extended Iwasawa log over a complete nonarchimedean char-0 field / `ℂ_p`, on all of `K^×`, ideally as a bundled `MonoidHom`): **not in mathlib**.

Closest existing mathlib objects (all confirmed *not* the same):
  - `Real.log_mul` / `Complex.log_mul_ofReal` / `ENNReal.log_mul_add` — archimedean additivity laws; wrong regime entirely.
  - `NormedSpace.exp` + `exp_add_of_mem_ball` (`Analysis/Normed/Algebra/Exponential.lean`) — the analytic exponential functional equation, but **no companion `log`**, no `exp_log`/`log_exp` inverse, archimedean radius. Cannot even phrase `extLog`, let alone its additivity.
  - `Complex.expHom`, `ENNReal.logHomeomorph` — bundled archimedean exp/log morphisms; the *idiom* `extLog` should follow, but for the wrong (archimedean) function.
  - `PowerSeries.log` (`RingTheory/PowerSeries/Log.lean`) — the **formal** log series; no convergence, no evaluation, no additivity *of an evaluated function*.

Concluded: **not in mathlib** (all available methods exhausted — source grep run in full for both the user's form and the literature-standard form; the entire mathlib `log_mul`/`log`-hom inventory enumerated; semantic MCP tools genuinely unavailable and recorded n/a). Mathlib has **no nonarchimedean / p-adic analytic logarithm of any kind**, hence no additivity law and no bundled homomorphism for one. Consistent with the sibling `extLog.md`, `padicLog.md`, `padicLog_mul.md` (all "not in mathlib") — `extLog_mul` is the additivity of an object two steps out (the off-ball extension of an already-missing `padicLog`), so it is doubly absent.

---

### Call sites — `PadicLFunctions.extLog_mul`

Internal use count: **3 genuine `extLog_mul` applications** (within the `PadicLFunctions`
project, NOT counting the declaring statement or docstring mentions), across **3 distinct
files** (2 external to `ExtLog.lean`, plus 1 internal-but-different-decl use that makes it
the backbone of `extLog_prod`).
External-to-file callers: **2 distinct files** (`ResidueZeta.lean`, `ValuesAtOne.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `ResidueZeta.lean:1766` | `rw [hmq, hsplit, extLog_mul p hωdom handom, …]` — split `u = ω(u)·⟨u⟩` (Teichmüller × principal), then `extLog(ω(u)·⟨u⟩) = extLog ω(u) + extLog⟨u⟩` with `extLog ω(u)=0` (the `μ_∞` kernel). The keystone "valuation-zero ⇒ log lands in `⟨u⟩`" step of the residue computation. |
| `ValuesAtOne.lean:1080` | `extLog_mul p (extLogDomain_of_integral_norm_one p …) …` — additivity used in the `±1`-invariance / `μ_p`-collapse chain (`extLog(−x)=extLog x`, `Σ extLog(ξ^i ε^c−1)`). |
| `ExtLog.lean:424` (inside `extLog_prod`) | `extLog_mul p (hf i …) (ExtLogDomain.prod p s f hdom), ih hdom` — the `insert` step of the **Finset additivity** `extLog(∏ f) = Σ extLog∘f`. `extLog_prod` *is* the iterated `extLog_mul`. |
| `ExtLog.lean:439` (inside `extLog_neg`) | `rw [show (-x:L)=(-1)*x …, extLog_mul p hneg1 hx, …]` — the `μ_2 ⊂ μ_∞` kernel fact `extLog(−x)=extLog x` (since `extLog(−1)=0`). |

Inline-derivation grep (was `extLog(xy)=extLog x+extLog y` re-derived without calling `extLog_mul`?):
  - **Within `PadicLFunctions`: none.** No site re-derives the additivity via the product-witness
    construction by hand; everyone routes through `extLog_mul`. (`ResidueZeta.lean:1735` is a
    *docstring* mention naming the lemma, not a re-derivation.)
  - **Cross-project:** no other `extLog`/extended-log additivity exists in the repo
    (`grep extLog projects/ --exclude PadicLFunctions` → empty; the
    `BernoulliRegular.FLT37.PadicL.padicLog` duplicate is the *unextended* log — different object,
    no `extLog_mul`).

Call-sites signal: **K = 3 genuine uses across 3 files (2 external), and it is the literal
backbone of `extLog_prod` and `extLog_neg`, with no inline re-derivation → real, load-bearing
API; consumers depend on it → strong YES-* lean.** (Per the Phase-6.0.1 table: "K ≥ 3 internal
uses, no inline re-derivation ⇒ real API ⇒ YES-* bucket.")

---

### Composition check (Phase 6)

Can `PadicLFunctions.extLog_mul` be derived from mathlib in ≤3 chained calls?

Attempt 1: some mathlib `log_mul` / additive-hom lemma applied to `extLog`.
  - Mathlib decls used: `Real.log_mul` / `Complex.log_mul` / `ENNReal.log_mul_add` / `map_mul`.
  - Result: **fails** — those are archimedean / discrete / for a *different* function; there is no
    mathlib `extLog`/`padicLog` to apply `map_mul` to, and no nonarchimedean `log_mul`. Not a composition.

Attempt 2: build it from `NormedSpace.exp_add_of_mem_ball` + an inverse `log`.
  - Mathlib decls used: `NormedSpace.exp`, `exp_add_of_mem_ball`.
  - Result: **fails** — mathlib has no `log` inverse for `NormedSpace.exp`, no `exp_log`/`log_exp`,
    and `NormedSpace.exp` is archimedean-radius; one cannot even phrase the extended `log_p`.

Attempt 3: assemble `extLog_mul` from the repo's own primitives in ≤3 mathlib calls.
  - Result: **fails as a *mathlib* composition** — the actual proof is a genuine multi-step argument
    over **project-local** primitives absent from mathlib: construct the product witness
    `(xy)^{mm'} = p^{km'+k'm}·(a^{m'} b^m)` (a `ring`/`zpow` computation), prove the factor is in the
    exp ball (`mul_mem_expBall`/`pow_mem_expBall`), evaluate all three `extLog`s via
    `extLog_eq_of_witness`, reduce to `padicLog_mul` + `padicLog_pow`, then run `ℚ_[p]`-scalar algebra
    (`Nat.cast_smul_eq_nsmul`, `smul_smul`, `field_simp`). Per the Phase-6b heuristics this is
    "multiple `have`s with non-trivial reasoning between" = **a proof, not a composition** — and every
    primitive (`extLog`, `padicLog`, `padicLog_mul`, `extLog_eq_of_witness`, `InExpBall`) is
    project-local and missing from mathlib.

Conclusion: **NOT-COMPOSABLE.** The additivity of the extended p-adic logarithm is a genuine
multi-step proof over an entire stack of project-local, mathlib-absent primitives; it is not a
1–3 mathlib-call glue.

---

## Verdict: `PadicLFunctions.extLog_mul`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the additivity `extLog(xy)=extLog x+extLog y` **is the defining /
  characterising property** of the extended Iwasawa logarithm — "log : C_p^× → C_p is the **unique
  group homomorphism** with log_p(p)=0", additivity holding on the **whole** `C_p^×` (Wikipedia
  verbatim, MIT 18.785, K. Conrad/Stoll, World Scientific, arXiv:1907.06437/2410.20934). Stated over
  `ℂ_p` / complete nonarchimedean char-0 fields, **not** restricted to `ℚ_p`-algebras.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 1 base-generality weakening
  (drop `[NormedAlgebra ℚ_[p] L]` for `[CharZero K]`, `m⁻¹ ∈ K`), inherited from `extLog`/`padicLog`.
  The `ExtLogDomain` hypotheses are the natural domain (not an extra narrowing); the exp-ball-vs-log-ball
  point is inherited. Phase 4c agrees and adds the `map_mul`-of-a-bundled-`MonoidHom` idiom.
- Mathlib search (Phase 5): **not in mathlib** under either form; the entire mathlib `log_mul`/`log`-hom
  inventory is archimedean / discrete / formal — there is **no** nonarchimedean log, hence no additivity
  law and no bundled homomorphism for one.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine multi-step proof over a stack of
  project-local, mathlib-absent primitives (`extLog`, `padicLog`, `padicLog_mul`, the witness machinery).

**Rationale (1–2 paragraphs):**

`extLog_mul` is the **additivity (homomorphism) law of the extended Iwasawa logarithm** —
`log_p(xy)=log_p x+log_p y` — and this is not a peripheral lemma but the property the literature
*defines the extension by*: every source (the Wikipedia "p-adic exponential function" article verbatim,
the MIT 18.785 problem set, K. Conrad's and Stoll's notes, World Scientific's *Value Distribution in
p-adic Analysis*, the modern arXiv principal-units papers) states that the extended `log_p` is the
**unique continuous group homomorphism** `C_p^× → (C_p,+)` with `log_p(p)=0`, with additivity holding
on the **whole** multiplicative group and kernel `p^ℚ·μ_∞`. Mathlib has **no nonarchimedean logarithm of
any kind** (only archimedean `Real`/`Complex`/`ENNReal` logs, discrete `Nat`/`Int`/`WithZero` logs, the
formal `PowerSeries.log`, and the archimedean bundled `Complex.expHom`/`ENNReal.logHomeomorph`), so it
has neither `extLog` nor its additivity. The lemma is genuine, load-bearing API: 3 applications across
`ResidueZeta.lean` and `ValuesAtOne.lean`, and it is the literal backbone of `extLog_prod` (Finset
additivity = iterated `extLog_mul`) and `extLog_neg` (the `μ_2 ⊂ μ_∞` kernel fact), with no inline
re-derivation anywhere. Phase 6 confirms NOT-COMPOSABLE: the proof is a genuine product-witness
construction plus a reduction to `padicLog_mul`/`padicLog_pow` and `ℚ_[p]`-scalar algebra, over an entire
stack of project-local primitives that mathlib lacks.

The verdict is **not** `YES-add-as-is` because Phase 4b found the Lean form **strictly narrower than the
literature standard**, on the very same base-field axis already flagged for its parent `extLog` and base
`padicLog` (both `YES-but-generalise-first`): it gratuitously assumes `[NormedAlgebra ℚ_[p] L]` and takes
`m⁻¹` (and, through `padicLog`, the `1/n`) in `ℚ_[p]`, whereas the additivity of the extended Iwasawa log
needs only a complete nonarchimedean **char-0** field — the literature states it over `ℂ_p` and arbitrary
such fields, never restricting to `ℚ_p`-algebras. (The `ExtLogDomain p x ∧ ExtLogDomain p y` hypotheses
are *not* an additional narrowing: they faithfully restrict to the domain on which `extLog` is even
defined — off-domain `extLog=0` is junk and additivity cannot hold there — and over `ℂ_p` they are
vacuous, recovering the literature's "on all of `C_p^×`" form exactly.) Crucially, `extLog_mul` is an
identity *about* `extLog` and is proven *through* `padicLog_mul`, so it **cannot be generalised
independently** — it must ride on the `extLog`/`padicLog` generalisation. Per the skill's verdict gate, a
known weakening forces `YES-but-generalise-first`, not `YES-add-as-is`; and cost (MODERATE, sequenced
behind the `padicLog`/`extLog` generalisation) is explicitly **not** a downgrade factor.

**Reason for the generalisation:**
  - **LITERATURE-WEAKENING (primary):** Phase 4b found the user's form strictly narrower than the
    literature-standard form — the redundant `ℚ_[p]`-algebra assumption (the additivity holds over any
    complete nonarchimedean char-0 field; the literature states it over `ℂ_p`).
  - **MODERN-IDIOM (secondary, same direction):** Phase 4c — `extLog_mul` is canonically the
    `map_mul`/`map_add` of the extended log bundled as a **`MonoidHom (domain subgroup ≤ Kˣ) → (K,+)`**.
    The literature's headline statement *is* "`log_p` is the unique continuous homomorphism `K^× → K` with
    `log_p(p)=0`"; the bundled form makes `extLog_mul` the structure field (and `extLog_prod`/`extLog_neg`
    become `map_prod`/kernel lemmas for free). `ExtLogDomain.mul` already half-proves the domain is a
    subgroup.

  Proposed restatement:
  ```lean
  variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

  /-- Additivity of the extended (Iwasawa-branch) p-adic logarithm on its rational-valuation
  domain: `extLog (x * y) = extLog x + extLog y`. The homomorphism law of `log_p`. -/
  theorem extLog_mul {p : ℕ} [Fact p.Prime] {x y : K}
      (hx : ExtLogDomain p x) (hy : ExtLogDomain p y) :
      extLog p (x * y) = extLog p x + extLog p y := …
  ```
  (the only change from the current statement is `[NormedAlgebra ℚ_[p] L]` → `[CharZero K]`, `m⁻¹ ∈ K`);
  ideally re-packaged so this *is* the `map_mul` field of `extLog : (domain subgroup of Kˣ) →* (Additive K)`
  per Phase 4c rows 3–4.

  Estimated cost of regeneralisation: **MODERATE** — the statement is a near-mechanical typeclass rewrite,
  but it is *sequenced behind* generalising `padicLog` and `extLog` (`extLog_mul` is proven *through*
  `padicLog_mul`/`padicLog_pow`/`extLog_eq_of_witness`, all of which must first sit on the `CharZero`-field
  setting). The `ℚ_[p]`-scalar algebra step re-runs straightforwardly once `m⁻¹ ∈ K`. EXPENSIVE/MODERATE
  does **not** downgrade the verdict.

  Mathlib downstream this enables:
  - the single general `extLog_mul` serves `ℚ_p`, finite extensions, and `ℂ_p` uniformly as the additivity
    of the canonical extended Iwasawa logarithm — the off-ball companion to a generalised `padicLog_mul`;
  - if bundled, `extLog_mul` becomes `map_mul`, giving `map_prod` (= `extLog_prod`), `map_pow`, and
    kernel/range lemmas (the `μ_∞`/`p^ℚ` kernel) **for free** from mathlib's `MonoidHom`/`Subgroup` API,
    instead of the project's bespoke `extLog_prod`/`extLog_neg` re-proofs;
  - it gives mathlib the canonical statement of "the unique homomorphic extension of `log_p` with
    `log_p(p)=0`" — a fact downstream p-adic L-function / Iwasawa-theory work (this project's
    `ResidueZeta.lean`/`ValuesAtOne.lean`) repeatedly needs.

  Proposed mathlib location (post-generalisation): ship **together with** the generalised `padicLog`/
  `extLog` (and `padicExp`/`InExpBall`) as one coherent "p-adic exponential and logarithm" contribution —
  e.g. `Mathlib/NumberTheory/Padics/Logarithm.lean` (new), with `extLog_mul` as the additivity/`map_mul`
  of the extended branch (or of the bundled `Padic.iwasawaLog`). **PR grouping (required):** do **not**
  upstream `extLog_mul` in isolation — it ships with `padicLog`, `padicLog_mul`, `extLog`,
  `extLog_witness_smul_eq`, `extLog_prod` (all sibling `YES-but-generalise-first`/supporting) as one package.

  Pre-PR checklist before opening:
    - [ ] `/generalise PadicLFunctions.extLog_mul` — confirm the `CharZero`-field restatement and the
          `map_mul`-bundling, after first generalising `padicLog` then `extLog` (its prerequisites).
    - [ ] `/cleanup projects/PadicLFunctions/PadicLFunctions/ExtLog.lean extLog_mul` — full audit + diff gates.
    - [ ] Pick a mathlib reviewer from `Mathlib/NumberTheory/Padics/` recent commits; announce the
          p-adic-exp/log package on the `#mathlib4` Zulip.

  Next action: **run `/generalise PadicLFunctions.extLog_mul`** (it will tension against both the
  literature-standard homomorphism form from Phase 3 and the modern-idiom bundled-`MonoidHom` form from
  Phase 4c) — **after** first generalising `padicLog` and `extLog` (its prerequisites; see `padicLog.md`
  and `extLog.md`). Then `/cleanup` `ExtLog.lean` and open the mathlib PR grouping `padicExp` + `padicLog`
  + `padicLog_mul` + `extLog` + `extLog_mul` + `extLog_prod` + `InExpBall` as one coherent contribution.

---

## Next step

Run `/generalise PadicLFunctions.extLog_mul` to restate it over a complete nonarchimedean `CharZero`
field `K` (dropping `[NormedAlgebra ℚ_[p] L]`, taking `m⁻¹ ∈ K`), and ideally bundle the extended log as
the `MonoidHom (domain subgroup of Kˣ) → (K,+)` whose `map_mul` this is — exactly the "unique continuous
homomorphism `K^× → K` with `log_p(p)=0`" the literature characterises `log_p` by. This is **sequenced
behind** generalising `padicLog` then `extLog` (`extLog_mul` is proven through `padicLog_mul` and is an
identity about `extLog`). Then `/cleanup` `ExtLog.lean` and open a single mathlib PR grouping the whole
p-adic exponential/logarithm core (`padicExp` + `padicLog` + `padicLog_mul` + `extLog` + `extLog_mul` +
`extLog_prod` + `InExpBall`), with the bundled-homomorphism `extLog_mul`/`map_mul` as the headline
additivity law.
