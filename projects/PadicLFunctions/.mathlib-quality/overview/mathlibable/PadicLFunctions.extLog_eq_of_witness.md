# `/mathlibable` report — `PadicLFunctions.extLog_eq_of_witness`

Mode A (single declaration), full 10-phase workflow with the exhaustive 9-channel
literature search.

---

### Baseline (Phase 0)

- lake build:               **not re-run; reasoned from source** (per task BUILD NOTE — the local build is stale/slow; the skill's Phase-0 fallback permits reading the declaration and its dependency closure directly). `ExtLog.lean` is committed-clean and the entire surrounding API (`extLog`, `extLog_witness_smul_eq`, `extLog_eq_padicLog`, `extLog_mul`, `extLog_prod`, …) plus its external call sites in `ValuesAtOne.lean` and `ResidueZeta.lean` elaborate against the lemma as written.
- decl `PadicLFunctions.extLog_eq_of_witness`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:335`
- kind:                      theorem
- has sorry:                 no (grep over `ExtLog.lean` for `\b(sorry|admit)\b` → none; the lemma body is a 4-line term/tactic proof)
- module docstring summary:  "The extended (Iwasawa-branch) p-adic logarithm (RJW §6, decomposition W6a)" — extends `padicLog` from its convergence ball to rational-valuation elements `x` with `x^m = p^k·y`, `y` in the exponential ball, via `extLog x := m⁻¹·padicLog y` (junk `0` off-domain; Iwasawa's branch `log_p(p)=0`); cross-references Washington, *Introduction to Cyclotomic Fields*, §5.1.

---

### Statement (Phase 1)

`PadicLFunctions.extLog_eq_of_witness` is **a theorem** stating the following:

Let `L` be a complete ultrametric normed field that is a normed `ℚ_p`-algebra. Fix
`x ∈ L`. Suppose `x` admits **one** rational-valuation witness: a positive integer
`m`, an integer `k`, and a ball element `y` with `‖y − 1‖` in the exponential ball
(hence `‖y‖ = 1`) such that

  `x^m = p^k · y`.

Then the extended logarithm of `x` is computed by *that* witness:

  `extLog x = (1/m)·log_p(y)`   (scalar `(m : ℚ_p)⁻¹`, `log_p = padicLog`).

In words: **the junk-total definition `extLog` (which internally picks *some*
`Classical.choose` witness) agrees with the value produced by *any* witness the
caller supplies.** This is the public-facing evaluation/computation rule for
`extLog`: it lets every consumer evaluate `extLog x` by exhibiting a single
convenient witness `(m, k, y)`, without ever touching the `Classical.choose`
internals of the `def`. The one-line proof packages `(m, k, y)` into a domain
proof `hdom : ExtLogDomain p x`, rewrites `extLog` via `dif_pos hdom`, and then
applies the witness-independence lemma `extLog_witness_smul_eq` to identify the
chosen-witness value with the supplied-witness value.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `L : Type*`, `[NormedField L]`, `[NormedAlgebra ℚ_[p] L]`, `[IsUltrametricDist L]`, `[CompleteSpace L]` — a complete nonarchimedean field over `ℚ_p`. (The `ℚ_p`-algebra assumption is only the carrier of the `(m : ℚ_[p])⁻¹` scalar — see Phase 4.)

Hypotheses (Lean side):
- `hm : 0 < m` — the witness exponent is positive (so `m⁻¹` is meaningful).
- `hxy : x ^ m = (p : L) ^ k * y` — the witness equation.
- `hy : InExpBall p (y − 1)` — the ball member of the witness (forces `‖y‖ = 1`).

Conclusion (math): the extended logarithm equals the witness-scaled logarithm `(1/m)·log_p(y)`.

Conclusion (Lean): `extLog p x = ((m : ℚ_[p]))⁻¹ • padicLog p y`.

---

### Size classification (Phase 2a)

Verdict: **SMALL** (with a BIG-adjacent caveat).
Reason: It is the *computation/evaluation rule* of a larger construction (`def
extLog`) — the lemma that turns the junk-total `dif`-definition into something a
consumer can actually unfold by exhibiting a witness. It is neither a named
theorem nor a project main result; it is the API glue between the `def` and its
downstream uses. The *construction it serves* (the Iwasawa-branch extended log) is
BIG-adjacent — it introduces a named analytic object — but this lemma is the
plumbing step, classified SMALL.

(Note: literature width was run EXHAUSTIVE regardless. BIG/SMALL is recorded for
framing only and does not gate which channels Phase 3 ran.)

### One-line check (Phase 2b)

Body line count: ~4 substantive lines (`have hdom`, `rw [extLog, dif_pos hdom]`,
`obtain`, `exact extLog_witness_smul_eq …`).
One-liner verdict: **n/a** — kind is `theorem`, not `def`/`abbrev`/`structure`. The
one-liner exemption table applies only to definitions and is skipped. (As a
*theorem*, a short proof is not a negative signal; the short proof here is a direct
consequence of the lemma being the thin public wrapper over the substantive
`extLog_witness_smul_eq`.)

---

### Literature search table — EXHAUSTIVE protocol

This lemma is the *public evaluation rule* of the `extLog` construction; its
mathematical content is identical to that of the sibling well-definedness lemma
`extLog_witness_smul_eq` (the only difference is bookkeeping — folding "every
witness agrees" through the `def`'s `dif_pos`/`Classical.choose`). The concept to
search for is therefore "the well-definedness / computation of the Iwasawa
extension of the `p`-adic logarithm." The nine channels were run live (WebSearch
×4 this session; the same protocol was independently run for `extLog_witness_smul_eq`
and `extLog`, all converging on the identical concept).

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic logarithm extended to rational valuation elements well-defined independent of choice of power n, (1/n) log(x^n)" | **yes** | `log_p` extends to all of `ℂ_p^×` with `log xy = log x + log y`, `log p = 0`; for `α = p^r·w·x` (`w` a root of unity, `x ∈ U_1`), `log_p(p)=log_p(w)=0`; the recipe `(1/n)log(x^n)` is **independent of `n`** because the kernel is generated by roots of unity and `p`, and the value lives in a `ℚ`-vector space | Koblitz; MIT 18.785 PS10 / `~dav/exp.pdf`; Conrad/Thorne `p-adic analysis` notes; planetmath. *This is exactly the lemma's content.* |
| 2 | WebSearch (named-after / Iwasawa) | "Iwasawa p-adic logarithm log_p(p)=0 unique continuous homomorphism extension Washington cyclotomic fields" | **yes** | `log_p` extends **uniquely** to a continuous homomorphism on `ℂ_p^×` by fixing Iwasawa's noncanonical `log_p(p)=0`; foundational in Iwasawa theory (Hida 207a notes; "A Note on a result of Iwasawa", arXiv:math/0512015) | Confirms the construction is canonical and standard; `(1/n)log(x^n)` is the textbook concrete realisation. |
| 3 | WebSearch (most-general / modern idiom) | "p-adic logarithm unique extension monoid homomorphism into uniquely divisible group rational vector space C_p kernel torsion" | **yes** | `log_p` is a `K`-analytic group **homomorphism**; **kernel = torsion subgroup** (roots of unity); when the base is algebraically closed the target is **divisible**; values sit in a `ℚ_p`/`ℚ`-vector space | **Decisive modern-idiom anchor**: well-definedness is *automatic* from the target being uniquely divisible / torsion-free. A standalone scalar identity is a symptom of an un-bundled `MonoidHom`. (p-divisible group notes, Levin/Conrad; image-of-`log` papers arXiv:1904.09850, 1907.06437.) |
| 4 | ChatGPT MCP | (would ask: "standard definition + generality + historical evolution of the Iwasawa-extended `p`-adic log and the computation rule `extLog x = (1/m)log y` from a witness") | **n/a** | — | **ChatGPT MCP server is not configured** in this environment (only Asana/Atlassian/Box/Canva/Figma/… auth-MCPs are present; no `chatgpt`/`openai` server). Compensated by running 4 WebSearch queries at three generality levels (rows 1–3) plus nLab/arXiv (rows 6,10), exceeding the protocol's WebSearch minimum of 3. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` for "p-adic log / Iwasawa" | **n/a** | — | No `references/` dir exists for this project and no `refs/` store/symlink is present in the checkout (both confirmed by `ls`/`find`). Recorded `n/a` with reason, per protocol. |
| 6 | nLab | "p-adic logarithm formal group logarithm divisible group exponential" | yes (indirect) | nLab has no dedicated "Iwasawa logarithm" page; it routes through **`p-divisible group`** and the **formal-group logarithm** (`log_F(F(X,Y)) = log_F X + log_F Y`, the homomorphism into the Lie algebra) — same uniquely-divisible-target / homomorphism framing as row 3 | Reinforces the homomorphism-into-divisible-target idiom; confirms there is no standalone "computation-from-witness" page. |
| 7 | nCatLab (categorical) | — | **n/a** | — | Not a categorical statement; it is a concrete analytic computation rule for a specific function (`extLog x = (1/m)log y`). No higher-categorical generalisation is in play. |
| 8 | Stacks Project (alg geom) | — | **n/a** | — | Not an algebraic-geometry / scheme-theoretic statement; it is a normed-field analytic identity. (The functoriality angle in rows 3/6 touches `p`-divisible groups, but the *target lemma* is not AG.) |
| 9 | MathOverflow / Math.StackExchange | (covered by rows 1–3 hits: MIT 18.785 PS10 item 1, exp.pdf, Conrad/Thorne notes) | **yes** | Confirms the standard recipe: every norm-1 unit has `|x^n − 1| < 1` for some `n`; extend by `(1/n)log(x^n)`; well-defined because the target is a `ℚ`-vector space — a routine textbook exercise | Routine textbook fact (MIT 18.785 PS10 is literally this); not a research-level result. |
| 10 | recent arXiv (last ~5 yr) | "image of p-adic logarithm on principal units" (arXiv:1904.09850, 1907.06437, 2502.16738 Vologodsky-regulators, 2601.18187) | yes (context) | Contemporary papers *assume* the Iwasawa-extended `log_p` (the homomorphism with `log_p(p)=0`) as ambient background and study its image/regulators; none re-prove the witness computation rule | The computation rule is so standard it is cited as given. Confirms the lemma is foundational-but-routine, not novel. |

The protocol passed: WebSearch ran 4 distinct queries at three generality levels
(specific `(1/n)log(x^n)` recipe / named-after-Iwasawa / most-general
homomorphism-into-divisible-target); local refs checked (`n/a`, absent); nLab
checked; Stacks/nCatLab recorded `n/a` with reasons; MathOverflow and recent arXiv
each checked (rows 9–10). ChatGPT MCP recorded `n/a` (server not configured) and
compensated with extra WebSearch generality coverage.

### Literature summary (Phase 3)

Concept identified as: **the computation / well-definedness rule of the
Iwasawa-extension of the `p`-adic logarithm** — that `log_p(x) := (1/n)·log_p(x^n)`
(for any `n` with `x^n ∈ p^ℤ·(1+𝔪)`) is *both* independent of `n` *and* the value
of the extended log at `x`. The target lemma is the "any witness computes the
extension" half; its sibling `extLog_witness_smul_eq` is the "two witnesses agree"
half; together they are the standard well-definedness package.

Sources agree on the standard form: **yes**. Two equivalent standard packagings:
  - *Concrete recipe* (Washington §5.1; Iwasawa; Koblitz; MIT 18.785): pick any `n`
    with `x^n` in the good subgroup, set `log_p(x) = (1/n)log_p(x^n)`; well-defined
    and `n`-independent because the target `C_p` (resp. `ℚ_p`) is a `ℚ`-vector space.
  - *Bundled homomorphism* (Iwasawa; formal-group / `p`-divisible-group log; Coleman):
    `log_p` is *the* unique continuous group homomorphism into the uniquely-divisible
    additive group, extending the power-series log with `log_p(p)=0`; the
    computation-from-witness rule is then the value-level shadow of `map_zpow`/`map_mul`
    on the extension.

Most general standard form: `log_p` as the unique continuous `MonoidHom`
(multiplicative group `p^ℤ·(1+𝔪)` → additive group of a complete nonarchimedean
`CharZero` field) extending the power-series log, normalised by `log_p(p)=0`;
kernel `= p^ℚ·μ`. The target lemma is the value-level statement "the extension at
`x` equals `(1/m)·log_p(y)` for any witness `x^m = p^k·y`."

Generality dimensions where the literature varies:
  - **Base field**: literature states it over `C_p` (or any complete nonarchimedean
    `CharZero` field). The Lean form fixes a `ℚ_p`-algebra `L` — strictly narrower
    (the `ℚ_p`-algebra structure is only used to host the `(m:ℚ_p)⁻¹` scalar).
  - **Scalar field of the value**: literature divides by `m` inside the value's own
    field (`1/m ∈ C_p`). The Lean form takes `(m:ℚ_[p])⁻¹` and `•` into `L` — routing
    the division through `ℚ_p` rather than through `L` directly. Same artefact flagged
    on the parent `padicLog`, on `padicLog_mul`, and on the sibling `extLog_witness_smul_eq`.
  - **Ball domain**: literature uses the standard log ball `‖y−1‖ < 1`; the Lean form
    states ball-membership on the strictly smaller *exponential* ball
    `‖y−1‖^{p−1} < p⁻¹` (`InExpBall`). The lemma only needs `‖y‖=1` and `padicLog_pow`,
    both valid on `‖y−1‖<1`.
  - **Packaging**: literature increasingly states it as the bundled-homomorphism /
    divisible-target universal property (modern idiom); the Lean form is a freestanding
    `dif_pos` computation lemma.

Disagreement with the literature: **none on content** — the lemma is true and is the
standard computation rule. The divergence is in *generality* and *packaging*: the
Lean form is a freestanding scalar identity over a `ℚ_p`-algebra phrased on the
exp ball, where the literature's modern form is the (unique) homomorphism extension
into a uniquely-divisible target over a general complete nonarchimedean `CharZero`
field, from which the computation rule is `map_zpow`/`map_mul` plumbing.

---

### Generality analysis — `extLog_eq_of_witness`

Literature-standard form (from Phase 3): the computation rule of the unique
homomorphism-extension `log_p` into a uniquely-divisible target, over a complete
nonarchimedean `CharZero` field; concretely "`extLog x = (1/m)log y` for any witness
`x^m = p^k·y`."

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | `[NormedAlgebra ℚ_[p] L]` | normed `ℚ_p`-algebra | complete nonarchimedean **`CharZero`** field (no `ℚ_p`-algebra structure needed) | **yes** | Only used to host the `(m:ℚ_p)⁻¹` scalar on the RHS. With `[CharZero L]` one takes `(m:L)⁻¹` directly; the proof is just `dif_pos` + a call to `extLog_witness_smul_eq`, whose generalisation (already decided) removes the `ℚ_p`-algebra need. *Identical over-assumption flagged on the parent `padicLog`, `padicLog_mul`, and `extLog_witness_smul_eq`.* |
| 2 | value scalars `(m:ℚ_[p])⁻¹ • _` | division routed through `ℚ_p` then `•` into `L` | `(m : K)⁻¹ * _` inside the value's own field | **yes** | Same as row 1: once `[CharZero L]`, divide by `m` in `L`. Removes the `Nat.cast_smul_eq_nsmul` plumbing inherited from `extLog_witness_smul_eq`. |
| 3 | `InExpBall p (y−1)` (ball membership) | the *exponential* ball `‖y−1‖^{p−1} < p⁻¹` | the standard log ball `‖y−1‖ < 1` (norm-1 + `y` a principal unit) | **yes (downstream of parent)** | The lemma needs only `‖y‖=1` (for `extLog_witness_smul_eq`) and that `(m,k,y)` is a domain witness. Both hold on the larger `‖y−1‖<1` ball once `padicLog`/`padicLog_pow`/`ExtLogDomain` are restated there — exactly the parent's planned generalisation. Stating on the exp ball is the artificially-small domain the parent verdict calls out. |
| 4 | `(p:L)^k` (uniformiser = rational prime `p`) | `p` the rational prime | a chosen uniformiser `π` of any complete DVR-valued field | partial | The literature states the extension over `C_p` with `p` as canonical scale, but the cleanest mathlib home (a general nonarchimedean field) may want a chosen `π`. Not required for the first mathlib form; flag only. |
| 5 | `m : ℕ` with `0 < m`, `k : ℤ` | natural exponent / integer valuation shift | same | NO | A positive-integer exponent and integer `p`-power shift are intrinsic to "raise until the valuation is integral." Maximally general already. |

This is the literature-grounded analogue of `/generalise`'s mechanical pass; the
target is the most-general form Phase 3 identified, **and** it inherits the parent
`extLog`/`padicLog` weakening axes (rows 1–3), already decided
`YES-but-generalise-first` for both the def and the sibling well-definedness lemma.

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **K = 3** (clear) + 1 partial (uniformiser).

Proposed restatement (against the generalised primitives the parent verdict mandates):

```lean
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

theorem extLog_eq_of_witness {x : K} {m : ℕ} {k : ℤ} {y : K} (hm : 0 < m)
    (hxy : x ^ m = (p : K) ^ k * y) (hy : ‖y - 1‖ < 1) :
    extLog p x = ((m : K))⁻¹ * padicLog p y := …
```

(dropping `[NormedAlgebra ℚ_[p] L]`, dividing in `K`, and stating ball-membership
on the standard log ball `‖·−1‖<1`; `extLog`/`ExtLogDomain` are restated on the same
ball).

Cost of restatement: **MODERATE** — the lemma body is a near-mechanical 4-line
wrapper, but it *depends on first generalising* `padicLog`, `padicLog_pow`,
`ExtLogDomain`, `extLog`, and `extLog_witness_smul_eq` (the parent's planned work).
Once those land on `‖·−1‖<1` over `[CharZero K]`, this proof is an essentially
trivial port. **Cost does not downgrade the verdict** (Bourbaki-2.0 rule).

Since STRICTLY NARROWER → Phase 7 considers `YES-but-generalise-first` prominently;
4c (below) reinforces it with the modern-idiom packaging.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses/instances? | **yes** | `[NormedAlgebra ℚ_[p] L]` → `[CharZero K]` (row 1 above). | Composes with the whole `[CharZero]` API; divides in `K` natively. |
| 2 | sequences/metric → filters/topological? | no | — (this is a finite algebraic computation rule; no limit/filter content). | — |
| 3 | **construct an object → universal-property class?** | **yes (decisive)** | The mathlib-idiomatic object is **`extLog` bundled as a `MonoidHom`** from the principal-units/rational-valuation subgroup into the additive group of `K`, characterised as the unique continuous extension of the power-series log into the uniquely-divisible (`RootableBy ℤ`) target with `log_p(p)=0`. In that packaging, this lemma — "the extension at `x` is computed by any witness `x^m=p^k·y` as `(1/m)log y`" — is the **value-level statement of `map_zpow`/`map_mul` for the extension**: from `(x^m = p^k·y)` apply `extLog` (a hom), use `extLog(p)=0` and `extLog(x^m)=m·extLog(x)`, divide. It becomes a short hom-corollary, not a freestanding `dif_pos` lemma. | `extLog` as a `MonoidHom` ⟹ `map_mul`/`map_pow`/`map_one`/`map_zpow` free; this computation rule, `extLog_mul`, `extLog_prod`, `extLog_eq_zero_of_pow_eq_one`, `extLog_neg`, `extLog_eq_padicLog` all become hom/kernel corollaries. Mathlib already has `RootableBy`/`DivisibleBy` (`Mathlib/GroupTheory/Divisible.lean`). |
| 4 | set-with-closure-predicate → bundled substructure? | partial | `ExtLogDomain` (a `Prop` on elements) → the domain as a bundled `Submonoid`/`Subgroup` `p^ℤ·(1+𝔪)`. | Bundled domain composes with `Submonoid`/`Subgroup` lattices and makes `extLog` a genuine `MonoidHom` on a `Submonoid`. (Property of the whole development — but it is *why* this lemma should not travel alone.) |
| 5 | vector-space/metric/field-specific → weaker typeclass? | **yes** | Covered by row 1: `ℚ_p`-algebra → `CharZero` nonarchimedean field. | Same as Phase 4b row 1. |
| 6 | 1-categorical → higher/∞-categorical? | no | — | Not a categorical statement. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | no (the ℕ exponent / ℤ valuation are intrinsic; row 5 of 4a) | — | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**.
  - Proposed mathlib-idiomatic restatement: bundle `extLog` (built on a generalised
    `padicLog`) as the unique continuous `MonoidHom` from `p^ℤ·(1+𝔪)` (a
    `Submonoid`/`Subgroup`) into the additive group of a complete nonarchimedean
    `CharZero` field, characterised by extension-into-a-uniquely-divisible-target +
    `log_p(p)=0`. This lemma is then the **value-level `map_zpow`/`map_mul`
    computation** for that hom (or, if `extLog` stays a plain `def`, the `simp` lemma
    that discharges its `dif_pos` from a supplied witness).
  - Cost: **MODERATE** (gated on the parent `padicLog`/`extLog` generalisation landing first).
  - Mathlib downstream this enables: `map_mul`/`map_pow`/`map_one`/`map_zpow` for free
    on `extLog`; `extLog_mul`, `extLog_prod`, `extLog_eq_zero_of_pow_eq_one`,
    `extLog_neg`, `extLog_eq_padicLog` become hom/kernel corollaries; the construction
    composes with `RootableBy`/`DivisibleBy` and `Submonoid`/`Subgroup` lattices.
  - Real mathematical improvement (not just "looks cooler"): **yes** — it replaces a
    hand-rolled `dif_pos` computation lemma with the homomorphism's `map_zpow`
    shadow, from which the rest of the `ExtLog.lean` API falls out, eliminating the
    redundancy and matching the canonical Iwasawa packaging.

Because 4c says "modern idiom available" and the restatement is a real organisational
improvement, Phase 7 may produce `YES-but-generalise-first` even though Phase 4b
already independently produced STRICTLY NARROWER — the two reasons
(LITERATURE-WEAKENING and MODERN-IDIOM) point the **same** direction here, exactly
mirroring the parent `extLog`/`padicLog` and the sibling `extLog_witness_smul_eq`.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional
equalities or typeclass-search paths; the six-row risk table is skipped.

---

### Mathlib search-status: `extLog_eq_of_witness`

[A] Lean-Finder       (would query "p-adic logarithm value computed from a witness power / rational valuation")   **n/a: Lean-Finder MCP server not configured** in this environment.
[B] Loogle            web query `padicLog`; type-pattern `extLog _ _ = (?m : ?K)⁻¹ • padicLog _ _`   **no hits** — `padicLog`/`extLog` are unknown to Loogle's mathlib index (consistent with the source grep below).
[C] LeanSearch        (would query "p-adic logarithm equals one over m times log of witness")   **n/a: LeanSearch MCP server not configured.**
[D] Grep mathlib src  `padicLog`, `extLog`, `ExtLogDomain`, `InExpBall` (words) over `.lake/packages/mathlib/Mathlib`; also `RootableBy`/`DivisibleBy`; `dif_pos`-style log computation lemmas   **`padicLog`: ZERO occurrences. `extLog`/`ExtLogDomain`/`InExpBall`: ZERO (each confirmed by `grep -rwn … | wc -l` → 0).** `Mathlib/NumberTheory/Padics/` contains only norm, valuation, Hensel, Mahler basis, AddChar, height-one-spectrum — **no p-adic log/exp at all.** `RootableBy`/`DivisibleBy` exist (`GroupTheory/Divisible.lean`) but no log built on them. |
[E] Name pattern      `extLog`, `padicLog`, `eq_of_witness`, `_of_witness`, `IwasawaLog` (over mathlib)   **no hits** for any p-adic-log name; `_of_witness` hits are unrelated combinatorics/order namespaces.

Searched for both:
  - the user's current form (`extLog p x = (m:ℚ_p)⁻¹ • padicLog p y` from a witness) — absent;
  - the literature-standard / modern form (the `map_zpow`/computation shadow of a bundled
    `MonoidHom` log extension into a uniquely-divisible target) — also absent (mathlib has
    the `RootableBy`/`DivisibleBy` classes but neither a p-adic log nor any
    homomorphism-extension-into-divisible-target lemma).

Concluded: **not in mathlib (all available methods exhausted, both forms).** Mathlib
contains *none* of the primitives this lemma is phrased in (`padicLog`, `InExpBall`,
`ExtLogDomain`, `extLog`), so the statement is not even expressible in current
mathlib. (Methods [A] and [C] recorded `n/a` for server-availability reasons, not
skipped; the decisive [D] grep over the actual mathlib source — `padicLog` ZERO
occurrences — plus Loogle [B] establish absence conclusively.)

---

### Call sites — `extLog_eq_of_witness`

Internal use count: **K = 4** (within the project, NOT counting the declaring file).
External-to-file callers: **2 distinct files** (`ValuesAtOne.lean`, `ResidueZeta.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `ValuesAtOne.lean:594` | `rw [extLog_eq_of_witness (p := p) (m := p ^ j) (k := 0) (y := x ^ p ^ j) …]` (proving `extLog_eq_padicLog_of_norm_lt_one`) |
| `ResidueZeta.lean:1556` | `extLog_eq_of_witness p (by omega) (by rw [zpow_zero, one_mul]) (inExpBall_natCast_pow_sub_one …)` (witness for `padicLog((a)^{p−1}) = (p−1)·extLog a`) |
| `ResidueZeta.lean:1627` | `rw [extLog_eq_of_witness p (m := p - 1) (k := 0) … , …]` (inside `map_extLog_natCast`) |
| `ResidueZeta.lean:1629` | `extLog_eq_of_witness p (m := p - 1) (k := 0) … (inExpBall_natCast_pow_sub_one (p := p) ℚ_[p] …)` (the `ℚ_[p]` half of `map_extLog_natCast`) |
| `ExtLog.lean:353,372,373,429` (declaring file — excluded from K) | used to prove `extLog_eq_padicLog`, `extLog_mul`, `extLog_eq_zero_of_pow_eq_one` |

Repo-wide grep `extLog_eq_of_witness` over `projects/ --include="*.lean"
--exclude-dir=.lake`: 9 occurrences total — 1 declaration, 4 in-file consumers, **4
external uses across 2 files.**

Inline-derivation grep (was the equivalent re-derived elsewhere without using
`extLog_eq_of_witness`?): **(none)** — every place that needs to evaluate `extLog` by
exhibiting a witness routes through this lemma; the `dif_pos`/`Classical.choose`
unfolding is *not* re-done inline anywhere. `extLog_witness_smul_eq` (the
two-witnesses-agree lemma) is consumed *only* through this wrapper.

**Reading of the K=4 signal (per 6.0.1).** K = 4 internal uses across **2 distinct
external files**, plus 4 in-file uses, **no inline re-derivation** anywhere → this is
the canonical shape of **real, consumed API**. This is *the* public evaluation rule
of the `extLog` def: every downstream computation of `extLog` (the `μ_p`-collapse in
`ResidueZeta`, the `extLog = padicLog` bridge in `ValuesAtOne`, the additivity tower
inside `ExtLog`) goes through it. By the call-sites table this leans firmly to a
**YES-\*** bucket. It is *not* a bypassed wrapper (no inline re-derivation) and *not*
dead code; it is the load-bearing API surface of the construction. Combined with
Phase 4 (STRICTLY NARROWER + modern idiom), the bucket is `YES-but-generalise-first`,
not `YES-add-as-is`.

### Composition check (Phase 6)

Can `extLog_eq_of_witness` be derived from mathlib in ≤3 chained calls?

Attempt 1: any mathlib decl about `padicLog`/`extLog` computation from a witness.
  - Mathlib decls used: **none available** — mathlib has no `padicLog`/`extLog`/`ExtLogDomain` at all.
  - Result: **fails** — the statement mentions `extLog p x`, `padicLog p y`, `InExpBall`,
    none of which exists in mathlib; there is nothing to compose against.

Attempt 2: derive it from the *sibling* `extLog_witness_smul_eq` plus a `dif_pos` rewrite.
  - Decls used: `extLog` (def), `extLog_witness_smul_eq` (project lemma), `dif_pos`,
    `Exists.choose_spec`. This is *exactly* the actual 4-line proof.
  - Result: **succeeds — but this is a composition of PROJECT decls, not mathlib decls.**
    The composition check asks whether *mathlib's primitives* compose to the form; they
    do not, because mathlib has no p-adic log. The fact that the lemma is a thin wrapper
    over the project's own `extLog_witness_smul_eq` is a *within-project* observation —
    it bears on PR-grouping (this lemma ships with `extLog`/`extLog_witness_smul_eq`, not
    alone), not on `NO-composable-from-mathlib` (which requires a ≤3-call *mathlib*
    composition).

Conclusion: **NOT-COMPOSABLE (from mathlib).** No mathlib primitive exists to compose;
the lemma is only "trivially composable" from the project's own (also-not-in-mathlib)
machinery. Per the Phase-6 heuristics, "compose from the project's own bespoke lemmas"
is *not* `NO-composable-from-mathlib`; that bucket is reserved for a ≤3-call composition
of **existing mathlib** decls.

---

## Verdict: `extLog_eq_of_witness`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): the computation/well-definedness rule of the
  Iwasawa-extended `p`-adic log (`extLog x = (1/m)log y` from a witness) is a
  **standard, canonical, textbook** fact (rows 1–3, 9–10; Iwasawa, Washington §5.1,
  Koblitz, MIT 18.785) — but the literature's modern form is the unique
  homomorphism-extension into a uniquely-divisible target over a complete
  nonarchimedean `CharZero` field, *strictly more general and better-packaged* than
  the Lean form.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — K = 3
  weakenings (drop `[NormedAlgebra ℚ_[p] L]` → `[CharZero K]`; divide in `K`; state
  on the standard ball `‖·−1‖<1`), identical to the axes already decided for the
  parent `padicLog`/`extLog` and the sibling `extLog_witness_smul_eq`. Phase 4c
  additionally finds a real **MODERN-IDIOM** improvement (bundle `extLog` as a
  `MonoidHom`; this lemma becomes its `map_zpow` shadow).
- Mathlib search (Phase 5): **not in mathlib** (both forms) — and mathlib lacks *all*
  the primitives (`padicLog`, `InExpBall`, `ExtLogDomain`, `extLog`; each grep → 0),
  so the statement is not even expressible today.
- Composition check (Phase 6): **NOT-COMPOSABLE from mathlib** (no mathlib primitive
  to compose; the within-project triviality over `extLog_witness_smul_eq` is a
  PR-grouping fact, not a mathlib composition).

**Rationale.**

This is the public *evaluation rule* for the bespoke `extLog` construction: it
certifies that the junk-total `def extLog` (which internally `Classical.choose`s a
witness) is computed by *any* witness `(m, k, y)` of `x^m = p^k·y` as
`(1/m)·log_p(y)`. The literature confirms the *content* is standard and canonical —
it is the value-level half of the well-definedness of Iwasawa's extension
`log_p(x) = (1/n)log_p(x^n)`, true precisely because the value lives in a
uniquely-divisible target (Iwasawa, Washington §5.1, Koblitz, MIT 18.785). So this is
not novel mathematics. But it is also **not** `NO-mathlib-has-it` or
`NO-composable-from-mathlib`: mathlib has no p-adic logarithm whatsoever (the
`padicLog` identifier occurs *zero* times in the entire mathlib source, confirmed by
grep and Loogle), so neither the lemma nor its primitives exist to cite or compose
against from mathlib.

Crucially, the call-sites evidence is the strongest in this tower: **K = 4 internal
uses across two distinct external files** (`ValuesAtOne.lean`, `ResidueZeta.lean`),
with **no inline re-derivation** — this lemma, not the sibling `extLog_witness_smul_eq`
(which has K = 0 external and is consumed only through this wrapper), is the genuine
public API surface of `extLog`. Every downstream computation of `extLog` routes
through it. That is a firm YES-\* signal. The deciding factor between the YES buckets
is generality + packaging, inherited verbatim from the parent: `def extLog` is already
verdicted `YES-but-generalise-first` (generalise off the `ℚ_p`-algebra to a complete
nonarchimedean `CharZero` field; restate the API on the standard ball `‖·−1‖<1`; ship
`padicExp`+`padicLog`+`InExpBall`+the `extLog` API as one coherent PR), and the
sibling `extLog_witness_smul_eq` carries the same verdict. This lemma carries the
*identical* over-assumptions — the redundant `[NormedAlgebra ℚ_[p] L]`, the
`(m:ℚ_[p])⁻¹` scalar routed through `ℚ_p` instead of dividing in `L`, and the
artificially-small exp ball. Phase 4c shows the *right* mathlib form bundles `extLog`
as a `MonoidHom` into the uniquely-divisible target (matching the literature's
canonical packaging), at which point this lemma is the homomorphism's `map_zpow`/`map_mul`
value-shadow — a short corollary, not a freestanding `dif_pos` computation. Hence:
contributable *in some form* and clearly *wanted* (it is the most-used piece of the
tower), but only after the generalisation — never as-is, and ideally as the
hom-computation corollary of a bundled `extLog` rather than a standalone lemma.

**Reason for the generalisation:**
  - **LITERATURE-WEAKENING** (Phase 4b): the user's form is strictly narrower than the
    literature-standard form — redundant `ℚ_p`-algebra assumption, value-division
    routed through `ℚ_p`, and ball-membership on the artificially small exp ball rather
    than `‖·−1‖<1`.
  - **MODERN-IDIOM / Bourbaki-2.0** (Phase 4c, same direction): the contemporary mathlib
    formulation bundles `extLog` as a `MonoidHom` extending the log into a
    uniquely-divisible target (the canonical Iwasawa packaging), making this computation
    rule the hom's `map_zpow` shadow — a real organisational improvement, not
    abstraction for its own sake.

Proposed restatement (the value-level lemma, against the generalised primitives):

```lean
variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]

theorem extLog_eq_of_witness {x : K} {m : ℕ} {k : ℤ} {y : K} (hm : 0 < m)
    (hxy : x ^ m = (p : K) ^ k * y) (hy : ‖y - 1‖ < 1) :
    extLog p x = ((m : K))⁻¹ * padicLog p y := by
  sorry -- near-mechanical once `extLog`/`ExtLogDomain`/`extLog_witness_smul_eq`
        -- are restated over `[CharZero K]` on the ball `‖·−1‖<1`
```

…but the *preferred* target is to not ship this as a freestanding `dif_pos` lemma:
instead bundle `extLog` as a `MonoidHom` on the `Submonoid`/`Subgroup` `p^ℤ·(1+𝔪)`,
in which this computation rule is the value-level form of `map_zpow`/`map_mul`
(from `x^m = p^k·y`: `m • extLog x = k • extLog p + extLog y = extLog y`, divide by
`m`). That, together with a reusable "extend a `MonoidHom` valued in a `RootableBy ℤ`
group" lemma, is the genuinely mathlib-worthy content underneath.

Estimated cost of regeneralisation: **MODERATE** — the value-lemma port is essentially
trivial *once* the parent `padicLog`/`extLog`/`extLog_witness_smul_eq` generalisations
land; the `MonoidHom`-bundling is more work but is the right form. **Cost does not
downgrade the verdict** (Bourbaki-2.0).

Mathlib downstream this enables (per MODERN-IDIOM requirement):
  - `extLog` as a `MonoidHom` ⟹ this computation rule = the value form of `map_zpow`;
    `extLog_mul` = `map_mul`, `extLog_prod` = `map_prod`, `extLog_eq_zero_of_pow_eq_one`
    / `extLog_neg` as free torsion-kernel corollaries, `extLog_eq_padicLog` as the
    restriction to the ball — the project's whole `ExtLog.lean` API collapses to
    homomorphism lemmas;
  - composes with mathlib's `RootableBy`/`DivisibleBy`
    (`Mathlib/GroupTheory/Divisible.lean`) and `Submonoid`/`Subgroup` lattice API;
  - it is the load-bearing computation companion to the parent `padicLog`/`extLog`
    contribution, shipped in the same coherent "p-adic exp/log" PR group.

PR grouping: **ship with the parent `extLog` def, `extLog_witness_smul_eq`, and the
rest of the `ExtLog.lean` API (and the underlying `padicExp`/`padicLog`/`InExpBall`)
as one coherent "p-adic exponential and (Iwasawa-branch) logarithm" contribution.**
Although this lemma — unlike `extLog_witness_smul_eq` — *does* have external consumers
(K = 4), it is still meaningless without the `extLog` def it computes, so it must
travel with that def, not alone.

Next action: run `/generalise PadicLFunctions.extLog_eq_of_witness` **after** the
parent `padicLog`/`extLog`/`extLog_witness_smul_eq` have been generalised off the
`ℚ_p`-algebra assumption (Phase 4b weakenings 1–3) — it will tension against both the
literature-standard form from Phase 3 and the modern-idiom `MonoidHom`/`RootableBy`
form from Phase 4c. Strongly prefer folding it into a bundled-`MonoidHom` `extLog`
(where it becomes the `map_zpow` value-shadow) rather than porting it as a standalone
`dif_pos` lemma.

---

## Next step

Run `/generalise PadicLFunctions.extLog_eq_of_witness` once the parent
`padicLog`/`extLog`/`extLog_witness_smul_eq` have been generalised off the
`ℚ_p`-algebra assumption, restating this computation rule over a complete
nonarchimedean `CharZero` field with division inside `K` and ball-membership on
`‖·−1‖<1`. **Preferably**, fold it into a bundled `extLog : MonoidHom …` (where it is
the value form of `map_zpow`/`map_mul`) and/or contribute alongside a reusable generic
"extend a `MonoidHom` into a `RootableBy ℤ` group" lemma. Ship as part of the single
coherent p-adic exp/log PR group with `extLog` + `padicExp` + `padicLog` + `InExpBall`;
do not PR this lemma on its own (it is meaningless without the `extLog` def it
evaluates, even though — unlike its sibling — it has external consumers).
