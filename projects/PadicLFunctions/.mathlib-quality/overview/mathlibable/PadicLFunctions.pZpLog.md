# `/mathlibable` report — `PadicLFunctions.pZpLog`

**Final verdict: `BORDERLINE-needs-human`**

`pZpLog` is the **integral `p`-adic logarithm** `1 + pℤ_p → pℤ_p` (odd `p`): the
junk-totalised restriction of the analytic `padicLog` to `ℤ_[p]`, packaged as a
`ℤ_[p]`-valued function via the integrality certificate `‖log x‖ ≤ 1`. The
mathematics is canonical and genuinely missing from mathlib — `log` is an
isometric isomorphism of the principal units `1 + pℤ_p` onto `pℤ_p` for `p` odd
(Cassels *Local Fields* §12, Washington *Cyclotomic Fields* §5.1, Iwasawa;
Wikipedia "P-adic exponential function"; RJW Lem 5.14). But its mathlib fate is a
**judgment call**, for the same reason its exact structural twin `pZpExp` is:
(a) it is a project-only **junk-totalised integral `def`** (`ℤ_[p] → ℤ_[p]` via
`Subtype` + `dif`, with junk value `0`) that mathlib has no analog of; (b) its
analytic parent `padicLog` is itself only `YES-but-generalise-first` (mathlib
lacks any nonarchimedean exp/log), so the integral wrapper sits *downstream* of an
unresolved upstreaming decision; and (c) whether mathlib wants this *integral
wrapper* at all — versus the analytic `padicLog` plus a bundled group/`IsometryEquiv`
`1 + pℤ_p ≃ pℤ_p`, with the subtype packaging inlined — is precisely the kind of
scope/idiom question the skill cannot resolve alone. This is **consistent with its
glue lemma `pZpLog_coe` (BORDERLINE) and its twin `pZpExp_sub_one_mem` (BORDERLINE)**.

- **Target:** `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1075` (kind: `def`)
- **Mode:** A (single declaration), full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               **build not re-run; reasoned from source** (per the task's BUILD NOTE — the build is stale/slow here; Phase 0 source-fallback used). The target file is part of `main`, is committed-clean, contains **0 `sorry`/`admit`**, and its full dependency chain (`padicLog`, `norm_padicLog`, `inExpBall_of_mem_span`, `coe_norm_le_inv_of_mem_span`, `PadicInt.norm_def`) was read directly from `PadicExp.lean`. The companion lemmas `pZpLog_coe`/`pZpLog_mem` elaborate against the def exactly as written. Baseline commit `d71766e`.
- decl `PadicLFunctions.pZpLog`:   ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/PadicExp.lean:1075`
- kind:                      `def` (plain `noncomputable def`; **not** `@[reducible]`, sealed)
- has sorry:                 no
- module docstring summary:  "The p-adic exponential and logarithm (RJW Lem 5.14)" — `exp(x)=∑xⁿ/n!` converges on the open ball `‖x‖<p^{−1/(p−1)}` of a nonarchimedean complete normed `ℚ_[p]`-algebra field and is an isometry there; for odd `p` the ball contains `pℤ_p`; `log(1+y)=∑(−1)^{n+1}yⁿ/n` converges for `‖y‖<1` and inverts `exp` on matched balls; realises `x^s := exp(s·log x)`, agreeing with the character `PadicInt.onePAdicPow`. Cites Cassels §12 and Washington §5.1.

---

### Statement (Phase 1)

`PadicLFunctions.pZpLog` is **a definition of the integral `p`-adic logarithm on the principal units `1 + pℤ_p`**:

> Let `p` be an (odd) prime. For `x ∈ ℤ_[p]`, set `pZpLog p x := ⟨log_p x, _⟩ ∈ ℤ_[p]`
> when the analytic logarithm `log_p (x : ℚ_[p])` is integral (`‖log_p x‖ ≤ 1`), and the
> junk value `0` otherwise. On `x ∈ 1 + pℤ_p` (odd `p`) it always takes the true branch
> (`pZpLog_coe`): `(pZpLog p x : ℚ_[p]) = log_p x`, and lands in `pℤ_p` (`pZpLog_mem`).

Mathematically this is the **integral logarithm half** of the classical isomorphism
`log_p : 1 + pℤ_p ≅ pℤ_p` (for `p` odd): the analytic `log` of a principal unit is again
a `p`-adic integer, in fact a multiple of `p`. The crux is the **isometry** `‖log_p x‖ = ‖x − 1‖`
on the unit ball (`norm_padicLog`), combined with `‖x − 1‖ ≤ p⁻¹` for `x ∈ 1 + pℤ_p`; together
`‖log_p x‖ ≤ p⁻¹ < 1`, so `log_p x ∈ pℤ_p ⊂ ℤ_[p]`. `pZpLog` is the junk-totalised packaging of
this into a total function `ℤ_[p] → ℤ_[p]` (junk value `0`, the logarithm's value at the
degenerate point `1`). It is the logarithmic inverse of the integral exponential `pZpExp`
(`ℤ_[p] → ℤ_[p]`), and the two together realise `x^s := exp(s·log x)` (`padicExp_smul_padicLog_eq_onePAdicPow`).

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [Fact p.Prime]` — the prime; the analytic `padicLog` underneath uses scalars in `ℚ_[p]`.
- (No general `L`: `pZpLog : ℤ_[p] → ℤ_[p]` is **`ℚ_p`-specific** — it depends on `PadicInt`'s `Subtype` packaging, `PadicInt.norm_def`, and the span/valuation API. The general parameter `L` of the surrounding file is *not* in scope here; the four `omit … in` lines around `pZpLog_coe`/`pZpLog_mem` drop `[NormedAlgebra ℚ_[p] L]` etc., underlining that this object lives entirely at `L = ℚ_[p]`.)

Hypotheses (Lean side):
- none on the def itself (junk-total). The meaning lemmas carry `hp2 : p ≠ 2` (odd prime) and `hx : x − 1 ∈ Ideal.span {(p : ℤ_[p])}` (i.e. `x ∈ 1 + pℤ_p`).

Conclusion (math): the integral `p`-adic logarithm of a principal unit, an element of `pℤ_p`.
Conclusion (Lean): `ℤ_[p]` (kind is `def`).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: introduces a **named mathematical object** — the integral `p`-adic logarithm on principal units, one half of the canonical isomorphism `1 + pℤ_p ≅ pℤ_p` — which is a building block of RJW Lem 5.14 ("The p-adic exponential and logarithm") and is named/used throughout the analytic-NT literature (Iwasawa `log_p`, Washington §5.1, Cassels §12). It is a `def` of a named concept, so BIG by the structure rule.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is narrative framing only.)

### One-line check (Phase 2b)

Body line count: **1 substantive line**, but it is a **two-branch `dif`** carrying an integrality certificate:
`if h : ‖padicLog p ((x : ℚ_[p]))‖ ≤ 1 then ⟨padicLog p ((x : ℚ_[p])), h⟩ else 0`.
One-liner verdict: **ONE-LINER** (kind is `def`; the body is a single `dite` expression). It is a *richer* one-liner than a bare alias — it bundles a `Subtype` membership proof (the integrality witness `h`) into the value — but it is still one substantive line, so the exemption table is required.

| Exemption                        | Applies? | Evidence |
|----------------------------------|----------|----------|
| Avoid defeq abuse                | yes      | The def is sealed (no `@[reducible]`). Downstream proofs unfold it **explicitly** via `rw [pZpLog]` then `dif_pos`/`dif_neg` (`pZpLog_coe` at PadicExp.lean:1092: `rw [pZpLog, dif_pos hle]`). The branch must not be unfolded by `simp`/unification unpredictably — the `else 0` junk branch would give wrong defeqs if exposed. |
| Avoid typeclass diamonds         | no       | No `Mul`/`Zero`/`AddCommMonoid` instance is anchored on this def; it is an ordinary function `ℤ_[p] → ℤ_[p]`. |
| Mark semantic intent / API name  | yes      | `pZpLog` is the public API name consumed by `ResidueZeta.lean` (≥6 call sites, incl. `pZpLog_mem`, `pZpLog_coe`, `pZpLog_angleUnit_ne_zero`, `extLog_natCast_eq_pZpLog_angle`). The integral-log abstraction with junk-totalisation is the stable surface the residue-zeta development depends on. |

Conclusion: **ONE-LINER WITH-EXEMPTION** — a `dif`-bodied junk-totalised integral function with a sealed body and a real API surface. The one-liner signal does **not** by itself bias toward NO. (But the *content* of the def — a junk-totalised subtype wrapper specific to `ℤ_[p]` — is what drives the eventual BORDERLINE, not the line count.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `p-adic logarithm 1 + pZ_p principal units isomorphism Iwasawa` | yes | `log_p : 1 + 𝔪_K → 𝔪_K`; for the `r=1` case the isomorphism `1 + pℤ_p ≅ pℤ_p` holds for `p` odd | ResearchGate "On the image of p-adic logarithm on principal units"; arXiv:1907.06437, arXiv:1904.09850, math/0512015, arXiv:2601.18187. Confirms the principal-units → ideal log map is the standard object and that `r=1`/`p=2` is the delicate case. |
| 2 | WebSearch (general form) | `p-adic logarithm convergence ball integral valued log Washington cyclotomic fields` | yes | `log` is an **isometry** between `{‖x‖ < p^{−1/(p−1)}}` (additive) and `{1 + y : ‖y‖ < p^{−1/(p−1)}}` (multiplicative); image of log on principal units is the key Iwasawa ingredient | Harvard p-adic heights thesis; Müller pBSD notes; Ferrero–Washington (Wikipedia). The isometry on matched balls is exactly `norm_padicLog` + the integrality used by `pZpLog`. |
| 3 | WebSearch (named-after / aliases) | `p-adic exponential logarithm isometry exp log inverse Cassels local fields` | yes | "p-adic exp has inverse the p-adic logarithm; `exp∘log=id`, `log∘exp=id` on their domains"; **Cassels *Local Fields* (1986) Ch. 12** is the standard reference | MIT `dav/exp.pdf` "Exponential and logarithm in p-adic fields"; Wikipedia; planetmath; World Scientific "Logarithm and exponential in a p-adic field". The `hp2`-gated integral iso is textbook. |
| 4 | ChatGPT MCP | (MCP unavailable in this environment) | n/a | — | ChatGPT MCP is **not configured** in this sandbox (no `mcp__*chatgpt*` tool surfaced). **Compensated** by an extra primary-source `WebFetch` of Wikipedia (row 11) + reading the in-repo Washington/Cassels-cited docstring; the standard-form + historical-evolution question is answered by rows 1–3, 6, 11. (Same limitation recorded across all siblings in this batch.) |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/`; `ls refs/` | n/a | (no references dir; no `refs/` symlink) | Both absent — recorded n/a per protocol. The module docstring itself cites RJW Lem 5.14, Cassels §12, Washington §5.1. |
| 6 | nLab | `nLab p-adic logarithm exponential` | partial | "p-adic exp has inverse the p-adic logarithm; converges `\|z−1\|_p<1`; `log_p(zw)=log_p z+log_p w`; extends to `ℂ_p^×` via `log_p(p)=0`" | nLab "p-adic number"; also surfaced MIT `dav/exp.pdf` and UChicago REU (Gupta) "The p-adic integers, analytically and algebraically". Confirms domain and inverse relation; no integral-wrapper-specific entry. |
| 7 | nCatLab (categorical) | (same as nLab) | n/a | — | Not a categorical concept; the nLab entry (row 6) is the relevant one. |
| 8 | Stacks Project (alg geom) | — | n/a | — | Not an algebraic-geometry / scheme-theoretic concept; the integral p-adic log is an analytic function on the units of a complete DVR. Stacks has no entry. |
| 9 | MathOverflow / Math.StackExchange | `site:mathoverflow.net p-adic logarithm isomorphism principal units exp` | yes | `log_p : 1 + 𝔪_K^r → 𝔪_K^r` is an **isomorphism iff `r > e/(p−1)`**; for `ℚ_p` (`e=1`) that is `r ≥ 1` with `p` odd; `r=1` fails for `p=2` | Search surfaced arXiv:1907.06437/1904.09850/2601.18187 (MO threads index into these). Gives the **exact generality threshold** `r > e/(p−1)` that the `hp2` hypothesis instantiates for `ℚ_p`. |
| 10 | recent arXiv (last 5 yr) | (rows 1, 9) | yes | "On the bases of the image of 2-adic logarithm on principal units" (arXiv:1907.06437, 2023); "On the image of the p-adic logarithm on annuli of principal units" (arXiv:2601.18187, 2026) | Active modern use of exactly this object — the image of `log_p` on principal units — same definition, same `r`/`p` delicacy. |
| 11 | Wikipedia primary fetch | `WebFetch en.wikipedia.org/wiki/P-adic_exponential_function` | yes | `log_p(1+x)=∑(-1)^{n+1}xⁿ/n`, converges `\|x−1\|_p<1`; extends to `ℂ_p^×` via `w=pʳ·ζ·z`, `log_p(p)=0`; `exp_p∘log_p=id`, `log_p∘exp_p=id`; multiplicative; "Iwasawa logarithm" = the `log_p(p)=0` choice | Confirms domain, inverse relation, isometry, and the standard extension. States it over `ℂ_p` / "p-adic fields", not restricted to `ℤ_p` — but the **integral-valued restriction to `1 + pℤ_p`** (what `pZpLog` packages) is the local-DVR specialisation, treated in Washington §5.1 / Cassels §12. |

The protocol passed: WebSearch ran 3 distinct generality levels (rows 1–3) plus arXiv (10) and a primary fetch (11); local refs checked (absent, n/a); nLab checked (6); Stacks/nCatLab/MathOverflow each adjudicated (8/7/9). Loogle was additionally run for the *mathlib* side (Phase 5). ChatGPT MCP is genuinely unavailable in this sandbox — recorded n/a with the compensating primary-source fetch noted.

### Literature summary (Phase 3)

Concept identified as: the **integral `p`-adic logarithm on principal units** — the restriction of the **Iwasawa logarithm `log_p`** to `1 + pℤ_p`, valued in `pℤ_p`; one half of the canonical isomorphism `log_p : 1 + pℤ_p ≅ pℤ_p`.
Sources agree on the standard form: **yes** — `log_p` is an isometry between matched balls and, on principal units, gives an isomorphism `1 + 𝔪_K^r ≅ 𝔪_K^r` exactly when `r > e/(p−1)`. For `K = ℚ_p` (`e = 1`) the `r = 1` case `1 + pℤ_p ≅ pℤ_p` holds **iff `p` is odd** — *precisely* the `hp2 : p ≠ 2` hypothesis on `pZpLog_coe`/`pZpLog_mem`. (For `p = 2`, `1 + 2ℤ_2 ≇ 2ℤ_2`; one needs `1 + 4ℤ_2 ≅ 4ℤ_2`.)
Most general standard form: `log_p : 1 + 𝔪_K^r → 𝔪_K^r` for a **finite (or complete) extension `K/ℚ_p`** with ramification index `e`, an isomorphism for `r > e/(p−1)`; over `ℚ_p` this specialises to `1 + pℤ_p ≅ pℤ_p` for odd `p`.
Generality dimensions where the literature varies:
  - **Base field / DVR**: `ℤ_p ⊂ 𝒪_K` for finite extensions `K/ℚ_p ⊂ 𝒪_{ℂ_p}`. The user's `pZpLog` is fixed at `ℤ_p` (`e = 1`). The literature-standard form is over a general local field's ring of integers `𝒪_K`, with the threshold `r > e/(p−1)`.
  - **Subgroup level `r`**: `1 + 𝔪^r` for `r ≥ 1`. The user fixes `r = 1` (`1 + pℤ_p`). This is the *delicate* boundary case (it is exactly where the `p`-odd condition is needed).
  - **Packaging**: the literature treats `log_p` as a *function/group homomorphism* `1 + 𝔪 → 𝔪` (often an `IsometryEquiv`), **not** as a junk-totalised total function on the whole DVR. The `Subtype` + `else 0` junk-totalisation is a **Lean engineering idiom**, not a mathematical feature of the standard object.
Disagreement with the literature: the user's Lean form is mathematically correct but (i) **narrower** than standard (fixed to `ℤ_p`, `e=1`, `r=1`) and (ii) **packaged** as a junk-total `def` rather than the standard group-iso/`IsometryEquiv` `1 + pℤ_p ≃ pℤ_p` — see Phase 4.

---

### Generality analysis — `PadicLFunctions.pZpLog`

Literature-standard form (from Phase 3): the integral logarithm `log_p : 1 + 𝔪_K → 𝔪_K` on the principal units of a local field `K/ℚ_p` (ring of integers `𝒪_K`, ramification `e`), an isometric **isomorphism** for `r > e/(p−1)`; over `ℚ_p` the `r=1` case `log_p : 1 + pℤ_p ≅ pℤ_p` for `p` odd.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|---------------------------------|
| 1 | base DVR `ℤ_[p]` | fixed to `ℤ_p` (`e = 1`) | `𝒪_K` for any finite/complete `K/ℚ_p` | **yes** | The whole construction (analytic `log` is integral on principal units) generalises verbatim to any local field `K`, with the threshold `r > e/(p−1)`. `pZpLog` is the `ℚ_p` special case. But the *analytic parent* `padicLog` is already general over `L` (any complete ultrametric `ℚ_[p]`-algebra field) — the narrowing happens precisely at the **`ℤ_[p]`-integral packaging** step, which uses `PadicInt`'s `Subtype`. |
| 2 | subgroup level `r = 1` (`1 + pℤ_p`) | fixed at `r = 1` | `1 + 𝔪^r`, any `r ≥ 1` | yes | Higher `r` works (and is *easier* — no `p`-odd condition needed once `r > e/(p−1)`). `r=1` is the boundary case the project actually needs. |
| 3 | `hp2 : p ≠ 2` (on the meaning lemmas) | odd prime | for `r=1, e=1`: needed; for `r > e/(p−1)`: not needed | NO (at `r=1`) | The `p`-odd condition is **mathematically essential** at `r=1` over `ℚ_p` (the iso genuinely fails for `p=2`). This is the *correct* hypothesis, not a weakenable one — it is the literature threshold instantiated. |
| 4 | packaging: junk-total `def` `ℤ_[p] → ℤ_[p]` (`Subtype` + `else 0`) | total function with junk value `0` | a group hom / `IsometryEquiv` `1 + pℤ_p ≃ pℤ_p` (a *bundled* map on the subgroup) | **yes (idiom change)** | The standard object is the *isomorphism on the subgroup*, not a junk-totalised global function. Mathlib would more likely want `(1 + pℤ_p) ≃ pℤ_p` (or an `AddMonoidHom`/`IsometryEquiv`) plus `padicLog`, with the `Subtype` packaging derived — see Phase 4c. The junk-totalisation is a project-engineering choice, not the maths. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (and additionally non-standard in *packaging*).
Number of weakening opportunities found: K = 3 (rows 1, 2, 4; row 3 is already optimal — `hp2` is the correct, essential hypothesis at `r = 1`).

Proposed restatement (the literature-standard target, two coupled moves):

```lean
-- (A) keep the general analytic logarithm `padicLog` (already over a general `L`), then
-- (B) bundle the integral isomorphism on principal units, rather than a junk-total def:
/-- For odd `p`, the `p`-adic logarithm is an isometric isomorphism of the principal
units `1 + pℤ_p` onto `pℤ_p` (Washington §5.1, Cassels §12). -/
noncomputable def pZpLogEquiv (hp2 : p ≠ 2) :
    {u : ℤ_[p]ˣ // (u : ℤ_[p]) - 1 ∈ Ideal.span {(p : ℤ_[p])}} ≃
      {y : ℤ_[p] // y ∈ Ideal.span {(p : ℤ_[p])}} := …
-- or, more generally, over a local field K with ramification e and level r > e/(p−1).
```

Cost of restatement: **MODERATE → EXPENSIVE.** The `ℤ_p`-internal restatement (subtype-valued junk-total → bundled `Equiv`/`IsometryEquiv`) is MODERATE (the inverse `pZpExp`, the isometry `norm_padicLog`, and `pZpLog_mem`/`pZpExp_sub_one_mem` already supply the round-trip and bound). The full **general-local-field** form (any `𝒪_K`, threshold `r > e/(p−1)`) is EXPENSIVE — it needs the ramification-aware convergence theory, which the project does not develop (it lives entirely at `ℚ_p`). Per the skill, EXPENSIVE does **not** downgrade the verdict; it is a *sequencing/scope* consideration — which is exactly what makes the bucket a human call (see Phase 7).

If MAXIMALLY GENERAL → consider YES/NO buckets. Here: **STRICTLY NARROWER** → Phase 7 considers YES-but-generalise-first **prominently**, but the *packaging* question (junk-total def vs. bundled iso) and the *scope* question (ship the `ℚ_p` integral wrapper at all, vs. only `padicLog` + the iso) are judgment calls → BORDERLINE.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let `X` be a foo" preamble → typeclass? | no | already typeclass-based; `pZpLog` is fixed at `ℤ_p` and uses `PadicInt` API directly | n/a |
| 2 | sequences/metric → filters/topological? | no | the analytic content is in `padicLog` (already `tsum`/`Summable`, i.e. filter-based); `pZpLog` only packages integrality | n/a |
| 3 | **construct object → universal-property / bundled-equiv class?** | **yes** | replace the junk-total `def` `ℤ_[p] → ℤ_[p]` by the **bundled isomorphism** `(1 + pℤ_p) ≃ pℤ_p` (an `AddEquiv`/`IsometryEquiv` between the additive group `pℤ_p` and the multiplicative principal-units group `1 + pℤ_p`), the standard object | composes with mathlib's `Equiv`/`MulEquiv`/`AddEquiv`/`IsometryEquiv` API, group-cohomology and Iwasawa-module machinery; auto-gives `pZpLog`/`pZpExp` as the two directions of the equiv |
| 4 | set-with-closure-pred → bundled substructure? | partial | the domain `1 + pℤ_p` and codomain `pℤ_p` are best modelled as the **subgroup / ideal** they are (mathlib `Subgroup`/`Ideal`), with the iso between them — rather than a function on the whole DVR keyed off a junk value | lattice/subgroup API; the iso restricts/corestricts cleanly |
| 5 | field-specific → weaken to ring? | partial (covered by 4a row 1) | generalise `ℤ_p` to a general local DVR `𝒪_K` (threshold `r > e/(p−1)`) | the one integral-log iso serves all local fields |
| 6 | 1-categorical → higher-categorical? | no | not categorical | n/a |
| 7 | concrete index → general structure? | no | no series index here (the series is inside `padicLog`); `pZpLog` is a packaging def | n/a |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes** — the contemporary mathlib formulation is a **bundled isomorphism** `(1 + pℤ_p) ≃ pℤ_p` (`AddEquiv`/`IsometryEquiv` between the principal-units group and the additive ideal), with `pZpLog`/`pZpExp` recovered as its two directions, in place of two separate junk-totalised `def`s.
  - Proposed mathlib-idiomatic restatement: `pZpLogEquiv` (sketch in Phase 4b), generalising over a local field where feasible.
  - Cost: MODERATE (the inverse, isometry, and image facts already exist as `pZpExp`, `norm_padicLog`, `pZpLog_mem`, `pZpExp_sub_one_mem`); the general-local-field version is EXPENSIVE.
  - Mathlib downstream this enables: the bundled equiv composes with the entire `Equiv`/`AddEquiv`/`IsometryEquiv` ecosystem and with Iwasawa-theory / local-class-field-theory machinery; it removes the need for *two* junk-totalised wrappers; it is the canonical statement of Washington §5.1 / Cassels §12.
  - Real mathematical improvement (not just "looks cooler"): the standard mathematical object **is** the isomorphism `1 + pℤ_p ≅ pℤ_p`; bundling it (rather than shipping a junk-total `ℤ_[p] → ℤ_[p]` function whose behaviour off `1 + pℤ_p` is meaningless) is the difference between the textbook theorem and an implementation detail.

Phase 4c **reinforces** that `pZpLog`-as-a-bare-junk-total-def is *not* the form mathlib would want; the bundled-equiv form is. But whether to do that bundling/generalisation now, ship the narrow `ℚ_p` wrapper, or only upstream `padicLog` + the equiv (inlining the integral packaging) is exactly the scope/idiom decision the skill defers to the user → BORDERLINE.

---

### Diamond / defeq risk — `PadicLFunctions.pZpLog`

(`def`, so Phase 4.5 runs. Probes reasoned from source — build not re-run.)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **none** | `pZpLog` returns a bare element of `ℤ_[p]`; it anchors no instance and appears in no instance head. No typeclass-search path is steered by it. |
| 2 | Reducibility leak | **low** | Plain `noncomputable def`, **not** `@[reducible]`. The body is a `dite` with a `Subtype` value and a `0` junk branch; sealing is correct and intentional (Phase 2b exemption 1). A reducibility leak would expose the `else 0` branch to defeq-checking — so keeping it sealed is exactly right; risk is low *because* it is sealed. |
| 3 | Non-canonical unfolding | **low** | `rfl`/`simp` will not spontaneously pick a `dite` branch (the discriminant `‖padicLog …‖ ≤ 1` is not decidable by `rfl`); unfolding only happens via the explicit `rw [pZpLog, dif_pos …]` the project uses. No `@[simp]` lemma exposes the branch. Surprise risk is low. |
| 4 | Instance priority collision | **n/a** | Not an `instance`. |
| 5 | Universe-polymorphism issues | **none** | Monomorphic — domain and codomain are `ℤ_[p]` (`Type 0`); no universe variable, no polymorphic call-site constraint. |
| 6 | Coercion ambiguity | **none** | No `CoeFun`/`CoeSort`; `pZpLog` is an ordinary function. The `(pZpLog p x : ℚ_[p])` in lemmas is the *existing* `PadicInt → ℚ_[p]` coercion, not a new one. |

### Risk verdict (Phase 4.5)

Overall risk: **NONE/LOW**
Top risks: none HIGH. The only mild items (reducibility/unfolding of the `dite`) are *already mitigated* by sealing the def — the standard mathlib-safe pattern for a junk-totalised subtype-valued function.
Recommended mitigations: none required. (Note: this LOW infra risk does **not** push the verdict toward YES — the verdict is driven by the Phase 4 generality/packaging gap + the Phase 7 scope judgment, not by diamond risk.)

---

### Mathlib search-status: `PadicLFunctions.pZpLog`

[A] Lean-Finder       — n/a: Lean-Finder MCP not available in this environment.
[B] Loogle            **executed** via `loogle.lean-lang.org/json`: `"padicLog"` → **0 declarations**; `"padicExp"` → **0 declarations**; type-pattern `PadicInt → PadicInt` log/exp-shaped → no p-adic exp/log hits. **no hit.**
[C] LeanSearch        "p-adic logarithm on principal units valued in pZ_p" — n/a: the `leansearch.net` API endpoint returned HTTP 404 (API shape changed); substituted by the literature channels (Phase 3) + the exhaustive source grep (D), which are authoritative for the absence question.
[D] Grep mathlib src  `def (pZpLog\|ZpLog\|pAdicLog\|padicLog\|principalLog\|unitLog)`, `PadicInt\.(log\|exp)`, `def .*: ℤ_\[` log/exp-valued, `ultrametric.*(exp\|log)`, `nonarchimedean.*(exp\|log)`, `NormedSpace.log`, p-adic exp/log under `NumberTheory/Padics/` — **executed in full** on `.lake/packages/mathlib/`. **no hit** for any p-adic / nonarchimedean / integral exp/log, and **no hit** for any `log` inverting a Banach-algebra exp.
[E] Name pattern      `pZpLog`, `padicLog`, `Padic.*log`, `principal.*unit.*(log\|exp)`, `oneUnits.*log` — only unrelated objects exist (`Real.log`, `Complex.log`, `CFC.log = cfc Real.log` for C*-algebras, `PowerSeries.log` formal, `NormedSpace.exp` archimedean radius-∞ with no `log`).

Searched for both:
  - the user's current form (integral `1 + pℤ_p → pℤ_p` junk-total def): **not in mathlib**.
  - the literature-standard form (the isomorphism `log_p : 1 + 𝔪_K ≅ 𝔪_K` / `IsometryEquiv` on principal units, over `ℚ_p` or a general local field): **not in mathlib**.

Closest existing mathlib objects (all confirmed *not* the same):
  - `PowerSeries.log A` (`Mathlib/RingTheory/PowerSeries/Log.lean`) — the **formal** log series; purely algebraic, no convergence / no analytic evaluation, no integrality on units. A building block for the *parent* `padicLog`, not for the integral wrapper.
  - `NormedSpace.exp 𝕂 𝔸` (`Mathlib/Analysis/Normed/Algebra/Exponential.lean:127`) — the analytic exponential, but radius `∞` (archimedean) and with **no companion `log`**. Wrong regime; no inverse log.
  - `CFC.log = cfc Real.log` (`…/ContinuousFunctionalCalculus/ExpLog/Basic.lean:121`) — the continuous-functional-calculus logarithm for C*-algebra elements with real spectrum; inapplicable to `ℤ_[p]`.
  - No mathlib object for the principal-units group `1 + pℤ_p`, its isomorphism with `pℤ_p`, or any integral p-adic logarithm.

Concluded: **not in mathlib** (all available methods exhausted: Loogle run for both `padicLog`/`padicExp`; source grep run in full for both the user's form and the literature-standard form; Lean-Finder/LeanSearch genuinely unavailable / 404 and recorded n/a with compensating channels). Mathlib has **no p-adic / nonarchimedean analytic logarithm of any kind**, and no principal-units machinery — so it has neither `pZpLog` nor its bundled-equiv generalisation, nor (per the parent report) the analytic `padicLog` it restricts.

---

### Call sites — `PadicLFunctions.pZpLog`

Internal use count: **K ≥ 6** uses of `pZpLog` (the def), all within **1 distinct file** (`ResidueZeta.lean`, excluding the declaring file `PadicExp.lean` and the def's own glue lemmas `pZpLog_coe`/`pZpLog_mem`).
External-to-file callers: **1 distinct file** (`ResidueZeta.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `PadicLFunctions/ResidueZeta.lean:106` | `set ℓ : ℤ_[p] := pZpLog p y with hℓ` — the integral log of a principal unit |
| `PadicLFunctions/ResidueZeta.lean:235–236` | `set L : ℤ_[p] := pZpLog p (PadicInt.angleUnit p u : ℤ_[p])` (used inside a `tendsto … (nhds (-(pZpLog …)))`) |
| `PadicLFunctions/ResidueZeta.lean:1719–1721` | `private lemma pZpLog_angleUnit_ne_zero … : pZpLog p (PadicInt.angleUnit p u) ≠ 0` |
| `PadicLFunctions/ResidueZeta.lean:1737–1740` | `extLog_natCast_eq_pZpLog_angle … = ((pZpLog p (angleUnit p u) : ℤ_[p]) : ℚ_[p])` |
| `PadicLFunctions/ResidueZeta.lean:1783, 1791–1792, 1822` | `Lq := ((pZpLog p (angleUnit p u) : ℤ_[p]) : ℚ_[p])`; `pZpLog_angleUnit_ne_zero …` |

(Plus the def's own API lemmas `pZpLog_coe`, `pZpLog_mem`, `padicExp_smul_padicLog_eq_onePAdicPow` in the declaring file, and the `pZpLog_*` consumers above.)

Inline-derivation grep (was the equivalent re-derived without using `pZpLog`?):
  - **Within the project: none** — every integral-log consumer goes through `pZpLog` (and its coe/mem lemmas). The `angleUnit` logarithm in `ResidueZeta` is *built on* `pZpLog`, not re-derived.

Call-sites signal: **K ≥ 3 internal uses, no inline re-derivation → real API; consumers (the residue-zeta development) depend on it → leans YES-\*.** This rules out the "dead code / wrapper bypassed" NO patterns. (Note the contrast with the twin `pZpExp_sub_one_mem`, which had *zero* call sites; `pZpLog` is more clearly load-bearing — yet still BORDERLINE for the *scope/packaging* reasons below, not for lack of use.)

---

### Composition check (Phase 6)

Can `PadicLFunctions.pZpLog` be derived from mathlib in ≤3 chained calls?

Attempt 1: `fun x => ⟨padicLog p (x : ℚ_[p]), _⟩` using a mathlib analytic log.
  - Mathlib decls used: (none available) — mathlib has **no** `padicLog`/nonarchimedean analytic log (Phase 5). The analytic parent is itself a project def (verdict `YES-but-generalise-first`), not a mathlib primitive. **Fails.**

Attempt 2: evaluate `PowerSeries.log` and package into `ℤ_[p]`.
  - Mathlib decls used: `PowerSeries.log`.
  - Result: **fails** — `PowerSeries.log` is purely formal (no convergence / no analytic evaluation), and even granting evaluation, the *integrality* (that `log x ∈ pℤ_p` for `x ∈ 1 + pℤ_p`) is the `norm_padicLog` isometry + span bound, which is genuine content (`pZpLog_mem`), not a mathlib call.

Attempt 3: reuse a mathlib principal-units log / `1 + 𝔪 ≅ 𝔪` iso.
  - Result: **fails** — no such object exists in mathlib (Phase 5).

Conclusion: **NOT-COMPOSABLE.** The integral p-adic logarithm requires (i) the nonarchimedean analytic `log` (absent from mathlib) and (ii) its integrality on principal units (the isometry + span bound, genuine content). This is not a 1–3 mathlib-call composition — so this is **not** a NO-composable case.

---

## Verdict: `PadicLFunctions.pZpLog`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the **integral `p`-adic (Iwasawa) logarithm on principal units** — `log_p : 1 + pℤ_p ≅ pℤ_p` for `p` odd (the `r=1` case of `1 + 𝔪_K^r ≅ 𝔪_K^r`, valid iff `r > e/(p−1)`; Cassels §12, Washington §5.1, Iwasawa, Wikipedia). Canonical, named, actively used. The `hp2 : p ≠ 2` hypothesis is *exactly* the standard threshold instantiated at `ℚ_p`, `r=1`.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** (fixed to `ℤ_p`/`e=1`/`r=1`) **and non-standard in packaging** (junk-total `def` vs. the standard bundled `AddEquiv`/`IsometryEquiv` `1 + pℤ_p ≃ pℤ_p`). Phase 4c confirms the bundled-equiv form is the mathlib-idiomatic target.
- Mathlib search (Phase 5): **not in mathlib** under either form — mathlib has no p-adic / nonarchimedean analytic log at all, and no principal-units machinery.
- Composition check (Phase 6): **NOT-COMPOSABLE** — needs the absent analytic `log` plus its integrality (genuine content).

**Rationale (1–2 paragraphs):**

`pZpLog` is true, textbook-standard, genuinely missing from mathlib, sorry-free, and (unlike its twin `pZpExp`'s image-lemma) actually load-bearing in the project (≥6 uses in `ResidueZeta.lean`, no inline re-derivation). All four evidence phases point at "real, missing content." So why **BORDERLINE** rather than `YES-but-generalise-first`? Because three facts converge on a decision the skill cannot ground in evidence alone. **First**, `pZpLog` is a *junk-totalised integral `def`* (`ℤ_[p] → ℤ_[p]` via `Subtype` + `else 0`) — but the standard mathematical object is the **isomorphism** `1 + pℤ_p ≅ pℤ_p`, not a total function whose values off the principal units are meaningless. Phase 4c shows the mathlib-idiomatic form is a bundled `AddEquiv`/`IsometryEquiv`, with `pZpLog`/`pZpExp` recovered as its two directions; shipping the bare junk-total def would be shipping an implementation detail, while shipping the equiv is a different (larger) deliverable. **Second**, `pZpLog` sits *downstream of an unresolved upstreaming decision*: its analytic parent `padicLog` is itself only `YES-but-generalise-first` (mathlib lacks any nonarchimedean exp/log), and `pZpLog`'s `ℤ_p`-integral content is the local-DVR specialisation (`e=1`, `r=1`) of the general `1 + 𝔪_K ≅ 𝔪_K` — generalising which is EXPENSIVE (needs ramification-aware convergence the project never develops). **Third**, per the skill's gate, "the more general/idiomatic form is expensive, so do we ship the narrow `ℚ_p` wrapper now?" is *explicitly* a BORDERLINE question to the user, never a self-resolving verdict downgrade. The honest verdict is therefore BORDERLINE — and it is **consistent with `pZpLog`'s own glue lemma `pZpLog_coe` (BORDERLINE) and its structural twin `pZpExp_sub_one_mem` (BORDERLINE)**: the entire `pZp*` integral-wrapper layer shares one human upstreaming/scope decision.

Note that this is **not** a NO verdict: Phase 5 found mathlib has neither the object nor (per the parent) the building blocks, and Phase 6 is NOT-COMPOSABLE. Nor is it `YES-add-as-is` (Phase 4b is STRICTLY NARROWER + non-standard packaging). It leans toward `YES-but-generalise-first` *as a sub-part of the whole p-adic exp/log contribution* — but only once the user fixes the packaging (bundled equiv vs. junk-total def) and scope (which generality, shipped when) questions below.

**Numbered questions (≤5):**

1. **Object vs. function.** Should mathlib get `pZpLog` as the bare junk-totalised function `ℤ_[p] → ℤ_[p]`, or as the **bundled isomorphism** `(1 + pℤ_p) ≃ pℤ_p` (`AddEquiv`/`IsometryEquiv`, with `pZpLog`/`pZpExp` as its two directions)? (Phase 4c argues the latter is the standard mathlib idiom.)
2. **Generality.** Target `ℤ_p` only (the `e=1`, `r=1` case, with `hp2`), or the general local-field form `log_p : 1 + 𝔪_K^r ≅ 𝔪_K^r` for `r > e/(p−1)`? The general form is EXPENSIVE (ramification-aware convergence the project doesn't build) — is it in scope, or is the `ℚ_p` case the intended mathlib contribution?
3. **Coupling to `padicLog`.** Since the analytic parent `padicLog` is `YES-but-generalise-first` and mathlib has *no* p-adic exp/log at all, should the whole "p-adic exponential and logarithm + principal-units iso" land as **one coordinated PR group** (`padicExp`, `padicLog`, `InExpBall`, `pZpExp`/`pZpLog` → the equiv)? If so, `pZpLog`'s fate is decided by that group, not individually.
4. **Junk-totalisation policy.** If the bare-def form *is* wanted (Q1 = function), is the `else 0` junk value the convention mathlib should adopt for an integral log (cf. `Real.log 0 = 0`, `tsum` junk), or should the API be subtype-/`Set`-restricted instead?
5. **Naming.** If kept as a `ℚ_p`-specific object, is `pZpLog` (or `PadicInt.log` / a name under `Mathlib/NumberTheory/Padics/`) the right name, given mathlib's `Padic`/`PadicInt` namespace conventions?

Next action: user answers the questions; re-run `/mathlibable PadicLFunctions.pZpLog` to resolve. Likely outcomes: (Q1 equiv + Q3 grouped) → folds into a single `YES-but-generalise-first` p-adic-exp/log PR built around `pZpLogEquiv`; (Q1 function + Q2 `ℚ_p` only) → `YES-but-generalise-first` shipping the narrow integral def alongside `padicLog`; (decision to keep the integral wrapper project-local and only upstream `padicLog` + a separate iso) → drop `pZpLog` from mathlib consideration and inline the packaging.

---

## Next step

User answers the 5 numbered questions above (the core is Q1 packaging — bundled `(1 + pℤ_p) ≃ pℤ_p` equiv vs. junk-total `ℤ_[p] → ℤ_[p]` def — and Q3 whether the whole p-adic exp/log layer ships as one coordinated PR), then re-run `/mathlibable PadicLFunctions.pZpLog`. The strong default, consistent with the parent `padicLog` (`YES-but-generalise-first`) and the twin `pZpExp_sub_one_mem`/`pZpLog_coe` (BORDERLINE): treat `pZpLog` as one direction of a bundled isometric isomorphism `1 + pℤ_p ≃ pℤ_p` and ship it inside a single "p-adic exponential and logarithm" contribution (with `padicExp`, `padicLog`, `InExpBall`), rather than upstreaming the bare junk-totalised integral wrapper on its own.
