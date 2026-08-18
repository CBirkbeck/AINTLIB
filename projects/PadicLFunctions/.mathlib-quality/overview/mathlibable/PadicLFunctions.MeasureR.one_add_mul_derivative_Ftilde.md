# /mathlibable report — `PadicLFunctions.MeasureR.one_add_mul_derivative_Ftilde`

**Final verdict: `BORDERLINE-needs-human`** — this is RJW Lemma 6.5 (first half, `∂F̃_θ = F_θ`)
for the mixed tame-and-wild case `N = D·pⁿ` (`D > 1`), the `θ ≠ 1` analogue of the already-assessed
`one_add_mul_derivative_FtildeA` (§7, also `BORDERLINE`). It is true, novel for mathlib, maximally
general for what it states, and **not** a 1–3-call composition (a real 54-line proof). But its
mathlib-worthiness is constitutively downstream of the upstreaming decision for the whole
Kubota–Leopoldt / Amice–Mahler-transform tower it is built on — a maintainer judgment the search
cannot make. The numbered questions are in Phase 7.

---

### Baseline (Phase 0)
- lake build:               build **not re-run** (stale/slow in this checkout per task note); **reasoned from source** — Phase 0 fallback. The declaration and its dependencies were read directly from `ValuesAtOne.lean` and the proof is sorry-free, so the elaborated type is taken from source.
- decl `PadicLFunctions.MeasureR.one_add_mul_derivative_Ftilde`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOne.lean:223`
- kind:                      theorem
- has sorry:                 no (verified: no `sorry`/`admit` in lines 223–283)
- module docstring summary:  "The p-adic value L_p(θ,1)" — RJW Theorem 6.1(ii) (Leopoldt's formula), decomposition cluster P6.

---

### Statement (Phase 1)

`one_add_mul_derivative_Ftilde` is a **theorem** stating the following.

Let `K` be a complete ultrametric `CharZero` normed `ℚ_p`-algebra (the stand-in for `ℂ_p`). Let
`θ` be a non-trivial Dirichlet character mod `N` valued in `K`, with `N > 1`, and let `ε` be a
primitive `N`-th root of unity in `K`. Define the explicit formal power series ("RJW's
antiderivative")
```
F̃_θ(T) = − Σ_{c=0}^{N−1} θ⁻¹(c) · logSeriesAt(ε^c)(T),
```
where `logSeriesAt(u)(T) = extLog_p(u−1) + Σ_{n≥1} ((−1)^{n−1}/n)(u/(u−1))ⁿ Tⁿ` is the per-root
formal series `log((1+T)·u − 1)` (with constant term the Iwasawa-branch p-adic logarithm). Then,
under the side condition that `ε^c − 1` is a unit for every `c` in range with `N ∤ c`,
```
(1+T) · ∂/∂T (F̃_θ)  =  − Σ_{c=0}^{N−1} θ⁻¹(c) · ((1+T)·ε^c − 1)⁻¹     ( = F_θ ).
```
Mathematically this is the formal logarithmic-derivative identity `∂F̃_θ = F_θ` for the operator
`∂ = (1+T) d/dT`, where `F_θ` is the (Amice/Mahler-transform) power series whose `∂`-antiderivative
`F̃_θ` is. It is the first half of RJW Lemma 6.5 (arXiv:2309.15692 §6.2), the engine that lets one
read off `L_p(θ,1)` from `F̃_θ(0)`.

Variables / typeclasses (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue prime.
- `K : Type*` with `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K] [CompleteSpace K] [CharZero K]` — the coefficient field (`CompleteSpace`, `CharZero` are `omit`-ted for this theorem; see Phase 4).
- `N : ℕ`, `[NeZero N]` — the modulus/conductor.
- `θ : DirichletCharacter K N` — the character; `Ring.inverse`, `PowerSeries.C/X/derivativeFun`, `IsPrimitiveRoot` are all mathlib.

Hypotheses (Lean side):
- `hN : 1 < N` — modulus > 1 (so `Σ_c θ⁻¹(c) = 0` is meaningful).
- `hθ1 : θ ≠ 1` — the character is non-trivial (kills the constant terms via orthogonality).
- `hε : IsPrimitiveRoot ε N` — `ε` a primitive `N`-th root of unity.
- `hunit : ∀ c ∈ Finset.range N, ¬ N ∣ c → IsUnit (ε ^ c − 1)` — the per-root unit side-condition (needed to invert the geometric factor in `one_add_mul_derivative_logSeriesAt`).

Conclusion (math): `(1+T)·∂F̃_θ = F_θ`, with `F_θ = −Σ_c θ⁻¹(c)·((1+T)ε^c − 1)⁻¹`.

Conclusion (Lean):
`(1 + PowerSeries.X) * PowerSeries.derivativeFun (Ftilde p K θ hε) = −∑ c ∈ Finset.range N, PowerSeries.C (θ⁻¹ ((c : ZMod N))) * Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C (ε ^ c) − 1)`.

---

### Size classification (Phase 2a)

Verdict: **BIG** (borderline) — it is **not** a new structure/def and **not** itself named after a
person, but it is a load-bearing step toward a **main result of the project** (`L_p(θ,1)`, the
file's `## Main results`; RJW Thm 6.1(ii), "Leopoldt"). It is the formal-derivative half of RJW
Lemma 6.5. Treating it as BIG is the right framing: the underlying `(1+T)d/dT(log) = 1/(1+T)`
identity is classical, and there is a definite literature home (RJW §6.2; Washington Ch. 5).

(Note: literature width is EXHAUSTIVE regardless. BIG/SMALL does not gate Phase 3.)

### One-line check (Phase 2b)

Body line count: ~54 substantive lines (`ValuesAtOne.lean:230–283`); kind is **theorem**.
One-liner verdict: **n/a (kind is theorem, not def)**. Section skipped per the rule.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Leopoldt formula p-adic L-function L_p(θ,1) ... logarithm cyclotomic units" | **yes** | `L_p(1,χ) = −(1−χ(p)/p)·(τ(χ)/f)·Σ_a χ̄(a) log_p(1−ζ^a)` | Returned the **exact** RJW Thm 6.1(ii) formula; Williams Warwick notes, Zhao arXiv:2201.08870, Dasgupta "Trilogies". |
| 2 | WebSearch (general form / operator) | "formal power series antiderivative (1+X) d/dX log = 1/(1+X) Iwasawa Mahler transform measure" | **yes** | Mahler/Amice iso `μ ↔ Φ_μ ∈ K[[T]]`; `(t d/dt)ᵐ Φ_μ\|_{t=1}` recovers moments | Confirms the **operator** `(1+X)d/dX` is the standard moment/L-value operator on the transform. Williams notes, Coates–Sujatha. |
| 3 | WebSearch (named-after / aliases) | "Rodrigues Jacinto Williams introduction p-adic L-functions Theorem 6.1 Leopoldt ... Mahler transform antiderivative" | **yes** | Identifies **"RJW" = Rodrigues Jacinto & Williams, arXiv:2309.15692**, §5 (interpolation at Dirichlet chars), §6 (values at s=1, Thm 6.1) | The project's exact primary source (matches the docstring's "RJW Theorem 6.1(ii)"). Published in Essential Number Theory (MSP). |
| 4 | ChatGPT MCP | (intended) "standard form + generality + historical evolution of: the formal identity `∂F̃ = F` for `∂ = (1+T)d/dT` and the antiderivative of the Amice transform used in Leopoldt's `L_p(θ,1)` formula" | **n/a** | — | **n/a — `plugin:mathlib-quality:chatgpt-math` is in `~/.claude/mcp-needs-auth-cache.json`; the server requires interactive auth not available in this non-interactive worker session.** Same as the sibling reports (`FtildeA.md`, `rhoA.md`, `Ftilde.md`) which all record this. Compensated by extra WebSearch depth (#1–#3, #10 below at three generality levels) + the project's verbatim RJW citations (authoritative). |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/PadicLFunctions/` | **n/a** | — | **n/a — neither directory exists** (no `.mathlib-quality/references/`, no `refs/` symlink in this checkout). The project instead carries its RJW/TeX line citations inline in docstrings (e.g. "TeX 2100–2110, Lem 6.3"). |
| 6 | nLab | "Amice transform / Iwasawa algebra / measures Z_p power series / Mahler" | **yes** (adjacent) | Mahler's theorem (binomial basis); Mahler transform = `O_L`-algebra iso measures ↔ power series; Iwasawa `Z_p[[T]]` with `T ↦ Δ₁−Δ₀` | nLab has the Mahler/Amice iso machinery but **no** standalone "shifted-log antiderivative" or Leopoldt-`L_p(θ,1)` page. The `(1+T)`-operator side is standard. |
| 7 | nCatLab (categorical) | — | **n/a** | — | **n/a — not a categorical statement.** It is a coefficient-level formal-power-series identity over a fixed ring; no universal property or higher structure is involved. |
| 8 | Stacks Project (alg geom) | — | **n/a** | — | **n/a — not an algebraic-geometry concept.** p-adic L-function / measure analysis, outside Stacks' scope (schemes/stacks/cohomology). |
| 9 | MathOverflow / Math.StackExchange | "p-adic L-function value at 1 Leopoldt formula sum θ⁻¹ log cyclotomic units derivation" | **yes** | `L_p(1,χ) = −(1−χ(p)/p)·(τ(χ)/f)·Σ_a χ̄(a) log_p(1−ζ^a)` (verbatim) | Surfaced the exact value formula again + the *route* (algebraic interpretation of the analytic value via principal-unit logs); confirms the antiderivative is the standard derivation device. |
| 10 | recent arXiv (last ~5 yrs) | "derivative of power series attached to Γ-transform of p-adic measures"; "Sum Expressions for Kubota–Leopoldt p-adic L-functions" (Zhao, 2201.08870) | **yes** | Γ-transform `(t d/dt)`-operator on the Amice transform (J. Number Theory 2009); Zhao gives sum expressions for KL `L_p` without restriction on `p` | The `∂ = (1+T)d/dT` operator acting on a measure's transform to extract L-values is an **active, standard** technique. The specific antiderivative `F̃_θ` is paper-internal to RJW. |

The protocol passed: WebSearch ran 4 distinct queries across three generality levels (specific
Leopoldt form #1/#9, general Mahler/operator form #2/#10, named-after / source-identification #3);
local references checked (`n/a`, absent); nLab checked (adjacent hit); Stacks / nCatLab `n/a` with
reasons; MathOverflow/arXiv checked (hits). ChatGPT MCP recorded `n/a` with a concrete reason
(server needs auth) and compensated.

### Literature summary (Phase 3)

Concept identified as: **RJW Lemma 6.5, first half (`∂F̃_θ = F_θ`)** — the formal
logarithmic-derivative identity for the operator `∂ = (1+T)d/dT` applied to the §6.2 antiderivative
`F̃_θ`, in the mixed conductor case `N = D·pⁿ` with `D > 1`. It is the engine of **Leopoldt's
value formula RJW Theorem 6.1(ii)** = `L_p(θ,1) = −(1−θ(p)p⁻¹)·G(θ⁻¹)⁻¹·Σ_c θ⁻¹(c)·log_p(1−ε_N^c)`,
equivalently `L_p(1,χ) = −(1−χ(p)/p)·(τ(χ)/f)·Σ_a χ̄(a) log_p(1−ζ^a)` (Washington Ch. 5 Thm 5.18;
Zhao arXiv:2201.08870; the value formula itself is the project's `LpFunction_one`, not this lemma).

Sources agree on the standard form: **yes** for the *value formula* (#1, #9, #10 all give the same
closed form) and for the *operator* `(1+T)d/dT` on the Amice transform (#2, #6, #10). The *specific
antiderivative* `F̃_θ` and the identity `∂F̃_θ = F_θ` are introduced **in-display inside the proof**
in RJW (not a numbered, exported object).

Most general standard form: the operator identity `(1+T)·∂(antiderivative of F) = F` for the formal
log derivative; mathlib's `PowerSeries.derivativeFun` already realises `d/dT`, and the project's own
`oneAddX_mul_derivative_log` (`PadicExp.lean:471`) already proves the maximally-general base case
`(1+T)·D(PowerSeries.log A) = 1` over any `ℚ`-algebra `A`.

Generality dimensions where the literature varies:
  - coefficient field: RJW/Washington use `ℂ_p`; the Lean form abstracts to any complete ultrametric `CharZero` `ℚ_p`-algebra `K` (already **more general** than the source).
  - conductor: split into `D = 1` (wild only; sibling `FtildeA`) vs `D > 1` (mixed; **this lemma**) for arithmetic reasons (norm-one of `1 − ε^c`); RJW handles both.

Disagreement with the literature: **none** — the Lean statement is a faithful, slightly-more-general
(abstract `K`) rendering of RJW Lemma 6.5's first half.

---

### Generality analysis — `one_add_mul_derivative_Ftilde`

Literature-standard form (from Phase 3): the formal identity `∂F̃_θ = F_θ` (`∂ = (1+T)d/dT`) for
RJW's §6.2 antiderivative, over `ℂ_p` (RJW) — here abstracted over a complete ultrametric `CharZero`
`ℚ_p`-algebra `K`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedField K] [NormedAlgebra ℚ_[p] K] [IsUltrametricDist K]` | complete-ultrametric `ℚ_p`-algebra `K` (ℂ_p stand-in) | RJW pins `ℂ_p` | **NO (this is already more general)** | The identity is purely formal at the *coefficient* level; the analytic instances are needed only because `Ftilde`/`logSeriesAt` carry the `extLog_p` constant terms (p-adic log of `K`). Already weaker than the source's `ℂ_p`. |
| 2 | `[CompleteSpace K] [CharZero K]` | present in the variable block but **`omit`-ted** for this theorem (line 219) | — | already dropped | The author already removed the two instances this formal identity doesn't use. No further weakening here. |
| 3 | `(hN : 1 < N)` | modulus > 1 | conductor of `θ` | NO | Needed so `Σ_{c} θ⁻¹(c) = 0` (orthogonality of the non-trivial character) holds over the full residue system; essential to cancel the constant `1`-terms. |
| 4 | `(hθ1 : θ ≠ 1)` | non-trivial character | non-trivial `θ` | NO | The constant-term cancellation `Σ_c θ⁻¹(c) = 0` is **false** for `θ = 1`; hypothesis is essential (used at `MulChar.sum_eq_zero_of_ne_one`). |
| 5 | `(hε : IsPrimitiveRoot ε N)` | primitive `N`-th root | `ε_N` primitive | NO | `Ftilde` is defined relative to this `ε`; primitivity pins `ε^c = 1 ⟺ N∣c`, used to identify which terms survive. |
| 6 | `(hunit : ∀ c…, ¬N∣c → IsUnit (ε^c−1))` | per-root unit side-condition | implicit (`ε^c ≠ 1` ⇒ field-unit) over `ℂ_p` | borderline | Could in principle be *derived* (a field nonzero is a unit, and `ε^c ≠ 1` for `¬N∣c` by primitivity — exactly what the consumer `p_mul_constantCoeff_mahlerK_rhoTheta:796` does). Carrying it as a hypothesis is a deliberate decoupling so `Ftilde` need not assume `K` is a field at this layer. A maximally-tidy mathlib version might internalise it; not a generality *weakening* in the literature sense. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (already abstracted beyond RJW's `ℂ_p`; the two unused
analytic instances are already `omit`-ted; every remaining hypothesis is essential or a deliberate
decoupling). Number of weakening opportunities found: **0** literature-grounded weakenings (row 6 is
a possible internalisation, not a generalisation).

Proposed restatement (if STRICTLY NARROWER): n/a — not narrower.

Cost of restatement: n/a.

→ MAXIMALLY GENERAL → Phase 7 considers YES-add-as-is or the NO/BORDERLINE buckets (after 4c).

### Modern-idiom check (Phase 4c)

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preamble → typeclass/instance? | **no** | — | Already fully typeclass-driven (`NormedAlgebra`, `IsUltrametricDist`, `DirichletCharacter`). No bundled-hypothesis preamble to convert. |
| 2 | sequences/metric → filters/topology? | **no** | — | This is a *formal* (coefficient-wise) power-series identity; no limits, sequences, or nets appear. Nothing to filter-ise. |
| 3 | construct object → universal-property class? | **partly, but no real win** | One could name the operator `∂ = (1+T)·derivativeFun` as a bundled derivation. | A named `∂` is mild reusable formal-NT infrastructure, but the *theorem* would read the same; it does not unlock new mathlib API. Flagged as a question for the human (Phase 7 Q4), not a forcing modernisation. |
| 4 | set+closure-predicate → bundled substructure? | **no** | — | No subset/substructure here. |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | **no (already done)** | — | Already over an abstract `K`; the field structure is used only incidentally (and row-6's unit hypothesis deliberately avoids assuming it). |
| 6 | 1-categorical → higher-categorical? | **no** | — | Not categorical. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary group/monoid? | **no** | — | The index `c ∈ range N` and the character `θ` mod `N` are intrinsic to the arithmetic (Dirichlet character orthogonality); generalising `N` away would destroy the statement. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (no real organisational improvement). The single candidate — a named
`∂ = (1+T)d/dT` derivation (row 3) — is a packaging nicety that does not change the mathematical
content or unlock blocked proofs; it is surfaced as a numbered question, not a forcing
YES-but-generalise-first. One-line reason: this is a fixed-`N`, fixed-`θ` analytic-NT formal
identity already stated at full coefficient-level generality over an abstract `ℚ_p`-algebra; there
is no contemporary mathlib formulation that composes with more of the library.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities or
typeclass-search paths, so the diamond/defeq phase is skipped.

---

### Mathlib search-status: `one_add_mul_derivative_Ftilde`

[A] Lean-Finder       "(1+X) times formal derivative of antiderivative equals F"; "p-adic L-function value at 1 Leopoldt logarithm sum"   → **n/a in this environment** (no Lean-Finder MCP/web access wired in this worker); compensated by [B]/[C]/[D]/[E] + the literature search.
[B] Loogle            type pattern `(1 + PowerSeries.X) * PowerSeries.derivativeFun _ = _`; `_ * Ring.inverse ((1 + PowerSeries.X) * PowerSeries.C _ - 1)`   → **no hits** (grep over local mathlib `RingTheory/PowerSeries/*.lean` for `(1 + .* derivativeFun` and `derivativeFun.*Ring.inverse` returned nothing).
[C] LeanSearch        "Kubota Leopoldt p-adic L-function value at s=1"; "formal antiderivative logarithmic derivative power series character sum"   → covered via WebSearch #1–#3/#9/#10; mathlib has **no** Kubota–Leopoldt / Iwasawa / Amice–Mahler development to match (see [D]).
[D] Grep mathlib src  in `/Users/administrator/Untitled/.lake/packages/mathlib/Mathlib/`: `kubota`/`leopoldt`/`iwasawa` (filenames) → **none**; `Mahler`/`Amice` → **none**; p-adic L-function → **none** (only `NumberTheory/DirichletCharacter/{Basic,Bounds}` + complex `EulerProduct/DirichletLSeries`); `PowerSeries.derivativeFun` → **present** (`RingTheory/PowerSeries/Derivative.lean:38`) with generic API only (`derivativeFun_{add,mul,smul,C,one}`, `coeff_derivativeFun`, `derivative_inv'`); the target identity and `F̃_θ` → **absent**.
[E] Name pattern      `lean_local_search`-style grep for `derivative.*Ftilde`, `one_add_mul_derivative`, `Leopoldt`, `LpFunction` across mathlib   → **no mathlib hits** (the only `one_add_mul_derivative_*` names are the project's own in `ValuesAtOne.lean`/`ResidueZeta.lean`/`FormalPsi.lean`).

Searched for both:
  - the user's current form (`(1+X)·∂F̃_θ = −Σ θ⁻¹(c)·Ring.inverse(...)`) — absent.
  - the literature-standard form (the operator identity `∂(antiderivative) = F`; the value formula `L_p(θ,1)`) — absent. Mathlib has the **base** maximally-general fact only via `PowerSeries.derivativeFun` (and, in the project's pinned mathlib, `PowerSeries.log` with `(1+X)·D log = 1`, which the project re-proves as `oneAddX_mul_derivative_log`/`one_add_mul_derivative_formalLog`). It does **not** have the character-weighted antiderivative identity.

Concluded: **not in mathlib** (all 5 methods exhausted, both forms). Mathlib supplies only the
generic `PowerSeries.derivativeFun` API the proof *consumes*; neither this identity nor the
Kubota–Leopoldt / Amice–Mahler-transform tower it lives in is present in any form.

---

### Call sites — `one_add_mul_derivative_Ftilde`

Internal use count: **K = 1** (within the project, not counting the declaring lemma).
External-to-file callers: **0 distinct files** (no project file outside `ValuesAtOne.lean` uses it; the only other file mentioning the name, `ResidueZeta.lean`, declares the *sibling* `one_add_mul_derivative_FtildeA`, not a call).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| ValuesAtOne.lean:815 | `... one_add_mul_derivative_Ftilde hN hθ1 hε hunit, hGtwist]` — rewrites `(1+X)·∂(C G⁻¹·F̃_θ)` inside `p_mul_constantCoeff_mahlerK_rhoTheta` (the assembly toward `LpFunction_one`). |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - (none) — the identity is used exactly once, at its sole consumer; not re-derived inline anywhere.

What this tells us: `K = 1` internal use, no inline re-derivation, 0 external callers. Per the
call-sites table this is the "possibly the wrong abstraction / private step in one computation"
signal — it leans **away** from a standalone YES and **toward** NO/BORDERLINE. It is a single,
faithful step in one computation (`L_p(θ,1)`), exactly as RJW treats it (an in-proof lemma).

### Composition check (Phase 6)

Can `one_add_mul_derivative_Ftilde` be derived from mathlib in ≤3 chained calls?

Attempt 1: unfold `Ftilde`, push `∂` through the negated sum, apply the per-root building block.
  - Mathlib decls used: `PowerSeries.derivativeFun` and its `map_neg`/`map_sum`/`derivativeFun_smul` API; **project** `one_add_mul_derivative_logSeriesAt` (itself a ~60-line proof); **project** `MulChar.sum_eq_zero_of_ne_one`.
  - Result: **fails as a composition** — even granting the per-root lemma, the proof still must (a) push `∂` through `−Σ_c θ⁻¹(c)·logSeriesAt(ε^c)` by linearity, (b) split off and *kill* the `c=0` term via `θ⁻¹(0)=0`, (c) apply the per-root identity to each surviving term, (d) reindex `range N ↔ ZMod N` and collapse the constant `1`-terms via the character orthogonality `Σ_c θ⁻¹(c)=0`. That is a genuine 54-line, ~25-tactic-step proof with non-trivial reasoning between steps (`Finset.sum_congr`, `by_cases N∣c`, `Finset.sum_nbij'`, `MulChar.sum_eq_zero_of_ne_one`).
  - Notes: the closest mathlib has is the **base** identity (one root, `PowerSeries.log`); the character-weighted finite-sum version with the orthogonality cancellation is new content, not a 1–3-call glue.

Attempt 2: n/a.

Conclusion: **NOT-COMPOSABLE.** (Per the Phase-6 heuristics table: "multiple `have`s with
non-trivial reasoning between" and "anything requiring `Finset.sum_congr`/orthogonality" = a proof,
not a composition.)

---

## Verdict: `one_add_mul_derivative_Ftilde`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): identified **exactly** as RJW Lemma 6.5 first half (`∂F̃_θ = F_θ`, arXiv:2309.15692 §6.2), the `θ≠1` mixed-conductor engine of Leopoldt's value formula Thm 6.1(ii). The value formula was matched **verbatim** against the literature (#1/#9/#10); the `(1+T)d/dT` operator on the Amice transform is standard (#2/#6/#10); the specific antiderivative is paper-internal (in-display, unnamed).
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — already abstracted over an arbitrary complete ultrametric `CharZero` `ℚ_p`-algebra `K` (beyond RJW's `ℂ_p`), the two unused instances already `omit`-ted, every remaining hypothesis essential. Phase 4c found **no** real modern-idiom improvement (the lone `∂`-naming idea is a packaging question, surfaced below).
- Mathlib search (Phase 5): **not in mathlib** — neither this identity nor the Kubota–Leopoldt / Amice–Mahler-transform development is present; only the generic `PowerSeries.derivativeFun` API the proof consumes.
- Composition check (Phase 6): **NOT-COMPOSABLE** (a real 54-line / ~25-step proof on project-specific objects; K = 1 internal use, 0 external).

**Rationale.**

This is not a "is it true and useful?" question — it is plainly both — but a "is this the right
*unit* for mathlib, and is now the right time?" question, and that turns on facts the search cannot
supply. The result is genuinely novel for mathlib and non-trivial, so it is neither
`NO-mathlib-has-it` nor `NO-composable-from-mathlib`; and it is maximally general for what it states,
so the generality gate does not force `YES-but-generalise-first`. The reason it is **not** a clean
`YES-add-as-is` is that the theorem is *constitutively* about objects — `Ftilde` (`F̃_θ`), the
per-root `logSeriesAt`, and the right-hand `F_θ` built from `Ring.inverse((1+T)C(ε^c)−1)` — that
exist only as bookkeeping inside this one formalisation of RJW §6.2. A theorem can only be
upstreamed once the *definitions it mentions* have a home and a name. The owning definition `Ftilde`
has already been assessed (`PadicLFunctions.MeasureR.Ftilde.md`) as **`NO-composable-from-mathlib`**:
mathlib has the reusable ingredient (the Mercator log of each summand, `PowerSeries.log`/`logOf`),
but the `θ⁻¹`-weighted, `G⁻¹`-cleared, `extLog`-constant-laden character sum is project-local, and
mathlib has **no** p-adic logarithm and **no** Kubota–Leopoldt p-adic L-function to host it. The
per-root `logSeriesAt` is likewise `NO-composable`. So the mathlib-worthiness of *this lemma about
those objects* is downstream of, and inseparable from, the upstreaming decision for the whole
p-adic-L tower (Kubota–Leopoldt ζ_p, the Amice/Mahler transform `μ ↦ Φ_μ`, `F_θ`, `F̃_θ`). If that
tower ever goes to mathlib, this lemma ships *with* it (then as `YES-add-as-is`, after the already-
done `omit`-tidy); if it stays project-local, this lemma stays with it.

Crucially, this is the **exact theorem-level analogue** of the already-assessed sibling
`one_add_mul_derivative_FtildeA` (the `D=1` wild-only case, RJW Lemma 7.3), which was decided
`BORDERLINE-needs-human` on identical grounds (maximally general, novel, NOT-composable, but
inseparable from the tower's upstreaming decision). The two should be decided **together**, by the
same answer. The single internal call site (`ValuesAtOne.lean:815`) and zero external consumers
reinforce that today it is a private step in one computation. Note the re-aim rule does **not**
fire: the owning def `Ftilde` is `NO-composable-from-mathlib`, not `NO-mathlib-has-it`, so there is
no more-general mathlib `D'` to re-aim this lemma at — which is exactly why the verdict is the
human-judgment bucket rather than an automatic NO.

**Numbered questions (≤5):**

1. Is the **p-adic L-function development as a whole** (Kubota–Leopoldt ζ_p, the Amice/Mahler
   transform of measures on ℤ_p, `F_θ`/`F̃_θ`, `ρ_θ`, `mahlerK`) intended for upstreaming to
   mathlib, or is it a standalone AINTLIB project formalising arXiv:2309.15692? (If standalone →
   drop from mathlib consideration; the lemma is correctly project-local.)
2. If yes to (1): should the **base objects** `Ftilde`/`logSeriesAt` (and the wild-case
   `FtildeA`/`uA`) be upstreamed first under mathlib-canonical names (e.g. a `PadicLFunction.`
   namespace), at which point this lemma — and its sibling `one_add_mul_derivative_FtildeA` — ship
   *with* them as `YES-add-as-is`?
3. Should `one_add_mul_derivative_Ftilde` (the `D>1` mixed case) and
   `one_add_mul_derivative_FtildeA` (the `D=1` wild case) be **merged or unified** into a single
   upstreamed statement, or kept as two lemmas (as RJW keeps Lemmas 6.5 and 7.3 separate for the
   norm-one-of-`1−ε^c` arithmetic)?
4. For an upstreamed version, keep the statement in the explicit
   `(1 + PowerSeries.X) * PowerSeries.derivativeFun` form, or repackage behind a **named**
   `∂ = (1+T)d/dT` derivation so the API reads `∂F̃_θ = F_θ` (RJW's `∂`)? A named `∂` would be a
   small but real piece of reusable formal-NT infrastructure, shared with the §7 sibling.
5. For an upstreamed version, is the abstract coefficient field `K` (any complete ultrametric
   `CharZero` `ℚ_p`-algebra) the form mathlib should carry, or should it be pinned to `ℂ_p` to match
   RJW and any future p-adic-L API? (Also: internalise the `hunit` side-condition by assuming `K` is
   a field, per the consumer's own derivation at `ValuesAtOne.lean:796`?)

Next action: the user answers the questions; re-run `/mathlibable one_add_mul_derivative_Ftilde` to
resolve. Likely outcomes: standalone project → drop from mathlib (correctly project-local); tower
upstreamed → flips to `YES-add-as-is`, shipped *with* `Ftilde`/`logSeriesAt` and jointly with the
§7 sibling `one_add_mul_derivative_FtildeA`.

---

## Next step

The user answers the five numbered questions above (the decisive one is Q1: is the Kubota–Leopoldt /
Amice–Mahler p-adic-L tower bound for mathlib, or is this a standalone AINTLIB formalisation of
arXiv:2309.15692?), then re-run `/mathlibable PadicLFunctions.MeasureR.one_add_mul_derivative_Ftilde`
to resolve. Decide it **together with** its sibling `one_add_mul_derivative_FtildeA`, which is
already `BORDERLINE` on the same grounds.
