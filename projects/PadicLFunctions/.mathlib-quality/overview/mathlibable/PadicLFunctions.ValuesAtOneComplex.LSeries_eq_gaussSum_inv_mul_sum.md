# `/mathlibable` report — `PadicLFunctions.ValuesAtOneComplex.LSeries_eq_gaussSum_inv_mul_sum`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

**Final verdict: `YES-but-generalise-first`** (reason: MODERN-IDIOM, Bourbaki 2.0).

---

### Baseline (Phase 0)
- lake build:               build not re-run; reasoned from source (per task BUILD NOTE — Phase-0 fallback)
- decl `PadicLFunctions.ValuesAtOneComplex.LSeries_eq_gaussSum_inv_mul_sum`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ValuesAtOneComplex.lean:197`
- kind:                      theorem
- has sorry:                 no (proof body lines 204–248, ~45 substantive lines)
- module docstring summary:  Complex-analysis "quarantine" file computing the classical value `L(θ,1)` (RJW Thm 6.1(i), following Washington Thm 4.9), stated against mathlib's `DirichletCharacter.LFunction`. This theorem is the `Re s > 1` Gauss-sum/Fourier rearrangement that feeds the `s = 1` result `LFunction_one_eq`.

---

### Statement (Phase 1)

`LSeries_eq_gaussSum_inv_mul_sum` is a **theorem** stating the **Gauss-sum / finite-Fourier expansion of the Dirichlet L-series** of a primitive character in the convergence half-plane:

> Let `θ` be a primitive Dirichlet character mod `N` over `ℂ`, with `θ ≠ 1`, and let `ε` be a primitive `N`-th root of unity. For `Re s > 1`,
> `L(θ, s) = G(θ⁻¹)⁻¹ · Σ_{c ∈ (ℤ/N)ˣ} θ⁻¹(c) · L(n ↦ ε^(n·c), s)`,
> where `G(θ⁻¹)` is the Gauss sum of `θ⁻¹` against the additive character `a ↦ ε^a`, and `L(n ↦ ε^(n·c), s) = Σ_{n≥1} ε^(n·c)/n^s` is the Dirichlet series of the geometric/periodic sequence `n ↦ ε^(n·c)`.

The mathematical engine is the **Fourier-inversion identity for a primitive character** (the "separability" relation): `θ(m)·G(θ⁻¹) = Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·ε^(m·c)`. Substituting this into the Dirichlet series of `θ` term by term and using L-series linearity yields the displayed rearrangement. Its `s → 1⁺` boundary limit is RJW Thm 6.1(i) / Washington Thm 4.9, proved next door as `LFunction_one_eq`.

Variables / typeclasses involved (Lean side):
- `{N : ℕ} [NeZero N]` — the conductor (module-level variable).
- `{θ : DirichletCharacter ℂ N}` — the (complex) Dirichlet character.
- `{ε : ℂ}` — the chosen primitive `N`-th root of unity (drives the additive character `AddChar.zmodChar N hε.pow_eq_one`, `a ↦ ε^(a.val)`).
- `{s : ℂ}` — the complex argument.

Hypotheses (Lean side):
- `(hθ : θ.IsPrimitive)` — primitivity (drives `gaussSum_mulShift_of_isPrimitive`, i.e. the Fourier-inversion / separability step).
- `(_hθ1 : θ ≠ 1)` — non-triviality (carried for the API; not used in this proof's body but used by the downstream consumer).
- `(hε : IsPrimitiveRoot ε N)` — `ε` is a primitive `N`-th root of unity.
- `(hs : 1 < s.re)` — convergence range (all the L-series in sight converge absolutely; `LSeriesSummable_of_bounded_of_one_lt_re`).

Conclusion (math): `L(θ,s)` equals the inverse Gauss sum of `θ⁻¹` times the sum over units `c` of `θ⁻¹(c)·L(εⁿᶜ, s)`.

Conclusion (Lean): `LSeries (fun n => θ n) s = (gaussSum θ⁻¹ (AddChar.zmodChar N hε.pow_eq_one))⁻¹ * ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N) * LSeries (fun n => ε ^ (n * ((c : ZMod N)).val)) s`.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: A classical, standard, essentially named result (the Gauss-sum/Fourier expansion of a primitive Dirichlet L-series — the `Re s > 1` half of Washington Thm 4.9 / RJW Thm 6.1(i)), and a structural step in the project's `L(θ,1)` computation. Guaranteed to be in the literature in some form.

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

n/a — kind is `theorem`, not a `def`. (Body is a ~45-line Fourier-inversion + L-series-linearity argument, not a one-liner.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "Dirichlet L-function Gauss sum expansion L(s,χ)=τ(χ̄)⁻¹ Σ χ̄(a) Σ ζ^(an)/nˢ primitive character"        | yes  | `χ(n) = τ(χ̄)⁻¹ Σ_a χ̄(a) e(an/q)` (Fourier inversion); hence `L(s,χ) = τ(χ̄)⁻¹ Σ_a χ̄(a) Σ_n e(an/q)/nˢ` | Encyclopedia of Math + multiple sources gave the inversion identity verbatim; `|τ(χ)| = √q` for primitive |
|  2 | WebSearch (Washington named source) | "Washington Introduction to Cyclotomic Fields Theorem 4.9 L(1,χ) Gauss sum log root of unity"        | yes (background) | confirms Washington's book is the standard source for `L(1,χ)` closed form via Gauss sums in cyclotomic fields | exact Thm 4.9 text not extractable, but the result is the recognised classical theorem the file header cites |
|  3 | WebSearch (general / aliases form) | "primitive Dirichlet character Fourier expansion χ(n)=τ(χ̄)⁻¹ Σ χ̄(a) e(an/q) separable character Gauss sum" | yes  | Fourier transform of primitive `χ` is `∝ χ̄`; `χ` primitive ⇔ `G_q(χ,n)=χ(n)G_q(χ,1)` (separability) | Harvard M259 (Elkies) "L(s,χ) as an entire function; Gauss sums" + Reed/Daileda–Jones notes; this is *exactly* mathlib's `gaussSum_mulShift_of_isPrimitive` |
|  4 | ChatGPT MCP                      | (would ask: standard form + generality + historical formulation of the Gauss-sum/Fourier expansion of a Dirichlet L-series) | n/a  | —                                | `codex`/ChatGPT MCP CLI not installed in this environment — channel recorded n/a (same as sibling `gaussSum_mul_coprime` report) |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/` (and repo `refs/`)                        | n/a  | (directory absent)               | no `references/` dir under this project's `.mathlib-quality/`, and no `refs/` in the checkout. NB the *file header itself* cites Washington Thm 4.9 / RJW Thm 6.1(i) as the source |
|  6 | nLab                             | "Dirichlet L-function" (ncatlab.org/nlab/show/Dirichlet+L-function)                                    | no (this form) | nLab gives only the Dirichlet-series definition + Mellin-transform/theta-function + Iwasawa–Tate adelic treatment | nLab does **not** treat the Gauss-sum/Fourier expansion of `L(s,χ)`; it stays at the theta/functional-equation level |
|  7 | nCatLab (categorical)            | same page, categorical angle                                                                           | n/a  | —                                | not a categorical statement; the result is concrete analytic NT. nLab's coverage (#6) is the relevant categorical-adjacent source, and it lacks this form |
|  8 | Stacks Project                   | —                                                                                                      | n/a  | —                                | not an algebraic-geometry concept; Dirichlet L-series Gauss-sum expansions are not in Stacks |
|  9 | MathOverflow / Math.StackExchange| "Hurwitz zeta is a sum of Dirichlet L-functions and vice-versa" (davidlowryduda / MixedMath) + Lerch/periodic-zeta threads | yes (adjacent) | `L(s,χ) = N⁻ˢ Σ_m χ(m) ζ(s, m/N)` (Hurwitz form) and the periodic-zeta/Lerch linear-combination form | confirms the *Hurwitz* decomposition (a **different** rearrangement, no Gauss sum) is also standard — important contrast for Phase 4c |
| 10 | recent arXiv (last 5 years)      | arXiv:2512.01779 (Karlsson–Müller, "A discrete approach to Dirichlet L-functions, their special values and zeros", 2026); arXiv:2108.13991 | yes (background) | modern work uses finite-Fourier / discrete-spectral expansions of Dirichlet L-functions routinely | the finite-Fourier expansion of a Dirichlet L-series is live, routine modern machinery — not novel mathematics, confirming the result is classical |

### Literature summary (Phase 3)

Concept identified as: **The Gauss-sum / finite-Fourier expansion of a primitive Dirichlet L-series** — substituting the Fourier-inversion identity `χ(n) = τ(χ̄)⁻¹ Σ_a χ̄(a) e(an/q)` (valid exactly because `χ` is primitive: the "separability" relation `G_q(χ,n) = χ(n)·G_q(χ,1)`) into `L(s,χ) = Σ χ(n)/nˢ` and interchanging the (finite) `a`-sum with the L-series. Standard textbook material: Washington, *Introduction to Cyclotomic Fields*, §4 (Thm 4.9 is the `s=1` closed form); Davenport, *Multiplicative Number Theory*, §9; Elkies' Harvard M259 notes "L(s, χ) as an entire function; Gauss sums".

Sources agree on the standard form: **yes**. The canonical statement, for primitive `χ` mod `q` with the *fixed* additive character `e(·/q) = e^{2πi·/q}`, is
`L(s,χ) = τ(χ̄)⁻¹ · Σ_{a mod q} χ̄(a) · Σ_{n≥1} e(an/q)/nˢ`
(equivalently, with the sum running only over the units `a ∈ (ℤ/q)ˣ`, since `χ̄(a)=0` on non-units). The target is exactly this, written with the inner sum over units and with the additive character realised by an **arbitrary** primitive root `ε` rather than the canonical `e^{2πi/q}`.

Most general standard form: holds for any primitive `χ` over any field carrying the requisite roots of unity; classically over `ℂ`. The inner Dirichlet series `Σ e(an/q)/nˢ` is the **periodic zeta / Lerch** function (mathlib's `expZeta (toAddCircle (a)) s` is exactly this for the canonical root).

Generality dimensions where the literature varies:
  - Additive-character / root choice: the literature almost always fixes `e^{2πi/q}`. The target uses an **arbitrary** primitive `N`-th root `ε ∈ ℂ` — a (mild) generalisation, genuinely needed because the downstream consumer `LFunction_one_eq` instantiates `ε` as a primitive root in `ℂ` not assumed to be `e^{2πiN}`.
  - L-function object: literature/textbooks write `L(s,χ) = Σ χ(n)/nˢ` (Dirichlet series) in the convergence range, then separately analytically continue. mathlib's idiom is the entire-function `LFunction` (Hurwitz-zeta-based) plus `LFunction_eq_LSeries` on `Re s > 1`. The target is stated at the **bare-`LSeries`, `Re s > 1`** level.
  - Inner-series object: the literature names the inner sum the *periodic zeta / Lerch* function; mathlib has it as `expZeta (toAddCircle a) s`. The target leaves it as the unevaluated `LSeries (n ↦ ε^(n·c)) s`.

Disagreement with the literature: **none on the mathematics** — the target is precisely the standard Gauss-sum/Fourier expansion in its convergence range, with an arbitrary primitive root in place of the canonical one. The differences are of *formulation* (bare `LSeries` vs mathlib's `LFunction`/`expZeta`), which Phase 4c addresses.

(Several source PDFs — Elkies M259, Reed gsmisc, Daileda–Jones primitivity — returned binary-encoded content that the fetcher could not parse; the standard form was nonetheless confirmed verbatim from the search-result snippets of those same documents plus the Encyclopedia of Mathematics page.)

---

### Generality analysis — `LSeries_eq_gaussSum_inv_mul_sum` (Phase 4)

Literature-standard form (from Phase 3): `L(s,χ) = τ(χ̄)⁻¹ Σ_{a∈(ℤ/q)ˣ} χ̄(a)·(periodic-zeta at a/q)`, for primitive `χ`, in the convergence range; classically over `ℂ` with the canonical root `e^{2πi/q}`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `{θ : DirichletCharacter ℂ N}` over `ℂ` | complex Dirichlet character | complex (classically) | NO (mathematically) | The statement is intrinsically over `ℂ` (Gauss sum invertibility uses `|G|²=N`, and the L-series is complex-analytic). `ℂ` is the right field. |
| 2 | `(hθ : θ.IsPrimitive)` | primitive | primitive | NO | Primitivity is **essential** — the Fourier inversion `θ(m)G(θ⁻¹)=Σ θ⁻¹(c)ε^(mc)` (`gaussSum_mulShift_of_isPrimitive`) holds exactly for primitive `θ` (separability). |
| 3 | `{ε : ℂ} (hε : IsPrimitiveRoot ε N)` | arbitrary primitive `N`-th root | usually fixed `e^{2πi/N}` | (already MORE general than literature) | The target is already *more* general than the textbook form in this axis — it works for any primitive root. This is a real generalisation, needed by the consumer. See Phase 4c #2. |
| 4 | `(hs : 1 < s.re)` | convergence half-plane | convergence range (then continue) | NO | The bare-`LSeries` statement only makes sense where the series converges; the analytic-continuation version is a *different* (and arguably more idiomatic) statement — see Phase 4c #2. |
| 5 | conclusion uses bare `LSeries` + `AddChar.zmodChar` | `LSeries (θ ·) s = G(θ⁻¹)⁻¹ Σ_c θ⁻¹(c) LSeries(εⁿᶜ) s` | `L(s,χ) = …` (periodic-zeta form) | (restatement, not weakening) | Could be re-expressed against mathlib's `LFunction`/`expZeta`/`stdAddChar` ecosystem. See Phase 4c #2,#3. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** on its genuine mathematical axes (complex coefficients, primitivity, arbitrary primitive root, correct convergence hypothesis). In fact it is *strictly more general than the textbook statement* in the root-of-unity axis (#3). No hypothesis is strictly narrower than the literature's; there are **0 true weakenings**.

Number of weakening opportunities found (true weakenings): **0**.
Number of *restatement* opportunities (Bourbaki-2.0 idiom): **2** (see 4c — both concern the `LSeries`-vs-`LFunction`/`expZeta` formulation, not the hypotheses).

Proposed restatement: see Phase 4c.

Cost of restatement: MODERATE-to-EXPENSIVE — moving from bare `LSeries` (convergence range) to the entire-function `LFunction`/`expZeta` form means re-proving against mathlib's analytic-continuation machinery (`LFunction_dft`, `LFunction_stdAddChar_eq_expZeta`), and the arbitrary-`ε` generality must be reconciled with `stdAddChar` (which fixes `ε = e^{2πi/N}`). The elementary `Re s > 1` proof does not directly survive the lift to the entire function.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "let X be a foo" preambles → typeclasses? | no | — | Hypotheses are already typeclass/structure-driven (`IsPrimitive`, `IsPrimitiveRoot`, `NeZero`); nothing to instance-ify. |
| 2 | sequences/metric → filters/topological? **(here: bare `LSeries` on `Re s>1` → entire-function `LFunction` + `expZeta`)** | **yes** | State the expansion against mathlib's entire-function `ZMod.LFunction` and the periodic-zeta `expZeta`, rather than bare `LSeries` valid only for `Re s>1`. The mathlib-idiomatic statement of "L-series = Gauss-sum-weighted sum of periodic-zeta functions" is essentially `LFunction_dft` combined with `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`. | Composes directly with `LFunction_dft` (`Mathlib/NumberTheory/LSeries/ZMod.lean:206`), `LFunction_stdAddChar_eq_expZeta` (ibid:171), the functional equation `LFunction_one_sub`, and `completedLFunction`/`rootNumber` machinery (`DirichletContinuation.lean`). |
| 3 | construct an object where a universal property / named function would characterise it? **(inner series → `expZeta`/periodic zeta)** | **yes** | Replace the unevaluated inner `LSeries (n ↦ ε^(n·c)) s` with mathlib's periodic-zeta `expZeta (toAddCircle …) s` (for the canonical root) — a *named* special function with its own API, rather than an opaque geometric-sequence L-series. | The inner term gains `expZeta`'s analytic-continuation, functional-equation, and special-value API; the whole identity then lives in the same ecosystem as `LFunction_dft`. |
| 4 | set-with-closure-predicate → bundled type? | no | — | No substructure involved. |
| 5 | vector-space/field-specific → modules/(semi)ring? | no | — | Intrinsically over `ℂ` (complex-analytic; Gauss-sum invertibility). Cannot weaken the field. |
| 6 | 1-categorical → higher-categorical? | no | — | Not a categorical statement. |
| 7 | concrete index (ℕ,ℤ,ℝ) → arbitrary monoid/group? | no | — | `N : ℕ` is the conductor (intrinsic to `ZMod`/`DirichletCharacter`); `s : ℂ` is intrinsic to L-series. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes**.
- Proposed mathlib-idiomatic restatement (sketch — for the eventual mathlib PR):
  ```lean
  -- Express the Gauss-sum/Fourier expansion against mathlib's entire-function
  -- LFunction and the periodic-zeta expZeta, in the canonical-root (stdAddChar)
  -- setting, so it sits next to LFunction_dft.
  theorem LFunction_eq_inv_gaussSum_mul_sum {N : ℕ} [NeZero N]
      {θ : DirichletCharacter ℂ N} (hθ : θ.IsPrimitive) (s : ℂ) (hs : s ≠ 1 ∨ θ ≠ 1) :
      LFunction (θ ·) s
        = (gaussSum θ⁻¹ stdAddChar)⁻¹
          * ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N) * expZeta (ZMod.toAddCircle (c : ZMod N)) s := by
    sorry  -- via LFunction_dft + IsPrimitive.fourierTransform_eq_inv_mul_gaussSum;
           -- the bare-LSeries Re s>1 proof does not survive the lift to the entire function
  -- The arbitrary-`ε` generality of the current statement (which the s=1 consumer needs)
  -- would then be recovered as a corollary on `Re s>1` via `LFunction_eq_LSeries`,
  -- relating `AddChar.zmodChar ε` to `stdAddChar` for that specific `ε`.
  ```
- Cost: MODERATE-to-EXPENSIVE (re-proving against `LFunction_dft`/`expZeta`; reconciling arbitrary `ε` with `stdAddChar`). **Cost does not downgrade the verdict.**
- Mathlib downstream this enables: composes with `LFunction_dft`, `LFunction_stdAddChar_eq_expZeta`, `LFunction_one_sub` (functional equation), `completedLFunction`/`rootNumber` — i.e. the entire `Mathlib/NumberTheory/LSeries/ZMod.lean` + `DirichletContinuation.lean` Gauss-sum/Fourier layer. The bare-`LSeries` form is a dead end there (it only exists on `Re s>1` and uses a non-canonical additive character `AddChar.zmodChar` that appears in **no** mathlib `LSeries` file).
- Real mathematical improvement (not just "looks cooler"): mathlib already has *half* of this result (`LFunction_dft` gives `LFunction (𝓕 Φ) s = Σ Φ(j) expZeta(toAddCircle(-j)) s`, and `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum` supplies the Gauss-sum substitution). The genuinely-missing piece is the **packaged** primitive-character statement `LFunction θ s = G(θ⁻¹)⁻¹ Σ_c θ⁻¹(c) expZeta(…) s`. Shipping it in the `LFunction`/`expZeta`/`stdAddChar` idiom makes it interoperate with that existing layer; shipping the bare-`LSeries`-with-hand-rolled-`zmodChar` form would be an orphan that duplicates `LFunction_dft`'s content in an incompatible spelling.

Because Phase 4c finds a real modern-idiom improvement on top of a MAXIMALLY-GENERAL (indeed already-more-general-than-textbook) form, Phase 7 leans **YES-but-generalise-first** (reason = MODERN-IDIOM), not YES-add-as-is, per the verdict gate. (This mirrors the sibling `gaussSum_mul_coprime` verdict in the same file.)

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `LSeries_eq_gaussSum_inv_mul_sum` (Phase 5)

[A] Lean-Finder       "L-series of Dirichlet character equals inverse Gauss sum times sum over units of character times L-series of root-of-unity power" / signature `LSeries (θ ·) s = (gaussSum θ⁻¹ _)⁻¹ * ∑ c, θ⁻¹ c * LSeries (ε^(n·c)) s`  →  endpoint returned 405/SPA (no machine result); the equivalent natural-language intent was run via LeanSearch (C) and WebSearch (#3 below) — no `LSeries`-level Gauss-sum lemma surfaced
[B] Loogle            `LSeries _ _ = gaussSum _ _`  →  **0 declarations**;  `gaussSum _ (AddChar.zmodChar _ _)`  →  **0 declarations** (the `zmodChar` Gauss-sum form used here appears in NO mathlib lemma);  `LSeries (fun n => z^n) _`  →  **0 declarations** (no geometric-series L-series lemma — the inner building block is itself absent from mathlib)
[C] LeanSearch        "L-function of Dirichlet character Gauss sum Fourier expansion sum over units"  →  surfaced only the *functional-equation* layer (`LFunction_dft`, `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`, `rootNumber`, `completedLFunction`), none of which is the `Re s>1` `LSeries` rearrangement
[D] Grep mathlib src  `grep -rn "LSeries" .lake/packages/mathlib/Mathlib/NumberTheory/ | grep -i gauss`  →  **none**;  `grep -rln "AddChar.zmodChar\|zmodChar" .../NumberTheory/LSeries/`  →  **none** (no `LSeries` file mentions `zmodChar`);  `gaussSum` ∩ `LSeries/LFunction` in `NumberTheory/`  →  only `DirichletContinuation.lean` (functional equation via `completedLFunction`/`rootNumber`) and `Analysis/Fourier/ZMod.lean` (`fourierTransform_eq_gaussSum_mulShift`, `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`)
[E] Name pattern      `lean_local_search`/grep for `LSeries.*gaussSum`, `LFunction.*gaussSum`, `*_eq_gaussSum_*`, `LFunction_dft`  →  only `LFunction_dft` (different object: DFT of `Φ` as a sum of `expZeta`, tied to `stdAddChar`) and the `DirichletContinuation` root-number lemmas

Searched for both:
  - the user's current form (bare `LSeries` + `AddChar.zmodChar ε` + sum over units, `Re s>1`) — **not found**.
  - the literature-standard / modern-idiom form (`LFunction`/`expZeta` Gauss-sum expansion via DFT) — **the ingredients exist** (`LFunction_dft` + `fourierTransform_eq_inv_mul_gaussSum`) **but the packaged primitive-character statement is not present** as a single declaration.

**Critical disambiguation.** Mathlib's closest decls are genuinely *different objects*:
- `ZMod.LFunction_dft` (`Mathlib/NumberTheory/LSeries/ZMod.lean:206`): `LFunction (𝓕 Φ) s = ∑ j : ZMod N, Φ j * expZeta (toAddCircle (-j)) s`. This is about the **entire-function `LFunction`** of a **DFT**, summed over **all** `j : ZMod N`, in terms of **`expZeta`** (periodic zeta), and is tied to **`stdAddChar`** (`a ↦ e^{2πi·a/N}`, defined `Circle.coeHom.compAddChar toCircle` at `Analysis/SpecialFunctions/Complex/CircleAddChar.lean:83`). The target uses **bare `LSeries`** (convergence range only), sums over **units** `(ZMod N)ˣ`, uses an **arbitrary** primitive root `ε` via `AddChar.zmodChar N hε.pow_eq_one` (`a ↦ ε^(a.val)`, `LegendreSymbol/AddCharacter.lean:139`), and leaves the inner series as `LSeries(εⁿᶜ)` — and produces `G(θ⁻¹)⁻¹`, not `G(θ)`.
- `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum` (`Analysis/Fourier/ZMod.lean:220`): `𝓕 χ k = χ⁻¹(-k) * gaussSum χ stdAddChar`. This is the Gauss-sum substitution mathlib uses, but only for `stdAddChar`, and only as a step in the **functional equation** (`DirichletContinuation.lean` `completedLFunction_one_sub` / `rootNumber`).

So mathlib deploys the very same Fourier-inversion engine (`gaussSum_mulShift_of_isPrimitive`, which the target also calls) toward the **functional equation in the `expZeta`/`LFunction`/`stdAddChar` idiom**, never toward the target's elementary `Re s>1` `LSeries` rearrangement with an arbitrary root.

Concluded: **not in mathlib** (all 5 methods exhausted, plus the literature-standard form). Mathlib has the *building blocks* of the modern-idiom form (`LFunction_dft` + `fourierTransform_eq_inv_mul_gaussSum`) but neither the packaged statement nor anything at the target's bare-`LSeries`/arbitrary-`ε` level.

---

### Call sites — `LSeries_eq_gaussSum_inv_mul_sum` (Phase 6.0)

Internal use count: **K = 0** external-to-file callers (the convention excludes the declaring file).
In-file consumers: **1** — `LFunction_one_eq`, the next-door theorem in the same file.

| Caller file:line               | Usage pattern (one-line excerpt) |
|--------------------------------|-----------------------------------------------------------|
| `PadicLFunctions/ValuesAtOneComplex.lean:463` (in-file, `LFunction_one_eq`) | `rw [LFunction_eq_LSeries θ hsre, LSeries_eq_gaussSum_inv_mul_sum hθ hθ1 hε hsre, hG]` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `LSeries_eq_gaussSum_inv_mul_sum`?):
  - (none) — no other file in the repo re-derives a Gauss-sum/Fourier L-series expansion. The only repo occurrences of the name are the declaration (line 197) and the in-file consumer (line 463).

Call-sites signal: K = 0 external callers, but exactly 1 *in-file* consumer (`LFunction_one_eq`), to which this theorem is a deliberately-factored intermediate step (the `Re s>1` expansion whose `s→1⁺` limit is the headline RJW Thm 6.1(i)). This is **not** the "K=0 dead code / wrapper bypassed by consumers" pattern: it is a genuine, used, named lemma cleanly separating the convergence-range algebra from the boundary-limit analysis. Combined with NOT-COMPOSABLE (below), the YES-family lean stands. (The narrowness of the consumer base is itself a mild signal that the *form* is project-tuned — reinforcing the Phase-4c restatement recommendation rather than a YES-add-as-is.)

### Composition check (Phase 6)

Can `LSeries_eq_gaussSum_inv_mul_sum` be derived from mathlib in ≤3 chained calls?

Attempt 1: `LFunction_dft` + `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum` + `LFunction_eq_LSeries`.
  - Mathlib decls used: `ZMod.LFunction_dft`, `DirichletCharacter.IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`, `ZMod.LFunction_eq_LSeries`.
  - Result: **fails / not a ≤3-call composition.** To reach the target one must: (i) write `θ = 𝓕 Φ` for `Φ = 𝓕⁻¹ θ` and compute `Φ` via Fourier inversion (`dft_dft`/`invDFT`) into `N⁻¹·θ⁻¹(·)·G(θ)`; (ii) feed that through `LFunction_dft` to get a sum of `expZeta(toAddCircle(-j))` over **all** `j`; (iii) restrict the all-`j` sum to **units** (the non-unit terms vanish because `θ⁻¹` kills non-units — a separate `Finset.sum_subset` argument, exactly as the target's lines 213–222 do by hand); (iv) convert each `expZeta(toAddCircle j) s` to `LSeries(n ↦ ε^(n·j)) s`, which requires relating `stdAddChar` (root `e^{2πi/N}`) to the target's **arbitrary** `AddChar.zmodChar ε` — these are *different additive characters* and there is no mathlib lemma equating their L-series for a general `ε`; (v) move from `LFunction` to `LSeries` via `LFunction_eq_LSeries` on `Re s>1`; (vi) reconcile `G(θ)` vs `G(θ⁻¹)⁻¹`. This is many more than 3 mathlib calls with substantial reasoning between them.

Attempt 2: the target's actual proof — `gaussSum_mulShift_of_isPrimitive` (Fourier inversion) + `LSeries_smul`/`LSeries_sum` (linearity) + summability/`pow_eq_pow_mod` bookkeeping.
  - Mathlib decls used: `gaussSum_mulShift_of_isPrimitive`, `LSeries_smul`, `LSeries_sum`, `LSeriesSummable_of_bounded_of_one_lt_re`, `IsPrimitiveRoot.norm'_eq_one`, `pow_eq_pow_mod`, `ZMod.val_mul`/`val_natCast`, plus the local `gaussSum_inv_ne_zero`/`isPrimitive_inv`.
  - Result: **this is the actual ~45-line proof**, not a composition. It requires (i) the Fourier-inversion identity `θ(m)·G(θ⁻¹)=Σ_c θ⁻¹(c)·ε^(mc)` reindexed from `ZMod N` to units via `Finset.sum_subset` + `MulChar.map_nonunit`; (ii) per-unit summability of `n ↦ ε^(n·c)`; (iii) the modular bookkeeping `ε^(n·c.val) = ε^((n·c).val)`; (iv) packaging the coefficient function as a scalar-times-finite-sum and applying L-series linearity `LSeries_smul`/`LSeries_sum`; (v) a final `Finset.sum_congr`. Far more than 3 mathlib calls, with genuine reasoning between steps.

Conclusion: **NOT-COMPOSABLE.** No ≤3-call mathlib composition yields the statement. Mathlib's `LFunction_dft` is a different (entire-function, `expZeta`, `stdAddChar`, all-residues) object, and bridging it to the target's bare-`LSeries`/units/arbitrary-`ε` form is itself a multi-step proof.

---

## Verdict: `PadicLFunctions.ValuesAtOneComplex.LSeries_eq_gaussSum_inv_mul_sum`

**Category:** `YES-but-generalise-first`

**Evidence:**
- Literature search (Phase 3): classical, standard result — the Gauss-sum/finite-Fourier expansion of a primitive Dirichlet L-series (Washington §4 / Thm 4.9; Davenport §9; Elkies M259). Standard form `L(s,χ)=τ(χ̄)⁻¹ Σ_a χ̄(a)·(periodic zeta)`; the target is exactly this with the inner sum over units and an arbitrary primitive root. ≥3 WebSearch channels (specific form, Washington source, separability/aliases) + nLab + MathOverflow/MixedMath + arXiv corroborate; ChatGPT MCP and local refs recorded n/a with reasons.
- Generality analysis (Phase 4): MAXIMALLY GENERAL on its true axes — and **strictly more general than the textbook form** in the root-of-unity axis (arbitrary `ε`, not just `e^{2πi/N}`). 0 true weakenings. Phase 4c found 2 *restatement* (Bourbaki-2.0) opportunities with real downstream payoff (lift bare `LSeries`→`LFunction`/`expZeta`; align `AddChar.zmodChar ε`→`stdAddChar`).
- Mathlib search (Phase 5): not in mathlib. Loogle returns 0 for `LSeries = gaussSum`, 0 for `gaussSum (zmodChar …)`, 0 for the geometric-series L-series. The adjacent decls (`LFunction_dft`, `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`) are the functional-equation/`expZeta`/`stdAddChar` layer — different objects.
- Composition check (Phase 6): NOT-COMPOSABLE (both the via-`LFunction_dft` route and the actual proof are multi-step, far exceeding 3 mathlib calls).

**Rationale (1–2 paragraphs):**

This is a genuinely missing, classical result: the Gauss-sum / finite-Fourier expansion of a primitive Dirichlet L-series in its convergence range — `L(θ,s) = G(θ⁻¹)⁻¹ Σ_{c∈(ℤ/N)ˣ} θ⁻¹(c)·L(εⁿᶜ,s)` — whose `s→1⁺` boundary limit is the headline RJW Thm 6.1(i) / Washington Thm 4.9. Phase 3 located the standard form across the canonical references, and Phase 5 confirmed mathlib has nothing at this level: there is no lemma relating `LSeries` of a Dirichlet character to a Gauss sum (Loogle: 0 hits), no lemma about `gaussSum (AddChar.zmodChar …)` (0 hits), and no `LSeries` file even mentions `zmodChar`. Mathlib *does* possess the very same Fourier-inversion engine the proof uses (`gaussSum_mulShift_of_isPrimitive`), but deploys it exclusively toward the **functional equation** in the entire-function `LFunction`/`expZeta`/`stdAddChar` idiom (`LFunction_dft`, `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`, `completedLFunction_one_sub`, `rootNumber`) — a structurally different object (all residues, periodic zeta, the canonical root `e^{2πi/N}`, `Re s` arbitrary via continuation). Phase 6 is decisively NOT-COMPOSABLE: bridging mathlib's machinery to the target's bare-`LSeries`/units/arbitrary-`ε` form is itself a multi-step proof, and the actual proof is a ~45-line Fourier-inversion + L-series-linearity argument.

It lands in **YES-but-generalise-first** rather than YES-add-as-is for the reason surfaced in Phase 4c (and mirroring the sibling `gaussSum_mul_coprime` verdict in the same file). Mathlib's idiom for exactly this content is the entire-function `ZMod.LFunction` together with the periodic-zeta `expZeta` and the canonical additive character `stdAddChar` — and mathlib already owns *half* the result via `LFunction_dft`. The target instead uses bare `LSeries` (valid only on `Re s>1`), a hand-rolled additive character `AddChar.zmodChar ε` for an arbitrary `ε` (which appears in **no** mathlib `LSeries` file), and leaves the inner term as an opaque geometric-sequence L-series. As stated it would be an orphan that duplicates `LFunction_dft`'s content in an incompatible spelling. The mathlib-worthy form packages the primitive-character statement against `LFunction`/`expZeta`/`stdAddChar`, sitting next to `LFunction_dft` and composing with the functional-equation layer; the project's arbitrary-`ε`, `Re s>1` form is then recoverable as a corollary via `LFunction_eq_LSeries`. The verdict gate requires YES-but-generalise-first (MODERN-IDIOM) since Phase 4c found a real organisational improvement on top of an already-maximally-general form.

**Reason for the generalisation:** MODERN-IDIOM (Bourbaki 2.0) — Phase 4c found a contemporary mathlib formulation (entire-function `LFunction` + periodic-zeta `expZeta` + canonical `stdAddChar`, interoperating with the existing `LFunction_dft` / functional-equation layer) that is a real API improvement. **NOT** a literature-weakening (Phase 4b found 0 weakenings; the form is already maximally general — indeed more general than the textbook statement in the root-of-unity axis).

**Proposed restatement:**
```lean
-- Lift the bare-`LSeries`, `Re s>1`, arbitrary-`ε` statement to mathlib's
-- entire-function `LFunction` + periodic-zeta `expZeta` + canonical `stdAddChar`
-- idiom, so it sits next to `LFunction_dft` and composes with the functional
-- equation. (The current arbitrary-`ε`, `Re s>1` form becomes a `Re s>1`
-- corollary via `LFunction_eq_LSeries`, relating `AddChar.zmodChar ε` to
-- `stdAddChar` for that specific `ε`.)
theorem LFunction_eq_inv_gaussSum_mul_sum {N : ℕ} [NeZero N]
    {θ : DirichletCharacter ℂ N} (hθ : θ.IsPrimitive) (s : ℂ) (hs : s ≠ 1 ∨ θ ≠ 1) :
    LFunction (θ ·) s
      = (gaussSum θ⁻¹ stdAddChar)⁻¹
        * ∑ c : (ZMod N)ˣ, θ⁻¹ (c : ZMod N) * expZeta (ZMod.toAddCircle (c : ZMod N)) s := by
  sorry  -- via LFunction_dft + IsPrimitive.fourierTransform_eq_inv_mul_gaussSum;
         -- the elementary `Re s>1` `LSeries`-linearity proof does not directly
         -- survive the lift to the entire function.
```

Estimated cost of regeneralisation: **MODERATE-to-EXPENSIVE** (re-proving against `LFunction_dft`/`expZeta`; the all-residues→units restriction; reconciling arbitrary `ε` with `stdAddChar`). Note: cost does not downgrade the verdict — mathlib's value is in shipping the right form.

Mathlib downstream this enables (MODERN-IDIOM, required):
- Composes with `ZMod.LFunction_dft` (`Mathlib/NumberTheory/LSeries/ZMod.lean:206`) and `LFunction_stdAddChar_eq_expZeta` (ibid:171) — the packaged primitive-character expansion is the natural companion to the DFT formula mathlib already has.
- Composes with the functional equation `ZMod.LFunction_one_sub` and the `completedLFunction`/`rootNumber` layer (`Mathlib/NumberTheory/LSeries/DirichletContinuation.lean`), which already consume `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`.
- The inner `expZeta` term inherits mathlib's periodic-zeta analytic-continuation / special-value API — proofs the bare `LSeries(εⁿᶜ)` form blocks (it only exists on `Re s>1`).
- Proofs blocked by the current form: any consumer wanting this in the entire-function setting (e.g. to read off `L(θ,1)` directly from `LFunction`, or to connect to the functional equation) must currently re-derive across the `LSeries`↔`LFunction` and `zmodChar ε`↔`stdAddChar` gaps — exactly what the in-file consumer `LFunction_one_eq` does by hand (`LFunction_eq_LSeries` + boundary-limit gymnastics, lines 440–464).

Proposed mathlib location (eventual PR): `Mathlib/NumberTheory/LSeries/ZMod.lean` (immediately after `LFunction_dft`), or `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` alongside the primitive-character Gauss-sum results. PR grouping: ship together with the sibling `gaussSum_mul_coprime` (also `YES-but-generalise-first` in this file) only if the latter's `coprodCoprime`/`stdAddChar` refactor lands first — otherwise as its own `feat(NumberTheory)` PR.

**Next action:** run `/generalise PadicLFunctions.ValuesAtOneComplex.LSeries_eq_gaussSum_inv_mul_sum` — it will tension the current statement against both the literature-standard form (Phase 3) and the modern-idiom form (Phase 4c: entire-function `LFunction` + `expZeta` + `stdAddChar`, built on `LFunction_dft` + `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`), and determine how much of the elementary proof survives the lift. Then `/cleanup` the restated lemma and open a `feat(NumberTheory): Gauss-sum/Fourier expansion of a primitive Dirichlet L-function` PR.

---

## Next step

Run `/generalise PadicLFunctions.ValuesAtOneComplex.LSeries_eq_gaussSum_inv_mul_sum` to restate against mathlib's entire-function `LFunction` + periodic-zeta `expZeta` + canonical `stdAddChar` (building on the existing `LFunction_dft` and `IsPrimitive.fourierTransform_eq_inv_mul_gaussSum`), recovering the current arbitrary-`ε`/`Re s>1` form as a corollary. Then `/cleanup` and open a `feat(NumberTheory)` PR against `Mathlib/NumberTheory/LSeries/ZMod.lean`.
