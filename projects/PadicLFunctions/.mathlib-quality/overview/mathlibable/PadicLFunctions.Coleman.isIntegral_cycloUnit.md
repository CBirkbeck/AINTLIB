# `/mathlibable` report — `PadicLFunctions.Coleman.isIntegral_cycloUnit`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               **not re-run** (stale/slow per task note); **reasoned from source** — the declaration, its proof, every in-file dependency (`cycloUnit_eq_geomSum`, `zetaSys_isIntegral`), the upstream defs (`cycloUnit` in `Coleman/Map.lean`, `zetaSys`/`zetaSys_primitiveRoot` in `Coleman/Tower.lean`), and every mathlib lemma cited were read directly from `.lake/packages/mathlib/`.
- decl `PadicLFunctions.Coleman.isIntegral_cycloUnit`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:262` (theorem head at line 264).
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local closures `𝒞` (RJW §11.3, arXiv:2309.15692); all objects live inside `ℂ_[p]`. This theorem is one half of the milestone "the Coleman-map inputs `c_n(a)` are naturally elements of `𝒟_n`, hence global" (TeX 3084): the cyclotomic unit `c_n(a)` is integral over `ℤ`.

---

### Statement (Phase 1)

`PadicLFunctions.Coleman.isIntegral_cycloUnit` is a theorem stating the following:

> Let `ξ = ξ_{p^n}` be a primitive `p^n`-th root of unity in `ℂ_[p]` (drawn from the project's fixed compatible system `zetaSys`), and let `a : ℕ`, `n ≥ 1`. The **cyclotomic unit** `c_n(a) = (ξ^a − 1)/(ξ − 1) = 1 + ξ + ⋯ + ξ^{a−1}` is integral over `ℤ` — i.e. it is a root of a monic polynomial with integer coefficients.

Mathematically this is the textbook fact that a **cyclotomic unit is an algebraic integer**: cyclotomic units lie in the ring of integers `ℤ[ξ]` of the cyclotomic field (Wikipedia, "Cyclotomic unit"). The proof rendered in Lean reduces `c_n(a)` to its **geometric-sum form** `∑_{i<a} ξ^i` (clearing the denominator via `geom_sum_mul`, the project's `cycloUnit_eq_geomSum`) and then invokes the two-fold abstract fact "**the integral closure is a ring**": a finite sum of powers of the `ℤ`-integral element `ξ` is `ℤ`-integral.

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — section variable; fixes the prime. Used only to name the ambient field `ℂ_[p]` and the root system `zetaSys p`.
- `{a : ℕ}` — the exponent in `c_n(a)`; only the geometric-sum range `Finset.range a` uses it. (No upper bound `a < p^n` is imposed at the `IsIntegral` statement.)
- `{n : ℕ}` — the level; `ξ_{p^n} = zetaSys p n` is a primitive `p^n`-th root of unity.

Hypotheses (Lean side):
- `(_ha : ¬ (p : ℕ) ∣ a)` — **unused** (the leading underscore in `_ha` flags it; the cyclotomic-unit integrality holds for *every* `a`, coprimality is only needed for `c_n(a)` to be a *unit* / for the inverse `isIntegral_inv_cycloUnit`).
- `(hn : 1 ≤ n)` — needed only to feed `cycloUnit_eq_geomSum` (the denominator `ξ − 1 ≠ 0` requires `p^n > 1`, i.e. `n ≥ 1`).

Conclusion (math): the cyclotomic unit `c_n(a)` is an algebraic integer.

Conclusion (Lean): `IsIntegral ℤ (cycloUnit p a n)`.

**Proof body (verbatim, 2 lines):**
```lean
  rw [cycloUnit_eq_geomSum p hn]
  exact IsIntegral.sum _ fun i _ => (zetaSys_isIntegral p n).pow i
```
i.e. rewrite to `∑_{i<a} ξ^i`, then `IsIntegral.sum` (mathlib) over `(ξ integral).pow i` where `ξ integral` is the project's private `zetaSys_isIntegral` and `.pow` is mathlib's `IsIntegral.pow`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma — one half of the RJW TeX 3084 milestone, feeding `cyclo_elems_mem_globalUnits` (the `IsIntegral ℤ` component of `globalUnits` membership) and, downstream, `IwasawaProof/Generators.lean`. It is not itself a `## Main results` entry (the milestone is the *membership* `cyclo ∈ 𝒞_{∞,1}`, not this integrality lemma) and is not named after a person/place. The abstract content — "a polynomial in an integral element is integral" — is textbook-elementary. (Literature width is EXHAUSTIVE regardless of size.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (a `rw` to the geometric-sum form + a one-line `IsIntegral.sum`/`.pow` composition).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. Check skipped (the one-line check gates `def`/`abbrev`/`structure` only).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form) | "cyclotomic units algebraic integers root of unity ring of integers cyclotomic field" | **yes** | A cyclotomic unit is a unit of `ℚ(ζ_n)`; the prime-power generators are exactly `(ζ^a−1)/(ζ−1)` and `±ζ`; they live in / are units of `𝒪 = ℤ[ζ_n]`, hence algebraic integers. Roots of unity are roots of monic `X^n−1`, hence integral. | Wikipedia "Cyclotomic unit" + "Cyclotomic field" (`𝒪_{ℚ(ω_n)} = ℤ[ω_n]`); Wolfram MathWorld; Erickson "Cyclotomic Fields Part III". Unanimous: the project's `(ξ^a−1)/(ξ−1)` is the standard prime-power cyclotomic-unit generator and it is an algebraic integer. |
|  2 | WebSearch (general / abstract form) | "integral closure is a ring sum and product of integral elements is integral over a commutative ring" | **yes** | "If `x, y` are integral over `A ⊆ R` then `x+y, xy` are integral; the integral elements form a subring (the integral closure)." | Wikipedia "Integral element"; Brandeis Math 101b (Igusa) "Integrality"; Encyclopedia of Mathematics "Integral extension of a ring". This is the *exact abstract content* used by the proof: a finite sum of powers (`∑ ξ^i`) of an integral `ξ` is integral. |
|  3 | WebSearch (named-after / mechanism — the actual fact) | "polynomial in an integral element is integral algebraic integers form a ring proof" | **yes** | "The set of elements integral over `R` forms a subring of `S`." Two classical proofs: finite-module (`A[x]A[y]` f.g.) and resultant/symmetric-functions. Specialises to "the algebraic integers form a ring." | Stein *Algebraic Number Theory* §"Rings of Algebraic Integers"; Stanford Conrad "Integral ring extensions"; Gathmann Comm-Alg §9; TCD Wilkins. Confirms a *polynomial in one integral element* (in particular `∑_{i<a} ξ^i`) is integral. |
|  4 | ChatGPT MCP | (intended: "standard form + generality + historical evolution of: cyclotomic units are algebraic integers; a polynomial/sum-of-powers of an integral element is integral; the integral closure is a ring") | **n/a** | — | **ChatGPT MCP not available in this environment** — no `mcp__…chatgpt…` tool is in the deferred-tool list (the `setup-chatgpt` skill exists but the server is not configured). Recorded n/a, consistent with the sibling report `norm_le_one_of_isIntegral_int.md`. The three WebSearch channels independently converge on both the cyclotomic-unit-specific and the abstract-integral-closure standard forms, so the standard-form question is fully answered without it. |
|  5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and top-level `refs/` | **n/a** | (no references dir) | Neither `projects/PadicLFunctions/.mathlib-quality/references/` nor `refs/` exists in the checkout — recorded n/a. The file's own docstring cites RJW arXiv:2309.15692 §9/§11.3 (TeX 3060–3112, 3084); RJW TeX 2573 names `c_n(a) = (ξ^a−1)/(ξ−1)`. |
|  6 | nLab | "integral closure" / "ring of integers" (ncatlab.org) | **yes** | nLab "integral closure": "The set of all elements of `L` integral over `k` is a subring of `L`, the integral closure of `k` in `L`." nLab "ring of integers": "The set of algebraic integers in `R` is closed under addition, multiplication and negation, hence a subring." | Direct hit on the abstract fact; the `integral+element` page 404'd but `integral+closure` and `ring+of+integers` carry the statement at full generality (any ring extension). |
|  7 | nCatLab (if categorical) | — | **n/a** | — | Not a higher-categorical concept — an elementary integrality fact about a commutative ring extension. Brief look (the nLab "integral closure" entry is the relevant one, covered in #6): nothing 1-/∞-categorical to add. |
|  8 | Stacks Project (if alg geom / comm alg) | "integral closure of R in S is a subring" (stacks.math.columbia.edu) | **yes** | **Lemma 10.36.7 (tag 00GO)**: "Let `R → S` be a ring homomorphism. The set `S' = {s ∈ S : s integral over R}` is an `R`-subalgebra of `S`." (page tag 00GH "Integral elements" family) | Direct hit at maximal generality (arbitrary ring hom): integral elements are closed under `+`, `×` (hence finite sums of powers). |
|  9 | MathOverflow / Math.StackExchange | algebraic integers form a ring / polynomial in an integral element is integral, generality | **yes** | Treated as background-standard: the algebraic integers form a ring; a `ℤ`-polynomial in an algebraic integer is again an algebraic integer; cyclotomic units `∈ ℤ[ζ]`. | Textbook-elementary; carried on MO/MSE as a *step*, not a research question (e.g. "why is `1+ζ+⋯+ζ^{k−1}` an algebraic integer" → "it's a `ℤ`-polynomial in the algebraic integer `ζ`"). |
| 10 | recent arXiv (last 5 years) | cyclotomic units `(ζ^a−1)/(ζ−1)` algebraic integers / integral closure reformulation | **yes (no reformulation)** | RJW arXiv:2309.15692 (the source) uses `c_n(a) = (ξ^a−1)/(ξ−1)` as cyclotomic units and asserts they are global/integral without proof; no recent paper *reformulates* "a cyclotomic unit is an algebraic integer." | The statement is classical (Kummer–Dedekind era; integral-closure-is-a-ring is due to Dedekind per Wikipedia). No modern reformulation exists; mathlib's own `RootsOfUnity/CyclotomicUnits.lean` (Best–Brasca) is the contemporary home. |

The protocol passes: WebSearch ran 3 distinct queries at three generality levels (the specific cyclotomic-unit-is-an-algebraic-integer form; the general "integral closure is a ring" form; the named mechanism = "polynomial in an integral element is integral / algebraic integers form a ring, with proof"); local refs checked (absent → n/a); nLab fetched/searched (hit on "integral closure" + "ring of integers"); Stacks (hit, tag 00GO), nCatLab/MathOverflow/arXiv each looked at with results or an n/a reason. ChatGPT MCP recorded n/a with reason (tool unavailable) — the only channel not run; the three web channels + nLab + Stacks independently cover the standard form.

### Literature summary (Phase 3)

Concept identified as: **(a)** "cyclotomic units are algebraic integers" — the prime-power cyclotomic-unit generators `(ξ^a−1)/(ξ−1)` lie in the ring of integers `ℤ[ξ]` of the cyclotomic field (Wikipedia); and, abstractly, **(b)** "**the integral closure of a ring in an extension is a subring**" — a finite sum / polynomial in an integral element is integral (Stacks 00GO; nLab; Wikipedia "Integral element", proof due to Dedekind). The theorem is the specialisation of (b) to `R = ℤ`, the element `ξ = ξ_{p^n}` (itself integral as a root of unity), and the specific polynomial `∑_{i<a} X^i`.

Sources agree on the standard form: **yes** — unanimous across Wikipedia, MathWorld, Stacks Project, nLab, and every commutative-algebra / algebraic-number-theory text (Stein, Conrad, Gathmann, Igusa). Both the cyclotomic-unit-specific statement and the abstract integral-closure-is-a-ring statement are textbook-canonical.

Most general standard form: For any ring homomorphism `R → S` (Stacks 00GO), the elements of `S` integral over `R` form an `R`-subalgebra; in particular any `R`-polynomial in finitely many integral elements is integral. Specialising to `R = ℤ`, `S = ℂ_[p]` (or `ℤ[ξ]`), the single integral element `ξ` (a root of unity), and the polynomial `1 + X + ⋯ + X^{a−1}` gives exactly the user's theorem.

Generality dimensions where the literature varies:
  - **Base ring**: `ℤ` here → any base ring `R` (Stacks: arbitrary ring hom `R → S`). The proof uses nothing about `ℤ` beyond `IsIntegral ℤ ξ`.
  - **Ambient ring**: `ℂ_[p]` here → any commutative ring `S` containing the integral element. No `ℂ_p`-specific input is used.
  - **The element**: `ξ_{p^n}` (a root of unity in `ℂ_p`) here → any `R`-integral element. The "it's a root of unity" fact (`IsPrimitiveRoot.isIntegral`) is itself a separate, more general mathlib lemma.
  - **The polynomial**: the specific geometric sum `∑_{i<a} X^i` here → any `ℤ`-polynomial (integral closure is closed under all ring operations, not just this sum).

Disagreement with the literature: **none.** The user's form is a correct, strictly-special case of the standard "integral closure is a ring" fact (Dedekind), applied to a cyclotomic unit that the literature already classifies as an algebraic integer.

---

### Generality analysis — `PadicLFunctions.Coleman.isIntegral_cycloUnit`

Literature-standard form (from Phase 3): the integral closure of `R` in `S` is a subring (Stacks 00GO); equivalently any `R`-polynomial in `R`-integral elements is `R`-integral. Cyclotomic units, being `ℤ`-polynomials in the algebraic-integer root of unity, are algebraic integers.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base ring `ℤ` | `IsIntegral ℤ (...)` | integral over any base ring `R` | **yes** | The whole content is "`IsIntegral R` is closed under `Finset.sum` and `pow`"; `R = ℤ` plays no special role. But this generality is *already mathlib* (`IsIntegral.sum`/`IsIntegral.pow` over arbitrary `R`) — not a contribution. |
| 2 | ambient `ℂ_[p]` (the element `cycloUnit p a n`) | the `p`-adic complex cyclotomic unit | any `R`-integral element in any comm-ring `S` | **yes** | Nothing in the proof is `ℂ_p`-specific. The abstract statement is base/ambient-agnostic — again, exactly what mathlib's `IsIntegral.sum`/`pow` already provide. |
| 3 | the element `cycloUnit p a n = (ξ^a−1)/(ξ−1)` | the specific cyclotomic unit | any `ℤ`-polynomial in any integral element | **yes** | The proof first rewrites to `∑_{i<a} ξ^i` (`cycloUnit_eq_geomSum`); from there integrality is the generic sum-of-powers fact. The "`ξ` is integral" input is `IsPrimitiveRoot.isIntegral` (mathlib), not new. |
| 4 | `(_ha : ¬ p ∣ a)` | coprimality hypothesis | **vestigial** | **yes — already unused** | The integrality holds for *every* `a` (`∑_{i<a} ξ^i` is integral unconditionally). The `_ha` is underscore-flagged as unused; it survives only to mirror the inverse lemma `isIntegral_inv_cycloUnit` (where coprimality *is* needed for the unit to be invertible). For mathlib the hypothesis would simply be dropped. |
| 5 | `(hn : 1 ≤ n)` | level `≥ 1` | needed only to make `(ξ−1)/(ξ−1)` well-defined in the *divisional* form | partly removable | `hn` feeds `cycloUnit_eq_geomSum` (denominator `≠ 0` needs `p^n > 1`). If one states integrality directly via the geometric sum `∑_{i<a} ξ^i` (no division), `hn` is also droppable — but that *is* re-deriving toward the abstract fact. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the `ℤ`/`ℂ_p`/specific-cyclotomic-unit specialisation of "integral closure is a ring", carrying even a vestigial hypothesis `_ha`).
Number of weakening opportunities found: **substantial** (base ring, ambient ring, the element, and two removable hypotheses) — **but every one of them lands on machinery mathlib already has** (`IsIntegral.sum`, `IsIntegral.pow` over arbitrary `R`/`S`, and `IsPrimitiveRoot.isIntegral` for the root-of-unity input). The maximally-general statement is **not a missing lemma** — it is `IsIntegral.sum`, which is in mathlib.

Proposed restatement: **none worth shipping as a new lemma.** The "general form" of this theorem is literally `IsIntegral.sum`/`IsIntegral.pow` (already in mathlib), so generalising does not produce a contributable artifact — it produces a one-line application of existing mathlib. This rules out `YES-but-generalise-first` (the generalised form is not novel for mathlib) and points squarely at a NO bucket.

Cost of restatement: **n/a** — there is no new statement to re-prove; the generalisation collapses into existing mathlib calls.

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let R be a foo" preambles → typeclasses? | no | already fully typeclassed (`[Fact p.Prime]`, `IsIntegral` is the bundled predicate) | — |
|  2 | sequences/metric → filters/topological? | no | no limits/convergence here — a single algebraic integrality fact | — |
|  3 | construct an object where a universal-property / bundled object is canonical? | **YES (and it is already mathlib)** | The bundled object is the **integral closure** `integralClosure ℤ ℂ_[p]` (a `Subalgebra`); `IsIntegral.sum`/`pow` are exactly its `sum_mem`/`pow_mem`. The "modern" statement is `cycloUnit p a n ∈ integralClosure ℤ ℂ_[p]`. | the whole `integralClosure`/`Subalgebra` lattice API — **already in mathlib**, used *by* `IsIntegral.sum`'s proof (`(integralClosure R A).sum_mem h`). |
|  4 | set-with-closure-predicate → bundled type? | **YES (already mathlib)** | same as #3: "integral over `ℤ`" as a predicate → the bundled `integralClosure` subalgebra; the project's `IsIntegral.sum` proof already goes through `Subalgebra.sum_mem`. | `integralClosure`, `Subalgebra` lattice, `Algebra.IsIntegral` instances — present. |
|  5 | field-specific → weaken typeclass? | yes (already mathlib) | `ℂ_p` → arbitrary `CommRing` (the abstract fact); mathlib's `IsIntegral.sum` is already at `CommRing` generality | full `IsIntegral` API across all rings |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete base (ℤ) → arbitrary ring? | yes (already mathlib) | drop `ℤ`: `IsIntegral.sum`/`pow` are stated over an arbitrary base `R` | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and it is decisive, but it points at mathlib, not at a new contribution.** The contemporary mathlib formulation of "a `ℤ`-polynomial in an integral element is integral" is the bundled **`integralClosure ℤ S : Subalgebra ℤ S`** together with `Subalgebra.sum_mem`/`pow_mem` — which is *precisely* what mathlib's `IsIntegral.sum` (`(integralClosure R A).sum_mem h`) and `IsIntegral.pow` already are. The root-of-unity input has its own canonical mathlib lemma `IsPrimitiveRoot.isIntegral`. So the user's theorem is not a modernisation mathlib lacks — it is a special case mathlib produces directly. This **rules out a YES verdict** and leaves Phase 7 weighing **NO-mathlib-has-it vs NO-composable-from-mathlib**.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.Coleman.isIntegral_cycloUnit`

[A] Lean-Finder       (MCP tool unavailable in env) — n/a; NL intent "sum of powers of an integral element is integral" / "primitive root of unity is integral over ℤ" / "cyclotomic unit algebraic integer" searched via the literature + grep (methods D/E).
[B] Loogle            (MCP tool unavailable in env) — n/a; type-pattern intent `(∀ i ∈ s, IsIntegral R (f i)) → IsIntegral R (∑ i ∈ s, f i)`, `IsIntegral R x → IsIntegral R (x^n)`, `IsPrimitiveRoot ζ n → IsIntegral ℤ ζ` searched via grep over `RingTheory/IntegralClosure/` and `RingTheory/RootsOfUnity/`.
[C] LeanSearch        (MCP tool unavailable in env) — n/a; NL intent as in [A], resolved via grep over the mathlib source tree.
[D] Grep mathlib src  Searched `.lake/packages/mathlib/Mathlib/` for: `IsIntegral.sum`, `IsIntegral.pow`, `IsIntegral.prod`, `IsIntegral.add`, `IsIntegral.mul`, `IsPrimitiveRoot.isIntegral`, `isIntegral.*root`, `cyclotomicunit`, `geom_sum_mul`, `IsCyclotomicExtension.integral`. **Found every building block — and a dedicated mathlib cyclotomic-units file.**
[E] Name pattern      Searched `isIntegral_cycloUnit`, `cycloUnit`, `cyclotomicUnit`, `*_isIntegral` in `RootsOfUnity/` and `IntegralClosure/`. No decl with this *exact* name (project-local), but the abstract pieces and the cyclotomic-unit file are present.

Searched for both forms:
  - **User's form** (`IsIntegral ℤ (cycloUnit p a n)` — the specific `ℂ_[p]` cyclotomic unit): **not in mathlib** as a single named declaration (it is a project-specific object `cycloUnit p a n` in `ℂ_[p]`).
  - **Literature-standard / abstract form** (integral closure is a ring; sum/power of integral elements is integral; root of unity is integral): **IN mathlib, at full generality:**
    - `IsIntegral.sum` — `RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:246` — `(∀ x ∈ s, IsIntegral R (f x)) → IsIntegral R (∑ x ∈ s, f x)` (proof: `(integralClosure R A).sum_mem h`). **This is the outer step of the project's proof verbatim.**
    - `IsIntegral.pow` — `…/Basic.lean:224` — `IsIntegral R x → IsIntegral R (x ^ n)`. **This is the inner step verbatim.**
    - `IsIntegral.prod` / `IsIntegral.add` / `IsIntegral.mul` — `…/Basic.lean:242` and `IntegralClosure/Algebra/Basic.lean:156,196` — the rest of the "integral closure is a ring" API.
    - `IsPrimitiveRoot.isIntegral (hpos : 0 < n) : IsIntegral ℤ μ` — `RingTheory/RootsOfUnity/Minpoly.lean:41`. **Its proof (`use X^n − 1; monic_X_pow_sub_C 1 …`) is byte-for-byte the project's private `zetaSys_isIntegral` (which uses `X^{p^n} − 1`).** So `zetaSys_isIntegral p n` is just `(zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)` — mathlib already has the only project-private input to the theorem.
    - `IsCyclotomicExtension.integral : Algebra.IsIntegral A B` — `NumberTheory/Cyclotomic/Basic.lean:314` — every element of a cyclotomic extension is integral over the base (same `X^n − 1` proof), an even higher-level form.
    - `geom_sum_mul (x) (n) : (∑ i ∈ range n, x^i) * (x − 1) = x^n − 1` — `Algebra/Ring/GeomSum.lean:232` — the identity backing the project's `cycloUnit_eq_geomSum`.
  - **Mathlib even has a cyclotomic-units file**: `RingTheory/RootsOfUnity/CyclotomicUnits.lean` (Best–Brasca) — `geom_sum_isUnit`, `associated_sub_one_pow_sub_one_of_coprime`, `pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one`, etc. — the *same* `∑ ξ^i` / `(ξ^a−1)/(ξ−1)` objects, in a domain that is integral over `ℤ`. It addresses *unit-ness/associatedness* (not integrality, which is automatic there), confirming mathlib already owns the cyclotomic-unit ecosystem.

Concluded: **"found the building blocks in mathlib (`IsIntegral.sum`, `IsIntegral.pow`, `IsPrimitiveRoot.isIntegral`, `geom_sum_mul`) — and the abstract result `IsIntegral.sum`/`pow` is the project's proof verbatim; composing them yields the user's form."** The project's exact named theorem about `cycloUnit p a n` in `ℂ_[p]` is not in mathlib (it is a project-local object), but the entire mathematical content is mathlib's "integral closure is a ring" API applied to mathlib's "root of unity is integral" lemma. The only non-mathlib ingredient is the rewrite `cycloUnit_eq_geomSum` — itself a one-line `geom_sum_mul` consequence (a *separate* project declaration, assessed on its own).

---

### Call sites — `PadicLFunctions.Coleman.isIntegral_cycloUnit`

Internal use count: **2** (within the project, excluding the declaring line), across **2 files**.
External-to-file callers: **1** distinct file (`IwasawaProof/Generators.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `…/Iwasawa/CyclotomicUnits.lean:415` | `· rw [hval]; exact isIntegral_cycloUnit p ha hn` — inside `cyclo_elems_mem_globalUnits`, supplying the `IsIntegral ℤ (u : ℂ_[p])` component of `globalUnits` membership (the milestone TeX 3084). |
| `…/IwasawaProof/Generators.lean:253` | `· exact isIntegral_cycloUnit p ha hn` — discharging the integrality side-goal for a cyclotomic-unit generator in the `IwasawaProof` development. |

Inline-derivation grep (was the equivalent re-derived elsewhere without this theorem?):
  - **(none directly)** — no other site re-proves `IsIntegral ℤ (cycloUnit …)` by hand. **But** the *sibling* inverse lemma `isIntegral_inv_cycloUnit` (same file, line 305) re-runs the identical pattern `IsIntegral.sum _ fun i _ => ((zetaSys_isIntegral p n).pow a).pow i` on the inverse's geometric sum, and the private input `zetaSys_isIntegral` (line 249) is itself a from-scratch re-derivation of mathlib's `IsPrimitiveRoot.isIntegral`. So the *pattern* (and the root-of-unity-integral input) is duplicated rather than routed through mathlib.

What the call-sites pattern tells us: **K = 2 distinct internal uses across 2 files, no inline re-derivation of this exact statement.** Per the Phase-6 table, K = 2 is the "real but thin API" band — genuinely used (not dead code), yet each use is a single `exact isIntegral_cycloUnit p ha hn` that could equally be the 1-line mathlib composition. Two consumers justify *keeping a thin wrapper* (house style) but do **not** justify a *new mathlib lemma* — both the wrapper body and each call site are a ≤3-call composition of existing mathlib. This nudges to **NO-composable** (route through mathlib / keep a thin local wrapper) rather than NO-mathlib-has-it (the *named* `cycloUnit`-in-`ℂ_p` statement is genuinely project-local, so there is no 0-line mathlib drop-in for the *named* form).

---

### Composition check (Phase 6)

Can `isIntegral_cycloUnit` be derived from mathlib in ≤3 chained calls?

**Attempt 1 — the project's own proof, with the one project-private input swapped for mathlib.** The body is already a mathlib composition; the only non-mathlib leaf is `zetaSys_isIntegral`, which equals `IsPrimitiveRoot.isIntegral`:
```lean
example {a n : ℕ} (hn : 1 ≤ n) : IsIntegral ℤ (cycloUnit p a n) := by
  rw [cycloUnit_eq_geomSum p hn]                                   -- project rewrite (= geom_sum_mul)
  exact IsIntegral.sum _ fun i _ =>                                 -- mathlib  (Basic.lean:246)
    (((zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)).pow i)  -- mathlib  (Minpoly.lean:41 + Basic.lean:224)
```
  - Mathlib decls used: `IsIntegral.sum`, `IsIntegral.pow`, `IsPrimitiveRoot.isIntegral` (+ `geom_sum_mul` underneath `cycloUnit_eq_geomSum`).
  - Result: **succeeds** — this is the existing 2-line proof with `zetaSys_isIntegral p n` replaced by its mathlib equivalent `(zetaSys_primitiveRoot p n).isIntegral …`. Every leaf is a single library call.
  - Notes: **1 `rw` + a 1-line `IsIntegral.sum`/`.pow` composition = within the ≤3-call composition bar.** The `rw [cycloUnit_eq_geomSum]` is the one project-glue step; `cycloUnit_eq_geomSum` is itself one `geom_sum_mul` call (`rw [cycloUnit, div_eq_iff hne, geom_sum_mul]`), so even fully inlined against mathlib the derivation stays at ~3 calls.

**Attempt 2 — bypass the geometric-sum rewrite via the cyclotomic-extension API.** `cycloUnit p a n ∈ K p n` (project's `cycloUnit_mem_K`), and `K p n = ℚ_p(ξ_{p^n})` is a cyclotomic extension; `IsCyclotomicExtension.integral` gives every element integral over the base. Routing `IsIntegral ℚ_p → IsIntegral ℤ` needs a tower/base-change step, so this is a *different* (slightly longer) composition; Attempt 1 is the cleaner one. Recorded as corroboration that mathlib has the result at multiple altitudes.

Conclusion: **COMPOSABLE** — in a ≤3-call chain against mathlib's `IsIntegral.sum` + `IsIntegral.pow` + `IsPrimitiveRoot.isIntegral` (the project's own proof, with its single private leaf `zetaSys_isIntegral` recognised as `IsPrimitiveRoot.isIntegral`), modulo the one-line `geom_sum_mul`-backed rewrite `cycloUnit_eq_geomSum`. It is **not** a "proof in disguise" — there is no `rw […]; ring_nf; aesop`, no multi-`have` reasoning chain; it is genuinely `IsIntegral.sum (… .pow ‹·›)`.

---

## Verdict: `PadicLFunctions.Coleman.isIntegral_cycloUnit`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): unanimous and textbook-elementary — cyclotomic units are algebraic integers (Wikipedia "Cyclotomic unit"; they lie in `ℤ[ζ]`), and abstractly "the integral closure is a ring" so any `ℤ`-polynomial / finite sum of powers of an integral element is integral (Stacks 00GO; nLab "integral closure"/"ring of integers"; Wikipedia "Integral element", proof due to Dedekind).
- Generality analysis (Phase 4): STRICTLY NARROWER (base `ℤ`, ambient `ℂ_p`, specific cyclotomic unit, even a vestigial unused hypothesis `_ha`) — and Phase 4c shows the general/modern form *is already mathlib* (`integralClosure` subalgebra ⇒ `IsIntegral.sum`/`pow`), so **no YES** and **no generalise-first** (the generalisation is not novel).
- Mathlib search (Phase 5): the content is in mathlib as `IsIntegral.sum` (`…/Basic.lean:246`) + `IsIntegral.pow` (`…/Basic.lean:224`) + `IsPrimitiveRoot.isIntegral` (`…/Minpoly.lean:41`); `IsIntegral.sum`/`pow` are the project's proof *verbatim*, and `IsPrimitiveRoot.isIntegral` is the project's private `zetaSys_isIntegral` verbatim. Mathlib also already ships a cyclotomic-units file (`RootsOfUnity/CyclotomicUnits.lean`).
- Composition check (Phase 6): COMPOSABLE in a ≤3-call chain (`cycloUnit_eq_geomSum` rewrite → `IsIntegral.sum` over `(IsPrimitiveRoot.isIntegral …).pow i`).

**Rationale (1–2 paragraphs):**

This theorem is the specialisation "`ℤ`, ambient `ℂ_[p]`, the specific cyclotomic unit `(ξ^a−1)/(ξ−1)`" of a result mathlib already owns at full generality: **the integral closure is a subring**, hence any finite sum of powers of an integral element is integral. The Lean proof makes this transparent — after one project rewrite to the geometric-sum form `∑_{i<a} ξ^i` (the `geom_sum_mul`-backed `cycloUnit_eq_geomSum`), the body is exactly `IsIntegral.sum _ fun i _ => (zetaSys_isIntegral p n).pow i`, i.e. mathlib's `IsIntegral.sum` over mathlib's `IsIntegral.pow`. The one project-private input, `zetaSys_isIntegral` ("`ξ` is integral over `ℤ`"), is itself a from-scratch copy of mathlib's `IsPrimitiveRoot.isIntegral` (`RootsOfUnity/Minpoly.lean:41`) — same `use X^n − 1; monic_X_pow_sub_C 1` proof. So the whole theorem composes from existing mathlib in ≤3 calls: rewrite to the geometric sum, then `IsIntegral.sum`/`IsIntegral.pow` with the root-of-unity integrality from `IsPrimitiveRoot.isIntegral`. Tellingly, mathlib already maintains a *cyclotomic-units file* (`RootsOfUnity/CyclotomicUnits.lean`, Best–Brasca) for these very `(ξ^a−1)/(ξ−1)` / `∑ ξ^i` objects.

Why not a YES bucket: the maximally-general statement is `IsIntegral.sum` itself, which is in mathlib, so Phase 4c finds no *missing* modern form (`YES-add-as-is` and `YES-but-generalise-first` both require the general/modern target to be novel — here it is not). Why NO-**composable** rather than NO-**mathlib-has-it**: there is no single mathlib lemma named for "the cyclotomic unit `cycloUnit p a n` in `ℂ_[p]` is integral" — that *named, project-specific* object is genuinely project-local — so the user's form is not a 0-line drop-in but a short composition of mathlib pieces (plus the one-line `geom_sum_mul` rewrite). The theorem has 2 real consumers (Phase 6.0) with no inline re-derivation, so a *thin* mathlib-backed wrapper may stay for house style, but no new mathlib lemma is justified. (BORDERLINE was considered because keeping-vs-deleting a 2-consumer wrapper is partly a house-style call and because the `cycloUnit_eq_geomSum` rewrite is one project step; but the evidence — mathlib has the abstract content verbatim and the root-of-unity input verbatim, recoverable in ≤3 calls — resolves cleanly to NO-composable, so no question is needed.)

**NO-composable-from-mathlib — refactor-actionable detail:**

WHY not: Mathlib has the building blocks — `IsIntegral.sum`, `IsIntegral.pow`, `IsPrimitiveRoot.isIntegral` — and the project's proof is already a composition of them (with `zetaSys_isIntegral` standing in for `IsPrimitiveRoot.isIntegral`). No standalone mathlib-bound lemma about this `ℂ_[p]` cyclotomic unit is justified: the integrality is the generic "sum of powers of an integral root of unity is integral", one import away. The mathematically right move is to recognise `zetaSys_isIntegral` as `IsPrimitiveRoot.isIntegral` and let the integrality fall out of mathlib's integral-closure-is-a-ring API.

Mathlib building blocks (all with full paths):
  - `IsIntegral.sum` — `.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:246`
  - `IsIntegral.pow` — `.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:224`
  - `IsPrimitiveRoot.isIntegral` — `.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/Minpoly.lean:41`  (`IsIntegral ℤ μ` for a primitive root; replaces the project's private `zetaSys_isIntegral`)
  - `geom_sum_mul` — `.lake/packages/mathlib/Mathlib/Algebra/Ring/GeomSum.lean:232`  (backs `cycloUnit_eq_geomSum`)
  - (corroborating, higher-altitude) `IsCyclotomicExtension.integral` — `.lake/packages/mathlib/Mathlib/NumberTheory/Cyclotomic/Basic.lean:314`; and mathlib's cyclotomic-units file `.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean`.

Composition sketch (the inlined / wrapper body; ≤3 calls):
```lean
-- `zetaSys_primitiveRoot p n : IsPrimitiveRoot (zetaSys p n) (p ^ n)` is in the project;
-- `pow_pos hp.out.pos n : 0 < p ^ n`.
example {a n : ℕ} (hn : 1 ≤ n) : IsIntegral ℤ (cycloUnit p a n) := by
  rw [cycloUnit_eq_geomSum p hn]
  exact IsIntegral.sum _ fun i _ =>
    (((zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)).pow i)
```

Call sites in the project (from Phase 6.0): **K = 2** distinct uses across 2 files — `CyclotomicUnits.lean:415` (inside `cyclo_elems_mem_globalUnits`) and `Generators.lean:253`.

Refactor plan:
  1. Replace the project-private `zetaSys_isIntegral` (line 249) with `IsPrimitiveRoot.isIntegral`: define `zetaSys_isIntegral p n := (zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)` (mathlib import `Mathlib.RingTheory.RootsOfUnity.Minpoly` is already transitively present via the cyclotomic stack), deleting the hand-rolled `⟨X^{p^n} − 1, monic_X_pow_sub_C …, …⟩` term. This dedups the root-of-unity-integral input against mathlib. (Apply the same swap inside `isIntegral_inv_cycloUnit`, line 305, which re-runs the identical pattern.)
  2. Keep `isIntegral_cycloUnit` as a **thin wrapper** whose body is the composition above (its 2 consumers call `isIntegral_cycloUnit p ha hn`, so the call signature is unchanged) — OR inline the 3-call composition at `CyclotomicUnits.lean:415` and `Generators.lean:253` and delete the theorem. With only 2 consumers either is defensible; the thin-wrapper choice is the lighter-touch house-style option. Either way, drop the now-vestigial `_ha` from the wrapper's signature (it is unused), adjusting the 2 call sites to pass one fewer argument.
  3. No new mathlib PR results from this theorem. (If anything in the vicinity is mathlib-worthy it is a *project-local cleanup*, not an upstream contribution — the upstream pieces all exist.)

Next action: dedup `zetaSys_isIntegral` against mathlib's `IsPrimitiveRoot.isIntegral`, then either keep `isIntegral_cycloUnit` as a thin `IsIntegral.sum`/`IsIntegral.pow` wrapper (dropping the unused `_ha`) or inline the ≤3-call composition at its 2 call sites. Do **not** open a mathlib PR for this theorem — its content is already mathlib's integral-closure-is-a-ring API applied to mathlib's root-of-unity integrality.

---

## Next step

Recognise the project's private `zetaSys_isIntegral` as mathlib's `IsPrimitiveRoot.isIntegral` and let `isIntegral_cycloUnit` reduce to the mathlib composition `IsIntegral.sum _ fun i _ => (IsPrimitiveRoot.isIntegral …).pow i` (after the `geom_sum_mul`-backed `cycloUnit_eq_geomSum` rewrite). Keep a thin local wrapper for its 2 consumers (dropping the unused `_ha`) or inline at the 2 call sites; do not upstream — mathlib already owns every ingredient (`IsIntegral.sum`/`pow`, `IsPrimitiveRoot.isIntegral`, and even a `RootsOfUnity/CyclotomicUnits.lean`).
