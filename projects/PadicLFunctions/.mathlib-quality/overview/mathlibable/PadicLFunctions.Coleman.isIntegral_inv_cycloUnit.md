# `/mathlibable` report — `PadicLFunctions.Coleman.isIntegral_inv_cycloUnit`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               **not re-run** (stale/slow per task note); **reasoned from source** — the declaration, its proof, and every dependency were read directly from source: the in-file private lemma `inv_cycloUnit_eq_geomSum` (line 277), the root-of-unity integrality input `zetaSys_isIntegral` (line 249), the upstream def `cycloUnit` (`Coleman/Map.lean:96`), and `zetaSys`/`zetaSys_primitiveRoot` (`Coleman/Tower.lean:86,89`); every mathlib lemma cited was read from `.lake/packages/mathlib/`.
- decl `PadicLFunctions.Coleman.isIntegral_inv_cycloUnit`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:303` (theorem head at line 305).
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local closures `𝒞` (RJW §11.3, arXiv:2309.15692); all objects live inside `ℂ_[p]`. This theorem is the **inverse half** of the milestone "the Coleman-map inputs `c_n(a)` are naturally elements of `𝒟_n`, hence global" (TeX 3084): the inverse `c_n(a)⁻¹` of the cyclotomic unit is integral over `ℤ`.

---

### Statement (Phase 1)

`PadicLFunctions.Coleman.isIntegral_inv_cycloUnit` is a theorem stating the following:

> Let `ξ = ξ_{p^n}` be a primitive `p^n`-th root of unity in `ℂ_[p]` (drawn from the project's fixed compatible system `zetaSys`), let `a : ℕ` with `p ∤ a`, and `n ≥ 1`. The **inverse** of the cyclotomic unit `c_n(a) = (ξ^a − 1)/(ξ − 1)` is integral over `ℤ`. Concretely (choosing `a'` with `a·a' ≡ 1 (mod p^n)`), `c_n(a)⁻¹ = (ξ − 1)/(ξ^a − 1) = 1 + ξ^a + ξ^{2a} + ⋯ + ξ^{(a'−1)a} = ∑_{i<a'} (ξ^a)^i` is a `ℤ`-polynomial in the algebraic-integer `ξ`, hence an algebraic integer.

Mathematically this is the second textbook half of "**a cyclotomic unit is a unit of the ring of integers**": not only is `c_n(a)` an algebraic integer (its `isIntegral_cycloUnit` sibling), but its inverse is too — i.e. `c_n(a)` is a genuine *unit* of `ℤ[ξ]`. The literature gives the explicit inverse as the geometric sum `1 + ξ^{rs} + ⋯ + ξ^{(u−1)rs}` (Wikipedia "Cyclotomic unit"; Washington, *Introduction to Cyclotomic Fields*, Ch. 8), which is exactly the project's `inv_cycloUnit_eq_geomSum`. The Lean proof reduces `c_n(a)⁻¹` to that geometric sum and then invokes the abstract fact "**the integral closure is a ring**": a finite sum of powers of the `ℤ`-integral element `ξ` is `ℤ`-integral.

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — section variable; fixes the prime. Used to name the ambient field `ℂ_[p]`, the root system `zetaSys p`, and to obtain `a'` (coprimality of `a` with `p^n` uses `p.Prime`).
- `{a : ℕ}` — the exponent in `c_n(a)`.
- `{n : ℕ}` — the level; `ξ_{p^n} = zetaSys p n` is a primitive `p^n`-th root of unity.

Hypotheses (Lean side):
- `(ha : ¬ (p : ℕ) ∣ a)` — **genuinely used** (unlike the vestigial `_ha` in the non-inverse sibling). It is needed so that `a` is coprime to `p^n`, which lets `inv_cycloUnit_eq_geomSum` produce `a'` with `a·a' ≡ 1 (mod p^n)` (via `Nat.exists_mul_mod_eq_one_of_coprime`) and hence write the inverse as a *finite* geometric sum.
- `(hn : 1 ≤ n)` — needed so `p^n > 1` (the denominators `ξ − 1`, `ξ^a − 1` are nonzero and `orderOf ξ = p^n` is used).

Conclusion (math): the inverse of the cyclotomic unit `c_n(a)` is an algebraic integer (so `c_n(a) ∈ ℤ[ξ]^×`).

Conclusion (Lean): `IsIntegral ℤ (cycloUnit p a n)⁻¹`.

**Proof body (verbatim, 3 lines):**
```lean
  obtain ⟨a', ha'⟩ := inv_cycloUnit_eq_geomSum p ha hn
  rw [ha']
  exact IsIntegral.sum _ fun i _ => ((zetaSys_isIntegral p n).pow a).pow i
```
i.e. obtain the inverse-as-geometric-sum identity `c_n(a)⁻¹ = ∑_{i<a'} (ξ^a)^i` (the project's private `inv_cycloUnit_eq_geomSum`), rewrite to it, then `IsIntegral.sum` (mathlib) over `((ξ integral).pow a).pow i`, where `ξ integral` is the project's private `zetaSys_isIntegral` and `.pow` is mathlib's `IsIntegral.pow`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma — the inverse half of the RJW TeX 3084 milestone, feeding `cyclo_elems_mem_globalUnits` (the `IsIntegral ℤ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])` component of `globalUnits` membership) and, downstream, `IwasawaProof/Generators.lean`. It is not itself a `## Main results` entry (the milestone is the *membership* `cyclo ∈ 𝒞_{∞,1}`, not this integrality lemma) and is not named after a person/place. The abstract content — "a polynomial in an integral element is integral" — is textbook-elementary. (Literature width is EXHAUSTIVE regardless of size.)

### One-line check (Phase 2b)

Body line count: 3 substantive lines (obtain the inverse-geometric-sum identity, a `rw`, then a one-line `IsIntegral.sum`/`.pow` composition).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. Check skipped (the one-line check gates `def`/`abbrev`/`structure` only).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form) | "cyclotomic unit inverse algebraic integer ring of integers cyclotomic field" | **yes** | A cyclotomic unit `(ζ^a−1)/(ζ−1)` (for `(a,n)=1`, `n` a prime power) is a unit of `𝒪 = ℤ[ζ_n]`; **and its inverse is also in `ℤ[ζ_n]`**: "if `u` with `n ∣ us−1`, then `ξ⁻¹ = (1−ω^{rus})/(1−ω^{rs}) = 1 + ω^{rs} + ⋯ + ω^{(u−1)rs} ∈ ℤ[ω]`." | Wikipedia "Cyclotomic unit" + "Cyclotomic field" (`𝒪_{ℚ(ω_n)} = ℤ[ω_n]`); Conrad/Stanford handout "Math 154"; Lean community blog "ring of integers of a cyclotomic field". **The explicit inverse-as-geometric-sum is byte-for-byte the project's `inv_cycloUnit_eq_geomSum`.** |
|  2 | WebSearch (general / standard form) | "cyclotomic units (zeta^a − 1)/(zeta − 1) unit ring of integers Washington" | **yes** | "For every `a` with `(a,n)=1`, `(ζ^a−1)/(ζ−1)` is a unit in the ring of integers of `ℚ(ζ)`." The prime-power generators `(ζ^a−1)/(ζ−1)` and `±ζ^a` generate the cyclotomic-unit group. | Wikipedia "Cyclotomic unit"; LTCC Algebraic Number Theory Part 4 §10; Washington's book is the canonical reference (Ch. 8 cyclotomic units, index formula). Confirms unit-ness in `𝒪`, i.e. both the element and its inverse are integral. |
|  3 | WebSearch (named mechanism — the geometric sum) | "\"cyclotomic unit\" definition geometric sum 1 + zeta + ⋯ + zeta^(a−1) is a unit" | **yes** | `(ζ^a−1)/(ζ−1) = 1 + ζ + ⋯ + ζ^{a−1}` is a unit; the inverse is the analogous geometric sum in `ζ^a`. Both are `ℤ`-polynomials in `ζ`. | Wikipedia "Cyclotomic unit"; Reed "The cyclotomic zeta function"; projecteuclid ASPM "Zeta function, class number and cyclotomic units". Confirms the geometric-sum mechanism for *both* the unit and its inverse. |
|  4 | ChatGPT MCP | (intended: "standard form + generality + historical evolution of: the inverse of a cyclotomic unit is an algebraic integer; explicit inverse = geometric sum `∑ (ζ^a)^i`; the integral closure is a ring") | **n/a** | — | **ChatGPT MCP not available in this environment** — no `mcp__…chatgpt…` tool is in the deferred-tool list (the `setup-chatgpt` skill exists but the server is not configured). Recorded n/a, consistent with the sibling reports `isIntegral_cycloUnit.md` and `norm_le_one_of_isIntegral_int.md`. The three WebSearch channels + nLab + Stacks independently converge on both the cyclotomic-unit-specific inverse form (explicit geometric sum) and the abstract integral-closure-is-a-ring form, so the standard-form question is fully answered without it. |
|  5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and top-level `refs/` | **n/a** | (no references dir) | Neither `projects/PadicLFunctions/.mathlib-quality/references/` nor `refs/` exists in the checkout (only `.mathlib-quality/overview/`). Recorded n/a. The file's own docstring cites RJW arXiv:2309.15692 §9/§11.3 (TeX 3060–3112, 3084); RJW TeX 2573 names `c_n(a) = (ξ^a−1)/(ξ−1)`. |
|  6 | nLab | "cyclotomic integer" / "integral closure" / "ring of integers" (ncatlab.org) | **yes** | nLab "cyclotomic integer": the ring of integers of `ℚ(ζ_n)` is `ℤ[ζ_n]`; roots of unity are algebraic integers (roots of monic `X^n−1`). The "integral closure"/"ring of integers" entries: "the set of elements integral over `k` is a subring." A unit of `ℤ[ζ]` has its inverse in `ℤ[ζ]` (units of a ring are closed under inverse, by definition of unit). | The search surfaced the same explicit inverse formula `ξ⁻¹ = (1−ω^{rus})/(1−ω^{rs}) ∈ ℤ[ω]`. The abstract "integral closure is a subring" carries the backbone fact. |
|  7 | nCatLab (if categorical) | — | **n/a** | — | Not a higher-categorical concept — an elementary integrality fact about a unit of a commutative ring extension. Brief look (the nLab "cyclotomic integer"/"integral closure" entries are the relevant ones, covered in #6): nothing 1-/∞-categorical to add. |
|  8 | Stacks Project (if alg geom / comm alg) | "integral closure of R in S is a subring" (stacks.math.columbia.edu) | **yes** | **Lemma 10.36.7 (tag 00GO)**: "Let `R → S` be a ring homomorphism. The set `S' = {s ∈ S : s integral over R}` is an `R`-subalgebra of `S`." (tag-00GH "Integral elements" family.) | Direct hit at maximal generality (arbitrary ring hom): the integral elements are closed under `+`, `×` — hence the geometric sum `∑ (ξ^a)^i` (a `ℤ`-polynomial in the integral `ξ`) is integral. Stacks does not single out "inverse of a cyclotomic unit" because, once you have the geometric-sum identity, it is just the subring fact. |
|  9 | MathOverflow / Math.StackExchange | "inverse of cyclotomic unit `(ζ^a−1)/(ζ−1)` integral geometric sum coprime" generality | **yes** | Treated as background-standard: `(ζ^a−1)/(ζ−1)` is a unit of `ℤ[ζ]`; the inverse is computed by the explicit geometric sum `∑ (ζ^a)^i` using `a·a' ≡ 1 (mod n)`; both lie in `ℤ[ζ]`. | Carried on MO/MSE as a *step* (e.g. "Ring of Integers of Cyclotomic Field" expositions), not a research question — the inverse formula via the coprime multiplier `a'` is folklore. |
| 10 | recent arXiv (last 5 years) | cyclotomic units inverse / `(ζ^a−1)/(ζ−1)` unit of `ℤ[ζ]` reformulation | **yes (no reformulation)** | RJW arXiv:2309.15692 (the source) uses `c_n(a) = (ξ^a−1)/(ξ−1)` as cyclotomic units and asserts they are global/integral (with integral inverse) without proof; no recent paper *reformulates* "the inverse of a cyclotomic unit is an algebraic integer." | The statement is classical (Kummer–Dedekind era; the cyclotomic-unit group is treated in Washington Ch. 8). Mathlib's own `RootsOfUnity/CyclotomicUnits.lean` (Best–Brasca) is the contemporary home — it proves `geom_sum_isUnit` (`∑ ζ^i` is a unit) and `associated_sub_one_pow_sub_one_of_coprime` using the *same* coprime-multiplier geometric-sum argument. |

The protocol passes: WebSearch ran 3 distinct queries at three generality levels (the cyclotomic-unit-inverse-is-an-algebraic-integer specific form with explicit geometric-sum inverse; the standard "`(ζ^a−1)/(ζ−1)` is a unit of `ℤ[ζ]`" form; the named mechanism = the geometric sum `1 + ζ + ⋯`); local refs checked (absent → n/a); nLab searched (hit on "cyclotomic integer"/"integral closure"); Stacks (hit, tag 00GO), nCatLab/MathOverflow/arXiv each looked at with results or an n/a reason. ChatGPT MCP recorded n/a with reason (tool unavailable) — the only channel not run; the three web channels + nLab + Stacks independently cover the standard form, including the explicit inverse geometric sum.

### Literature summary (Phase 3)

Concept identified as: **(a)** "the inverse of a cyclotomic unit is an algebraic integer" — equivalently "the prime-power cyclotomic unit `(ξ^a−1)/(ξ−1)` is a *unit* of the ring of integers `ℤ[ξ]`", with the **explicit inverse** `(ξ−1)/(ξ^a−1) = 1 + ξ^a + ⋯ + ξ^{(a'−1)a} = ∑_{i<a'} (ξ^a)^i` where `a·a' ≡ 1 (mod p^n)` (Wikipedia "Cyclotomic unit"; Washington Ch. 8); and, abstractly, **(b)** "**the integral closure of a ring in an extension is a subring**" — any finite sum of powers of an integral element is integral (Stacks 00GO; nLab; Wikipedia "Integral element", proof due to Dedekind). The theorem is the specialisation of (b) to `R = ℤ`, the integral element `ξ = ξ_{p^n}` (a root of unity), and the explicit inverse polynomial `∑_{i<a'} X^{a·i}` produced by (a).

Sources agree on the standard form: **yes** — unanimous across Wikipedia, Conrad's handout, the Lean community blog, Stacks, nLab, and Washington's canonical text. Both the cyclotomic-unit-inverse statement (with its explicit geometric-sum inverse) and the abstract integral-closure-is-a-ring statement are textbook-canonical.

Most general standard form: For any ring homomorphism `R → S` (Stacks 00GO), the elements of `S` integral over `R` form an `R`-subalgebra; in particular any `R`-polynomial in an integral element is integral. The "inverse" specificity is supplied by the elementary identity that the field-inverse `(ξ−1)/(ξ^a−1)` equals the geometric sum `∑_{i<a'} (ξ^a)^i` (clearing denominators via `geom_sum_mul` and the coprime multiplier `a'`). Specialising to `R = ℤ`, the integral root of unity `ξ`, and that geometric sum gives exactly the user's theorem.

Generality dimensions where the literature varies:
  - **Base ring**: `ℤ` here → any base ring `R` (Stacks: arbitrary ring hom `R → S`). The integrality step uses nothing about `ℤ` beyond `IsIntegral ℤ ξ`.
  - **Ambient ring**: `ℂ_[p]` here → any commutative domain/field `S` containing `ξ`. No `ℂ_p`-specific input is used in the integrality step (the *inverse identity* uses only `orderOf ξ = p^n` and nonzero denominators).
  - **The element**: `ξ_{p^n}` (a root of unity in `ℂ_p`) here → any `R`-integral element that is a root of unity (so the inverse-geometric-sum identity applies). The "it's a root of unity, hence integral" fact is mathlib's `IsPrimitiveRoot.isIntegral`.
  - **The polynomial**: the specific inverse geometric sum `∑_{i<a'} (ξ^a)^i` here → any `ℤ`-polynomial (integral closure is closed under all ring operations).

Disagreement with the literature: **none.** The user's form is a correct, strictly-special case of the standard "the inverse of a cyclotomic unit lies in `ℤ[ξ]`" fact, which itself is the integral-closure-is-a-ring fact applied to the explicit geometric-sum inverse.

---

### Generality analysis — `PadicLFunctions.Coleman.isIntegral_inv_cycloUnit`

Literature-standard form (from Phase 3): the integral closure of `R` in `S` is a subring (Stacks 00GO); equivalently any `R`-polynomial in an `R`-integral element is `R`-integral. The inverse of a prime-power cyclotomic unit equals the explicit geometric sum `∑ (ξ^a)^i` (a `ℤ`-polynomial in the algebraic-integer `ξ`), hence is an algebraic integer.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | base ring `ℤ` | `IsIntegral ℤ (...)` | integral over any base ring `R` | **yes** | The integrality step is "`IsIntegral R` is closed under `Finset.sum` and `pow`"; `R = ℤ` plays no special role. But this generality is *already mathlib* (`IsIntegral.sum`/`IsIntegral.pow` over arbitrary `R`) — not a contribution. |
| 2 | ambient `ℂ_[p]` (the element `(cycloUnit p a n)⁻¹`) | the `p`-adic complex cyclotomic-unit inverse | any `R`-integral element in any comm-ring `S` | **yes** | Nothing in the *integrality* step is `ℂ_p`-specific. The inverse-geometric-sum identity uses only `orderOf ξ` and field division — again base/ambient-agnostic. The integral-closure-is-a-ring fact mathlib already provides. |
| 3 | the element `(cycloUnit p a n)⁻¹` | the specific cyclotomic-unit inverse | any `ℤ`-polynomial in any integral root of unity | **yes** | The proof first rewrites via `inv_cycloUnit_eq_geomSum` to `∑_{i<a'} (ξ^a)^i`; from there integrality is the generic sum-of-powers fact. The "`ξ` is integral" input is `IsPrimitiveRoot.isIntegral` (mathlib), not new. |
| 4 | `(ha : ¬ p ∣ a)` | coprimality hypothesis | **genuinely needed** | **no (it is real here)** | Unlike the non-inverse sibling (where `_ha` is vestigial), coprimality is *essential*: it is what lets `inv_cycloUnit_eq_geomSum` produce the multiplier `a'` (`a·a' ≡ 1 mod p^n`, via `Nat.exists_mul_mod_eq_one_of_coprime`) so the inverse is a *finite* geometric sum. Without it, `c_n(a)` need not be a unit of `ℤ[ξ]` at all. |
| 5 | `(hn : 1 ≤ n)` | level `≥ 1` | needed for `p^n > 1` (nonzero denominators, `orderOf ξ = p^n`) | no | `hn` feeds `inv_cycloUnit_eq_geomSum` (denominators `ξ−1`, `ξ^a−1 ≠ 0` need `p^n > 1`; `orderOf ξ = p^n` is used to reduce `ξ^{a·a'} = ξ`). Real here. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is the `ℤ`/`ℂ_p`/specific-cyclotomic-unit-inverse specialisation of "integral closure is a ring" applied to the explicit geometric-sum inverse).
Number of weakening opportunities found: **substantial on the integrality axis** (base ring, ambient ring, the element) — **but every one lands on machinery mathlib already has** (`IsIntegral.sum`, `IsIntegral.pow` over arbitrary `R`/`S`, and `IsPrimitiveRoot.isIntegral` for the root-of-unity input). The two hypotheses `ha`, `hn` are *not* removable here (both are genuinely used to build the finite geometric-sum inverse). The maximally-general *integrality* statement is **not a missing lemma** — it is `IsIntegral.sum`, which is in mathlib.

Proposed restatement: **none worth shipping as a new lemma.** The "general form" of the integrality content is literally `IsIntegral.sum`/`IsIntegral.pow` (already in mathlib), and the cyclotomic-unit-inverse-as-geometric-sum content is the same argument mathlib already runs in `IsPrimitiveRoot.geom_sum_isUnit` / `associated_sub_one_pow_sub_one_of_coprime`. Generalising does not produce a contributable artifact. This rules out `YES-but-generalise-first` (the generalised form is not novel for mathlib) and points at a NO bucket.

Cost of restatement: **n/a** — there is no new statement to re-prove; the generalisation collapses into existing mathlib calls.

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let R be a foo" preambles → typeclasses? | no | already fully typeclassed (`[Fact p.Prime]`; `IsIntegral` is the bundled predicate) | — |
|  2 | sequences/metric → filters/topological? | no | no limits/convergence in this lemma — a single algebraic integrality fact about an inverse | — |
|  3 | construct an object where a universal-property / bundled object is canonical? | **YES (and it is already mathlib)** | The bundled object is the **integral closure** `integralClosure ℤ ℂ_[p]` (a `Subalgebra`); `IsIntegral.sum`/`pow` are exactly its `sum_mem`/`pow_mem`. The "modern" statement is `(cycloUnit p a n)⁻¹ ∈ integralClosure ℤ ℂ_[p]`. | the whole `integralClosure`/`Subalgebra` lattice API — **already in mathlib**, used *by* `IsIntegral.sum`'s proof (`(integralClosure R A).sum_mem h`). |
|  4 | set-with-closure-predicate → bundled type? | **YES (already mathlib)** | same as #3: "integral over `ℤ`" predicate → the bundled `integralClosure` subalgebra. | `integralClosure`, `Subalgebra` lattice, `Algebra.IsIntegral` instances — present. |
|  5 | field-specific → weaken typeclass? | yes (already mathlib) | `ℂ_p` → arbitrary `CommRing` for the integrality step; mathlib's `IsIntegral.sum` is already at `CommRing` generality | full `IsIntegral` API across all rings |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete base (ℤ) → arbitrary ring? | yes (already mathlib) | drop `ℤ`: `IsIntegral.sum`/`pow` are stated over an arbitrary base `R` | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and it is decisive, but it points at mathlib, not at a new contribution.** The contemporary mathlib formulation of "a `ℤ`-polynomial in an integral element is integral" is the bundled **`integralClosure ℤ S : Subalgebra ℤ S`** with `Subalgebra.sum_mem`/`pow_mem` — precisely what mathlib's `IsIntegral.sum`/`IsIntegral.pow` already are. The root-of-unity input has its canonical mathlib lemma `IsPrimitiveRoot.isIntegral`. The *inverse-as-geometric-sum* content is the same coprime-multiplier argument mathlib already runs in `RootsOfUnity/CyclotomicUnits.lean`. So the user's theorem is not a modernisation mathlib lacks — it is a special case mathlib produces directly. This **rules out a YES verdict** and leaves Phase 7 weighing **NO-mathlib-has-it vs NO-composable-from-mathlib**.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.Coleman.isIntegral_inv_cycloUnit`

[A] Lean-Finder       (MCP tool unavailable in env) — n/a; NL intent "sum of powers of an integral element is integral" / "primitive root of unity is integral over ℤ" / "inverse of a cyclotomic unit is an algebraic integer" / "geom sum of (ζ^a)^i is the inverse of (ζ^a−1)/(ζ−1)" searched via the literature + grep (methods D/E).
[B] Loogle            (MCP tool unavailable in env) — n/a; type-pattern intent `(∀ i ∈ s, IsIntegral R (f i)) → IsIntegral R (∑ i ∈ s, f i)`, `IsIntegral R x → IsIntegral R (x^n)`, `IsPrimitiveRoot ζ n → IsIntegral ℤ ζ`, `IsIntegral R x⁻¹` searched via grep over `RingTheory/IntegralClosure/` and `RingTheory/RootsOfUnity/`.
[C] LeanSearch        (MCP tool unavailable in env) — n/a; NL intent as in [A], resolved via grep over the mathlib source tree.
[D] Grep mathlib src  Searched `.lake/packages/mathlib/Mathlib/` for: `IsIntegral.sum`, `IsIntegral.pow`, `IsIntegral.inv`, `Algebra.IsIntegral.inv`, `IsIntegral.of_mul_unit`, `IsPrimitiveRoot.isIntegral`, `geom_sum_isUnit`, `associated_sub_one_pow_sub_one_of_coprime`, `mul_geom_sum`, `geom_sum_mul`, `exists_mul_mod_eq_one_of_coprime`, `cyclotomicunit`. **Found every building block — and a dedicated mathlib cyclotomic-units file with the same coprime-multiplier geometric-sum argument.**
[E] Name pattern      Searched `isIntegral_inv_cycloUnit`, `inv_cycloUnit`, `cycloUnit`, `cyclotomicUnit`, `*_isIntegral`, `*inv*Integral` in `RootsOfUnity/` and `IntegralClosure/`. No decl with this *exact* name (project-local), but the abstract pieces and the cyclotomic-unit file are present.

Searched for both forms:
  - **User's form** (`IsIntegral ℤ (cycloUnit p a n)⁻¹` — the inverse of the specific `ℂ_[p]` cyclotomic unit): **not in mathlib** as a single named declaration (it is a project-specific object `cycloUnit p a n` in `ℂ_[p]`).
  - **Literature-standard / abstract form** (the inverse is the geometric sum `∑ (ξ^a)^i`, which is integral since integral closure is a ring; root of unity is integral): **IN mathlib, at full generality:**
    - `IsIntegral.sum` — `.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:246` — `(∀ x ∈ s, IsIntegral R (f x)) → IsIntegral R (∑ x ∈ s, f x)` (proof: `(integralClosure R A).sum_mem h`). **This is the outer step of the project's proof verbatim.**
    - `IsIntegral.pow` — `.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:224` — `IsIntegral R x → IsIntegral R (x ^ n)`. **This is the inner step verbatim** (applied twice: `((zetaSys_isIntegral …).pow a).pow i`).
    - `IsPrimitiveRoot.isIntegral (hpos : 0 < n) : IsIntegral ℤ μ` — `.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/Minpoly.lean:41`. **Its proof (`use X^n − 1; monic_X_pow_sub_C 1 …`) is byte-for-byte the project's private `zetaSys_isIntegral`** (which uses `X^{p^n} − 1`). So `zetaSys_isIntegral p n` is just `(zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)`.
    - `Nat.exists_mul_mod_eq_one_of_coprime` — `.lake/packages/mathlib/Mathlib/Data/Int/GCD.lean:140` — the coprime-multiplier lemma the project's `inv_cycloUnit_eq_geomSum` uses to obtain `a'`. **Mathlib's own cyclotomic-units file uses this exact lemma** (`RootsOfUnity/CyclotomicUnits.lean:54`) in `associated_sub_one_pow_sub_one_of_coprime` — the same argument backing the inverse-geometric-sum identity.
    - `geom_sum_mul (x) (n) : (∑ i ∈ range n, x^i) * (x − 1) = x^n − 1` — `.lake/packages/mathlib/Mathlib/Algebra/Ring/GeomSum.lean:232` — the identity backing the project's `inv_cycloUnit_eq_geomSum` (`(ξ^a − 1)·∑ (ξ^a)^i = (ξ^a)^{a'} − 1 = ξ − 1`).
  - **Crucial non-applicability of the obvious one-liner.** Mathlib's `IsIntegral.inv` (`.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:74`) states `IsIntegral R x → IsIntegral R x⁻¹` **but only under `variable [Field R]`** — i.e. for integrality over a *field*. Here the base is `R = ℤ` (not a field), and over a general commutative ring the inverse of an integral element is *not* generally integral (e.g. `2` is integral over `ℤ`, `1/2` is not). So `IsIntegral.inv` does **not** discharge this goal; the result is true only because `c_n(a)` is a genuine *unit of `ℤ[ξ]`*, which is exactly what the explicit geometric-sum inverse witnesses. This is the key subtlety distinguishing the verdict from a trivial `.inv` application.
  - **Mathlib has a cyclotomic-units file**: `.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean` (Best–Brasca) — `geom_sum_isUnit` (`∑ ζ^i` is a *unit*), `geom_sum_isUnit'`, `associated_sub_one_pow_sub_one_of_coprime`, `pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one` — the *same* `∑ ξ^i` / `(ξ^a−1)/(ξ−1)` objects. In a comm domain integral over `ℤ`, "is a unit" already *encodes* "its inverse is integral", so this file confirms mathlib owns the cyclotomic-unit-inverse content (it states the unit-ness, from which integrality of the inverse is automatic in the ring of integers).

Concluded: **"found the building blocks in mathlib (`IsIntegral.sum`, `IsIntegral.pow`, `IsPrimitiveRoot.isIntegral`, `Nat.exists_mul_mod_eq_one_of_coprime`, `geom_sum_mul`) — and a cyclotomic-units file (`RootsOfUnity/CyclotomicUnits.lean`) running the identical coprime-multiplier geometric-sum argument; composing them yields the user's form."** The project's exact named theorem about `(cycloUnit p a n)⁻¹` in `ℂ_[p]` is not in mathlib (it is a project-local object), and the obvious `IsIntegral.inv` shortcut is *unavailable* over `ℤ`. But the mathematical content is mathlib's "integral closure is a ring" API applied to the explicit geometric-sum inverse (whose existence is mathlib's coprime-multiplier argument). The non-mathlib ingredient is the rewrite `inv_cycloUnit_eq_geomSum` — itself a `geom_sum_mul` + `exists_mul_mod_eq_one_of_coprime` consequence (a *separate* project declaration, assessed on its own).

---

### Call sites — `PadicLFunctions.Coleman.isIntegral_inv_cycloUnit`

Internal use count: **2** (within the project, excluding the declaring line), across **2 files**.
External-to-file callers: **1** distinct file (`IwasawaProof/Generators.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `…/Iwasawa/CyclotomicUnits.lean:416` | `· rw [Units.val_inv_eq_inv_val, hval]; exact isIntegral_inv_cycloUnit p ha hn` — inside `cyclo_elems_mem_globalUnits`, supplying the `IsIntegral ℤ ((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])` component of `globalUnits` membership (the milestone TeX 3084). |
| `…/IwasawaProof/Generators.lean:259` | `· exact isIntegral_inv_cycloUnit p ha hn` — discharging the integral-inverse side-goal for the `γ⁻¹` part of a cyclotomic-unit generator in the `IwasawaProof` development. |

Inline-derivation grep (was the equivalent re-derived elsewhere without this theorem?):
  - **(none directly)** — no other site re-proves `IsIntegral ℤ (cycloUnit …)⁻¹` by hand. **But** the pattern is twinned with its sibling: `isIntegral_cycloUnit` (line 264) runs `IsIntegral.sum _ fun i _ => (zetaSys_isIntegral p n).pow i` on the *non*-inverse geometric sum, and this lemma runs the parallel `IsIntegral.sum _ fun i _ => ((zetaSys_isIntegral p n).pow a).pow i` on the inverse's geometric sum; the private input `zetaSys_isIntegral` (line 249) is itself a from-scratch re-derivation of mathlib's `IsPrimitiveRoot.isIntegral`. So the *pattern* (and the root-of-unity-integral input) is duplicated rather than routed through mathlib.

What the call-sites pattern tells us: **K = 2 distinct internal uses across 2 files, no inline re-derivation of this exact statement.** Per the Phase-6 table, K = 2 is the "real but thin API" band — genuinely used (not dead code), yet each use is a single `exact isIntegral_inv_cycloUnit p ha hn` that could equally be the short mathlib-backed composition (the obstruction is only the project-local `inv_cycloUnit_eq_geomSum` rewrite). Two consumers justify *keeping a thin wrapper* (house style) but do **not** justify a *new mathlib lemma*. This nudges to **NO-composable** (route through mathlib / keep a thin local wrapper) rather than NO-mathlib-has-it (the *named* `cycloUnit`-inverse-in-`ℂ_p` statement is genuinely project-local, so there is no 0-line mathlib drop-in for the *named* form — and `IsIntegral.inv` is unavailable over `ℤ`).

---

### Composition check (Phase 6)

Can `isIntegral_inv_cycloUnit` be derived from mathlib in ≤3 chained calls?

**Attempt 0 — the obvious shortcut `IsIntegral.inv`. FAILS.** One might hope `exact (isIntegral_cycloUnit p ha hn).inv` discharges it via mathlib's `IsIntegral.inv`. But `IsIntegral.inv` carries `variable [Field R]` and is about integrality over a *field*; here the base is `R = ℤ`. Over a general commutative ring the inverse of an integral element need not be integral, so this lemma does not apply. **Not composable this way** — recorded because ruling it out is what makes the verdict non-trivial.

**Attempt 1 — the project's own proof, with the one project-private leaf swapped for mathlib.** The body is already a mathlib composition once the inverse-geometric-sum identity is in hand; the only non-mathlib leaf in the *integrality step* is `zetaSys_isIntegral`, which equals `IsPrimitiveRoot.isIntegral`:
```lean
example {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) :
    IsIntegral ℤ (cycloUnit p a n)⁻¹ := by
  obtain ⟨a', ha'⟩ := inv_cycloUnit_eq_geomSum p ha hn          -- project identity (geom_sum_mul + exists_mul_mod_eq_one_of_coprime)
  rw [ha']
  exact IsIntegral.sum _ fun i _ =>                              -- mathlib  (Basic.lean:246)
    (((zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)).pow a).pow i  -- mathlib (Minpoly.lean:41 + Basic.lean:224 ×2)
```
  - Mathlib decls used: `IsIntegral.sum`, `IsIntegral.pow` (twice), `IsPrimitiveRoot.isIntegral` (+ `geom_sum_mul` and `Nat.exists_mul_mod_eq_one_of_coprime` underneath `inv_cycloUnit_eq_geomSum`).
  - Result: **succeeds** — this is the existing 3-line proof with `zetaSys_isIntegral p n` replaced by its mathlib equivalent. Every leaf in the integrality step is a single library call.
  - Notes: **1 `obtain` + 1 `rw` + a 1-line `IsIntegral.sum`/`.pow` composition = within the ≤3-call composition bar for the integrality step.** The `obtain … inv_cycloUnit_eq_geomSum` is the one project-glue step; `inv_cycloUnit_eq_geomSum` is itself a short composition (`exists_mul_mod_eq_one_of_coprime` to get `a'`, `geom_sum_mul` + `pow_mod_orderOf` to verify the identity, then `div_eq_iff`). It is a *separate project declaration* assessed on its own merits — and it is the same coprime-multiplier geometric-sum argument mathlib runs in `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`.

**Attempt 2 — route through mathlib's cyclotomic-units API.** Mathlib's `IsPrimitiveRoot.geom_sum_isUnit (hζ) (hn : 2 ≤ n) (hj : j.Coprime n) : IsUnit (∑ i ∈ range j, ζ^i)` proves the geometric sum is a *unit* in the comm domain. Combined with `associated_sub_one_pow_sub_one_of_coprime` (which gives the explicit unit relating `ξ−1` and `ξ^a−1`), one obtains in the ring of integers that `c_n(a)` is a unit, hence its inverse is integral. Porting this to "`(cycloUnit p a n)⁻¹` in `ℂ_[p]` is integral over `ℤ`" requires transferring along the algebra map `ℤ[ξ] ↪ ℂ_[p]` (the inverse in `ℂ_[p]` agrees with the ring-inverse in `ℤ[ξ]`). This is a *slightly longer* composition than Attempt 1; recorded as corroboration that mathlib owns the content at the unit-ness altitude too.

Conclusion: **COMPOSABLE** — in a short chain against mathlib's `IsIntegral.sum` + `IsIntegral.pow` + `IsPrimitiveRoot.isIntegral` (the project's own proof, with its single private leaf `zetaSys_isIntegral` recognised as `IsPrimitiveRoot.isIntegral`), modulo the project's `inv_cycloUnit_eq_geomSum` rewrite (itself the same `geom_sum_mul` + coprime-multiplier argument mathlib already has). It is **not** a "proof in disguise" — the integrality step is genuinely `IsIntegral.sum (… .pow (… .pow ‹·›))` with no `ring_nf`/`aesop` glue. The one thing that is *not* a mathlib one-liner is the inverse-geometric-sum identity, which is a distinct project declaration carrying its own (mathlib-shaped) proof.

---

## Verdict: `PadicLFunctions.Coleman.isIntegral_inv_cycloUnit`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): unanimous and textbook-canonical — the inverse of a prime-power cyclotomic unit `(ξ^a−1)/(ξ−1)` lies in `ℤ[ξ]`, with explicit inverse `(ξ−1)/(ξ^a−1) = 1 + ξ^a + ⋯ + ξ^{(a'−1)a} = ∑_{i<a'} (ξ^a)^i` (Wikipedia "Cyclotomic unit"; Washington Ch. 8); abstractly this is "the integral closure is a ring" (Stacks 00GO; nLab; proof due to Dedekind) applied to that geometric sum.
- Generality analysis (Phase 4): STRICTLY NARROWER (base `ℤ`, ambient `ℂ_p`, the specific cyclotomic-unit inverse) — and Phase 4c shows the general/modern form *is already mathlib* (`integralClosure` subalgebra ⇒ `IsIntegral.sum`/`pow`; the inverse-geometric-sum argument is mathlib's `RootsOfUnity/CyclotomicUnits.lean`), so **no YES** and **no generalise-first** (the generalisation is not novel). Both `ha` and `hn` are genuinely used here (so not removable).
- Mathlib search (Phase 5): the integrality content is in mathlib as `IsIntegral.sum` (`…/Basic.lean:246`) + `IsIntegral.pow` (`…/Basic.lean:224`) + `IsPrimitiveRoot.isIntegral` (`…/Minpoly.lean:41`); `IsIntegral.sum`/`pow` are the project's proof *verbatim*, and `IsPrimitiveRoot.isIntegral` is the project's private `zetaSys_isIntegral` verbatim. The coprime-multiplier geometric-sum argument is mathlib's (`exists_mul_mod_eq_one_of_coprime`, used in `RootsOfUnity/CyclotomicUnits.lean`). **Critically, mathlib's `IsIntegral.inv` is unavailable** (it requires `[Field R]`; here the base is `ℤ`), so this is *not* a one-call `.inv` reduction.
- Composition check (Phase 6): COMPOSABLE — short chain (`inv_cycloUnit_eq_geomSum` rewrite → `IsIntegral.sum` over `((IsPrimitiveRoot.isIntegral …).pow a).pow i`); the `IsIntegral.inv` shortcut explicitly FAILS over `ℤ`.

**Rationale (1–2 paragraphs):**

This theorem is the specialisation "`ℤ`, ambient `ℂ_[p]`, the inverse of the specific cyclotomic unit `(ξ^a−1)/(ξ−1)`" of content mathlib already owns: **the integral closure is a subring**, hence the explicit geometric-sum inverse `∑_{i<a'} (ξ^a)^i` — a `ℤ`-polynomial in the algebraic-integer root of unity `ξ` — is integral. The Lean proof makes this transparent: after the project's rewrite `inv_cycloUnit_eq_geomSum` to that geometric sum, the body is exactly `IsIntegral.sum _ fun i _ => ((zetaSys_isIntegral p n).pow a).pow i`, i.e. mathlib's `IsIntegral.sum` over mathlib's `IsIntegral.pow`. The one project-private integrality leaf, `zetaSys_isIntegral` ("`ξ` is integral over `ℤ`"), is a from-scratch copy of mathlib's `IsPrimitiveRoot.isIntegral` (`RootsOfUnity/Minpoly.lean:41`) — the same `use X^n − 1; monic_X_pow_sub_C 1` proof. The inverse-geometric-sum identity itself is the same coprime-multiplier argument (`exists_mul_mod_eq_one_of_coprime` + `geom_sum_mul`) that mathlib runs in `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`. Tellingly, mathlib maintains a *cyclotomic-units file* (`RootsOfUnity/CyclotomicUnits.lean`, Best–Brasca) for these very `(ξ^a−1)/(ξ−1)` / `∑ ξ^i` objects, where `geom_sum_isUnit` already encodes that these are *units* (whence integral inverse).

The verdict is **NO-composable** rather than a YES because the maximally-general statement of the integrality content is `IsIntegral.sum` itself (in mathlib) and the inverse-as-geometric-sum is mathlib's existing argument — Phase 4c finds no *missing* modern form. It is NO-**composable** rather than NO-**mathlib-has-it** for two reasons: (i) there is no single mathlib lemma named for "the inverse of `cycloUnit p a n` in `ℂ_[p]` is integral over `ℤ`" — that *named, project-specific* object is genuinely project-local; and (ii) the obvious 0-line reduction `IsIntegral.inv` is *not available* here, because `IsIntegral.inv` requires `[Field R]` and our base is `ℤ` (over a non-field ring the inverse of an integral element is generally not integral — the result is true only because the cyclotomic unit is a genuine *unit* of `ℤ[ξ]`, which the explicit geometric-sum inverse witnesses). So the user's form is a *short composition* of mathlib pieces plus the project's `inv_cycloUnit_eq_geomSum` rewrite, not a drop-in. (BORDERLINE was considered — the result has 2 consumers, the `IsIntegral.inv` shortcut is blocked, and the proof relies on a project-local inverse-identity lemma — but the evidence resolves cleanly: mathlib has the integral-closure-is-a-ring content verbatim, the root-of-unity input verbatim, and the coprime-multiplier geometric-sum argument; the result is recoverable as a short composition, so no human question is needed. This is consistent with the sibling `isIntegral_cycloUnit`, also NO-composable.)

**NO-composable-from-mathlib — refactor-actionable detail:**

WHY not: Mathlib has the building blocks — `IsIntegral.sum`, `IsIntegral.pow`, `IsPrimitiveRoot.isIntegral`, `Nat.exists_mul_mod_eq_one_of_coprime`, `geom_sum_mul` — and the project's proof is already a composition of them (with `zetaSys_isIntegral` standing in for `IsPrimitiveRoot.isIntegral`). No standalone mathlib-bound lemma about this `ℂ_[p]` cyclotomic-unit inverse is justified: the integrality is the generic "sum of powers of an integral root of unity is integral", and the inverse identity is mathlib's existing coprime-multiplier geometric-sum argument. The result is *not* an `IsIntegral.inv` corollary (that lemma needs a field base; ours is `ℤ`), so the explicit geometric-sum route is the right one — and it is short.

Mathlib building blocks (all with full paths):
  - `IsIntegral.sum` — `.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:246`
  - `IsIntegral.pow` — `.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:224`
  - `IsPrimitiveRoot.isIntegral` — `.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/Minpoly.lean:41`  (`IsIntegral ℤ μ` for a primitive root; replaces the project's private `zetaSys_isIntegral`)
  - `Nat.exists_mul_mod_eq_one_of_coprime` — `.lake/packages/mathlib/Mathlib/Data/Int/GCD.lean:140`  (the coprime multiplier `a'`; backs `inv_cycloUnit_eq_geomSum`)
  - `geom_sum_mul` — `.lake/packages/mathlib/Mathlib/Algebra/Ring/GeomSum.lean:232`  (backs `inv_cycloUnit_eq_geomSum`)
  - (corroborating, the cyclotomic-units API) `IsPrimitiveRoot.geom_sum_isUnit` and `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime` — `.lake/packages/mathlib/Mathlib/RingTheory/RootsOfUnity/CyclotomicUnits.lean:86,47` — the *same* `∑ ξ^i` / `(ξ^a−1)/(ξ−1)` objects and the same coprime-multiplier geometric-sum argument.
  - NOT applicable: `IsIntegral.inv` — `.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegralClosure/Basic.lean:74` — requires `[Field R]`; **cannot** be used with base `ℤ`.

Composition sketch (the inlined / wrapper body; short chain):
```lean
-- `zetaSys_primitiveRoot p n : IsPrimitiveRoot (zetaSys p n) (p ^ n)` is in the project;
-- `pow_pos hp.out.pos n : 0 < p ^ n`.
example {a : ℕ} (ha : ¬ (p : ℕ) ∣ a) {n : ℕ} (hn : 1 ≤ n) :
    IsIntegral ℤ (cycloUnit p a n)⁻¹ := by
  obtain ⟨a', ha'⟩ := inv_cycloUnit_eq_geomSum p ha hn
  rw [ha']
  exact IsIntegral.sum _ fun i _ =>
    (((zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)).pow a).pow i
```

Call sites in the project (from Phase 6.0): **K = 2** distinct uses across 2 files — `CyclotomicUnits.lean:416` (inside `cyclo_elems_mem_globalUnits`) and `Generators.lean:259`.

Refactor plan:
  1. Replace the project-private `zetaSys_isIntegral` (line 249) with `IsPrimitiveRoot.isIntegral`: define `zetaSys_isIntegral p n := (zetaSys_primitiveRoot p n).isIntegral (pow_pos hp.out.pos n)` (mathlib import `Mathlib.RingTheory.RootsOfUnity.Minpoly` is already transitively present via the cyclotomic stack), deleting the hand-rolled `⟨X^{p^n} − 1, monic_X_pow_sub_C …, …⟩` term. This dedups the root-of-unity-integral input against mathlib for *both* `isIntegral_cycloUnit` (line 264) and this lemma (line 305), which share the leaf. (Generators.lean:255 and 258 also re-inline this exact `⟨X^{p^n}−1, …⟩` term and should be swapped too.)
  2. Keep `isIntegral_inv_cycloUnit` as a **thin wrapper** whose body is the composition above (its 2 consumers call `isIntegral_inv_cycloUnit p ha hn`, so the call signature is unchanged) — OR inline the short composition at `CyclotomicUnits.lean:416` and `Generators.lean:259` and delete the theorem. With only 2 consumers either is defensible; the thin-wrapper choice is the lighter-touch house-style option. Do **not** drop `ha` or `hn` — both are genuinely used (they build the finite geometric-sum inverse via `inv_cycloUnit_eq_geomSum`).
  3. (Optional, larger) If the project ever wants to *eliminate* the project-local `inv_cycloUnit_eq_geomSum`, route through mathlib's `IsPrimitiveRoot.geom_sum_isUnit` / `associated_sub_one_pow_sub_one_of_coprime` in the ring of integers and transfer along `ℤ[ξ] ↪ ℂ_[p]` (Attempt 2). This is a structural refactor, not a one-liner; track it as a project-cleanup ticket, not an upstream PR.
  4. No new mathlib PR results from this theorem. The upstream pieces all exist; any nearby mathlib-worthy work is project-local dedup, not an upstream contribution.

Next action: dedup the shared private leaf `zetaSys_isIntegral` against mathlib's `IsPrimitiveRoot.isIntegral`, then keep `isIntegral_inv_cycloUnit` as a thin `IsIntegral.sum`/`IsIntegral.pow` wrapper (after the project's `inv_cycloUnit_eq_geomSum` rewrite) or inline the short composition at its 2 call sites. Do **not** open a mathlib PR — mathlib already owns every ingredient (`IsIntegral.sum`/`pow`, `IsPrimitiveRoot.isIntegral`, the coprime-multiplier geometric-sum argument, and a `RootsOfUnity/CyclotomicUnits.lean`); and note that `IsIntegral.inv` is *not* a usable shortcut here (it requires a field base).

---

## Next step

Recognise the project's private `zetaSys_isIntegral` as mathlib's `IsPrimitiveRoot.isIntegral` and let `isIntegral_inv_cycloUnit` reduce to the mathlib composition `IsIntegral.sum _ fun i _ => ((IsPrimitiveRoot.isIntegral …).pow a).pow i` (after the project's `inv_cycloUnit_eq_geomSum` rewrite, which is mathlib's coprime-multiplier geometric-sum argument). Keep a thin local wrapper for its 2 consumers (keeping `ha`, `hn` — both used) or inline at the 2 call sites; do not upstream. The obvious `IsIntegral.inv` shortcut is unavailable because the base ring is `ℤ`, not a field.
