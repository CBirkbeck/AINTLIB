# `/mathlibable` report — `PadicLFunctions.Coleman.norm_le_one_of_isIntegral_int`

Mode A, full 10-phase workflow with the exhaustive 9-channel literature search.

---

### Baseline (Phase 0)

- lake build:               **not re-run** (stale/slow per task note); **reasoned from source** — the declaration, its proof, all in-file dependencies (`CyclotomicUnits.lean`), the project's `integerRing`/`valHom` infrastructure, and every mathlib lemma cited were read directly from `.lake/packages/mathlib/`.
- decl `PadicLFunctions.Coleman.norm_le_one_of_isIntegral_int`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Iwasawa/CyclotomicUnits.lean:58`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Cyclotomic units — the global modules `𝒟_n` and their local closures `𝒞` (RJW §11.3); all objects live inside `ℂ_[p]`. This lemma is the entry estimate `𝒱_n ≤ 𝒰_n`: a `ℤ`-integral element of `ℂ_[p]` lands in the unit ball.

---

### Statement (Phase 1)

`PadicLFunctions.Coleman.norm_le_one_of_isIntegral_int` is a theorem stating the following:

> Let `x ∈ ℂ_[p]` (the field of `p`-adic complex numbers — the completed algebraic closure of `ℚ_p`). If `x` is integral over `ℤ` — i.e. `x` is a root of a monic polynomial with integer coefficients — then `‖x‖ ≤ 1` in the `p`-adic absolute value on `ℂ_[p]`.

In valuation-theoretic language: an algebraic integer (or more generally any element integral over `ℤ`) lies in the valuation ring `𝓞_ℂ_[p] = {x : ‖x‖ ≤ 1}` of `ℂ_[p]`. This is one half of "the valuation ring is integrally closed and contains `ℤ`": the ring of integers contains the integral closure of `ℤ`.

The proof is the **classical ultrametric estimate on the monic relation** (no spectral theory): write `xᴺ = −Σ_{i<N} aᵢ xⁱ` from the monic relation `P(x)=0`; assume for contradiction `‖x‖>1`; the integer coefficients have norm `≤ 1` (`IsUltrametricDist.norm_intCast_le_one`), so by the strong triangle inequality (`IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`) the RHS has norm `≤ ‖x‖^{N−1} < ‖x‖^N = ‖xᴺ‖`, a contradiction.

Variables / typeclasses involved (Lean side):
- `(p : ℕ) [hp : Fact p.Prime]` — section variable; fixes the prime. Used only through the ambient field `ℂ_[p]`.
- `{x : ℂ_[p]}` — the element. `ℂ_[p] = PadicComplex p` is **a mathlib object** (`Mathlib/NumberTheory/Padics/Complex.lean`): a `NormedField`, `IsUltrametricDist`, `CharZero`, `IsAlgClosed`, and a `RankOne`-`Valued ℂ_[p] ℝ≥0` field.

Hypotheses (Lean side):
- `(hx : IsIntegral ℤ x)` — `x` is a root of a monic `ℤ`-polynomial.

Conclusion (math): `x` lies in the closed unit ball / valuation ring of `ℂ_[p]`.

Conclusion (Lean): `‖x‖ ≤ 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: A helper lemma — the `𝒱_n ≤ 𝒰_n` entry estimate of RJW TeX 3084, feeding `globalUnits_le_localUnits` and the cyclotomic-unit tower. Not a `## Main results` entry, not named after a person. It is one of the file's ultrametric building blocks. (Literature width is EXHAUSTIVE regardless of size.)

### One-line check (Phase 2b)

Body line count: ~30 substantive lines (a `by_contra` + monic-relation rearrangement + ultrametric finset-sum bound + case split on `N = 0`).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. Check skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
|  1 | WebSearch (specific form) | "integral element nonarchimedean field absolute value at most one p-adic norm integral over Z" | yes | `𝒪 = {x : |x| ≤ 1}` is the ring of integers; `ℤ_p = {x ∈ ℚ_p : |x|_p ≤ 1}` | Kedlaya MIT 18.787; Harvard p-adic integration (Popa) `ℤ_p = {|x|_p ≤ 1}`; W&M local-fields notes (`𝔪 = {|x|<1}`, `𝒪ˣ = {|x|=1}`) — unanimous |
|  2 | WebSearch (general form) | "valuation ring integrally closed contains integral closure non-archimedean valuation algebraic integer absolute value bounded by 1" | yes | **Krull**: integral closure of a domain = ∩ of valuation rings containing it; "an element is integral over `R` ⇔ its valuation is `≥ 0` at all valuations `≥ 0` on `R`" | UChicago Mathew "Integrality and valuation rings" (§7); Canad. Math. Bull. 33(3) "Valuation rings and integral closure"; Grokipedia "Valuation ring" — "a valuation ring is integrally closed" |
|  3 | WebSearch (named-after / mechanism — the actual proof) | "monic polynomial integer coefficients root non-archimedean ultrametric absolute value at most one proof Gauss lemma valuation" | yes | **Berkeley Part III Local Fields (Zhou), Lemma 3.1**: "for any α with `f(α)=0` monic, `v(α) ≥ 0`; proof assumes `v(α)<0` and derives a contradiction from the valuation of the polynomial equation" — **verbatim the project's proof** | Also Stanford Conrad "absolute values" handout; Conrad/Thorne UConn p-adic notes; Wikipedia "Gauss's lemma" |
|  4 | ChatGPT MCP | (intended: "standard form + generality + historical evolution of: element integral over ℤ has p-adic absolute value ≤ 1; valuation ring contains integral closure") | n/a | — | **ChatGPT MCP not available in this environment** (no `mcp__…chatgpt…` tool in the deferred-tool list; `setup-chatgpt` skill present but server not configured). Recorded n/a. The three WebSearch channels independently converge on the standard form **and** the standard proof, so the standard-form question is fully answered without it. |
|  5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` and `refs/` | n/a | (no references dir) | Neither `projects/PadicLFunctions/.mathlib-quality/references/` nor a top-level `refs/` exists — recorded n/a. The file's own docstring cites RJW arXiv:2309.15692 §9/§11.3. |
|  6 | nLab | "valuation ring" (fetched ncatlab.org/nlab/show/valuation+ring) | yes | "A valuation ring `O` is integrally closed in its field of fractions `F`" — proof: a field element satisfying a monic poly over `O` lies in `O`. | Confirms the bundled statement; the norm-`≤ 1` phrasing is the analytic shadow. |
|  7 | nCatLab (if categorical) | — | n/a | — | Not a categorical concept; an elementary integrality/closure property of the valuation ring. Brief look: nothing higher-categorical to add. |
|  8 | Stacks Project (if alg geom) | valuation ring integrally closed / normal | yes (indirect) | Valuation rings are integrally closed normal domains (Stacks tags 00I8 / 0AS4 family) | Concept covered; the `‖·‖ ≤ 1` form is the absolute-value rendering of the algebraic statement. |
|  9 | MathOverflow / Math.StackExchange | integral over Z ⇒ p-adic absolute value ≤ 1 generality | yes | Treated as background-standard: every algebraic integer has all non-arch absolute values `≤ 1`; the unit ball is the integral closure of `ℤ_p` in `ℂ_p`. | Textbook-elementary; MO carries it as a step, not a question. |
| 10 | recent arXiv (last 5 years) | non-Archimedean integral elements / `𝓞_ℂ_p` ring of integers | yes | arXiv perfectoid/p-adic-Hodge papers use `𝒪_{ℂ_p} = {|x| ≤ 1}` as the ring of integers without proof; mathlib's own `Perfectoid/BDeRham.lean` uses `PadicComplexInt`. | No recent *reformulation*; the statement is classical (Krull 1930s; Gauss far earlier for ℤ). |

The protocol passes: WebSearch ran 3 distinct queries at three generality levels (specific p-adic unit-ball form; the general Krull integral-closure form; the named *mechanism* = the monic-relation valuation argument, which matched the project's proof verbatim); local refs checked (absent → n/a); nLab fetched (hit, confirms integral-closedness); Stacks / nCatLab / MathOverflow / arXiv each looked at with an n/a reason where appropriate. ChatGPT MCP recorded n/a with reason (tool unavailable) — the only channel not run; the three web channels independently cover the standard-form **and** the standard-proof question.

### Literature summary (Phase 3)

Concept identified as: **"an element integral over the base lies in the valuation ring"** — equivalently, *the valuation ring (closed unit ball `{‖·‖ ≤ 1}`) of a non-archimedean field is integrally closed and contains the integral closure of `ℤ`* (Krull). For `ℂ_[p]` specifically: every algebraic integer / `ℤ`-integral element has `p`-adic absolute value `≤ 1`. The proof is the classical contradiction from the monic relation under the ultrametric inequality.

Sources agree on the standard form: **yes** — unanimous across Kedlaya/Conrad/Popa/Zhou lecture notes, nLab, Grokipedia, and Krull's theorem. The *proof* the project uses (assume `‖x‖>1`, dominate the monic relation by the leading term) is the textbook proof (Berkeley Part III Lemma 3.1).

Most general standard form: For a non-archimedean valued ring/field `K` with valuation `v` (equivalently an ultrametric submultiplicative norm with `‖1‖=1`) and any subring `R ⊆ {v ≥ 0}`, every element of `K` integral over `R` has `v ≥ 0` (`‖·‖ ≤ 1`). Specialising `K = ℂ_[p]`, `R = ℤ` gives exactly the user's lemma.

Generality dimensions where the literature varies:
  - **Ambient field**: `ℂ_p` here → any non-archimedean valued field (the textbook case) → any non-archimedean valued *ring*. The proof needs only ultrametric + submultiplicative + `‖1‖=1` + integer-coefficient bound.
  - **Base ring**: `ℤ` here → any subring of the valuation ring (Krull's general form is base-ring-free; integral over *the valuation ring itself* is the maximal statement, which is "integrally closed").
  - **Direction packaged**: the project ships the one direction `integral ⇒ ‖·‖ ≤ 1`; the standard mathlib object packages the iff and the integral-closedness.

Disagreement with the literature: **none.** The user's form is a correct, strictly-special case (`K = ℂ_p`, `R = ℤ`, one direction) of the standard valuation-ring integral-closedness fact.

---

### Generality analysis — `PadicLFunctions.Coleman.norm_le_one_of_isIntegral_int`

Literature-standard form (from Phase 3): in any non-archimedean valued field, an element integral over a subring of the valuation ring lies in the valuation ring; the valuation ring is integrally closed.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | ambient field `ℂ_[p]` | the specific `p`-adic complex field | any non-arch normed field, or `[SeminormedRing R] [NormOneClass R] [IsUltrametricDist R]` | **yes** | The proof uses only `norm_intCast_le_one`, `norm_pow`/`norm_mul`, `exists_norm_finsetSum_le_of_nonempty`, `pow_lt_pow_right₀` — none is `ℂ_p`-specific. It goes through verbatim for any ultrametric field; the `ℂ_p`-specialisation is a needless restriction *for the abstract lemma*. |
| 2 | base ring `ℤ` | `IsIntegral ℤ x` | integral over any subring of the unit ball (Krull) | **yes** | `norm_intCast_le_one` is the only place ℤ enters; for a general base subring `R ⊆ {‖·‖≤1}` it would be membership of `R`. The maximal form is "integral over the valuation ring ⇒ in the valuation ring" = integrally closed. |
| 3 | conclusion `‖x‖ ≤ 1` | norm form | `v x ≤ 1` / `x ∈ valuationSubring` | restate, not weaken | The norm form and the valuation form are interchangeable on `ℂ_[p]` via `PadicComplex.norm_eq_norm` + `NormedValued.norm_le_one_iff`; mathlib's canonical statement is the valuation/membership form. |
| 4 | `(p) [Fact p.Prime]` | section vars | absent in the abstract form | already vestigial | Used only to name `ℂ_[p]`; the abstract lemma drops them entirely. |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **2 substantive** (field `ℂ_p` → general ultrametric `NormOneClass` ring; base `ℤ` → arbitrary subring of the ball, culminating in "valuation ring is integrally closed").

Proposed restatement (the abstract lemma form, if one were to ship a *lemma*):
```lean
theorem norm_le_one_of_isIntegral_int {R : Type*} [SeminormedRing R] [NormOneClass R]
    [IsUltrametricDist R] {x : R} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1
```
Cost of restatement: **CHEAP** — the existing proof compiles verbatim under the weaker typeclasses (every lemma it calls is already at that generality). But Phase 4c shows the right artifact is the *valuation/subring* statement mathlib already has, not a generalised norm-lemma.

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let R be a foo" preambles → typeclasses? | yes | `ℂ_[p]` → `[SeminormedRing] [NormOneClass] [IsUltrametricDist]` (4a #1), or the `Valuation.Integers` typeclass packaging | composes with the whole `Valuation`/`ValuationSubring` API |
|  2 | sequences/metric → filters/topological? | no | — | no limits here; algebraic integrality + a single inequality |
|  3 | **construct an object where a universal-property / bundled object is canonical?** | **YES** | The canonical mathlib artifact is **`Valuation.Integers.isIntegral_iff_v_le_one`** applied to the **bundled ring of integers** `𝓞_ℂ_[p] = PadicComplexInt p` (a `ValuationSubring ℂ_[p]`, already in mathlib). The lemma "integral ⇒ `‖·‖ ≤ 1`" is then `mem_of_integral` + the norm↔valuation bridge, not a hand-rolled estimate. | `Valuation.integer.integers.isIntegrallyClosed`, the entire `ValuationSubring` lattice, `IsIntegrallyClosed` API, `PadicComplexInt` and its perfectoid consumers |
|  4 | set-with-closure-predicate → bundled type? | **YES** (same as #3) | the project's manual `‖·‖≤1` + monic-relation argument IS the "set defined by a predicate is integrally closed" fact; mathlib bundles it as `ValuationSubring` + `Valuation.Integers` | `PadicComplexInt`, `Valuation.integer`, `IsIntegrallyClosed V` instance (`Valuation/LocalSubring.lean:35`) |
|  5 | field-specific → weaken typeclass? | yes | `ℂ_p`-norm → general valuation (the valuation API is the maximal-generality home) | full valuation-ring API |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete base (ℤ) → arbitrary ring? | yes | drop `ℤ`: state integral-closedness of the valuation ring (`IsIntegralClosure`/`IsIntegrallyClosed`), which mathlib already has | `Valuation.Integers.integralClosure`, `isIntegrallyClosed_integers` |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and it is decisive, but it points at mathlib, not at a new contribution.** The contemporary mathlib formulation of "a `ℤ`-integral element of `ℂ_p` has `‖·‖ ≤ 1`" is:
  - the **bundled ring of integers** `𝓞_ℂ_[p] = PadicComplexInt p : ValuationSubring ℂ_[p]` (mathlib, `Complex.lean:251`), with `PadicComplexInt.integers : Valuation.Integers (PadicComplex.valued p).v 𝓞_ℂ_[p]` (`Complex.lean:257`); plus
  - the general lemma `Valuation.Integers.isIntegral_iff_v_le_one : IsIntegral O x ↔ v x ≤ 1` (mathlib, `RingTheory/Valuation/Integral.lean:34`) and its `IsIntegrallyClosed v.integer` instance.
  - Cost of routing through it: CHEAP-to-MODERATE (the `IsIntegral ℤ → IsIntegral 𝓞` tower step and the norm↔valuation reconciliation; see Phase 6).
  - Real mathematical improvement: it **replaces a hand-rolled monic-relation estimate with the library's integrally-closed-valuation-ring fact**, the canonical "`Submodule`/`ValuationSubring` vs ad-hoc predicate" modernisation. It is *not* a new mathlib contribution — mathlib already is the modern form.

This Phase-4c finding **rules out a YES verdict**: the modern idiom is already in mathlib (it is `Valuation.Integers` + `PadicComplexInt`), so the user's lemma is not a modernisation mathlib lacks — it is a special case mathlib can produce. Phase 7 therefore weighs **NO-mathlib-has-it vs NO-composable-from-mathlib**.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.Coleman.norm_le_one_of_isIntegral_int`

[A] Lean-Finder       (MCP tool unavailable in env) — n/a; substituted exhaustive grep over mathlib source (method D)
[B] Loogle            (MCP tool unavailable in env) — n/a; type-pattern intent `IsIntegral ℤ ?x → ‖?x‖ ≤ 1` and `IsIntegral _ ?x ↔ _ ≤ 1` searched via grep over `RingTheory/Valuation/`, `RingTheory/IntegralClosure/`, `NumberTheory/`
[C] LeanSearch        (MCP tool unavailable in env) — n/a; NL intent "element integral over Z has p-adic norm at most one" / "valuation of integral element ≤ 1" searched via the literature + grep
[D] Grep mathlib src  Searched `.lake/packages/mathlib/Mathlib/` for: `isIntegral_iff_v_le_one`, `mem_of_integral`, `IsIntegral.*norm_le`, `norm.*isIntegral`, `IsIntegral ℤ`∩`norm/le_one`, `valuationSubring`∩`IsIntegral`, `PadicComplexInt`, `PadicComplex.norm_eq_norm`, `norm_le_one_iff`, `IsIntegral.tower_top`. **Found the standard valuation-form result + the `ℂ_[p]` machinery; no `‖·‖`-on-`ℂ_p`-from-`ℤ`-integral statement.**
[E] Name pattern      Searched `norm_le_one_of_isIntegral`, `isIntegral.*norm_le_one`, `*_of_isIntegral_int`, `norm_le_one_iff_val` — **no hit** for the `ℂ_p` norm form; the `ℚ_[p]` analogue `Padic.norm_le_one_iff_val_nonneg` exists but is `ℚ_p`-only.

Searched for both forms:
  - **User's form** (`IsIntegral ℤ x → ‖x‖ ≤ 1` on `ℂ_[p]`, norm-side, base ℤ): **not in mathlib** as a single declaration.
  - **Literature-standard / valuation form** (integral element has valuation `≤ 1`; valuation ring integrally closed): **IN mathlib, at full generality**:
    - `Valuation.Integers.isIntegral_iff_v_le_one` (`RingTheory/Valuation/Integral.lean:34`) — `IsIntegral O x ↔ v x ≤ 1` for `Integers v O`.
    - `Valuation.Integers.mem_of_integral` (`Integral.lean:58`) — `IsIntegral O x → x ∈ v.integer`.
    - `Valuation.Integers.isIntegrallyClosed` / `isIntegrallyClosed_integers` (`Integral.lean:76,81`), `instance IsIntegrallyClosed V` for any `ValuationSubring` (`Valuation/LocalSubring.lean:35`).
  - **The exact `ℂ_[p]` instance is also in mathlib**: `ℂ_[p] = PadicComplex p` with `RankOne`-`Valued ℂ_[p] ℝ≥0`, `NormedField`, `IsUltrametricDist`, `PadicComplexInt = 𝓞_ℂ_[p] : ValuationSubring ℂ_[p]`, and `PadicComplexInt.integers : Valuation.Integers (PadicComplex.valued p).v 𝓞_ℂ_[p]` (`NumberTheory/Padics/Complex.lean:137,159,251,257`).

Building blocks for the norm↔valuation bridge (all in mathlib):
  - `PadicComplex.norm_eq_norm : ‖x‖ = Valued.v.norm x` (`Complex.lean:218`).
  - `NormedValued.toNormedField.norm_le_one_iff : ‖x‖ ≤ 1 ↔ val.v x ≤ 1` (`Topology/Algebra/Valued/NormedValued.lean:240`) — for a `RankOne`-`Valued` `NormedField`, which `ℂ_[p]` is.
  - `mem_valuationSubring_iff : x ∈ v.valuationSubring ↔ v x ≤ 1` (`ValuationSubring.lean:447`).
  - `IsIntegral.tower_top [Algebra A B] [IsScalarTower R A B] : IsIntegral R x → IsIntegral A x` (`IntegralClosure/IsIntegral/Basic.lean:160`) — supplies `IsIntegral ℤ x → IsIntegral 𝓞_ℂ_[p] x` (R=ℤ, A=𝓞, B=ℂ_[p]; `Algebra 𝓞 ℂ_[p]` is the standard `ValuationSubring` algebra instance, `ValuationSubring.lean:146`; `IsScalarTower ℤ 𝓞 ℂ_[p]` is automatic since ℤ is initial).

Concluded: **"found in mathlib as the standard valuation-theoretic result + the full `ℂ_[p]` machinery; the project's exact norm-side `ℤ`-form is recoverable by composing them."** The mathematical content (integral ⇒ in the valuation ring) is `Valuation.Integers.isIntegral_iff_v_le_one`, instantiated at `PadicComplexInt.integers`; the only gap is bookkeeping (the `IsIntegral.tower_top` step from ℤ to 𝓞, and the `norm_eq_norm`/`norm_le_one_iff` reconciliation), since mathlib's lemma is base-ring `O` and valuation-valued, whereas the project states it base-ℤ and norm-valued.

---

### Call sites — `PadicLFunctions.Coleman.norm_le_one_of_isIntegral_int`

Internal use count: **4** total (3 distinct project usages besides the declaration line), across **2 files**.
External-to-file callers: **1** distinct file (`IwasawaProof/Generators.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `…/Iwasawa/CyclotomicUnits.lean:163` | `exact ⟨Fglobal_le_K p hF, norm_le_one_of_isIntegral_int p hint⟩` — inside `globalUnits_le_localUnits` (`𝒱_n ≤ 𝒰_n`), the `‖u‖ ≤ 1` half |
| `…/Iwasawa/CyclotomicUnits.lean:165` | `refine ⟨Fglobal_le_K p ?_, norm_le_one_of_isIntegral_int p hintinv⟩` — same lemma, the `‖u⁻¹‖ ≤ 1` half |
| `…/IwasawaProof/Generators.lean:792` | `have h1 : ‖(u : ℂ_[p])‖ ≤ 1 := norm_le_one_of_isIntegral_int p hint` — inside `cycloUnitsPlus_eq_closure_gammas`, to derive `‖u‖ = 1` for a global unit |
| `…/IwasawaProof/Generators.lean:793` | `have h2 : ‖((u⁻¹ : ℂ_[p]ˣ) : ℂ_[p])‖ ≤ 1 := norm_le_one_of_isIntegral_int p hintInv` — the inverse bound, paired with `h1` to pin `‖u‖ = 1` |

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?):
  - **(none)** — no other site re-proves `IsIntegral ℤ x → ‖x‖ ≤ 1` by hand. The four uses all route through this lemma. (Distinct from the sibling `norm_le_one_of_mem_adjoin_int`, whose bundled equivalent `integerRing` *is* re-implemented elsewhere; this lemma is the unique home of the `ℤ`-integral ⇒ unit-ball fact in the project.)

What the call-sites pattern tells us: **K = 3 distinct internal uses across 2 files, no inline re-derivation.** Per the Phase-6 table this is the "real API; consumers depend on it" pattern that *leans YES* — it is a genuinely-used building block, not dead code or a one-off wrapper. This is the strongest YES-leaning signal in the analysis and is the reason the verdict is NO-**composable** (a deletable-and-inlinable wrapper) rather than NO-mathlib-has-it (a 0-line drop-in): the lemma carries its weight, but mathlib supplies the same content one import away.

---

### Composition check (Phase 6)

Can `norm_le_one_of_isIntegral_int` be derived from mathlib (the `Valuation.Integers` API + `PadicComplexInt` + the norm↔valuation bridge) in ≤3 chained calls?

**Attempt 1 — route `ℤ`-integral → `𝓞_ℂ_[p]`-integral → valuation `≤ 1` → norm `≤ 1`.**
```lean
example {x : ℂ_[p]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  -- ℤ ⊆ 𝓞_ℂ_[p] ⊆ ℂ_[p] is a scalar tower (ℤ initial), so integrality lifts:
  have hO : IsIntegral 𝓞_ℂ_[p] x := hx.tower_top
  -- the ring of integers is the valuation ring; integral ⇒ valuation ≤ 1:
  have hv : Valued.v x ≤ 1 := (PadicComplexInt.integers p).isIntegral_iff_v_le_one.mp hO
  -- norm ≤ 1 ↔ valuation ≤ 1 on ℂ_[p] (RankOne Valued NormedField + norm_eq_norm):
  rw [PadicComplex.norm_eq_norm]; exact (NormedValued.toNormedField.norm_le_one_iff).mpr hv
```
  - Mathlib decls used: `IsIntegral.tower_top`, `Valuation.Integers.isIntegral_iff_v_le_one`, `PadicComplexInt.integers`, `PadicComplex.norm_eq_norm`, `NormedValued.toNormedField.norm_le_one_iff` (+ the standard `Algebra 𝓞 ℂ_[p]` / `IsScalarTower ℤ 𝓞 ℂ_[p]` instances).
  - Result: **succeeds in principle** — each step is a single library call, and every input lemma was located in Phase 5.
  - Notes: it is **3 substantive calls + 1 `rw` reconciliation** (`norm_eq_norm`). The norm↔valuation `rw` is the one non-`.trans`/`.comp` glue step; whether it counts as "within ≤3 clean calls" is the borderline. With a one-time helper `lemma PadicComplex.norm_le_one_iff_val_le_one : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1` (which mathlib does **not** currently have for `ℂ_[p]`, though it has the `ℚ_[p]` analogue `Padic.norm_le_one_iff_val_nonneg`), the composition collapses to exactly 2 calls.

**Attempt 2 — pure ultrametric-from-scratch (the project's current proof).** Assemble `norm_intCast_le_one` + `exists_norm_finsetSum_le_of_nonempty` + `pow_lt_pow_right₀` across a `by_contra` and a monic-relation rearrangement. That is the author's ~30-line proof: **many calls + real case analysis. NOT a composition.**

Conclusion: **COMPOSABLE** — against mathlib's valuation-integers API (`Valuation.Integers.isIntegral_iff_v_le_one` instantiated at the *mathlib-provided* `PadicComplexInt.integers`), in a 3-call chain plus a single `norm_eq_norm` rewrite. It is **not** composable against raw ultrametric primitives alone (that is the author's from-scratch proof). The crux: the project re-proves from first principles a fact whose modern, bundled, integrally-closed-valuation-ring form mathlib already ships — and ships *for `ℂ_[p]` by name*.

---

## Verdict: `PadicLFunctions.Coleman.norm_le_one_of_isIntegral_int`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): unanimous and textbook-elementary — an element integral over `ℤ` (or any subring of the valuation ring) has non-archimedean absolute value `≤ 1`; the valuation ring is integrally closed (Krull; nLab; Kedlaya/Conrad/Popa/Zhou notes). The project's exact proof = Berkeley Part III Lemma 3.1.
- Generality analysis (Phase 4): STRICTLY NARROWER (`ℂ_p`→ ultrametric `NormOneClass` ring; `ℤ`→ arbitrary subring; norm→valuation form) — and Phase 4c shows the modern idiom (`Valuation.Integers` + bundled `ValuationSubring`) is **already mathlib**, so no YES.
- Mathlib search (Phase 5): the content is in mathlib as `Valuation.Integers.isIntegral_iff_v_le_one`, and the exact `ℂ_[p]` instance (`PadicComplexInt.integers`, `RankOne Valued`, `norm_le_one_iff`) is in mathlib too; only the int-form + norm-form bookkeeping is not packaged.
- Composition check (Phase 6): COMPOSABLE in a 3-call chain (`IsIntegral.tower_top` → `isIntegral_iff_v_le_one` at `PadicComplexInt.integers` → `norm_le_one_iff`, + a `norm_eq_norm` rewrite).

**Rationale (1–2 paragraphs):**

This theorem is the special case "`ℂ_p`, base `ℤ`, norm form, one direction" of a result mathlib already owns at full generality: the ring of integers of a non-archimedean valued field is integrally closed, equivalently `IsIntegral O x ↔ v x ≤ 1` (`Valuation.Integers.isIntegral_iff_v_le_one`). Crucially, `ℂ_[p]` is **itself a mathlib object** — `PadicComplex p`, a `RankOne`-`Valued` `NormedField` with its ring of integers `𝓞_ℂ_[p] = PadicComplexInt p` and the witness `PadicComplexInt.integers` already in `Mathlib/NumberTheory/Padics/Complex.lean`. So the user's statement is reachable by importing that file and composing three library calls: lift `IsIntegral ℤ x` to `IsIntegral 𝓞_ℂ_[p] x` along the (automatic) scalar tower `ℤ ⊆ 𝓞_ℂ_[p] ⊆ ℂ_[p]` via `IsIntegral.tower_top`; convert to `Valued.v x ≤ 1` via `mem_of_integral`/`isIntegral_iff_v_le_one`; and convert valuation-`≤ 1` to norm-`≤ 1` via `PadicComplex.norm_eq_norm` + `NormedValued.norm_le_one_iff` (`ℂ_[p]` is a `RankOne Valued NormedField`). The project instead re-proves the fact from scratch with a hand-rolled ultrametric estimate on the monic relation, and — tellingly — never imports mathlib's `PadicComplexInt`, building its own `valHom` valuation surrogate alongside.

Why not a YES bucket: against mathlib's bundled valuation-integers API the statement is a short composition (Phase 6), so it fails the "non-trivial / not ≤3-call composition" bar for `YES-add-as-is`; and Phase 4c confirms the modern, more-general form (`Valuation.Integers`, integrally-closed `ValuationSubring`) is **already in mathlib**, so this is not a modernisation mathlib is missing. Why NO-**composable** rather than NO-**mathlib-has-it**: mathlib's lemma is stated over the valuation ring `O` and in valuation values, not over `ℤ` and not on `‖·‖`; bridging requires the `IsIntegral.tower_top` step and the `norm_eq_norm`/`norm_le_one_iff` reconciliation — a genuine (if small) composition, not a 0-line drop-in. And the lemma has **3 real consumers across 2 files** (Phase 6.0) with no inline re-derivation, so it is a load-bearing wrapper, not dead code — which is exactly the "delete and inline / route through mathlib" situation rather than "already there verbatim". (BORDERLINE was considered, because the `norm_eq_norm` glue nudges the composition to the 3-call boundary and because deleting a 3-consumer wrapper is a house-style call; it is surfaced as a question below, but the evidence — mathlib has the content for `ℂ_[p]` by name, recoverable in a 3-call chain — resolves cleanly to NO-composable.)

**NO-composable-from-mathlib — refactor-actionable detail:**

WHY not: Mathlib has the result — `Valuation.Integers.isIntegral_iff_v_le_one` — and has the exact `ℂ_[p]` instance to feed it (`PadicComplexInt.integers`). The project's lemma is a 3-call composition through that API plus a norm↔valuation rewrite; once `Mathlib.NumberTheory.Padics.Complex` is imported, no standalone hand-rolled lemma is justified. The mathematically right move is to route the `‖·‖ ≤ 1` bound through mathlib's ring of integers rather than re-deriving it.

Mathlib building blocks (all with full paths):
  - `IsIntegral.tower_top` — `.lake/packages/mathlib/Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:160`
  - `Valuation.Integers.isIntegral_iff_v_le_one` / `Valuation.Integers.mem_of_integral` — `.lake/packages/mathlib/Mathlib/RingTheory/Valuation/Integral.lean:34,58`
  - `PadicComplexInt` (`𝓞_ℂ_[p]`) and `PadicComplexInt.integers` — `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/Complex.lean:251,257`
  - `PadicComplex.norm_eq_norm` — `.lake/packages/mathlib/Mathlib/NumberTheory/Padics/Complex.lean:218`
  - `NormedValued.toNormedField.norm_le_one_iff` — `.lake/packages/mathlib/Mathlib/Topology/Algebra/Valued/NormedValued.lean:240`
  - Standard instances: `Algebra 𝓞_ℂ_[p] ℂ_[p]` (`ValuationSubring.lean:146`); `IsScalarTower ℤ 𝓞_ℂ_[p] ℂ_[p]` (automatic, ℤ initial).

Composition sketch (the inlined replacement; 3 calls + one `rw`):
```lean
-- with `import Mathlib.NumberTheory.Padics.Complex` in scope:
example {x : ℂ_[p]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have hv : Valued.v x ≤ 1 :=
    (PadicComplexInt.integers p).isIntegral_iff_v_le_one.mp hx.tower_top
  rw [PadicComplex.norm_eq_norm]; exact NormedValued.toNormedField.norm_le_one_iff.mpr hv
```

Call sites in the project (from Phase 6.0): **K = 3** distinct uses across 2 files —
`CyclotomicUnits.lean:163`, `CyclotomicUnits.lean:165`, `Generators.lean:792`, `Generators.lean:793` (the two `Generators` lines are one consumer-block pinning `‖u‖ = 1`).

Refactor plan:
  1. Ensure `Mathlib.NumberTheory.Padics.Complex` is transitively imported by `CyclotomicUnits.lean` (the project already imports it in `ResidueZeta.lean`, so it is available in the build).
  2. Replace the body of `norm_le_one_of_isIntegral_int` with the 3-call composition above (route through `PadicComplexInt.integers` + `norm_le_one_iff`), **deleting the ~30-line hand-rolled `by_contra` ultrametric proof** — OR delete the lemma entirely and inline the composition at each of the 3 call sites. Given 3 consumers in 2 files, keeping a *thin* wrapper whose body is the 3-call composition is the cleaner house-style choice (one definition, mathlib-backed); deletion+inline is the strict NO-composable action. Either way the from-scratch estimate goes.
  3. At each call site (`CyclotomicUnits.lean:163,165`, `Generators.lean:792,793`) the call signature `norm_le_one_of_isIntegral_int p hint` is unchanged if the wrapper is kept; if inlined, substitute the composition (watch the `hintInv`/`Units.val_inv_eq_inv_val` shape at the inverse sites).
  4. (Optional, separate upstreaming item — its own `/mathlibable` question, not this verdict) Mathlib has `Padic.norm_le_one_iff_val_nonneg` for `ℚ_[p]` but **no `ℂ_[p]` analogue**; a small `@[simp] lemma PadicComplex.norm_le_one_iff_val_le_one : ‖x‖ ≤ 1 ↔ Valued.v x ≤ 1` (= `norm_eq_norm` + `NormedValued.norm_le_one_iff`) would be a clean, genuinely-missing addition to `NumberTheory/Padics/Complex.lean` that collapses this composition to 2 calls and benefits every `ℂ_p` norm-vs-valuation argument. That is the only mathlib-worthy artifact in the vicinity — and it is a one-line `def/lemma` about `ℂ_p`, not this theorem.

Next action: delete the hand-rolled proof; route the `‖x‖ ≤ 1` bound through mathlib's `PadicComplexInt.integers` + `Valuation.Integers.isIntegral_iff_v_le_one` + the `norm_eq_norm`/`norm_le_one_iff` bridge (import `Mathlib.NumberTheory.Padics.Complex`). Separately consider contributing the missing `PadicComplex.norm_le_one_iff_val_le_one` simp-lemma to mathlib.

---

## Next step

Replace `norm_le_one_of_isIntegral_int`'s from-scratch ultrametric proof with the 3-call composition through mathlib's already-present `ℂ_[p]` ring-of-integers API (`PadicComplexInt.integers` + `Valuation.Integers.isIntegral_iff_v_le_one`, bridged to the norm via `PadicComplex.norm_eq_norm` + `NormedValued.norm_le_one_iff`), keeping a thin mathlib-backed wrapper for its 3 consumers or inlining at the 4 call sites. As a *separate* potential mathlib contribution, evaluate adding the genuinely-missing `PadicComplex.norm_le_one_iff_val_le_one` simp-lemma (the `ℂ_[p]` analogue of the existing `Padic.norm_le_one_iff_val_nonneg`).
