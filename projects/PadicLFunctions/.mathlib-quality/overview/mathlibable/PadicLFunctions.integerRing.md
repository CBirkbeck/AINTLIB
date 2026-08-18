# `/mathlibable` report — `PadicLFunctions.integerRing`

**Final verdict (five-bucket): `BORDERLINE-needs-human`**

> One-line summary: the *carrier* (`{x : L | ‖x‖ ≤ 1}` as a `Subring`) is essentially
> already in mathlib as `(NormedField.valuation L).integer` / `.valuationSubring`, so this
> is not a clean YES; but the project's value-add is a bundle of analytic/topological
> instances on the subtype (`IsUltrametricDist`, `CompleteSpace`, **`IsLinearTopology`**,
> `Algebra ℤ_[p]`, `IsBoundedSMul`) that mathlib carries on **no** valuation/normed integer
> ring, so it is not a clean NO either. The remaining decision — refactor onto mathlib's
> `ValuationSubring` and contribute the missing instances upstream, vs. keep the local
> `Subring` anchor — is an architecture/taste call the skill cannot make alone.

---

### Baseline (Phase 0)
- lake build:               **not re-run** (stale/slow per task note); reasoned from source — the decl and all its dependencies were read directly from `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean` and the pinned mathlib tree under `.lake/packages/mathlib/`.
- decl `PadicLFunctions.integerRing`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/Coefficients.lean:41`
- kind:                      `def` (bundled `Subring L`)
- has sorry:                 no
- module docstring summary:  Coefficient rings for §5 — the integer ring (norm-unit ball) of a nonarchimedean complete normed `ℚ_[p]`-algebra field `L`, together with its analytic instance bundle (ultrametric, complete, linear topology, `ℤ_[p]`-algebra) and root-of-unity norm lemmas (W1/W2/W3).

---

### Statement (Phase 1)

`PadicLFunctions.integerRing` is **a definition** of the following:

> Let `L` be a complete nonarchimedean (ultrametric) normed field that is a normed
> `ℚ_[p]`-algebra. The **integer ring** (a.k.a. ring of integers / valuation ring)
> `integerRing L` is the closed unit ball `{x ∈ L : ‖x‖ ≤ 1}`, packaged as a subring of
> `L`. For a finite extension `L/ℚ_p` this is the usual `𝒪_L`; `ℚ_p` and `ℂ_p` are
> instances. Closure under addition is exactly the ultrametric inequality
> `‖x + y‖ ≤ max ‖x‖ ‖y‖ ≤ 1`; closure under multiplication is `‖xy‖ = ‖x‖‖y‖ ≤ 1`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the residue characteristic.
- `L : Type*`, `[NormedField L]` — the ambient field carrying the norm whose unit ball we take.
- `[NormedAlgebra ℚ_[p] L]` — the `ℚ_p`-algebra structure (used by the *sibling* `Algebra ℤ_[p]` instance and downstream, **not** by the carrier itself).
- `[IsUltrametricDist L]` — the nonarchimedean (ultrametric) hypothesis; this is what makes the unit ball additively closed.
- `[CompleteSpace L]` — used only by the sibling `CompleteSpace (integerRing L)` instance, not by the `Subring` carrier.

Hypotheses (Lean side): none — it is a definition.

Conclusion (math): the closed unit ball of `L` is a subring (the valuation ring / ring of integers).

Conclusion (Lean): `Subring L`. (n/a — definition.)

The body is a `Subring` constructor:
```lean
def integerRing : Subring L where
  carrier := {x : L | ‖x‖ ≤ 1}
  mul_mem' {x y} hx hy := by simpa using mul_le_one₀ hx (norm_nonneg _) hy
  one_mem' := by simp
  add_mem' {x y} hx hy := (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  zero_mem' := by simp
  neg_mem' {x} hx := by simpa using hx
```
Note `add_mem'` is literally `IsUltrametricDist.norm_add_le_max ▸ max_le` — the **same** term mathlib uses for `map_add_le_max'` when it builds `NormedField.valuation` (see Phase 5).

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it introduces a **named mathematical structure** (the ring of integers / valuation ring of a nonarchimedean field, as a bundled `Subring`) and is the foundational coefficient object for the entire §5 development — it is the `R` over which `MeasureR`, the Iwasawa algebra `Λ_R(ℤ_p)`, the Mahler transform, and the Coleman/Interpolation machinery are all defined. It is named in the file's "Main declarations" as W1.

(Literature width is EXHAUSTIVE regardless; BIG/SMALL recorded for framing only.)

### One-line check (Phase 2b)

Body line count: **5 substantive proof fields** (one `Subring` constructor with `carrier` + four membership obligations).
One-liner verdict: **MULTI-LINE** (a bundled-structure `def` with five proof fields, not a one-substantive-line `def`/`abbrev`). The 2b exemption table is therefore not required. Note for the record: even read as "thin", the def would qualify under exemption 3 (semantic intent / API stability) — it is the named anchor of an instance ecosystem (582 uses, see Phase 6.0) — and exemption 2 (typeclass-search anchor: the `Algebra ℤ_[p] (integerRing L)` and `IsLinearTopology` instances need a single canonical target type).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | `ring of integers nonarchimedean valued field unit ball "valuation ring" {x : \|x\| ≤ 1}` | **yes** | `𝒪 = {x ∈ F : \|x\| ≤ 1}`; open ball `m = {\|x\| < 1}` is its maximal ideal → local ring | MIT 18.785 Lec.8; Wikipedia "Valuation ring"; Achinger "Intro to non-Archimedean Geometry"; Cambridge Part III Local Fields. Unanimous: closed unit ball **is** the ring of integers. |
| 2 | WebSearch (general form / mechanism) | `nonarchimedean field "norm ≤ 1" closed unit ball is a subring ultrametric inequality additive closure` | **yes** | "The closed ball of radius 1 is a local ring, called the ring of integers"; additive closure follows from `\|x+y\| ≤ max{\|x\|,\|y\|}` | Kedlaya 18.787 (absolute values); Baldassarri non-arch functional analysis; rigidity result: a submultiplicative `μ ≤ \|·\|` whose unit ball is a subring forces `μ = \|·\|`. Confirms the ultrametric is *exactly* what makes it a subring. |
| 3 | WebSearch (named-after / Iwasawa context / aliases) | `"ring of integers" finite extension Qp valuation ring 𝒪_L Iwasawa algebra coefficient ring p-adic L-function` | **yes** | `𝒪_K` = elements of nonneg valuation = integral closure of `ℤ_p`; in Iwasawa theory "the Iwasawa algebra is a finite flat extension … with coefficients in the ring of integers of a finite extension of `ℚ_p`" | Mustață p-adic appendix; FU Berlin valuation-rings notes; arXiv 2407.06983, archive.ymsc Wan. Matches the docstring's RJW §3.1/§5 use precisely. Also arXiv 1401.1062 "Dynamics of convergent power series on the **integral ring** of a finite extension of `ℚ_p`" — the same `PowerSeries (𝒪_L)` setting. |
| 4 | ChatGPT MCP | — | **n/a** | — | ChatGPT MCP server is not connected in this environment (the `/setup-chatgpt` skill exists but no MCP tool is registered). Compensated by 4 distinct WebSearch/WebFetch literature channels (#1–3, #6) plus the in-repo mathlib source as primary text. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` | **n/a** | (no references dir) | The project has `.mathlib-quality/overview/` but **no** `references/` directory; recorded as n/a per protocol. |
| 6 | nLab | `valuation ring` (WebFetch of ncatlab.org/nlab/show/valuation+ring) | partial | abstract valuation ring: for nonzero `x` in the fraction field, `x` or `x⁻¹` lies in the ring; arises from a valuation `v` | nLab gives the *algebraic* characterization, not the unit-ball one — but it is the same object (`v x ≤ 1`). Confirms the concept is standard; the norm/unit-ball phrasing lives in the analysis literature (channels #1–2). |
| 7 | nCatLab (categorical) | — | **n/a** | — | Not a categorical concept; the valuation ring is a 1-categorical algebraic object with no higher-categorical generalisation relevant here. |
| 8 | Stacks Project (alg geom) | (valuation ring is in Stacks tag 00I8, well-known) | **n/a (not searched in depth)** | — | The valuation-ring/ring-of-integers concept is standard in Stacks (valuation rings, tag 00I8) but this is an analytic-normed-field object, not an AG-scheme construction; no Stacks-specific form is needed beyond what #1/#6 give. |
| 9 | MathOverflow / Math.SE | covered transitively by #1–2 (the lecture-note + Wikipedia hits) | **n/a** | — | The statement is textbook-level; MO/MSE add nothing beyond the unanimous lecture notes. |
| 10 | recent arXiv (last 5 yr) | surfaced under #1–3 (arXiv 2402.14772, 2508.11268, 1401.1062, 2407.06983) | **yes** | modern usage identical: `𝒪 = \{\|x\| ≤ 1\}` as the integer subring; condensed/almost-math and Iwasawa papers all use it as-is | Confirms the form has **not** evolved — it is the same object in 2024–2025 literature as in classical local-field theory. |

### Literature summary (Phase 3)

Concept identified as: the **ring of integers** / **valuation ring** of a nonarchimedean (ultrametric) valued field — `𝒪 = {x : ‖x‖ ≤ 1}`. In the finite-extension case it is written `𝒪_L`.

Sources agree on the standard form: **yes**, unanimously. Every channel that addresses nonarchimedean fields gives the closed unit ball as the integer subring, with the ultrametric inequality as the reason it is additively closed.

Most general standard form: the valuation ring `{x : v x ≤ 1}` of **any** valued field (Krull valuation into a `LinearOrderedCommGroupWithZero`), of which the rank-≤-1 / real-absolute-value / nonarchimedean-normed case is a specialisation.

Generality dimensions where the literature varies:
- **Index of the valuation:** real absolute value (`‖·‖ : L → ℝ`) ⊂ rank-one valuation (`ℝ≥0`) ⊂ general Krull valuation (`Γ₀`). The most general is the Krull valuation. The target uses the most specific (a real norm).
- **Ambient structure:** complete normed `ℚ_p`-algebra field (target) ⊂ nonarchimedean normed field ⊂ valued field. The literature object needs only "valued field"; completeness and the `ℚ_p`-algebra structure are extra.

Disagreement with the literature: **none** — the target's def is exactly the classical object, at the narrow (real-norm, `ℚ_p`-algebra) end of the generality spectrum.

---

### Generality analysis — `PadicLFunctions.integerRing`

Literature-standard form (from Phase 3): the valuation ring `{x : v x ≤ 1}` of a valued field; specialised, for a nonarchimedean normed field, to the closed unit ball `{x : ‖x‖ ≤ 1}`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[NormedField L]` | a real-normed **field** | a valued field (Krull valuation into `Γ₀`) | **yes** (in principle) | The carrier-as-subring needs only a valuation `v` and `v(x+y) ≤ max …`; mathlib's `Valuation.integer` is stated for any `[Ring R]` + `Valuation R Γ₀`. The norm is one rank-≤-1 instance. |
| 2 | `[IsUltrametricDist L]` | ultrametric (nonarchimedean) | nonarchimedean valuation `v(x+y) ≤ max(v x, v y)` | **NO** | Essential. Over an archimedean norm the unit ball is *not* a subring (triangle ineq gives `≤ 2`). The whole construction needs this; it is the literature's hypothesis too. |
| 3 | `[NormedAlgebra ℚ_[p] L]` | `ℚ_p`-algebra | (absent from the literature object) | **yes** (for the def) | The carrier/`Subring` does **not** use this; it is only consumed by the *sibling* `Algebra ℤ_[p] (integerRing L)` instance. The bare ring-of-integers needs no scalar field. |
| 4 | `[CompleteSpace L]` | complete | (absent from the literature object) | **yes** (for the def) | The carrier/`Subring` does **not** use this; only the sibling `CompleteSpace (integerRing L)` instance does. The ring of integers exists for incomplete fields too. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL for the carrier in the narrow class it targets, but STRICTLY NARROWER than the literature/mathlib-standard object.** The `Subring` itself is the standard ring of integers; the *typeclass cluster* `[NormedField] [NormedAlgebra ℚ_[p]] [IsUltrametricDist] [CompleteSpace]` is much narrower than what the object requires (the carrier needs only `[NormedField]+[IsUltrametricDist]`; `Valuation.integer` needs only a `Valuation`).

Number of weakening opportunities found: **3** (`NormedAlgebra ℚ_[p]` and `CompleteSpace` are unused by the carrier; the norm could be a general valuation). But — see 4c — the dominant signal is not "weaken the typeclasses", it is "**mathlib already has this object**, in a more idiomatic bundled form, via `NormedField.valuation` + `Valuation.integer`/`valuationSubring`".

Proposed restatement (if pursued): drop `CompleteSpace`/`NormedAlgebra` from the def itself and either (a) re-express as `(NormedField.valuation L).integer` (carrier `{x | ‖x‖₊ ≤ 1}`, requires only `[NormedField L] [IsUltrametricDist L]`), or (b) use `(NormedField.valuation L).valuationSubring : ValuationSubring L` to inherit the bundled local-ring/valuation-ring API.

Cost of restatement: **MODERATE → EXPENSIVE** — see Phase 6: refactoring 582 call sites onto a mathlib object that lacks the project's analytic instance bundle is non-trivial, and re-housing those instances on the mathlib object is itself a mathlib-PR-sized task.

### Modern-idiom check (Phase 4c) — the Bourbaki 2.0 check

| # | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|---|----------|----------|------------------------|----------------------------------|
| 1 | "let `L` be a foo" preambles → typeclasses/instances? | **already done** | the def already uses typeclasses; n/a | — |
| 2 | sequences/metric → filters/topological? | no | this is a subring construction, no convergence in the *statement* | (the *instances*, e.g. `IsLinearTopology`, are already filter/topological) |
| 3 | constructs an object where a **universal-property class** would characterise it? | **partially** | `Valuation.Integers` (in `Integers.lean`) is the characteristic predicate "`O` is the integers of `v`"; mathlib has the universal characterisation already | `Valuation.Integers v O` API: `one_of_isUnit`, integral-closure facts |
| 4 | **set-with-closure-predicate** → **bundled-substructure type**? | **YES — this is the dominant finding** | `(NormedField.valuation L).valuationSubring : ValuationSubring L` (a bundled type, `SubringClass`, `IsLocalRing`, `ValuationRing`, `IsFractionRing`, lattice of valuation subrings) | the entire `ValuationSubring`/`Valuation.Integers` ecosystem: local-ring structure, maximal ideal (the open ball), fraction field `L`, valuation-ring lattice |
| 5 | vector-space/metric/field-specific → weaken typeclasses (modules / (semi)ring)? | **YES** | `Valuation.integer : Subring R` is stated for any `[Ring R]` + `Valuation R Γ₀`; the norm/field/`ℚ_p`-algebra are all specialisations | scalar-tower lemmas, the general valuation API independent of the analytic structure |
| 6 | 1-categorical → higher/∞-categorical? | no | finite-dimensional algebra; no categorification target | — |
| 7 | concrete index (ℕ,ℤ,ℝ) → arbitrary monoids/groups/orders? | **YES** | the real norm `→ ℝ` generalises to a valuation into an arbitrary `LinearOrderedCommGroupWithZero Γ₀` (exactly `Valuation.integer`'s signature) | unifies with mathlib's Krull-valuation machinery |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — and it already exists in mathlib.**
- Proposed mathlib-idiomatic form: the ring of integers of a nonarchimedean normed field is `(NormedField.valuation L).integer : Subring L`, or the bundled `(NormedField.valuation L).valuationSubring : ValuationSubring L`. Mathlib's own `ℂ_p` integer ring is built precisely this way: `PadicComplexInt : ValuationSubring ℂ_[p] := (PadicComplex.valued p).v.valuationSubring` (`Mathlib/NumberTheory/Padics/Complex.lean:251`).
- Cost: re-housing onto the mathlib object is **MODERATE–EXPENSIVE** (582 internal uses; the analytic instances must move with it).
- Mathlib downstream this enables: `SubringClass`, `CommRing`, `IsDomain`, `IsLocalRing`, `ValuationRing`, `IsFractionRing A L`, the valuation-subring lattice, and `Valuation.Integers` characteristic-predicate API — none of which the bare project `Subring` exposes.
- Real mathematical improvement (not just "looks cooler"): **yes** — it eliminates a genuine duplication of mathlib's valuation-subring and connects the coefficient ring to the local-ring/fraction-field API the project re-derives by hand elsewhere.

**However**, the honesty bar cuts both ways here. The modernisation is only a *net* win if the project's analytic instance bundle can ride on the mathlib object — and that bundle (`IsUltrametricDist`/`CompleteSpace`/**`IsLinearTopology`**/`Algebra ℤ_[p]`/`IsBoundedSMul`) is **absent from mathlib for every valuation/normed integer ring** (Phase 5 grep is empty). So Phase 4c says "mathlib has the object" while Phase 5/6 say "mathlib does not have what makes this object *useful here*". That tension is what pushes the verdict to BORDERLINE rather than a self-resolving YES-but-generalise-first or NO-mathlib-has-it.

---

### Diamond / defeq risk — `PadicLFunctions.integerRing` (Phase 4.5; kind = `def`)

| # | Risk | Verdict | Evidence / rationale |
|---|------|---------|----------------------|
| 1 | Typeclass diamond | **low** | The def is a plain `Subring`; instances are searched on `↥(integerRing L)`. The only live diamond risk is if both this `Subring` and a mathlib `ValuationSubring`/`Submonoid.unitClosedBall` instance were in scope on the *same* carrier subtype — but the project never imports/uses the valuation route (Phase 6 grep: 0 uses), so today there is one canonical target. Upstreaming a *duplicate* `Subring` alongside mathlib's `Valuation.integer` **would** create exactly such a diamond — a reason the duplicate should not be added as-is. |
| 2 | Reducibility leak | **none** | Not `@[reducible]`; the `Subring` body is sealed, so `simp`/defeq do not unfold the carrier `{x | ‖x‖ ≤ 1}` spuriously. The sibling `Algebra ℤ_[p]` instance even *relies* on this sealing (it `change`s through the carrier explicitly). |
| 3 | Non-canonical unfolding | **low** | Membership reduces to `‖x‖ ≤ 1` definitionally (the `simpa`/`change` proofs in the file depend on this), which is the expected behaviour. No surprising `rfl`. |
| 4 | Instance priority collision | **low** | The siblings are instances on the subtype with default priority. `IsLinearTopology (integerRing L) (integerRing L)` and `Algebra ℤ_[p] (integerRing L)` have no competing mathlib instance on this exact (project-local) type today, so no collision; default priority is fine. |
| 5 | Universe-polymorphism issues | **none** | `L : Type*`; `Subring L : Type*`; no forced universe annotation. |
| 6 | Coercion ambiguity | **none** | Standard `SubringClass` coercion `↥(integerRing L) → L`; no bespoke `CoeFun`/`CoeSort` competing with mathlib. |

### Risk verdict (Phase 4.5)

Overall risk: **LOW.** No HIGH rows.
Top risks: none HIGH. The only one worth flagging is row 1 in the *upstreaming* direction: shipping `integerRing` to mathlib **as a second `Subring`** for the same carrier mathlib already has via `Valuation.integer` would be a deliberate diamond and is the main reason "add the duplicate as-is" is wrong.

---

### Mathlib search-status: `PadicLFunctions.integerRing`

[A] Lean-Finder — n/a: the Lean-Finder HF Space is not reachable as a tool in this environment. Compensated by [B]–[E] + the literature channels.
[B] Loogle — `Subring _` with carrier `{x | ‖x‖ ≤ 1}` / `closedBall`-as-`Subring` patterns, attempted via web (loogle.lean-lang.org not directly callable here; queried through WebSearch over the mathlib4 docs). **Hits:** `Valuation.integer` (`Subring R`), `Valuation.valuationSubring` (`ValuationSubring K`), `Submonoid.unitClosedBall` (only a `Submonoid`). No `Subring` keyed directly on a *norm* exists beyond `PadicInt.subring`.
[C] LeanSearch — natural-language `closed unit ball of nonarchimedean field as a subring` / `ring of integers of a normed field` (via WebSearch over mathlib4 docs). **Hits:** the valuation-subring family; `Mathlib/RingTheory/Valuation/Discrete/Basic.html` (valuationSubring is a DVR when value group cyclic).
[D] Grep mathlib src — `grep -rn` over `.lake/packages/mathlib/Mathlib/`:
  - `carrier := { x | ‖x‖ ≤ 1 }` as a `Subring` → **one hit only**: `PadicInt.subring` (`NumberTheory/Padics/PadicIntegers.lean:80`), specific to `ℚ_[p]`.
  - `unitClosedBall` / `unitBall` → `Subsemigroup.unitBall`, `Subsemigroup.unitClosedBall`, `Submonoid.unitClosedBall` (`Analysis/Normed/Field/UnitBall.lean`) — **all stop at `Submonoid`**; the file's docstring states it uses "the weakest possible typeclass … from `NonUnitalSeminormedRing` to `NormedField`", i.e. it deliberately does **not** add additive/ring structure (which needs the ultrametric).
  - `Subring.closedBall` / `AddSubgroup.closedBall` / `Subring.unitClosedBall` over a normed ring → **empty** (the `ArchimedeanClass.*closedBall*` hits are an unrelated order-theoretic construction).
  - `Valuation.integer : Subring R` → `RingTheory/Valuation/Integers.lean:32`; its `add_mem'` is `le_trans (v.map_add x y) (max_le hx hy)` — the valuation analogue of the target's `add_mem'`.
  - `NormedField.valuation : Valuation K ℝ≥0` → `Topology/Algebra/Valued/NormedValued.lean:48`, `toFun := nnnorm`, `map_add_le_max' := IsUltrametricDist.norm_add_le_max`, needs only `[NormedField K] [IsUltrametricDist K]`; `valuation_apply : valuation x = ‖x‖₊ := rfl`.
  - `IsLinearTopology` on a valuation/normed integer ring → **empty** (only the abstract `PowerSeries/Evaluation.lean` consumers); `CompleteSpace`/`IsUltrametricDist`/`MetricSpace`/`NormedRing` on `ValuationSubring`/`valuationSubring` → **empty**.
[E] Name pattern (lean_local_search analogue, grep) — `integerRing`, `normSubring`, `integerSubring` over mathlib → **no hits**; mathlib has no `integerRing`.

Searched for both:
  - the user's current form (norm-unit-ball `Subring`) — **carrier exists** only as `PadicInt.subring` (for `ℚ_p`); no general-`NormedField` `Subring`-by-norm.
  - the literature-standard / general form (valuation ring) — **exists**: `Valuation.integer` / `Valuation.valuationSubring`, instantiable here via `NormedField.valuation` with exactly the target's `[NormedField]+[IsUltrametricDist]` hypotheses.

Concluded: **"found a partial match"** — mathlib has the *carrier object* (`(NormedField.valuation L).integer` / `.valuationSubring`, a `Subring`/`ValuationSubring` with the identical set `{x | ‖x‖ ≤ 1}`), but it does **not** have the project's analytic/topological instance bundle on that object (`IsUltrametricDist`, `CompleteSpace`, **`IsLinearTopology`**, `Algebra ℤ_[p]`, `IsBoundedSMul`). The single most load-bearing gap is `IsLinearTopology` on the integer ring of a nonarchimedean normed field — absent from all of mathlib.

---

### Call sites — `PadicLFunctions.integerRing`

Internal use count: **582** occurrences (project-wide, excluding the declaring file `Coefficients.lean`).
External-to-file callers: **20 distinct files**:
`ResidueZeta.lean`, `ValuesAtOne.lean`, `MeasureR/{Basic, Convolution, Fubini, MahlerTransform, Toolbox, BaseChange, UnitsRing, FormalPsi, UnitsZp}.lean`, `IwasawaProof/LogDerivative.lean`, `Coleman/{NormOperator, Tower}.lean`, `Interpolation/{TameConductor, NonTame, Twist, Characters, LpFunction}.lean`.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `MeasureR/MahlerTransform.lean:67` | `def mahlerTransform (μ : MeasureR K ℤ_[p]) : PowerSeries (integerRing K)` — coefficient ring of the Mahler/Iwasawa power series |
| `MeasureR/MahlerTransform.lean:43` | `def mahlerCM (n : ℕ) : C(ℤ_[p], integerRing K)` — Mahler basis valued in the integer ring |
| `MeasureR/Convolution.lean:94` | `def mahlerRingEquiv : MeasureR K ℤ_[p] ≃+* PowerSeries (integerRing K)` — the `Λ_R(ℤ_p)` isomorphism |
| `MeasureR/Fubini.lean:32` | `def innerInt … (F : C(X × Y, integerRing K)) : C(X, integerRing K)` |
| `ValuesAtOne.lean:291,293,…` | `(η : DirichletCharacter (integerRing K) D)`, `{ζ : integerRing K}` — characters/roots of unity over the integer ring |
| `ResidueZeta.lean:727–728` | docstring: `algebraMap ℤ_[p] (integerRing K)` composite; the `Algebra ℤ_[p] (integerRing K)` instance |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `integerRing`?):
  - The mathlib valuation route (`NormedField.valuation` / `Valuation.integer` / `valuationSubring`) is **never** used anywhere in the project (grep = 0). So the project does not bypass `integerRing` via mathlib's object — it uses `integerRing` uniformly. (This is the dedup signal: `integerRing` is a *reimplementation* of a mathlib object that the project then never reconciles with mathlib.)

What the call-sites pattern tells us: **K = 582 internal uses across 20 files, no inline re-derivation, no use of the mathlib alternative.** Per the signal table this is a *real, foundational API* — consumers depend on it pervasively. That biases strongly toward a YES bucket *for the role*, while Phase 5 shows the carrier itself is a mathlib duplicate. The two signals point in opposite directions — the hallmark of a BORDERLINE architecture call.

---

### Composition check (Phase 6)

Can `PadicLFunctions.integerRing` be derived from mathlib in ≤3 chained calls?

Attempt 1 (carrier only): `(NormedField.valuation L).integer`
  - Mathlib decls used: `NormedField.valuation` (`NormedValued.lean:48`), `Valuation.integer` (`Integers.lean:32`), `NormedField.valuation_apply` (`= ‖x‖₊`, `rfl`).
  - Result: **succeeds for the `Subring` carrier.** `(NormedField.valuation L).integer : Subring L` has carrier `{x | (NormedField.valuation L) x ≤ 1} = {x | ‖x‖₊ ≤ 1}`, which equals `integerRing L`'s carrier `{x | ‖x‖ ≤ 1}` since `‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1`. The membership iff is `≤1`-line: `Valuation.mem_integer_iff` + `valuation_apply` + `NNReal.coe_le_one` (or `coe_le_one`).
  - Notes: this is a genuine ≤3-call composition **for the def's underlying subring**.

Attempt 2 (the full object as used — i.e. with the instances): re-house `IsUltrametricDist`/`CompleteSpace`/`IsLinearTopology`/`Algebra ℤ_[p]`/`IsBoundedSMul` onto `(NormedField.valuation L).integer`.
  - Mathlib decls used: none suffice — Phase 5 shows mathlib carries **none** of these instances on any valuation/normed integer ring.
  - Result: **fails.** Each instance is its own genuine proof (the `IsLinearTopology` instance alone is a ~10-line `mk_of_hasBasis'` argument; `CompleteSpace` needs the closedness argument; `Algebra ℤ_[p]` is the `codRestrict` of the scalar embedding). These are not 1–3 mathlib calls.
  - Notes: this is precisely why the def is **not** a throwaway wrapper.

Conclusion: **PARTIAL — COMPOSABLE at the carrier level, NOT-COMPOSABLE at the level of the object-plus-instance-bundle that the project actually uses.** The `Subring` carrier is a clean ≤3-call composition of mathlib primitives (`(NormedField.valuation L).integer`); the *instance ecosystem* that makes `integerRing` the workable coefficient ring for §3–§5 is not in mathlib and is not composable. Because the value of this declaration is the bundle, not the carrier, "just inline `(NormedField.valuation L).integer`" does **not** discharge what `integerRing` provides.

---

## Verdict: `PadicLFunctions.integerRing`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): unanimous — the closed unit ball of a nonarchimedean field **is** the ring of integers / valuation ring; maximally classical; the target matches the standard form exactly (≥4 channels: WebSearch ×3 + nLab; arXiv corroboration).
- Generality analysis (Phase 4): the carrier is the standard object but the typeclass cluster is narrower than required; **Phase 4c is decisive** — mathlib's idiomatic form `(NormedField.valuation L).valuationSubring` already exists and is how mathlib builds `𝓞_{ℂ_p}`.
- Mathlib search (Phase 5): **partial match** — the carrier object exists (`Valuation.integer` / `valuationSubring` via `NormedField.valuation`); the analytic instance bundle (esp. `IsLinearTopology`, `CompleteSpace`, `Algebra ℤ_[p]`) does **not** exist on any mathlib valuation/normed integer ring.
- Composition check (Phase 6): **PARTIAL** — COMPOSABLE for the carrier (`(NormedField.valuation L).integer`, ≤3 calls), NOT-COMPOSABLE for the instance bundle that is the declaration's actual value.

**Rationale (why BORDERLINE, not a self-resolving bucket):**

The two strongest signals contradict each other, and reconciling them is an architecture/taste call the skill is explicitly forbidden to make alone. On one side, Phase 5 + Phase 4c show the **carrier is a mathlib duplicate**: `integerRing L` is set-theoretically and structurally `(NormedField.valuation L).integer`, with the very same `IsUltrametricDist.norm_add_le_max` proof of additive closure that mathlib uses to build `NormedField.valuation`; mathlib even constructs its own `ℂ_p` ring of integers exactly this way (`PadicComplexInt := …valuationSubring`). That argues for `NO-mathlib-has-it` (refactor onto `Valuation.integer`/`valuationSubring`) — and the gate forbids `YES-add-as-is` because Phase 5 found the carrier. On the other side, Phase 6 shows the declaration's *real content* is an instance bundle — `IsUltrametricDist`, `CompleteSpace`, and above all **`IsLinearTopology` on the integer ring** (needed for `PowerSeries.eval₂` substitution into `(integerRing L)⟦T⟧`), plus the project's `Algebra ℤ_[p]`/`IsBoundedSMul` — none of which mathlib carries on **any** valuation or normed integer ring (Phase 5 grep is empty). Re-housing those instances onto `(NormedField.valuation L).valuationSubring` is itself mathlib-PR-sized work, and would have to thread the `NormedField.valuation`/RankOne bridge through all 582 uses across 20 files. So `NO-mathlib-has-it` is also wrong as stated (the user's object does *not* "follow in ≤1 line" once the instances are counted), and `NO-composable-from-mathlib` is wrong (Phase 6 is only PARTIAL — the instances are real proofs, not a ≤3-call composition).

The mathlib-worthy contribution that this declaration *gestures at* is real and namable: **`IsLinearTopology` (and `CompleteSpace`, `IsUltrametricDist`) for the integer ring / valuation subring of a complete nonarchimedean normed field** — a genuine gap (mathlib's `UnitBall.lean` deliberately stops at `Submonoid`; `ValuationSubring` carries no topology). But whether to (a) keep `integerRing` project-local as the convenient anchor, or (b) refactor onto mathlib's `ValuationSubring` and upstream the missing topological-ring instances *against the existing object*, depends on facts the skill cannot weigh: how much the project relies on the bare-`Subring` defeq (the `Algebra ℤ_[p]` instance `change`s through the carrier), whether the `ℚ_p`-algebra coefficient structure is in-scope for mathlib at all, and the cost the user is willing to pay. That is a BORDERLINE call by construction (generality-vs-duplication-vs-cost), which the verdict doc routes to the user rather than self-resolving on cost.

**Refactor-actionable detail — Numbered questions (≤5):**

1. **Should the coefficient ring be re-based on mathlib's `(NormedField.valuation L).valuationSubring` (or `.integer`)?** The carriers coincide and mathlib's bundled object brings `IsLocalRing`/`ValuationRing`/`IsFractionRing L`/the maximal-ideal API for free. The cost is rewriting 582 uses across 20 files and threading the `NormedField.valuation` bridge. Worth it, or keep `integerRing` as the local anchor?

2. **Is the missing instance bundle the real upstream target?** Specifically: would you like `/develop` or a mathlib PR for **`IsLinearTopology`, `CompleteSpace`, and `IsUltrametricDist` instances on `(NormedField.valuation L).valuationSubring`** (i.e. the integer ring of a *complete nonarchimedean normed field*)? That is the genuinely-novel, namable gap (mathlib's `UnitBall.lean` stops at `Submonoid`; `ValuationSubring` carries no topology). If yes, the verdict on *those instances* would be YES-add-as-is; `integerRing` itself becomes a `def`-alias to delete.

3. **Is the `Algebra ℤ_[p] (integerRing L)` structure (and the `ℚ_[p]`-algebra hypothesis) in-scope for mathlib?** It is the coefficient-of-Iwasawa-algebra structure specific to this development. If it is project-specific, then `integerRing` is intentionally a *local* enrichment of a mathlib object and should stay local — pushing the verdict to "keep, do not PR the def".

4. **Does any downstream proof depend on `integerRing L` being a bare `Subring` with the literal carrier `{x | ‖x‖ ≤ 1}` (rather than a `ValuationSubring` whose membership goes through `‖x‖₊ ≤ 1`)?** The `Algebra ℤ_[p]` instance and several `change`/`simpa [integerRing]` proofs in `Coefficients.lean` rely on the carrier defeq; re-basing onto `valuationSubring` must preserve or replace those. Acceptable to adjust them?

**Next action:** user answers 1–4; then re-run `/mathlibable PadicLFunctions.integerRing` to resolve. Likely outcomes:
  - **(Q1 no, Q2 yes, Q3 project-specific)** → keep `integerRing` local; extract the topological-ring instances as a mathlib PR *against `ValuationSubring`* (`YES-add-as-is` for the instances, not the def).
  - **(Q1 yes)** → `NO-mathlib-has-it` for the def: replace `integerRing L` with `(NormedField.valuation L).valuationSubring` (or a thin `abbrev`) at the 582 sites, and contribute the missing instances upstream.
  - **(Q3 in-scope, Q2 yes)** → larger mathlib contribution: the integer ring of a complete nonarchimedean normed `ℚ_p`-algebra with its full analytic API — still BORDERLINE on naming/placement.

---

## Next step

User answers the four numbered questions above (Q1: re-base on `valuationSubring`? Q2: upstream the topological-ring instances on the valuation integer ring? Q3: is the `Algebra ℤ_[p]` structure mathlib-scope? Q4: carrier-defeq dependence?), then re-run `/mathlibable PadicLFunctions.integerRing` to resolve to a concrete YES/NO. The most actionable upstreaming target identified is **`IsLinearTopology`/`CompleteSpace`/`IsUltrametricDist` instances on `(NormedField.valuation L).valuationSubring`** — a real mathlib gap — with `integerRing` itself most likely refactored onto, or aliased to, mathlib's existing `Valuation.integer` / `valuationSubring`.
