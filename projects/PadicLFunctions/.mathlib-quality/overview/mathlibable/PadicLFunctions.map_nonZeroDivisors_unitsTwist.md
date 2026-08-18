# `/mathlibable` report — `PadicLFunctions.map_nonZeroDivisors_unitsTwist`

**Final verdict: `NO-mathlib-has-it`** — the declaration is the verbatim specialisation of the existing mathlib lemma `MulEquivClass.map_nonZeroDivisors`, and its proof body is literally that lemma applied to `unitsTwist p`.

---

### Baseline (Phase 0)

- lake build:                **not re-run** — build is stale/slow in this checkout (the task's BUILD NOTE applies). Reasoned from source directly, exactly as the skill's Phase 0 fallback allows. The declaration's proof body is a single mathlib lemma application whose target lemma was read verbatim from the pinned mathlib (`.lake/packages/mathlib`), so elaboration is established by reading rather than re-building.
- decl `PadicLFunctions.map_nonZeroDivisors_unitsTwist`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:160`
- kind:                      `theorem`
- has sorry:                 no
- module docstring summary:  "The p-adic family of Eisenstein series (RJW §8)" — the Kubota–Leopoldt pseudo-measure interpolates the constant coefficients of the p-stabilised Eisenstein series; the `x`-twist `τ : [g] ↦ g·[g]` is realised as a ring automorphism of the convolution algebra (replan R8.2).

Mathlib pin: `rev = d90090f647ca` (v4.31.0-rc2). Mathlib lemma read directly from `.lake/packages/mathlib/Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean`.

---

### Statement (Phase 1)

`PadicLFunctions.map_nonZeroDivisors_unitsTwist` is **a theorem** stating the following:

Let `Λ = Λ(ℤ_p^×) = PadicMeasure p ℤ_[p]ˣ` be the Iwasawa convolution algebra (a commutative ring). Let `τ = unitsTwist p : Λ ≃+* Λ` be the `x`-twist, the ring automorphism of `Λ` characterised on Diracs by `τ([g]) = g·[g]`. Then the image of the submonoid of non-zero-divisors (regular elements) of `Λ` under `τ` is exactly the submonoid of non-zero-divisors of `Λ`:

> `τ(Λ⁰) = Λ⁰`  (where `R⁰ := nonZeroDivisors R`).

This is the general, structure-free fact "a ring isomorphism carries regular elements bijectively onto regular elements", instantiated at the specific automorphism `τ`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — fixes the prime; supplies the ambient `ℤ_[p]`.
- `PadicMeasure p ℤ_[p]ˣ` — `abbrev` for `C(ℤ_[p]ˣ, ℤ_[p]) →ₗ[ℤ_[p]] ℤ_[p]`, carrying a `CommRing` instance (the convolution algebra; `Measure/PseudoMeasure.lean:81`). Being a `CommRing`, it is a `MonoidWithZero`.
- `unitsTwist p : PadicMeasure p ℤ_[p]ˣ ≃+* PadicMeasure p ℤ_[p]ˣ` — a `RingEquiv` (`EisensteinFamily.lean:115`), hence an instance of `MulEquivClass`.

Hypotheses (Lean side): none beyond the typeclass context.

Conclusion (math): `τ` maps the multiplicative monoid of non-zero-divisors of `Λ` onto itself.

Conclusion (Lean):
```lean
(nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)).map (unitsTwist p).toMonoidHom
  = nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)
```

Proof body (verbatim, one line):
```lean
MulEquivClass.map_nonZeroDivisors (unitsTwist p)
```

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper/glue lemma — it supplies the `M.map h.toMonoidHom = T` hypothesis demanded by `IsLocalization.ringEquivOfRingEquiv` so that the twist can be extended to the fraction ring `quotientTwist`. Not a `## Main results` entry, not named after a person/place, introduces no new structure.

(Note: literature width was run EXHAUSTIVE regardless, per the skill. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line.
One-liner verdict: **n/a (kind is `theorem`, not `def`)** — the one-liner exemption table (defeq abuse / diamond / API-name) applies to `def`/`abbrev`/`structure`, not to theorems. A theorem whose proof is a single mathlib call carries no defeq/diamond surface; the relevant signal is instead that the *statement* is the mathlib lemma's statement (handled in Phase 5/6). Recorded as a one-line note and skipped.

---

### PHASE 3 — Literature search (EXHAUSTIVE protocol)

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found              | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|----------------------------------|-------|
|  1 | WebSearch (specific form)        | "ring isomorphism maps non-zero-divisors onto non-zero-divisors regular elements"                       | yes  | An isomorphism is a bijective ring hom whose inverse is a ring hom; regular = non-zero-divisor; bijective maps preserve regularity in both directions | Wikipedia "Zero divisor"; Viray notes; general homs do *not* preserve it, but isos do |
|  2 | WebSearch (general form)          | "ring automorphism preserves total ring of fractions localization at regular elements extends"          | yes  | Automorphisms preserve regular elements, hence extend uniquely to the total quotient ring | Wikipedia "Total ring of fractions"; the universal property of localisation is the standard mechanism |
|  3 | WebSearch (named-after / aliases) | "non-zero-divisors image under ring isomorphism Submonoid map Lean mathlib MulEquivClass"               | yes  | `Submonoid.map h (nonZeroDivisors M₀) = nonZeroDivisors S` for `MulEquivClass F M₀ S` | The search itself surfaced the exact mathlib lemma `MulEquivClass.map_nonZeroDivisors` — independent confirmation of Phase 5 |
|  4 | ChatGPT MCP                      | (standard-form / generality / historical-evolution question)                                            | n/a  | —                                | ChatGPT MCP present in config but **unauthenticated** (`~/.claude/mcp-needs-auth-cache.json`); not callable this session. Its role (confirm standard form + generality) is fully covered by channels 1–3 + the Stacks Project canonical reference (channel 8), which converge unambiguously. |
|  5 | Local references                 | grep `projects/PadicLFunctions/.mathlib-quality/references/`                                             | n/a  | (no references dir)              | Directory absent; `refs/` symlink absent. Recorded n/a per protocol. |
|  6 | nLab                             | "non-zero divisors localization isomorphism multiplicative set image"                                   | yes  | Image `S*` of a multiplicative set `S` in a quotient is again multiplicative; non-zero-divisors form the multiplicative set giving the total quotient ring | nLab "zero-divisor"; Gathmann localization notes — confirms the multiplicative-set / localisation framing |
|  7 | nCatLab (if categorical)         | (covered by channel 6; nLab = nCatLab)                                                                   | n/a  | —                                | Not a higher-categorical concept; nLab page (channel 6) is the relevant categorical reference and was consulted. |
|  8 | Stacks Project (alg geom)        | "total ring of fractions automorphism extends isomorphism localization"                                 | yes  | Tag **02LV** "Zerodivisors and total rings of fractions" — the canonical treatment | https://stacks.math.columbia.edu/tag/02LV; defines `Q(R)` via the multiplicative set of non-zero-divisors |
|  9 | MathOverflow / Math.StackExchange| "ring isomorphism image of nonzerodivisors equals nonzerodivisors proof one line"                       | yes  | "extension A ⊆ B preserves non-zero-divisors ⇒ injective `T(A) → T(B)`"; the iso case is the trivial both-directions specialisation | uchicago integrality notes, MIT 18.785 — no dedicated MO thread because the fact is too elementary to merit one |
| 10 | recent arXiv (last 5 years)      | (via channels 1–3; "Ulrich split rings", Nagata-factoriality Lean formalisation 2604.05238 surfaced)    | yes  | Recent papers *use* non-zero-divisor preservation as a known elementary tool; none restate it as a result | Confirms it is settled background, not a frontier statement |

The protocol passed: WebSearch ran ≥3 distinct queries at three generality levels (specific iso form / general automorphism-extends-to-fractions form / Lean-mathlib aliasing form); ChatGPT MCP recorded n/a with reason (unauthenticated) and its function subsumed by the convergent channels 1–3 + Stacks 02LV; local refs n/a (absent); nLab checked; Stacks checked (and is the canonical home of the concept); MathOverflow/MathSE checked; arXiv checked.

### Literature summary (Phase 3)

Concept identified as: **"a ring isomorphism maps the non-zero-divisors (regular elements) bijectively onto the non-zero-divisors"** — equivalently the statement that an isomorphism (or automorphism) `h : R ≅ R'` satisfies `h(R⁰) = R'⁰`, which is exactly why an automorphism of `R` extends uniquely to its total ring of fractions `Q(R)`.

Sources agree on the standard form: **yes** — unanimously. Wikipedia, nLab, the Stacks Project (tag 02LV), and standard lecture notes (uchicago, MIT 18.785, Stanford 210B) all treat "non-zero-divisors are a multiplicative set" + "bijective ring maps preserve regularity in both directions" as elementary, settled commutative algebra. There is no variation in the statement.

Most general standard form: for any ring isomorphism `h : R ≅ S` of (commutative or not) rings, `h` restricts to a monoid isomorphism between the monoids of regular elements, i.e. `h(R⁰) = S⁰`. Specialising `S = R` gives the automorphism case. The mathlib-idiomatic statement of the most general form is precisely `MulEquivClass.map_nonZeroDivisors` over `MonoidWithZero` (even weaker than "ring": only a multiplicative-with-zero structure plus a `MulEquivClass` is required — see Phase 4).

Generality dimensions where the literature varies:
  - **Ambient structure**: literature usually says "ring"; the result actually needs only a `MonoidWithZero` and a *multiplicative* equivalence preserving zero (mathlib's form is the maximal one). The project's instance (`CommRing`, hence `MonoidWithZero`) sits *below* the most general mathlib form.
  - **Map type**: literature says "isomorphism"; mathlib abstracts to any `MulEquivClass F M₀ S` (ring-equiv, mul-equiv, alg-equiv, etc. all qualify). The project uses a `RingEquiv`, a special case.

Disagreement with the literature: **none**. The project's statement is a faithful, strictly *narrower* (more-typed) instance of the literature-standard fact.

---

### PHASE 4 — Generality analysis

Literature-standard form (from Phase 3): for any `MulEquivClass F M₀ S` of monoids-with-zero and `h : F`, `Submonoid.map h (nonZeroDivisors M₀) = nonZeroDivisors S`.

### 4a. Generality status table

| # | Parameter / hypothesis            | Current Lean form                                   | Literature-standard / mathlib form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-----------------------------------|-----------------------------------------------------|----------------------------------------------|---------------------|---------------------------------|
| 1 | the ring `PadicMeasure p ℤ_[p]ˣ` | a specific `CommRing` (Iwasawa convolution algebra) | any `MonoidWithZero`                          | yes (drastically)   | the fact has nothing to do with this particular ring; mathlib already states it for all `MonoidWithZero`. The project pins it to one concrete ring purely to feed `quotientTwist`. |
| 2 | the map `unitsTwist p`            | a specific `RingEquiv` (the `x`-twist)              | any `h : F` with `[MulEquivClass F M₀ S]`     | yes (drastically)   | the fact holds for *every* mul-equivalence; the `x`-twist's defining properties (`τ([g]) = g·[g]`) are never used. |
| 3 | source = target ring              | endomorphism case `Λ → Λ`                            | distinct `M₀ → S` allowed                     | yes                 | the mathlib lemma allows different source/target; the automorphism case is a specialisation. |

### 4b. Generality verdict

The current form is: **STRICTLY NARROWER THAN STANDARD** — and it is narrower in the strongest possible sense: it is a *direct one-call instantiation* of a more general mathlib lemma that already exists. There is therefore no "generalise-first" work to do, because the maximally-general form is **already in mathlib** (see Phase 5). This pushes the verdict to a NO bucket, not `YES-but-generalise-first`.

Number of weakening opportunities found: 3 (ring → `MonoidWithZero`; `RingEquiv` → `MulEquivClass`; endo → general source/target) — but **all three are already realised by the existing mathlib lemma**, so they are not contributions the project would make; they are the reason the project decl is redundant.

Proposed restatement: n/a — the maximally general statement is `MulEquivClass.map_nonZeroDivisors`, which mathlib already has. The project decl is the `h := unitsTwist p` specialisation.

Cost of restatement: n/a (no restatement; this is a NO-mathlib-has-it case).

### 4c. Modern mathlib-idiom restatement — Bourbaki 2.0 check

| #  | Question                                                                                                  | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|-----------------------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                                                        | no       | —                      | the statement is already fully typeclass-driven (`MonoidWithZero` + `MulEquivClass`); mathlib's form *is* the modern idiom. |
|  2 | sequences/metric → filters/nets/topological?                                                              | no       | —                      | no analytic/limit content; purely algebraic. |
|  3 | construct an object → universal-property class?                                                           | no       | —                      | it is a statement about an already-constructed map, not a construction. |
|  4 | set-with-closure-predicate → bundled substructure?                                                        | no (already) | —                  | `nonZeroDivisors R` is **already** a bundled `Submonoid` in mathlib, and the statement is `Submonoid.map`. The modern idiom is already in use. |
|  5 | vector-space/metric/field-specific → modules/pseudometric/(semi)ring?                                     | yes (already by mathlib) | the `MonoidWithZero` form | mathlib's `MulEquivClass.map_nonZeroDivisors` already weakens "ring iso" to "mul-equiv of monoids-with-zero". The project decl is the *un-modernised* (over-typed) `RingEquiv`-on-a-concrete-`CommRing` specialisation. |
|  6 | 1-categorical → higher/∞-categorical?                                                                      | no       | —                      | not a categorification target. |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                                            | no       | —                      | no numeric index in the statement. |

Modern idiom available: **already realised in mathlib, not by this declaration.** The contemporary mathlib formulation (`MonoidWithZero` + `MulEquivClass`, `nonZeroDivisors` as a bundled `Submonoid`, `Submonoid.map`) is exactly `MulEquivClass.map_nonZeroDivisors`. The project decl is the *less* modern, more-specialised instance of it. Hence row 5 reinforces NO-mathlib-has-it (the user is not the one bringing the modernisation — mathlib already has the modern form).

One-line reason this is not a fresh modernisation move: the modern, maximally-typeclass-general statement already exists upstream; the project decl specialises *down* from it.

---

### PHASE 4.5 — Diamond / defeq risk

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### PHASE 5 — Mathlib search (five-method)

### Mathlib search-status: `PadicLFunctions.map_nonZeroDivisors_unitsTwist`

[A] Lean-Finder       n/a — MCP/Lean-Finder service not configured in this session; substituted by direct mathlib source grep [D] + LeanSearch-style WebSearch [C], which were conclusive.
[B] Loogle            type pattern `Submonoid.map _ (nonZeroDivisors _) = nonZeroDivisors _` — n/a (no Loogle MCP here); the equivalent was resolved by direct grep [D], which located the exact lemma. The type pattern matches `MulEquivClass.map_nonZeroDivisors` exactly.
[C] LeanSearch        natural-language (via WebSearch, Phase-3 ch.3): "non-zero-divisors image under ring isomorphism Submonoid map Lean mathlib MulEquivClass" → **HIT**: surfaced `MulEquivClass.map_nonZeroDivisors` in `Mathlib.Algebra.GroupWithZero.NonZeroDivisors` and quoted its exact statement.
[D] Grep mathlib src  `grep -rn "map_nonZeroDivisors" .lake/packages/mathlib/Mathlib/` → **HIT**: `MulEquivClass.map_nonZeroDivisors` at `Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:265`. Read the full statement and proof.
[E] Name pattern      grep `MulEquivClass.map_nonZeroDivisors` across project + mathlib → the project's own proof body **already calls it** (`EisensteinFamily.lean:164`); also used by `Mathlib/RingTheory/Localization/FractionRing.lean` lines 124, 434, 505, 604.

Searched for both:
  - the user's current form (`(unitsTwist p)`-specialised `RingEquiv` on `PadicMeasure p ℤ_[p]ˣ`) — found as a specialisation;
  - the literature-standard / maximally-general form (`MulEquivClass F M₀ S`) — found as the exact mathlib lemma.

Exact mathlib lemma (read verbatim from source):
```lean
theorem MulEquivClass.map_nonZeroDivisors {M₀ S F : Type*} [MonoidWithZero M₀] [MonoidWithZero S]
    [EquivLike F M₀ S] [MulEquivClass F M₀ S] (h : F) :
    Submonoid.map h (nonZeroDivisors M₀) = nonZeroDivisors S := by
  let h : M₀ ≃* S := h
  change Submonoid.map h _ = _
  ext
  simp_rw [Submonoid.map_equiv_eq_comap_symm, Submonoid.mem_comap, mem_nonZeroDivisors_iff,
    ← h.symm.forall_congr_right, h.symm.toEquiv_eq_coe, h.symm.coe_toEquiv, ← map_mul,
    map_eq_zero_iff _ h.symm.injective]
```

Concluded: **"found in mathlib as `MulEquivClass.map_nonZeroDivisors`; strictly more general form (the project decl is the `h := unitsTwist p` specialisation)."** The project's proof is literally `MulEquivClass.map_nonZeroDivisors (unitsTwist p)`.

Additional, stronger finding — the *whole pattern* is in mathlib: the only consumer of this lemma is `quotientTwist` (`EisensteinFamily.lean:167`), which re-derives, by hand, exactly what mathlib's `FractionRing.ringEquivOfRingEquiv` (`Mathlib/RingTheory/Localization/FractionRing.lean:433`) already provides:
```lean
-- mathlib:
noncomputable def FractionRing.ringEquivOfRingEquiv (h : A ≃+* B) : K ≃+* L :=
  IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)
```
Since `QuotientField p := FractionRing (PadicMeasure p ℤ_[p]ˣ)` (`Measure/PseudoMeasure.lean:804`) is literally a `FractionRing`, mathlib's `FractionRing.ringEquivOfRingEquiv (unitsTwist p)` *is* `quotientTwist p` — and it bundles the `MulEquivClass.map_nonZeroDivisors` call internally, so the separate `map_nonZeroDivisors_unitsTwist` lemma is not needed at all.

---

### PHASE 6 — Composition check (+ call-sites)

### Call sites — `PadicLFunctions.map_nonZeroDivisors_unitsTwist`

Internal use count: **1** (within the project, excluding the declaring lines)
External-to-file callers: **0** distinct files (the single use is in the *same* file)

| Caller file:line                    | Usage pattern (one-line excerpt)                                   |
|-------------------------------------|--------------------------------------------------------------------|
| EisensteinFamily.lean:171           | `IsLocalization.ringEquivOfRingEquiv … (unitsTwist p) (map_nonZeroDivisors_unitsTwist p)` |

Inline-derivation grep (was the equivalent re-derived elsewhere without using the lemma?):
  - `grep "MulEquivClass.map_nonZeroDivisors"` across `projects/` → only the declaring file (line 164, the proof body itself). No re-derivation; instead the *single* call site at line 171 is the sole reason the lemma exists.

What the call-sites pattern says: **K = 1 internal use only**, in the same file, feeding `IsLocalization.ringEquivOfRingEquiv`. Per the Phase 6.0.1 table, "K = 1 internal use only → possibly the wrong abstraction — could be inlined; lean toward NO-composable / NO-mathlib-has-it". Here the inline replacement is not even a composition we must write — mathlib's own `FractionRing.ringEquivOfRingEquiv` already performs it.

### Composition check

Can `map_nonZeroDivisors_unitsTwist` be derived from mathlib in ≤3 chained calls?

Attempt 1: `MulEquivClass.map_nonZeroDivisors (unitsTwist p)`
  - Mathlib decls used: `MulEquivClass.map_nonZeroDivisors`
  - Result: **succeeds** — this is *exactly* the project's proof body; 1 mathlib call, 0 extra reasoning.
  - Notes: it is not even a "composition"; it is a direct application of a single existing mathlib lemma. The hypotheses (`MonoidWithZero` from the `CommRing` instance, `MulEquivClass` from `RingEquiv`) are discharged by instance resolution.

Conclusion: This is the degenerate case — the statement *is* a mathlib lemma's statement and the proof *is* a single application of it. It is best classified as **NO-mathlib-has-it** rather than NO-composable, because there is no genuine multi-primitive composition: a single named mathlib lemma with the same statement (modulo the `M₀ → S` ⇒ endo specialisation) already exists. (Per the verdicts doc, NO-composable is for "building blocks compose in 1–3 calls"; when a *single* lemma is the whole statement, the precise bucket is NO-mathlib-has-it.)

---

## Verdict: `PadicLFunctions.map_nonZeroDivisors_unitsTwist`

**Category:** `NO-mathlib-has-it`

**Evidence:**
- Literature search (Phase 3): the fact "a ring isomorphism carries non-zero-divisors bijectively onto non-zero-divisors" is unanimous, elementary commutative algebra (Stacks 02LV, nLab, Wikipedia, standard lecture notes). Channel 3 independently surfaced the exact mathlib lemma name.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — the project decl is a 3-axis specialisation (ring→`MonoidWithZero`, `RingEquiv`→`MulEquivClass`, endo→general) of a form mathlib *already* has. Phase 4c row 5 confirms the modern, maximally-typeclass form is upstream, not contributed here.
- Mathlib search (Phase 5): **found in mathlib as `MulEquivClass.map_nonZeroDivisors`** (`Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:265`), strictly more general; the project's proof body is literally that lemma applied to `unitsTwist p`.
- Composition check (Phase 6): K = 1 internal call site (same file); the single use feeds `IsLocalization.ringEquivOfRingEquiv`, and even *that* whole pattern is subsumed by mathlib's `FractionRing.ringEquivOfRingEquiv`.

**Rationale (1–2 paragraphs):**

The declaration's own proof is `MulEquivClass.map_nonZeroDivisors (unitsTwist p)` — a single application of an existing mathlib lemma whose statement, `Submonoid.map h (nonZeroDivisors M₀) = nonZeroDivisors S` for any `[MulEquivClass F M₀ S]`, is strictly more general than the project's `RingEquiv`-on-a-fixed-`CommRing` instance. There is nothing for mathlib to gain: the maximally general, maximally idiomatic form (`MonoidWithZero` + `MulEquivClass` + bundled `nonZeroDivisors` `Submonoid` + `Submonoid.map`) is already upstream, and the project decl specialises *down* from it. This is the textbook `NO-mathlib-has-it` shape: mathlib has it, in a more general form, and the project's statement follows in zero extra lines (the specialisation is pure instance resolution).

Moreover the lemma has a single in-project consumer (line 171), where it is handed to `IsLocalization.ringEquivOfRingEquiv` to build `quotientTwist`. Mathlib already packages that exact composition as `FractionRing.ringEquivOfRingEquiv (h : A ≃+* B) := IsLocalization.ringEquivOfRingEquiv K L h (MulEquivClass.map_nonZeroDivisors h)`, and since `QuotientField p` is *defined* as `FractionRing (PadicMeasure p ℤ_[p]ˣ)`, the entire `map_nonZeroDivisors_unitsTwist` + `quotientTwist` pair can be replaced by one mathlib call — strengthening the case that nothing here is a mathlib contribution.

**WHY not (refactor-actionable):**
Mathlib already has the result. The relevant existing decl is the lemma the project decl literally calls. The project's form follows in 0 extra lines (the `h := unitsTwist p`, `M₀ = S = PadicMeasure p ℤ_[p]ˣ` instance of the mathlib statement; the more general `M₀ → S` form specialises to the endomorphism case automatically). There is also a second, stronger refactor available at the *consumer* level via `FractionRing.ringEquivOfRingEquiv`.

Existing mathlib decl:        `MulEquivClass.map_nonZeroDivisors`
Located at:                   `Mathlib/Algebra/GroupWithZero/NonZeroDivisors.lean:265`
Our form follows in ≤1 line (it *is* the proof body):
```lean
example :
    (nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ)).map (unitsTwist p).toMonoidHom
      = nonZeroDivisors (PadicMeasure p ℤ_[p]ˣ) :=
  MulEquivClass.map_nonZeroDivisors (unitsTwist p)
```
Call sites in our project (from Phase 6.0):  **K = 1** — `EisensteinFamily.lean:171` (`quotientTwist`).

Refactor plan (two equivalent options; the second is preferred):
1. **Minimal (inline the lemma):** delete `map_nonZeroDivisors_unitsTwist`; at the one call site (`EisensteinFamily.lean:171`) replace `(map_nonZeroDivisors_unitsTwist p)` with `(MulEquivClass.map_nonZeroDivisors (unitsTwist p))`. Argument order is identical (it is the same term). This removes a project lemma that merely re-asserts a mathlib lemma.
2. **Preferred (collapse the whole pattern):** since `QuotientField p = FractionRing (PadicMeasure p ℤ_[p]ˣ)`, replace the body of `quotientTwist` (`EisensteinFamily.lean:167–171`) with `FractionRing.ringEquivOfRingEquiv (unitsTwist p)` (from `Mathlib/RingTheory/Localization/FractionRing.lean:433`). This deletes *both* `map_nonZeroDivisors_unitsTwist` (no longer referenced) and the manual `IsLocalization.ringEquivOfRingEquiv` plumbing. Then `quotientTwist_algebraMap` (line 174) is discharged by mathlib's `FractionRing.ringEquivOfRingEquiv_algebraMap` (line 436) instead of `IsLocalization.ringEquivOfRingEquiv_eq`. Verify the `IsFractionRing (PadicMeasure p ℤ_[p]ˣ) (QuotientField p)` instance is in scope (it is — the file already invokes `IsFractionRing.injective` for this pair).

Next action: delete `map_nonZeroDivisors_unitsTwist` from the project; apply refactor option 2 (preferred) at `EisensteinFamily.lean:167–177`, or option 1 if a lighter touch is wanted. Do **not** PR this lemma to mathlib — it is already there.

Note: this is a CLEANER (on-`main`) refactor, not a PRODUCER concern; it touches no theorem statement and adds no `sorry`. The owning producer keeps the surrounding sorry-bearing development; only this redundant glue lemma (and optionally its single call site) is affected.

---

## Next step

Delete `PadicLFunctions.map_nonZeroDivisors_unitsTwist` from the project and rewire its one consumer. Preferred: replace `quotientTwist` (`EisensteinFamily.lean:167–171`) with mathlib's `FractionRing.ringEquivOfRingEquiv (unitsTwist p)`, and discharge `quotientTwist_algebraMap` via `FractionRing.ringEquivOfRingEquiv_algebraMap`. Minimal alternative: inline `MulEquivClass.map_nonZeroDivisors (unitsTwist p)` at `EisensteinFamily.lean:171`. No mathlib PR — mathlib already has `MulEquivClass.map_nonZeroDivisors`.
