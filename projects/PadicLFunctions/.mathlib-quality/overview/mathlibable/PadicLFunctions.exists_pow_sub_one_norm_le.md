# `/mathlibable` report — `PadicLFunctions.exists_pow_sub_one_norm_le`

Mode: A (single declaration, full 10-phase workflow with the exhaustive 9-channel literature search).

**Final verdict: `BORDERLINE-needs-human`.** The mathematics is a genuine, classical fact (the "existence" half of the Teichmüller construction: a norm-one algebraic integer has a power landing in `1 + 𝔪`, here via pigeonhole in the finite ring `ℤ[z]/p`). Mathlib does **not** have it (its Teichmüller machinery is Witt-vector/perfectoid `Perfection.teichmuller`; the `norm_pow_sub_one_*` lemmas are about cyclotomic field norms). The proof is a real multi-step argument, **not** a ≤3-call composition. But the user's form is a *specialised, deliberately weakened* version of the literature-standard statement — it yields a non-explicit exponent `m` and only the bound `‖z^m − 1‖ ≤ p⁻¹`, where the standard form gives the explicit exponent `q−1` (q = residue-field size) and the full convergence `z^{p^n} → ω(z)` to a root of unity. The decision of *which* form mathlib should host — this project-shaped pigeonhole lemma, or the proper Teichmüller statement it is a fragment of — is a taste/scope judgment the skill cannot make alone. Hence BORDERLINE, with the questions spelled out in Phase 7.

---

### Baseline (Phase 0)
- lake build:               **build not re-run; reasoned from source** (per task BUILD NOTE — `lake build` may be stale/slow here). The mathlib clone is present at `.lake/packages/mathlib/Mathlib` (pin `d90090f`, toolchain `leanprover/lean4:v4.32.0-rc1`) and was grepped directly; the project file `ExtLog.lean` and its dependencies were read directly.
- decl `PadicLFunctions.exists_pow_sub_one_norm_le`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:243`
- kind:                      theorem
- has sorry:                 no (the entire file is `sorry`-free)
- module docstring summary:  the extended (Iwasawa-branch) `p`-adic logarithm `extLog` (RJW §6, decomposition W6a); this file extends `padicLog` to rational-valuation elements `x` with `x^m = p^k·y` and builds the domain-membership engine `extLogDomain_of_integral_norm_one`, whose first step is exactly this pigeonhole lemma.

---

### Statement (Phase 1)

`exists_pow_sub_one_norm_le` is a theorem stating the following:

Let `L` be a complete ultrametric normed field that is a normed `ℚ_[p]`-algebra, and let `z ∈ L` be **integral over `ℤ`** with **norm exactly `1`**. Then there is a positive integer `m` such that `z^m` is within distance `p⁻¹` of `1`, i.e. `‖z^m − 1‖ ≤ p⁻¹`.

Mathematically: *a norm-one algebraic integer in a complete ultrametric field has a positive power lying in the closed ball `1 + 𝔪_{p⁻¹}` around `1`.* This is the **existence half of the Teichmüller construction** specialised to a single algebraic-integer unit: because `z` is integral, the order `R = ℤ[z]` is `ℤ`-module-finite, so its residue ring `R/(p)` is finite; the powers `z^n` must therefore repeat modulo `(p)`, giving `z^i ≡ z^j (mod p)` for some `i < j`; cancelling the norm-one factor `z^i` yields `z^{j−i} ≡ 1 (mod p)`, and `‖p‖ = p⁻¹` upgrades the congruence to the analytic bound. The exponent `m = j − i` is **not** explicit (it is whatever the pigeonhole produces).

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the rational prime; supplies `p ≠ 0` and `‖(p:L)‖ = p⁻¹`.
- `L : Type*`, `[NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L] [CompleteSpace L]` — the ambient field. **`[CompleteSpace L]` is `omit`-ed for this theorem** (line 238); the proof uses completeness nowhere. `IsUltrametricDist` and `NormedAlgebra ℚ_[p]` *are* used: the former bounds integers by `1` (via `norm_le_one_of_mem_adjoin_int`), the latter pins `‖(p:L)‖ = p⁻¹` (via `norm_natCast_p`).
- `z : L` — the unit being analysed.

Hypotheses (Lean side):
- `hz : IsIntegral ℤ z` — makes `ℤ[z]` a finite `ℤ`-module, hence `ℤ[z]/(p)` finite (this is the engine, the dependency `finite_adjoin_int_quotient`).
- `hz1 : ‖z‖ = 1` — `z` is a unit of norm 1; used to (a) cancel `‖z^i‖ = 1` and (b) bound the conjured `s` by `‖s‖ ≤ 1`.

Conclusion (math): `∃ m > 0` with `z^m` in the closed `p⁻¹`-ball about `1`.

Conclusion (Lean): `∃ m : ℕ, 0 < m ∧ ‖z ^ m - 1‖ ≤ (p : ℝ)⁻¹`.

**Proof body (what it does — a genuine multi-step argument):**
1. Set `R = Algebra.adjoin ℤ {z}`, `I = Ideal.span {(p:R)}`; obtain `Finite (R ⧸ I)` from the dependency `finite_adjoin_int_quotient p hz`.
2. Pigeonhole `f : ℕ → R ⧸ I`, `n ↦ mk (⟨z,_⟩^n)`, via `Finite.exists_ne_map_eq_of_infinite` → distinct `i ≠ j` with `f i = f j`.
3. `wlog i < j`; set `m = j − i > 0`.
4. From `f i = f j`: `⟨z,_⟩^j − ⟨z,_⟩^i ∈ I` (`Ideal.Quotient.mk_eq_mk_iff_sub_mem`); write it as `p·s` (`Ideal.mem_span_singleton'`).
5. Push to `L`: `z^j − z^i = (p:L)·(s:L)`; then `‖z^j − z^i‖ = ‖p‖·‖s‖ ≤ p⁻¹·1 = p⁻¹`, using `norm_natCast_p` and `norm_le_one_of_mem_adjoin_int` (`‖s‖ ≤ 1`).
6. Factor `z^j − z^i = z^i·(z^{j−i} − 1)` with `‖z^i‖ = 1`, so `‖z^{j−i} − 1‖ ≤ p⁻¹`. ∎

---

### Size classification (Phase 2a)

Verdict: **SMALL** (but a borderline-BIG mathematical fragment).
Reason: it is a helper lemma — the docstring tags it `W6a-a5 (pigeonhole)`, and it is consumed once internally by the domain engine `extLogDomain_of_integral_norm_one`. It is not a `def`/`structure`, not a person/place-named theorem, and not a listed `## Main result` of the project (the main result is `extLog` and its laws). HOWEVER, the *content* is a recognisable named-construction fragment (Teichmüller existence), which is why Phase 3 finds it everywhere — so its mathematical weight exceeds its syntactic "helper" status. (Literature width is EXHAUSTIVE regardless; recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~25 substantive lines (pigeonhole + wlog + ideal manipulation + norm pushforward + factoring).
One-liner verdict: **n/a** — kind is `theorem`, not `def`. The Phase 2b exemption table is skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "p-adic algebraic integer norm one power congruent to 1 mod p Teichmuller pigeonhole finite residue ring" | yes | Teichmüller representative `ω(x) = lim_{n} x^{p^n}`; ℤ_p contains the `(p−1)`-th roots of unity, distinct mod `p`; for `p∤a`, `a^{p^n}` converges | Wikipedia "Teichmüller character"; K. Conrad, Hensel's lemma; U. Chicago REU (Gupta). The "power lands in `1+𝔪`" statement is the classical existence half. |
| 2 | WebSearch (general / ultrametric form) | "unit ultrametric field power close to 1 root of unity Teichmuller representative congruence mod p" | yes | for a complete DVR with **perfect** residue field of char `p`, a unique multiplicative section (Teichmüller); for odd `p`, ℤ_p^× ≅ μ_{p−1} × (1+pℤ_p) | numberanalytics; Wikipedia; wstein.org BSD notes; Browning *Local Fields*. The decomposition unit = root-of-unity × principal-unit is standard. |
| 3 | WebSearch (named-after / finite-residue form) | "complete local field unit residue field finite power lands in 1 plus maximal ideal q-1 root of unity proof" | yes | for a non-archimedean **local** field with residue field `κ ≅ 𝔽_q`, `μ_n(K)` is cyclic of order `gcd(n, q−1)`; `u^{q−1} ≡ 1 (mod 𝔪)` for every unit | Fisher *Local Fields* (Cambridge III); Crew *LCFT*; Tengan; Hsu PAWS 2024. **The textbook hypothesis is a FINITE residue field, with the explicit exponent `q−1`.** |
| 4 | ChatGPT MCP | (intended: "standard form, generality, and historical evolution of: a norm-one algebraic integer in a complete ultrametric field has a power in `1+𝔪`") | **n/a** | — | **ChatGPT MCP server (`chatgpt-math`) failed to connect in this environment** (configured for a Linux path `/home/chris/.claude/mcp-servers/chatgpt-math/server.js`; this is macOS — `claude mcp list` reports it as ✘ Failed to connect, alongside `mathlib-rag` and `lean-lsp`). Compensated by extra WebSearch coverage (rows 1–3, 5–6) and direct mathlib-source reading. The concept is classical and unambiguous, so the substitution is sound — matching the documented house pattern in the sibling report `PadicLFunctions.finite_adjoin_int_quotient.md`. |
| 5 | Local references | grep `projects/PadicLFunctions/.mathlib-quality/references/` | **n/a** | (no references dir) | The directory does not exist; `refs/` (the local-only PDF store) is also absent on this checkout. Recorded as n/a. The docstring's own citation — Washington, *Introduction to Cyclotomic Fields*, §5.1 — was searched directly (rows 1–3, 6) but the PDF is not present to read. |
| 6 | nLab | "Teichmüller lift / Teichmüller representative / Witt vectors" + Wikipedia "Teichmüller character" (fetched, since the nLab page 404'd) | yes (via Wikipedia) | `ω(x) = lim x^{p^n}`, `ω(x)^p = ω(x)`; ℤ_p^× = (finite roots of unity) × (≅ ℤ_p); finite group is cyclic of order `p−1` (odd `p`) | The dedicated nLab URL returned 404; substituted the canonical Wikipedia "Teichmüller character" article (fetched in full). The role of the **finite** residue field is explicit: it sizes the root-of-unity group. |
| 7 | nCatLab (categorical) | — | **n/a** | — | Not a categorical concept: this is a concrete existence/estimate statement about powers of one element in one field; nothing higher-categorical to consult. (Mathlib's categorical Teichmüller content lives in Witt-vector/perfectoid land — checked in Phase 5, different setting.) |
| 8 | Stacks Project | tag 0AKD (Teichmüller/algebraization) checked | **n/a** | — | Tag 0AKD is obsolete ("unused after a rearrangement"). Stacks treats Witt vectors / Cohen rings abstractly but has no clean "norm-one element has a power near 1" lemma; this is not naturally an algebraic-geometry topic. Recorded n/a after looking. |
| 9 | MathOverflow / Math.StackExchange | "pigeonhole finite ring powers of element eventually congruent algebraic integer mod prime exists exponent" | yes | finite monoid/group ⇒ by pigeonhole `∃ i>j, a^i = a^j`, hence `a^{i−j}` is the identity (resp. ≡ 1) — the generic eventual-periodicity argument | MIT PRIMES notes; TCD *Rings* notes. This is exactly the **proof technique** (the analytic bound `‖p‖=p⁻¹` is the project's own packaging on top). |
| 10 | recent arXiv (last 5 years) | "Teichmüller / finite residue / units of local rings 2020–2025" (surfaced in rows 1–3) | yes | the Teichmüller lift and unit-group decomposition are used routinely (e.g. arXiv:2505.12877, 2104.03299) without re-proving the elementary existence step | Confirms classical/folklore status; modern papers cite it, don't reprove it. |

The protocol passed: WebSearch ran ≥3 distinct queries at three generality levels — the specific Teichmüller/pigeonhole form (#1), the general ultrametric/DVR form (#2), and the finite-residue-field named form with explicit `q−1` exponent (#3), plus the proof-technique query (#9) and arXiv currency check (#10). ChatGPT MCP recorded `n/a` with the explicit reason that the server failed to connect (and was compensated). Local references recorded `n/a` (absent). nLab/Wikipedia, nCatLab, Stacks, MathOverflow, arXiv each checked with a result or a one-line `n/a` reason.

### Literature summary (Phase 3)

Concept identified as: **the existence half of the Teichmüller lift** — *a unit (here: a norm-one algebraic integer) in a complete non-archimedean field has a positive power congruent to `1` modulo the maximal ideal*. Equivalently, the elementary fact behind it: *powers of an element in a finite ring are eventually periodic* (pigeonhole), specialised to `ℤ[z]/(p)` and dressed with the analytic bound `‖p‖ = p⁻¹`.

Sources agree on the standard form: **yes, but the standard form is STRONGER and stated under a different (stronger) hypothesis.** The textbook statement (rows 2–3, 6) assumes a **finite residue field** `κ ≅ 𝔽_q` and gives:
  (i) the **explicit** exponent `q − 1`: `u^{q−1} ≡ 1 (mod 𝔪)`;
  (ii) the full **convergence** `u^{p^n} → ω(u)`, a root of unity (the Teichmüller representative);
  (iii) the structural decomposition `O_K^× ≅ μ_{q−1} × (1 + 𝔪)`.

Most general standard form: for a complete DVR / local ring with **perfect** residue field of characteristic `p`, the Teichmüller multiplicative section exists and `u^{p^n}` converges to it; with a **finite** residue field the torsion is `μ_{q−1}` and the explicit congruence `u^{q−1} ∈ 1+𝔪` holds.

Generality dimensions where the literature varies, **and where the Lean form sits**:
  - **Residue-field hypothesis.** Literature: residue field of `L` finite (or at least perfect). Lean: **no hypothesis on `L`'s residue field at all** — instead it imposes `IsIntegral ℤ z`, which makes the *sub*-residue ring `ℤ[z]/(p)` finite. This is an **incomparable** hypothesis: the Lean form applies to `z` even when `L`'s own residue field is infinite, but it only concludes a property of `z`, not of all of `L^×`. *This is the one axis where the Lean form is genuinely more general than the textbook statement.*
  - **Exponent.** Literature: explicit `q − 1`. Lean: a non-explicit, pigeonhole-produced `m` (weaker — loses the canonical exponent).
  - **Conclusion strength.** Literature: convergence to a root of unity ω(z) (`z^{p^n} → ω`). Lean: a single power within `p⁻¹` of `1` (weaker — the existence step only, not the lift).
  - **The constant `p⁻¹`.** Literature works modulo `𝔪` (or `p`). Lean fixes the closed ball of radius `p⁻¹` = `‖p‖`, which is exactly `z^m ≡ 1 (mod p)`. Equivalent to the mod-`p` congruence; the `p⁻¹` packaging is the project's own (it is what the downstream `exists_pPow_pow_inExpBall` consumes).

Disagreement with the literature: **the Lean statement is a weaker, hypothesis-shifted fragment of the standard Teichmüller existence result.** It is not "the same form" — it trades the finite-residue-field hypothesis (on all of `L`) for an integrality hypothesis (on `z`), and correspondingly weakens the conclusion from "explicit `q−1`-power / convergence to ω(z)" to "some power within `p⁻¹` of 1". Both the hypothesis and the conclusion differ from the textbook anchor.

---

### Generality analysis — `PadicLFunctions.exists_pow_sub_one_norm_le`

Literature-standard form (from Phase 3): for a complete non-archimedean field with **finite residue field** `𝔽_q`, every unit `u` satisfies `u^{q−1} ≡ 1 (mod 𝔪)`, and `u^{p^n} → ω(u)` (the Teichmüller lift).

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | residue-field hypothesis | **none on `L`**; instead `hz : IsIntegral ℤ z` (⇒ `ℤ[z]/(p)` finite) | residue field of `L` finite (`κ ≅ 𝔽_q`) | incomparable, not strictly weaker | The Lean hypothesis is genuinely different: it localises finiteness to `ℤ[z]` rather than assuming it for `L`. This is a real, deliberate generalisation away from the "local field" frame — it covers algebraic-integer units in fields with infinite residue field. It cannot be "weakened further" in the naive sense; it is already a clever side-step of the standard hypothesis. |
| 2 | `hz1 : ‖z‖ = 1` | norm exactly 1 (a unit) | unit of `O_K` | NO (essential) | Used twice (cancel `‖z^i‖=1`; bound `‖s‖≤1` via `norm_le_one_of_mem_adjoin_int`, which needs `‖z‖≤1`). The exact `=1` could in principle relax to `≤1` for the `‖s‖` bound, but the `‖z^i‖=1` cancellation in the final factoring needs `=1`. Essential as stated. |
| 3 | `[IsUltrametricDist L]` | ultrametric | non-archimedean (same) | NO | Essential: integers are bounded by 1 only ultrametrically; `norm_le_one_of_mem_adjoin_int` is an ultrametric induction. |
| 4 | `[NormedAlgebra ℚ_[p] L]` | `ℚ_[p]`-algebra | residue char `p` / a `p`-adic field | NO (as stated) | Used to pin `‖(p:L)‖ = p⁻¹` (`norm_natCast_p`). Could conceivably weaken to "any field where `‖p‖ < 1` and the residue char is `p`", but that is a different (mixed-characteristic valuation) framing, not a free weakening. |
| 5 | `[CompleteSpace L]` | complete | complete (needed for the *lift*, not for *this* step) | **yes — already dropped** | `omit`-ed at line 238. Correctly identified by the author as irrelevant to the existence step (completeness is only needed to form ω(z) = lim, which this lemma does not do). |
| 6 | conclusion: `∃ m, ‖z^m−1‖ ≤ p⁻¹` | non-explicit `m`, bound `p⁻¹` | explicit `m = q−1`, plus convergence | the literature form is STRONGER | The Lean conclusion is strictly weaker than the textbook one (no explicit exponent, no convergence). Strengthening to the explicit `q−1` would *require* a finite residue field for `L` (hypothesis #1), which the Lean form deliberately avoids — so the weaker conclusion is the price of the more general hypothesis. The two are linked. |

This is grounded in the literature-standard form Phase 3 identified, not in typeclass-hierarchy walking alone.

### Generality verdict (Phase 4b)

The current form is: **NEITHER cleanly "maximally general" NOR cleanly "strictly narrower"** — it is *hypothesis-shifted*. On the residue-field axis (row 1) it is **more general** than the textbook statement (algebraic-integer units in arbitrary `L`, vs. units in a finite-residue local field). On the conclusion axis (row 6) it is **strictly weaker** (no explicit `q−1` exponent, no convergence to ω(z)). These two facts are coupled: the weaker conclusion is exactly what the more-general hypothesis can buy. There is therefore no single "generalise-first" target that dominates the current form — generalising the *conclusion* (to explicit `q−1` / convergence) would *narrow* the *hypothesis* (force a finite residue field). This tension is the core of the BORDERLINE verdict.

Number of clean weakening opportunities found: **0 that strictly dominate** (the only typeclass that was dead weight — `CompleteSpace` — is already `omit`-ed). The available "moves" are *trades*, not free weakenings.

Proposed restatement: there is **no unambiguous restatement** — the two natural mathlib targets pull in opposite directions:
  (A) the **Teichmüller-existence** form keeping the integrality hypothesis: essentially the current statement, perhaps phrased as `∃ m > 0, z^m ≡ 1 [mod (p:R)]` or membership in a `1+𝔪` set; or
  (B) the proper **finite-residue-field Teichmüller** statement `[Finite (residue field)] → ∃ (ω : root of unity), u^{p^n} → ω` and `u^{q−1} ∈ 1+𝔪`, which is a substantially larger development (and the *real* mathlib-grade target for "Teichmüller for local fields").
The choice between (A) and (B) is the human question.

Cost of restatement: (A) CHEAP (re-spell the current proof). (B) EXPENSIVE (a new Teichmüller-lift development for finite-residue fields — genuinely new API). Per the Bourbaki-2.0 rule, EXPENSIVE does not downgrade a verdict; but here the issue is not cost, it is *which statement is the right one*, which is a taste call.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | "Let X be a foo" preambles → typeclasses/instances? | partially | The finite-residue hypothesis could be a typeclass (`[Finite (LocalRing.ResidueField O)]`) if one took route (B); the current route uses `IsIntegral ℤ z` (already a clean predicate). | A `[Finite residue field]` instance would let the full Teichmüller API (route B) compose with the local-field hierarchy. |
| 2 | sequences/metric → filters/topology? | **yes (for the lift, route B)** | The *convergence* `z^{p^n} → ω(z)` is naturally a `Filter.Tendsto … atTop (𝓝 (ω z))` statement — and indeed the sibling lemma `exists_pPow_pow_inExpBall` already uses `Filter.Tendsto`. But *this* lemma is only the existence step and has no limit. | Route B's lift would be a `Tendsto` statement composing with all of mathlib's limit API. Not applicable to the existence-only fragment. |
| 3 | construct an object → universal-property class? | **yes (route B)** | The Teichmüller lift is canonically a multiplicative section `O^× → μ` / a map characterised by `ω(x) ≡ x` and `ω(x)^q = ω(x)`. Mathlib already has this for the perfection (`Perfection.teichmuller`). | The universal-property/section form (route B) is the mathlib-idiomatic target; the current existence lemma is a sub-step of building it. |
| 4 | set-with-closure-predicate → bundled-substructure type? | no | — | The objects (`Algebra.adjoin`, `Ideal.span`) are already bundled. |
| 5 | field-specific → weaker typeclass (module/(semi)ring)? | no (analytic core is essential) | — | The norm/ultrametric structure is the content; cannot drop to a bare ring. |
| 6 | 1-categorical → higher/∞-categorical? | no | — | Not categorical at this level. |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive group/monoid? | no | — | `m : ℕ` is intrinsic (a multiplicative exponent). |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but it is precisely route (B), a different and larger theorem, not a restatement of this one.** The mathlib-idiomatic object in this area is the Teichmüller *lift/section* as a `Tendsto`-characterised multiplicative map (cf. mathlib's `Perfection.teichmuller`, and the filter-based convergence the project already uses in `exists_pPow_pow_inExpBall`). The current lemma is the **existence sub-step** of that construction, deliberately stripped down for the `extLog`-domain engine. So Phase 4c does **not** convert this into a clean `YES-but-generalise-first` with a drop-in modern restatement; instead it confirms that the *full* modern object is a separate, larger development. Whether mathlib wants this fragment on its own, or only as part of the full lift, is exactly the human question. (Honesty bar: the modernisation here is real and concrete — a `Tendsto`/section formulation of Teichmüller for finite-residue fields would compose with mathlib's limit and unit-group API — but it is a *different theorem*, so it cannot be auto-selected as the generalise-first target for *this* declaration without a scope decision.)

---

### Diamond / defeq risk — `PadicLFunctions.exists_pow_sub_one_norm_le`

**n/a — declaration kind is `theorem`.** Phase 4.5 runs only for `def`/`abbrev`/`structure`/`inductive`/`class`/`instance`; a `Prop`-valued existence theorem introduces no definitional equalities or typeclass-search paths.

### Risk verdict (Phase 4.5)

Overall risk: **n/a** (theorem).

---

### Mathlib search-status: `PadicLFunctions.exists_pow_sub_one_norm_le`

[A] Lean-Finder       "norm-one unit power close to 1 p-adic"; "Teichmuller existence power congruent 1"   → **n/a (server)**: Lean-Finder is a hosted web index, not reachable as a tool here; the offline MCP servers (`mathlib-rag`, `lean-lsp`, `chatgpt-math`) all failed to connect. Compensated by exhaustive grep over the present mathlib clone (method [D]).
[B] Loogle (type)     `‖_ ^ _ - 1‖ ≤ _`, `IsIntegral ℤ _ → ‖_‖ = 1 → ∃ _, _`, `∃ m, _ ∧ ‖_ ^ m - 1‖ ≤ _`   → via grep over the clone: **no lemma** concludes `‖z^m − 1‖ ≤ c` for a conjured `m`. The only `‖_ ^ _ - 1‖`-shaped results are `IsPrimitiveRoot.norm_pow_sub_one_*` (see [D]) — a different concept. No hit.
[C] LeanSearch        "a power of a p-adic unit is close to 1"; "Teichmuller representative existence"; "algebraic integer power congruent to 1 mod p"   → **n/a (server)**: hosted, not reachable. Compensated by [D].
[D] Grep mathlib src  ran over `.lake/packages/mathlib/Mathlib/` (clone present, pin `d90090f`): searched `teichmuller`/`Teichmuller`, `norm_pow_sub`, `exists_pow_eq_one`, `isOfFinOrder`, `‖_^_-1‖`, and the Padics / Valuation / DVR dirs.   → findings below.
[E] Name pattern      `exists_pow`, `_norm_le`, `pow_sub_one`, `teichmuller`   → `IsPrimitiveRoot.norm_pow_sub_one_*` (Cyclotomic; different), `Perfection.teichmuller`, `WittVector.teichmuller` (different setting).

Searched for both:
- the user's current form (`∃ m > 0, ‖z^m − 1‖ ≤ p⁻¹` for an integral norm-one `z`) — **not present.**
- the literature-standard / Teichmüller form (unit `u`, finite residue field, `u^{q−1} ∈ 1+𝔪`, `u^{p^n} → ω`) — **not present as a normed-field statement.**

Findings (by qualified name + path):
- **`Perfection.teichmuller`** — `Mathlib/RingTheory/Teichmuller.lean:~60`. The Teichmüller map `Perfection (R ⧸ I) p →*₀ R` for an `I`-adically complete ring with `CharP (R/I) p`. **Different object** (the multiplicative section in the perfection/Witt-vector setting); it is not the "norm-one element has a power near 1" statement, and its hypotheses (`AdicCompletion`, `Perfection`, `CharP (R/I) p`) are a different frame. Building toward route (B), not this lemma.
- **`WittVector.teichmuller` / `WittVector.TeichmullerSeries` / `RingTheory/Perfectoid/FontaineTheta` / `Untilt`** — `Mathlib/RingTheory/WittVector/…`, `Mathlib/RingTheory/Perfectoid/…`. Teichmüller representatives in Witt-vector / perfectoid theory. Different setting entirely.
- **`IsPrimitiveRoot.norm_pow_sub_one_of_prime_ne_two` / `…_of_prime_pow_ne_two` / `…_eq_prime_pow_of_ne_zero`** — `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean:391,445,505`. These compute the **field norm** `Norm_{K/ℚ}(ζ^s − 1)` for a primitive `p^k`-th root of unity `ζ` in a cyclotomic field — a *number-field norm* (absolute norm / discriminant input), NOT the analytic `‖·‖` of "`z^m` is close to 1". Name-collision only; mathematically unrelated.
- **`Finite.exists_ne_map_eq_of_infinite`** — `Mathlib/Data/Fintype/Pigeonhole.lean:74` (`[Infinite α] [Finite β] (f : α → β) : ∃ x y, x ≠ y ∧ f x = f y`). The pigeonhole engine the proof actually invokes. A general combinatorial primitive, not the target.
- **`Ideal.Quotient.mk_eq_mk_iff_sub_mem`** and **`Ideal.mem_span_singleton'`** — `Mathlib/RingTheory/Ideal/Span.lean` and quotient API. Used in the proof; generic ideal lemmas.

Concluded: **not in mathlib** (all five methods exhausted — [A][C] unreachable but compensated by an exhaustive [D] grep over the present clone, plus [B][E]; searched both the user's form and the literature-standard Teichmüller form). Mathlib's Teichmüller content is the Witt-vector/perfectoid multiplicative section (`Perfection.teichmuller`), which neither states this estimate nor shares its normed-field hypotheses. The `norm_pow_sub_one_*` family is a same-name, different-concept cyclotomic-field-norm result. There is **no** lemma asserting that a norm-one algebraic integer has a power within `p⁻¹` of 1.

---

### Call sites — `PadicLFunctions.exists_pow_sub_one_norm_le`

Internal use count: **K = 1** (within the project, excluding the declaring file's definition line).
External-to-file callers: 0 distinct files (the single use is in the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:448` | `obtain ⟨m, hm, hmle⟩ := exists_pow_sub_one_norm_le p hz hz1` — the first step of `extLogDomain_of_integral_norm_one` (the W6a-a11 domain engine); the produced `m` feeds `exists_pPow_pow_inExpBall p hlt` to land `z^{m·p^j}` in the exponential ball. |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `exists_pow_sub_one_norm_le`?):
- (none) — the pigeonhole `Finite.exists_ne_map_eq_of_infinite` appears only inside this theorem's own body (`ExtLog.lean:252`); no other site rebuilds "a power of `z` is near 1".

What the call-sites pattern tells us: **K = 1, single internal use, no external consumers, no inline re-derivation.** Per the heuristic table this leans toward "possibly the wrong abstraction / could be inlined" (NO-composable) — *if* the body were a short composition. But the body is a genuine ~25-line proof (pigeonhole + ideal pushforward + factoring), so it is NOT inlinable as a ≤3-call composition (Phase 6 confirms). The K=1 signal here therefore says "narrow, project-internal helper", which *supports the BORDERLINE concern about audience* (is this wanted by anyone outside this `extLog` development?) rather than pointing at a NO-composable verdict.

---

### Composition check (Phase 6)

Can `exists_pow_sub_one_norm_le` be derived from mathlib in ≤3 chained calls?

**Attempt 1 — direct mathlib lemma:** none exists (Phase 5). No `Teichmuller`/unit-power lemma in the normed-field setting to call. Fails.

**Attempt 2 — pigeonhole one-liner:** `Finite.exists_ne_map_eq_of_infinite (fun n => mk (⟨z,_⟩^n))` gives `i ≠ j` with equal images — but that is only step 2 of 6. Turning that into `‖z^{j−i} − 1‖ ≤ p⁻¹` requires: a `wlog i<j`; extracting `z^j − z^i ∈ (p)` (`mk_eq_mk_iff_sub_mem`); writing `= p·s` (`mem_span_singleton'`); pushing to `L` with `push_cast`/`ring`; the norm computation `‖p‖·‖s‖` with `norm_natCast_p` + the project lemma `norm_le_one_of_mem_adjoin_int`; and the factoring `z^j − z^i = z^i(z^{j−i}−1)` with `‖z^i‖=1`. That is multiple `have`s with non-trivial reasoning between them (the heuristic table's explicit NO row), plus it depends on the project's *own* `finite_adjoin_int_quotient` and `norm_le_one_of_mem_adjoin_int`, neither of which is a single mathlib call. Fails as a composition.

Conclusion: **NOT-COMPOSABLE.** This is a real multi-step proof, not a ≤3-call composition of mathlib primitives. (It composes two project lemmas — `finite_adjoin_int_quotient`, `norm_le_one_of_mem_adjoin_int` — with the mathlib pigeonhole and ideal API, but that composition is itself a genuine proof, and two of the three ingredients are project-internal.) Phase 7 therefore considers the YES and BORDERLINE buckets, and is steered away from both NO buckets.

---

## Verdict: `PadicLFunctions.exists_pow_sub_one_norm_le`

**Category:** `BORDERLINE-needs-human`

**Evidence:**
- Literature search (Phase 3): the content is the **existence half of the Teichmüller construction** — classical, in every local-fields text — but the **standard form is stated under a stronger hypothesis (finite residue field) with a stronger conclusion (explicit `q−1` exponent + convergence to ω(z))**. The Lean form is a hypothesis-shifted, conclusion-weakened fragment.
- Generality analysis (Phase 4): **hypothesis-shifted, not cleanly comparable.** More general on the residue-field axis (integral `z` vs. finite-residue `L`), strictly weaker on the conclusion axis (non-explicit `m`, only `≤ p⁻¹`). The two are coupled — no single restatement dominates. Phase 4c: the mathlib-idiomatic object (a `Tendsto`/section Teichmüller lift for finite-residue fields) is a *different, larger* theorem, not a drop-in restatement of this one.
- Mathlib search (Phase 5): **not in mathlib** under either form. Mathlib's Teichmüller content is the Witt-vector/perfectoid `Perfection.teichmuller`; the `norm_pow_sub_one_*` family is a same-name, different-concept cyclotomic field-norm result.
- Composition check (Phase 6): **NOT-COMPOSABLE** — a genuine ~25-line proof, two of whose three ingredients are project-internal lemmas.

**Rationale:**

This declaration sits in a genuine grey zone, which is why the honest verdict is BORDERLINE rather than a forced YES or NO. The two NO buckets are cleanly excluded: Phase 5 shows mathlib has nothing of this shape in the normed-field setting (its Teichmüller machinery is the perfectoid/Witt-vector `Perfection.teichmuller`, a different object with `AdicCompletion`/`Perfection`/`CharP (R/I) p` hypotheses; the `IsPrimitiveRoot.norm_pow_sub_one_*` lemmas are an unrelated field-norm computation that merely shares a name), and Phase 6 shows the proof is a real multi-step pigeonhole-plus-pushforward argument — not a ≤3-call composition, and in fact built on two *project-internal* lemmas (`finite_adjoin_int_quotient`, `norm_le_one_of_mem_adjoin_int`). So if mathlib were to host this content, it would be a new lemma, not a deletion. That pushes toward a YES bucket.

But it is **not** a clean `YES-add-as-is`, for two coupled reasons surfaced in Phase 4. First, the user's statement is a *deliberately weakened* fragment of the standard Teichmüller existence result: the literature gives the explicit exponent `q − 1` (q = residue-field cardinality) and the convergence `z^{p^n} → ω(z)` to a root of unity, whereas this lemma gives only a non-explicit `m` and the single bound `‖z^m − 1‖ ≤ p⁻¹`. The `YES-add-as-is` gate requires the form to be at the right generality, and a non-explicit-exponent existence statement is plausibly *not* the form mathlib would want — mathlib would more likely want the proper Teichmüller lift (route B in Phase 4b: `[Finite residue field] → u^{p^n} → ω` as a `Tendsto`, the modern-idiom object from Phase 4c, mirroring `Perfection.teichmuller`'s role). Second, the hypothesis is shifted, not strengthened or weakened: this lemma drops any finiteness assumption on `L`'s residue field and instead imposes `IsIntegral ℤ z`, localising the finiteness to `ℤ[z]/(p)`. That is a real and somewhat unusual generalisation (it covers algebraic-integer units even when `L` has an infinite residue field), but it is precisely the shape the *project* needs (its arguments `1 − ε_N^c` are algebraic integers in a possibly-large `L`), and it is not obviously the shape *mathlib* wants for a general-purpose Teichmüller lemma. Whether mathlib should host (A) this integral-element existence fragment as-is, or only (B) the full finite-residue-field Teichmüller lift of which it is a sub-step, is a mathematical-taste and scope decision the skill cannot ground in the search evidence — so it is surfaced as the human question. The call-site profile (K = 1, single internal use, no external or downstream consumers, docstring tag `W6a-a5`) reinforces that this is currently a narrow, project-shaped helper rather than a recognised reusable API, which is itself one of the documented BORDERLINE triggers (audience-narrow result).

**Numbered questions (≤5):**

1. **Is the intended mathlib contribution this *existence fragment* (some power of a norm-one algebraic integer lies in `1 + p·O`), or the full *Teichmüller lift* it is a step of (for a complete field with finite residue field, `u^{p^n}` converges to a root of unity `ω(u)`, with the explicit `q−1` congruence)?** If the latter, this lemma is an internal sub-step and should *not* be PR'd on its own — it would be absorbed into that larger development (route B in Phase 4b / 4c).

2. **Is the non-explicit exponent acceptable, or does mathlib want the explicit `q−1` (residue-field-cardinality) exponent?** The explicit exponent requires a *finite residue field on `L`* (not just integrality of `z`); committing to it changes the hypothesis (question 3) and the statement.

3. **Which hypothesis is the right one for mathlib: `IsIntegral ℤ z` (this lemma — localises finiteness to `ℤ[z]`, works for infinite-residue `L`), or `[Finite (residue field of L)]` (the textbook frame — gives the stronger explicit conclusion)?** They are incomparable; the project uses the former because its inputs are algebraic integers in a possibly-large `L`.

4. **Is this result intended for downstream consumers outside the `PadicLFunctions` extended-logarithm development, or is it internal to it?** It currently has exactly one internal call site (`extLogDomain_of_integral_norm_one`) and no external or downstream users; if it is purely internal, mathlib upstreaming may be premature regardless of the form.

5. **If a mathlib version is pursued, should it be phrased analytically (`‖z^m − 1‖ ≤ p⁻¹`, as now) or algebraically (`z^m ≡ 1 [mod (p)]` / `z^m ∈ 1 + 𝔪`)?** The algebraic phrasing composes with mathlib's ideal/valuation API; the analytic phrasing is what *this* project's `exists_pPow_pow_inExpBall` consumes.

**Next action:** user answers the questions; re-run `/mathlibable PadicLFunctions.exists_pow_sub_one_norm_le` to resolve the verdict. Likely outcomes based on the answers:
  - *Full Teichmüller lift wanted (Q1 = lift) / explicit `q−1` wanted (Q2) / finite-residue hypothesis (Q3)* → this fragment is an internal sub-step; **do not PR it alone** — open a `/develop` ticket for the full finite-residue-field Teichmüller lift (the route-B modern object), of which this is one lemma. Verdict effectively folds into that larger plan.
  - *Existence fragment wanted as-is (Q1 = fragment) + reusable beyond this project (Q4 = external)* → flips to **`YES-but-generalise-first`**: keep the integrality hypothesis but state it over a general commutative-`ℤ`-algebra / valuation framing, prefer the algebraic phrasing (Q5), and run `/generalise` before a PR.
  - *Purely internal (Q4 = internal)* → drop from mathlib consideration; keep as a project-local helper (the current form is exactly right for the `extLog` engine).

---

## Next step

User answers the five questions above; re-run `/mathlibable PadicLFunctions.exists_pow_sub_one_norm_le` to resolve. The crux is **which statement mathlib should host** — this deliberately-weakened existence fragment (non-explicit exponent, integral-element hypothesis, analytic `≤ p⁻¹` bound, tailored to the `extLog`-domain engine) versus the full finite-residue-field Teichmüller lift it is a sub-step of (explicit `q−1`, convergence to a root of unity, the modern `Tendsto`/section idiom mirroring mathlib's `Perfection.teichmuller`). Mathlib has neither today (confirmed across all five search methods), and the proof is a genuine pigeonhole argument (NOT-COMPOSABLE), so the question is one of mathematical scope and taste, not of redundancy.
