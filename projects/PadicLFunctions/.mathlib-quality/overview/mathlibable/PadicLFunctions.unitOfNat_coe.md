# `/mathlibable` report — `PadicLFunctions.unitOfNat_coe`

**Final verdict: `NO-composable-from-mathlib`.**

---

### Baseline (Phase 0)

- lake build:               build not re-run (stale/slow per task note); **reasoned from source**
- decl `PadicLFunctions.unitOfNat_coe`: ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/EisensteinFamily.lean:56`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  the p-adic family of Eisenstein series (RJW §8) — interpolation of the p-stabilised Eisenstein series by the Kubota–Leopoldt pseudo-measure.

Dependencies read directly from source:
- `PadicLFunctions.unitOfNat` (`EisensteinFamily.lean:53`): `noncomputable def unitOfNat (d : ℕ) : ℤ_[p]ˣ := if h : IsUnit ((d:ℕ):ℤ_[p]) then h.unit else 1` — a **junk-valued** (`dite`) constructor.
- `PadicInt.isUnit_natCast_of_not_dvd` — **project-local** lemma (`projects/PadicLFunctions/PadicLFunctions/KubotaLeopoldt/MuA.lean:35`, in the `PadicInt` namespace), *not* a mathlib lemma. Built on mathlib's `PadicInt.isUnit_iff` + `PadicInt.norm_int_lt_one_iff_dvd`.
- `IsUnit.unit` / `IsUnit.unit_spec` — mathlib (`Mathlib/Algebra/Group/Units/Defs.lean:497` / `:505`); `unit_spec` is `@[simp]` with proof `rfl`.
- `IsUnit.unit_spec` usage in the proof body confirms the elaboration shape.

---

### Statement (Phase 1)

`unitOfNat_coe` is a theorem stating the following:

For a prime `p` and a natural number `d` not divisible by `p`, the underlying p-adic integer of the unit `unitOfNat p d ∈ ℤ_p^×` (the unit attached to `d`) is just `d` itself: `(unitOfNat p d : ℤ_p) = (d : ℤ_p)`.

`unitOfNat p d` is defined by the junk-value pattern `if IsUnit (d:ℤ_p) then (that proof).unit else 1`. The lemma says that **on the good branch** (`p ∤ d`, so `d` is a unit) the bundled unit coerces back to `d`. Mathematically this is the triviality "the canonical unit attached to a unit element coerces to that element"; the only non-`rfl` content is selecting the `dif_pos` branch.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[Fact p.Prime]` — the prime.
- `d : ℕ` (implicit) — the natural number being viewed in `ℤ_p^×`.

Hypotheses (Lean side):
- `hd : ¬ (p : ℕ) ∣ d` — `d` is coprime to `p` (so `(d : ℤ_p)` is a unit).

Conclusion (math): the unit attached to a p-coprime `d` has underlying p-adic integer `d`.

Conclusion (Lean): `((unitOfNat p d : ℤ_[p]ˣ) : ℤ_[p]) = (d : ℤ_[p])`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a coercion/`@[simp]`-style glue lemma about a project-local junk-valued helper `unitOfNat`; not a named theorem, not a `## Main results` entry, not person/place-named.

(Note: literature width was EXHAUSTIVE regardless. BIG/SMALL recorded for framing only.)

### One-line check (Phase 2b)

Body line count: 1 substantive line (`rw [unitOfNat, dif_pos (PadicInt.isUnit_natCast_of_not_dvd hd), IsUnit.unit_spec]`).
One-liner verdict: **n/a — kind is `theorem`, not `def`.** (The one-liner exemption table is for `def`/`abbrev`/`structure`. Recorded as a note: this is a one-line *proof* of a glue lemma, which only reinforces the "composition" reading in Phase 6.)

---

### Literature search — EXHAUSTIVE protocol (Phase 3)

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "natural number coprime to p as a unit in p-adic integers Z_p^times" | yes | `gcd(x,p)=1 ⇒ x ∈ ℤ_p^×` (`a₀ = x mod p ≠ 0`) | Standard, elementary; Gupta REU 2018, Leiden notes, MathWorld. Not a *named* theorem. |
| 2 | WebSearch (general/idiom form) | "IsUnit.unit coercion equals element lemma group units monoid" | yes | mathlib `IsUnit.unit` / coercion lemmas | surfaced `Mathlib.Algebra.Group.Units.Defs` directly — the general bundled-unit coercion (`unit_spec`) is exactly the underlying fact |
| 3 | WebSearch (named-after / context) | "canonical embedding integer coprime to p into unit group p-adic integers Iwasawa theory" | partial | `x` coprime to `p` ⇒ invertible in ℤ_p; characters into ℤ_p^× | Iwasawa-theory framing (RJW context); confirms the embedding is used casually, never as a standalone named result |
| 4 | ChatGPT MCP | (server not configured in this environment) | n/a | — | MCP unavailable; substituted with additional targeted WebSearch (#1–3 already span specific/general/named levels). Recorded as n/a-with-reason. |
| 5 | Local references | `ls projects/PadicLFunctions/.mathlib-quality/references/`; `ls refs/` | n/a | (absent) | No `references/` dir and no `refs/` PDF store present in this checkout — recorded n/a. Source is the RJW notes (TeX 2376 "viewing `d` as an element of `ℤ_p^×`"). |
| 6 | nLab | "p-adic number" / units | yes | ℤ_p^× = `{Σ aᵢpⁱ : a₀ ≠ 0}` | nLab `p-adic number` page; the unit characterisation, again elementary, unnamed |
| 7 | nCatLab (if categorical) | — | n/a | — | not a categorical concept (a coercion lemma about a concrete unit) |
| 8 | Stacks Project (if alg geom) | — | n/a | — | not an algebraic-geometry concept |
| 9 | MathOverflow / MSE | "units of Z_p coprime integers" generality | yes | same elementary characterisation | covered by #1/#6; no distinct general form beyond "a₀ ≠ 0" |
| 10 | recent arXiv (last 5y) | p-adic units / Iwasawa main conj formalisation | yes | — | arXiv:1907.06437, 1601.04195, 2408.03836 use ℤ_p^× freely; the *embedding of a coprime integer* is never a stated lemma — it is background |

The protocol passed: WebSearch ran 3 distinct queries at specific / general-idiom / named-context levels; ChatGPT MCP recorded n/a-with-reason (unavailable) and compensated by an extra WebSearch level; local refs checked (absent → n/a); nLab checked (hit); nCatLab / Stacks recorded n/a-with-reason; MathOverflow/MSE and arXiv checked.

### Literature summary (Phase 3)

Concept identified as: "a natural number coprime to `p` is a unit of `ℤ_p`", and the bundled unit attached to it coerces back to the number. (RJW notes: "viewing `d` as an element of `ℤ_p^×`", TeX 2376.)

Sources agree on the standard form: **yes** — `gcd(d,p)=1 ⇔ d ∈ ℤ_p^×`; the coercion-back is a triviality (`↑(the unit) = d`).

Most general standard form: in any monoid, the bundled unit attached to a unit element coerces to that element — this is mathlib's `IsUnit.unit_spec`. Specialised to `ℤ_p` (or any commutative ring) via `d` coprime to `p`. The literature never *names* either the embedding or its coercion lemma; both are background facts.

Generality dimensions where the literature varies:
  - **ambient ring**: from `ℤ_p` (the project's choice) up to `ZMod n` (mathlib's `unitOfCoprime`) and to *any monoid* for the bare `IsUnit.unit_spec`. The most general is the monoid-level `IsUnit.unit_spec`.
  - **the coprimality witness**: `¬ p ∣ d` (project) vs `Nat.Coprime x n` (mathlib `ZMod.unitOfCoprime`) vs `IsCoprime` (mathlib `ZMod.unitOfIsCoprime`) — all equivalent to "is a unit".

Disagreement with the literature: none. The lemma is mathematically correct and standard; the question is purely whether mathlib should carry *this* form (about a project-local junk-valued `ℤ_p` helper).

---

### Generality analysis — `PadicLFunctions.unitOfNat_coe` (Phase 4)

Literature-standard form (from Phase 3): the monoid-level statement `↑(IsUnit.unit h) = a`, i.e. mathlib's `IsUnit.unit_spec`; or, for the "coprime nat ↦ unit" packaging, `ZMod`'s `coe_unitOfCoprime`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | ambient ring `ℤ_[p]` | p-adic integers | any monoid (`IsUnit.unit_spec`) / any comm ring with a `unitOf*` helper | yes | the coercion-back fact is monoid-level; `ℤ_p` plays no role except that `isUnit_natCast_of_not_dvd` provides the unit witness |
| 2 | `unitOfNat` (the def this is about) | junk-valued `dite` on `IsUnit (d:ℤ_p)` | mathlib's hypothesis-carrying `ZMod.unitOfCoprime`/`unitOfIsCoprime` (no junk branch ⇒ coercion is pure `rfl`) | yes | the junk-value pattern is what *forces* this lemma to exist (a `dif_pos` is needed); a hypothesis-in-the-def design makes the analogue `rfl` and the lemma `@[simp]`-trivial |
| 3 | `hd : ¬ p ∣ d` | `p ∤ d` (Nat) | `Nat.Coprime`/`IsCoprime` | equivalent | `¬ p ∣ d ⇔ Coprime d p` for prime `p`; pure repackaging |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** (it is about a `ℤ_p`-specific junk-valued def, where the underlying fact is monoid-level).
Number of weakening opportunities found: 2 substantive (ambient ring; junk-value vs hypothesis-carrying def design) + 1 cosmetic (coprimality spelling).
Proposed restatement: not applicable as a *mathlib contribution of this lemma* — the right "general form" is **already in mathlib** (`IsUnit.unit_spec`, and the `ZMod.unitOfCoprime` packaging). Restating `unitOfNat_coe` more generally just reproduces `IsUnit.unit_spec`. So this is not a "generalise then ship" case; it is a "mathlib already provides the general building block" case (steers Phase 5/6, not a YES-but-generalise).
Cost of restatement: n/a (no restatement to ship).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream |
|----|----------|----------|------------------------|--------------------|
| 1 | bundled hypotheses → typeclasses/instances? | no | — | the hypothesis `p ∤ d` is data-level coprimality, not a class |
| 2 | sequences/metric → filters/topology? | no | — | no limit/topology content |
| 3 | construct object → universal-property class? | no | — | `unitOfNat` is a value, not a constructed object with a UP |
| 4 | set+closure predicate → bundled substructure? | no | — | not a substructure |
| 5 | vector-space/metric/field-specific → weaken typeclasses? | **yes (already realised by mathlib)** | the monoid-level `IsUnit.unit_spec` / the `ZMod.unitOfCoprime` packaging | **already exists** — no new contribution; mathlib's existing API is the modern idiom |
| 6 | 1-categorical → higher-categorical? | no | — | n/a |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary algebraic structure? | yes (subsumed by #5) | monoid `IsUnit.unit_spec` | already in mathlib |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes — but it is already in mathlib**, not a new contribution. The contemporary mathlib idiom for "coercion of the unit attached to an element equals the element" is `IsUnit.unit_spec` (`@[simp]`, `rfl`), and for the "coprime nat ↦ unit" packaging it is `ZMod.unitOfCoprime` + `ZMod.coe_unitOfCoprime`. The project's `unitOfNat_coe` does not *introduce* a modern idiom; it *consumes* `IsUnit.unit_spec` for one junk-valued `ℤ_p` def. Therefore Phase 4c does **not** flip this to YES-but-generalise-first — there is nothing new to generalise toward.

One-line reason this is not a modernisation move to upstream: the "more modern / more general" form is precisely the mathlib lemma `IsUnit.unit_spec` that this proof already calls.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `PadicLFunctions.unitOfNat_coe` (Phase 5)

```
[A] Lean-Finder       (server n/a here) — substituted with [D] grep over the vendored mathlib tree
[B] Loogle            type pattern `↑(IsUnit.unit _) = _` / `(unitOfCoprime _ _ : _) = _`  → hits: IsUnit.unit_spec, ZMod.coe_unitOfCoprime (found via grep equivalent below)
[C] LeanSearch        "coercion of unit attached to coprime number equals the number"      → maps to ZMod.coe_unitOfCoprime / IsUnit.unit_spec
[D] Grep mathlib src  `IsUnit.unit_spec`, `unitOfCoprime`, `coe_unitOfCoprime`, `unitOfIsCoprime`, `isUnit_natCast_of_not_dvd`, `unitOf`  → hits (see below)
[E] Name pattern      `unitOfNat`, `unitOf*`, `*_coe` for ℤ_[p] in mathlib  → no `PadicInt.unitOf*`; ZMod analogues only
```

Searched for both:
  - **the user's current form** — `(unitOfNat p d : ℤ_p) = d` for the project's junk-valued `ℤ_p` def: **no mathlib decl** (`unitOfNat` is project-local; there is no `PadicInt.unitOfCoprime`/`unitOfNat`).
  - **the literature-standard / general form** — found in mathlib:
    - `IsUnit.unit_spec` (`Mathlib/Algebra/Group/Units/Defs.lean:505`, `@[simp]`, `rfl`): `↑h.unit = a` for any monoid. **This is the underlying fact.**
    - `ZMod.unitOfCoprime` (`Mathlib/Data/ZMod/Basic.lean:789`) + `ZMod.coe_unitOfCoprime` (`:793`, `@[simp]`, `rfl`): `(unitOfCoprime x h : ZMod n) = x` — the **exact structural analogue** of `unitOfNat_coe`, for `ZMod n` rather than `ℤ_p`.
    - `ZMod.unitOfIsCoprime` / `ZMod.coe_unitOfIsCoprime` (`Mathlib/Data/ZMod/Units.lean:140`/`:148`) — the integer-coprimality version.
  - `PadicInt.isUnit_natCast_of_not_dvd` (the proof's other input) is **project-local** (`MuA.lean:35`), *not* mathlib — but it is itself a separate decl, out of scope for this assessment.

Concluded: **found building blocks** (`IsUnit.unit_spec`; plus the project-local `PadicInt.isUnit_natCast_of_not_dvd`) — a ≤3-call composition yields `unitOfNat_coe`. The *exact* form about `unitOfNat`/`ℤ_p` is **not in mathlib** (only the `ZMod` analogue), and `unitOfNat` is project-local, so this is **not** `NO-mathlib-has-it`.

---

### Call sites — `PadicLFunctions.unitOfNat_coe` (Phase 6.0)

Internal use count: **0** (within the project, NOT counting the declaring file `EisensteinFamily.lean`).
External-to-file callers: **0 distinct files** (the only use is at `EisensteinFamily.lean:81`, inside the same file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|----------------------------------|
| EisensteinFamily.lean:81 (declaring file) | `rw [unitOfNat_coe p (Finset.mem_filter.1 hd).2, Nat.cast_pow]` — inside `divisorMeasure_moment` |

Inline-derivation grep (was the equivalent re-derived elsewhere?):
  - `EisensteinFamily.lean:204` — `have hspec : ((u : ℤ_[p]ˣ) : ℤ_[p]) = 2 := IsUnit.unit_spec _` (the team discharges the same shape of goal directly via `IsUnit.unit_spec`, not via `unitOfNat_coe`).
  - `Iwasawa/ResidueField.lean:258` — `rw [IsUnit.unit_spec]; ...` (again, `IsUnit.unit_spec` used directly for `(h.unit : ℤ_[p]) = …`).

Signal: this is the **"K = 0 internal uses, single in-file use; building block is re-used inline elsewhere"** pattern → strong NO-composable lean. The lemma is a thin packaging of `IsUnit.unit_spec` (after a `dif_pos`) for one junk-valued def, and the rest of the project reaches for `IsUnit.unit_spec` directly when it needs the same fact.

### Composition check (Phase 6)

Can `unitOfNat_coe` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the existing proof, verbatim from source):
```lean
rw [unitOfNat, dif_pos (PadicInt.isUnit_natCast_of_not_dvd hd), IsUnit.unit_spec]
```
  - Mathlib decls used: `IsUnit.unit_spec` (the only mathlib lemma; `dif_pos` is core `dite` reduction). Plus project-local `PadicInt.isUnit_natCast_of_not_dvd` for the branch witness.
  - Result: **succeeds** (this is the shipped proof).
  - Notes: two steps — unfold `unitOfNat` + pick the `dif_pos` branch, then close by the `@[simp]`/`rfl` lemma `IsUnit.unit_spec`. Equivalently `simp only [unitOfNat, dif_pos (PadicInt.isUnit_natCast_of_not_dvd hd), IsUnit.unit_spec]`.

Attempt 2 (purely mathlib building blocks, if `unitOfNat` is unfolded at the call site): the only content beyond unfolding the project def is `IsUnit.unit_spec`, a single mathlib call. The `dif_pos` is forced by the junk-value design of `unitOfNat`, not by mathematics.

Conclusion: **COMPOSABLE.** It is `IsUnit.unit_spec` applied after unfolding the project-local `unitOfNat` to its `dif_pos` branch — a ≤3-call definitional composition, not a real proof (per the Phase-6 heuristics: "`Foo.bar (Bar.baz hx)` — one function call after an unfold").

---

## Verdict: `PadicLFunctions.unitOfNat_coe`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the embedding "p-coprime `d` ↦ unit of `ℤ_p`" and its coercion-back are standard, **unnamed** background facts; the general form is mathlib's monoid-level `IsUnit.unit_spec`.
- Generality analysis (Phase 4): STRICTLY NARROWER (about a `ℤ_p`-specific junk-valued def); the general form is already in mathlib — not a generalise-then-ship case. Phase 4c: modern idiom = the existing mathlib `IsUnit.unit_spec`, nothing new to upstream.
- Mathlib search (Phase 5): exact `unitOfNat`/`ℤ_p` form not present (project-local def); building blocks present — `IsUnit.unit_spec` (`@[simp]`, `rfl`), plus the structural analogue `ZMod.unitOfCoprime`/`ZMod.coe_unitOfCoprime`.
- Composition check (Phase 6): COMPOSABLE — `IsUnit.unit_spec` after a `dif_pos` unfold of the project def (≤3 calls). Call sites: K=0 external; one in-file use; the same fact is re-derived inline elsewhere via `IsUnit.unit_spec` directly.

**Rationale:**

`unitOfNat_coe` is not a freestanding mathematical fact suitable for mathlib — it is the coercion-glue lemma for the **project-local, junk-valued** definition `unitOfNat p d := if IsUnit (d:ℤ_p) then h.unit else 1`. Its entire content is: on the good branch the bundled unit `IsUnit.unit` coerces back to `d`. That is precisely mathlib's `IsUnit.unit_spec` (a `@[simp]` lemma proved by `rfl`), specialised through `dif_pos` once the junk branch is ruled out by the unit witness. Mathlib already carries the general building block (`IsUnit.unit_spec`) and even the *exact structural analogue* for `ZMod` (`ZMod.coe_unitOfCoprime`, also `@[simp]`/`rfl`); it simply has no `ℤ_p`-specific junk-valued `unitOf*` def, because that design (hypothesis-free def + separate coercion lemma) is a project convenience, whereas mathlib's `ZMod.unitOfCoprime` carries the coprimality hypothesis in the def so its coercion lemma is pure `rfl`. Shipping `unitOfNat_coe` would mean shipping a wrapper around `IsUnit.unit_spec` tied to a non-mathlib def.

The composability signal reinforces this: `unitOfNat_coe` has **zero** call sites outside its declaring file (one use, at line 81, inside the same file), while elsewhere in the very same project (`EisensteinFamily.lean:204`, `Iwasawa/ResidueField.lean:258`) the authors discharge the identical `(h.unit : ℤ_p) = …` goal by calling `IsUnit.unit_spec` **directly**. So the canonical way to get this fact is already the inline mathlib call; `unitOfNat_coe` is a one-off convenience, not API anyone depends on.

**Refactor-actionable section (NO-composable-from-mathlib):**

WHY not (refactor-actionable detail):
- Mathlib has the building block `IsUnit.unit_spec`; the user's form is the 1-call composition `IsUnit.unit_spec` applied after unfolding the project-local `unitOfNat` to its `dif_pos` branch. The remaining input, `PadicInt.isUnit_natCast_of_not_dvd`, is itself project-local (a separate decl; assess it on its own — it wraps mathlib's `PadicInt.isUnit_iff`/`norm_int_lt_one_iff_dvd`). No new *general* lemma is justified for mathlib here, because the general lemma (`IsUnit.unit_spec`) and the `ZMod` analogue (`ZMod.coe_unitOfCoprime`) already exist.

Mathlib building blocks:
- `IsUnit.unit_spec` — `Mathlib/Algebra/Group/Units/Defs.lean:505` (`@[simp]`, `↑h.unit = a`, `rfl`).
- (structural precedent, not used directly) `ZMod.unitOfCoprime` / `ZMod.coe_unitOfCoprime` — `Mathlib/Data/ZMod/Basic.lean:789`/`:793`; and `ZMod.unitOfIsCoprime` / `ZMod.coe_unitOfIsCoprime` — `Mathlib/Data/ZMod/Units.lean:140`/`:148`.
- (project-local input, out of scope) `PadicInt.isUnit_natCast_of_not_dvd` — `projects/PadicLFunctions/PadicLFunctions/KubotaLeopoldt/MuA.lean:35`.

Composition sketch (≤3 lines) — exactly the shipped proof:
```lean
-- goal: ((unitOfNat p d : ℤ_[p]ˣ) : ℤ_[p]) = (d : ℤ_[p])  given hd : ¬ p ∣ d
rw [unitOfNat, dif_pos (PadicInt.isUnit_natCast_of_not_dvd hd), IsUnit.unit_spec]
```

Call sites in our project (from Phase 6.0): **K = 0 external** (one use at `EisensteinFamily.lean:81`, inside the declaring file).

Refactor plan: this lemma need not be deleted purely on call-count grounds (it is a clean local helper, and keeping it as a private lemma in `EisensteinFamily.lean` is harmless). The actionable point for **mathlib** is: **do not upstream `unitOfNat_coe`.** If `unitOfNat` itself is ever considered for upstreaming, prefer mathlib's hypothesis-carrying design (cf. `ZMod.unitOfCoprime`) — i.e. a `PadicInt.unitOfCoprime (d : ℕ) (h : ¬ p ∣ d) : ℤ_[p]ˣ` whose value is the genuine unit, making its coercion lemma a pure `@[simp]`/`rfl` (matching `ZMod.coe_unitOfCoprime`) rather than a `dif_pos` rewrite. At the single in-file call site (`divisorMeasure_moment`, line 81), the lemma may equally be inlined as the composition above; no other site is affected.

Next action: do **not** open a mathlib PR for `unitOfNat_coe`. It is `NO-composable-from-mathlib` (composition: `IsUnit.unit_spec` after the `dif_pos` unfold). Keep it local, or inline at line 81. Separately, if upstreaming a p-adic "coprime nat ↦ unit" helper is ever desired, design `PadicInt.unitOfCoprime` with the hypothesis in the definition (à la `ZMod.unitOfCoprime`) so the coercion lemma is `rfl`, and assess *that* def on its own merits.

---

## Next step

Do **not** open a mathlib PR for `unitOfNat_coe`. It is `NO-composable-from-mathlib`: it is the one-call composition `rw [unitOfNat, dif_pos (PadicInt.isUnit_natCast_of_not_dvd hd), IsUnit.unit_spec]`, a thin coercion wrapper (built on mathlib's `@[simp]`/`rfl` lemma `IsUnit.unit_spec`) for the project-local junk-valued def `unitOfNat`. Keep it as a local helper or inline it at its single call site (`EisensteinFamily.lean:81`). Mathlib already provides both the general fact (`IsUnit.unit_spec`) and the structural analogue (`ZMod.coe_unitOfCoprime`); the only mathlib-worthy follow-up, if ever desired, is a redesigned `PadicInt.unitOfCoprime` carrying the coprimality hypothesis in the definition — assessed separately.
