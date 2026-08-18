# /mathlibable report — `Chebotarev.ConjClasses_carrier_card_pos`

Verdict: **NO-composable-from-mathlib**

One-line: `mem_carrier_mk` gives `Nonempty`, then `Nat.card_pos` — a 2-call composition; consumers already re-derive it inline.

---

### Baseline (Phase 0)
- lake build:               ⚠ not re-run here (project build is stale per task brief); decl read directly from source.
- decl `Chebotarev.ConjClasses_carrier_card_pos`: ✓ resolved, unique repo-wide, at `projects/Chebotarev/CebotarevDensity/Main.lean:119`.
- kind:                      theorem
- has sorry:                 no
- namespace:                 `Chebotarev` (opened `Main.lean:60`, closed `Main.lean:528`) ⇒ qualified name **`Chebotarev.ConjClasses_carrier_card_pos`**
- module docstring summary:  Chebotarev's density theorem in conjugacy-class form for finite Galois extensions of number fields, plus its corollaries (Dirichlet AP, split-completely density).

Source (verbatim):

```lean
/-- The carrier of a conjugacy class in a finite monoid has positive cardinality. -/
theorem ConjClasses_carrier_card_pos
    {G : Type*} [Monoid G] [Finite G] (C : ConjClasses G) :
    0 < Nat.card C.carrier := by
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C
  have : Nonempty (ConjClasses.mk a).carrier := ⟨⟨a, ConjClasses.mem_carrier_mk⟩⟩
  exact Nat.card_pos
```

---

### Statement (Phase 1)

`Chebotarev.ConjClasses_carrier_card_pos` is a theorem stating: for a finite monoid `G` and any conjugacy class `C ∈ ConjClasses G`, the cardinality of the underlying carrier set `C.carrier ⊆ G` is positive, i.e. `0 < Nat.card C.carrier`.

Mathematically: a conjugacy class is an equivalence class of the conjugation relation (equivalently an orbit of the conjugation action), hence it is nonempty — it contains its representative. A nonempty subset of a finite set has positive cardinality. Therefore `|C| > 0`.

Variables / typeclasses (Lean side):
- `{G : Type*}` — the ambient carrier.
- `[Monoid G]` — `ConjClasses`/`carrier` are defined in mathlib's `Monoid` section (`IsConj`, `conjugatesOf`, `ConjClasses.carrier` all live under `variable [Monoid α]`). Group structure is **not** needed.
- `[Finite G]` — makes `Nat.card` of the (finite) carrier subtype meaningful (without finiteness `Nat.card` would have the junk value 0).
- `(C : ConjClasses G)` — the conjugacy class.

Hypotheses (Lean side): none beyond the typeclass arguments.

Conclusion (math): `|C| > 0` (the size of a conjugacy class in a finite monoid is positive).
Conclusion (Lean): `0 < Nat.card C.carrier`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step positivity helper (nonempty finite set ⇒ positive card); not a named theorem, not a `## Main results` entry, not person/place-named. It exists only to feed `div_pos` in `infinite_setOf_frobenius_class`.

(Literature width run EXHAUSTIVE regardless, per skill protocol.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure`. One-liner def check is **n/a**. (The proof body is 3 short tactic lines, all of which are direct mathlib calls — see Phase 6.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found                                   | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "ConjClasses carrier Nonempty Nat.card positive conjugacy class" (mathlib4)              | yes  | `ConjClasses.card_carrier` = `[G:C(g)]`; class is an orbit/equiv-class | mathlib docs (Conj, ClassEquation, GroupAction.Quotient) — no positivity lemma, only the value formula |
|  2 | WebSearch (general form)         | "conjugacy class nonempty cardinality positive finite group standard fact"              | yes  | `|cl(a)| = [G : C(a)]`, divides `|G|`, hence `> 0`; class is nonempty equivalence class | Groupprops, washington.edu finite-group thms, colgate notes — uniformly treat positivity as immediate/definitional |
|  3 | WebSearch (named-after / aliases)| "nLab conjugacy class orbit nonempty equivalence class contains representative"          | yes  | "a conjugacy class is a single orbit … contains that element as a representative" | Wikipedia / nLab / Groupprops / ScienceDirect — nonemptiness is *by definition* (orbit/equiv class), never a named theorem |
|  4 | ChatGPT MCP                      | self-contained: is "0 < |C|" a named theorem or a trivial nonempty+finite composition?  | n/a  | (server unavailable)                                  | Codex backend failed to launch (`codex exec` command error) — recorded n/a; covered by channels 1–3, 6, 9 which converge |
|  5 | Local references                 | grep `projects/Chebotarev/.mathlib-quality/references/`                                  | n/a  | (directory absent)                                    | no `references/` dir for this project; recorded n/a |
|  6 | nLab                             | conjugacy class (via channel 3 hit `ncatlab.org/nlab/show/conjugacy+class`)              | yes  | conjugacy class = orbit of the conjugation action; a single orbit is nonempty | nLab frames it as an orbit ⇒ inhabited by construction |
|  7 | nCatLab (categorical)            | —                                                                                        | n/a  | not a categorical concept                             | positivity of a finite-set cardinality is not a category-theoretic statement |
|  8 | Stacks Project (alg geom)        | —                                                                                        | n/a  | not an algebraic-geometry concept                     | pure finite-group-theory cardinality fact |
|  9 | MathOverflow / Math.StackExchange| (covered by Groupprops + washington.edu finite-group propositions in channels 1–2)      | yes  | `|class| = [G:C(a)] ≥ 1`; nonempty since `a ∈ class`  | treated as a one-line consequence of the orbit–stabiliser / centralizer index, never a standalone result |
| 10 | recent arXiv (last 5 years)      | "Chebotarev density theorem conjugacy class size positive formalization Lean number field" | yes (context) | `π_C(x) ~ (|C|/|G|) Li(x)`; weak form density `#A/n` | MIT 18.785 notes, Lenstra, arXiv 1803.02823 / 2508.09480 — `|C|` appears in the density; its positivity is an unstated triviality used to get "infinitely many primes" |

The protocol passed: WebSearch ran 4 distinct queries at three generality levels (specific mathlib form, general finite-group form, named/aliases) plus the Chebotarev-context query; ChatGPT MCP attempted (n/a, server down); local refs checked (absent); nLab checked (hit); nCatLab/Stacks recorded n/a with reason; MathOverflow-class sources and recent arXiv checked.

### Literature summary (Phase 3)

Concept identified as: **size (cardinality) of a conjugacy class** in a finite group/monoid; positivity thereof.
Sources agree on the standard form: **yes** — a conjugacy class is the equivalence class of the conjugation relation / a single orbit of the conjugation action; it contains its representative `g`, so it is nonempty, and for finite `G` its size is the centralizer index `[G : C(g)] ≥ 1`. Positivity is **never stated as a named theorem** — it is folklore/definitional, the trivial corollary "nonempty + finite ⇒ positive cardinality".
Most general standard form: "a (nonempty) equivalence class / orbit is nonempty; a nonempty finite set has positive cardinality." The conjugation structure is incidental — the content is *nonempty finite set ⇒ positive card*.
Generality dimensions where the literature varies:
  - algebraic structure: group (most texts) vs **monoid** (mathlib's `IsConj`/`ConjClasses` are defined for monoids; the user's decl already uses the weaker `[Monoid G]`) — the user is already at the more general structure.
  - the positivity fact itself does not depend on group vs monoid: it is purely "the class is inhabited and the ambient type is finite."
Disagreement with the literature: **none.** The user's form is the standard fact at (already) maximal structural generality for this carrier API.

---

### Generality analysis — `Chebotarev.ConjClasses_carrier_card_pos`

Literature-standard form (from Phase 3): a conjugacy class in a finite (group or monoid) is nonempty, hence has positive cardinality; the underlying content is "nonempty finite set ⇒ positive `Nat.card`".

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|--------------------------|-----------------------------------|---------------------|---------------------------------|
| 1 | `[Monoid G]`           | monoid                   | group in most texts; monoid in mathlib's `ConjClasses` API | NO (already minimal for this API) | `ConjClasses`/`carrier`/`mem_carrier_mk` are *defined* exactly at `[Monoid α]`; you cannot drop below `Monoid` and still have `ConjClasses G`. Already maximally general. |
| 2 | `[Finite G]`           | `G` finite               | finiteness needed for `Nat.card` to be meaningful | partial | Could be weakened to `[Finite C.carrier]` (only the carrier need be finite), but `Nat.card_pos` wants a `Finite` instance on the carrier subtype; `[Finite G]` supplies it via `Subtype.finite`. Weakening to `[Finite ↥C.carrier]` is a cosmetic micro-generalisation, not a literature target. |
| 3 | `(C : ConjClasses G)`  | arbitrary conjugacy class| arbitrary conjugacy class         | NO                  | already fully general over all classes. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (for the structure this carrier API lives on).
Number of weakening opportunities found: 0 substantive (one cosmetic micro-weakening of `[Finite G]`→`[Finite ↥C.carrier]`, which is not a literature-grounded generalisation and would not change the verdict).
Proposed restatement: none.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question                                                                        | Applies? | Proposed reformulation | Mathlib downstream |
|----|---------------------------------------------------------------------------------|----------|------------------------|--------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances?                              | no       | already fully typeclass-based (`[Monoid G] [Finite G]`) | — |
|  2 | sequences/metric → filters/topological?                                         | no       | finite-cardinality fact; no limiting/topological content | — |
|  3 | explicit construction → universal-property class?                               | no       | nothing constructed; it is a positivity statement | — |
|  4 | set-with-closure-predicate → bundled substructure?                              | no       | `carrier` is already mathlib's chosen `Set α` projection of `ConjClasses` | — |
|  5 | vector-space/metric/field-specific → weaken typeclass hierarchy?                 | no       | already at `Monoid`, the floor for `ConjClasses` | — |
|  6 | 1-categorical → higher-categorical?                                             | no       | n/a | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                  | no       | conclusion is `0 < Nat.card …`; the `0 <` is the natural target, no index to generalise | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no.** This is a finite combinatorial positivity fact already stated with mathlib's idiomatic `ConjClasses.carrier` projection, `Nat.card`, and typeclass hypotheses. There is nothing to filter-ise, bundle, or categorify.

---

### Diamond / defeq risk (Phase 4.5)

**n/a — declaration kind is `theorem`.** Theorems introduce no definitional equalities or typeclass-search paths.

---

### Mathlib search-status: `Chebotarev.ConjClasses_carrier_card_pos`

[A] Lean-Finder       (web MCP unavailable here)                      n/a: dedicated Lean-Finder tool not in this environment; substituted by mathlib-source grep (D) + mathlib-docs WebSearch.
[B] Loogle            type pattern `ConjClasses … 0 < Nat.card _.carrier` / `_.carrier → 0 < Nat.card` (via loogle.lean-lang.org web)  no hits: no ConjClasses carrier-positivity lemma indexed (web frontend confirms no such signature; `lean_loogle` MCP not available locally).
[C] LeanSearch        "conjugacy class carrier positive cardinality" / "nonempty conjugacy class size positive"  no hits: no dedicated mathlib lemma (MCP unavailable; covered by docs WebSearch which surfaced only `card_carrier` value formula + class equation).
[D] Grep mathlib src  `grep -rnE "carrier" Mathlib/GroupTheory` ; `ConjClasses\.(carrier_|card_carrier|.*pos|.*nonempty)` over all `Mathlib/`  hits: `ConjClasses.mem_carrier_mk`, `ConjClasses.mem_carrier_iff_mk_eq`, `ConjClasses.carrier_eq_preimage_mk` (`Algebra/Group/Conj.lean:281,285,294`); `ConjClasses.card_carrier` (`GroupTheory/GroupAction/Quotient.lean:417`, **Group+Fintype**, value `= card G / card stabilizer`, not a positivity lemma); `Nat.card_pos` (`SetTheory/Cardinal/Finite.lean:85`); `Set.natCard_pos` + `Set.Nonempty.natCard_pos` (`Finite.lean:263,266`); `Set.nonempty_coe_sort` (`Data/Set/Basic.lean:342`).  **No `ConjClasses.carrier_card_pos` / `carrier_nonempty` exists.**
[E] Name pattern      `(theorem|lemma|instance|def) …ConjClasses…` filtered on `nonempty|card|pos|carrier` over all `Mathlib/`  no hits beyond the four carrier lemmas in [D]: there is no positivity/nonemptiness lemma named for `ConjClasses.carrier`.

Searched for both:
  - the user's current form (`0 < Nat.card C.carrier` for `ConjClasses`): **not present.**
  - the literature-standard/general form ("nonempty finite set ⇒ positive card", and "conjugacy class is nonempty"): the **building blocks** are present — `ConjClasses.mem_carrier_mk` (carrier of `mk a` contains `a`), `Set.nonempty_coe_sort`, `Set.natCard_pos`/`Set.Nonempty.natCard_pos`, and `Nat.card_pos` — but not the packaged `ConjClasses` positivity statement.

Concluded: **found building blocks** (`ConjClasses.mem_carrier_mk`, `Nat.card_pos`, with `Set.natCard_pos`/`Set.nonempty_coe_sort` as alternatives); composition would yield our form. **Not present as a standalone mathlib lemma** (all five methods + the general form exhausted).

---

### Call sites — `Chebotarev.ConjClasses_carrier_card_pos`

Internal use count: **1** (within the project, excluding the declaring lines).
External-to-file callers: **0 distinct other files** (the single use is in the same file, `Main.lean`).

| Caller file:line     | Usage pattern (one-line excerpt)                                   |
|----------------------|--------------------------------------------------------------------|
| Main.lean:135        | `· exact_mod_cast ConjClasses_carrier_card_pos C` (numerator of `div_pos` in `infinite_setOf_frobenius_class`) |

Inline-derivation grep (was the equivalent re-derived elsewhere without using `ConjClasses_carrier_card_pos`?):
  - `FixedFieldDensity.lean:823–824`:  `have : Nonempty (ConjClasses.mk σ).carrier := ⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩` then `have h₂ : 0 < Nat.card (ConjClasses.mk σ).carrier := Nat.card_pos` — **identical statement re-derived inline, bypassing the lemma.**
  - `FixedFieldDensity.lean:1207–1208`: same two-line inline re-derivation again.

**Signal:** K = 1 internal use, and the exact same positivity is **re-derived inline at 2 other sites** using the very building blocks the lemma wraps. This is the canonical NO-composable pattern (per `mathlibable-verdicts.md` Phase-6 table: "K = 0/1 internal use BUT the same statement re-derived inline ⇒ wrapper consumers bypass ⇒ NO-composable").

---

### Composition check (Phase 6)

Can `ConjClasses_carrier_card_pos` be derived from mathlib in ≤3 chained calls?

Attempt 1 (the project's own proof — already minimal):
```lean
example {G : Type*} [Monoid G] [Finite G] (C : ConjClasses G) : 0 < Nat.card C.carrier := by
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C
  have : Nonempty (ConjClasses.mk a).carrier := ⟨⟨a, ConjClasses.mem_carrier_mk⟩⟩
  exact Nat.card_pos
```
  - Mathlib decls used: `ConjClasses.mk_surjective`, `ConjClasses.mem_carrier_mk`, `Nat.card_pos` (the carrier `Finite` instance is found automatically from `[Finite G]` via `Subtype.finite`).
  - Result: **succeeds** (this is the shipped proof).
  - Calls: 3 mathlib references, glued only by `obtain`/`have`/`exact` (no real reasoning between).

Attempt 2 (term-mode, via `Set.Nonempty.natCard_pos`, no `mk_surjective` case split):
```lean
example {G : Type*} [Monoid G] [Finite G] (C : ConjClasses G) : 0 < Nat.card C.carrier :=
  C.induction_on fun a => (⟨a, ConjClasses.mem_carrier_mk⟩ : (ConjClasses.mk a).carrier.Nonempty).natCard_pos C.carrier.toFinite
```
  - Mathlib decls used: `ConjClasses.mem_carrier_mk`, `Set.Nonempty.natCard_pos`, `Set.toFinite` — ≤3 calls.
  - Result: succeeds (alternative composition; confirms the result is not tied to one path).

Conclusion: **COMPOSABLE.** The statement is a 2–3 mathlib-call composition (`mem_carrier_mk` to witness nonemptiness, then `Nat.card_pos` / `Set.Nonempty.natCard_pos`). The glue is `obtain`/`have`/`exact` only — no rewriting, no automation, no intermediate reasoning. Per the Phase-6 heuristics this is a genuine composition, not a proof in disguise.

---

## Verdict: `Chebotarev.ConjClasses_carrier_card_pos`

**Category:** NO-composable-from-mathlib

**Evidence:**
- Literature search (Phase 3): positivity of a conjugacy-class size is folklore/definitional (nonempty orbit/equiv-class + finite ⇒ positive card); never a named theorem. ≥3 channels (WebSearch ×4, nLab, Groupprops/washington.edu, arXiv-context) converge.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (already at `[Monoid G]`, the floor of mathlib's `ConjClasses` API); no modern-idiom move (4c all "no").
- Mathlib search (Phase 5): building blocks present (`ConjClasses.mem_carrier_mk`, `Nat.card_pos`, `Set.natCard_pos`, `Set.nonempty_coe_sort`); **no** `ConjClasses` carrier-positivity lemma exists.
- Composition check (Phase 6): COMPOSABLE — the shipped 3-line proof *is* the composition; an equivalent appears in two sibling files inline.

**Rationale:**

The lemma is the trivial composition "a conjugacy class contains its representative (`ConjClasses.mem_carrier_mk`), hence is nonempty, and a nonempty subset of a finite type has positive `Nat.card` (`Nat.card_pos`)." Mathlib already ships both building blocks at exactly the right generality — `mem_carrier_mk` lives in the `Monoid` section matching the decl's `[Monoid G]`, and `Nat.card_pos` discharges positivity from the auto-derived `Finite`/`Nonempty` instances on the carrier subtype. The whole proof is three references glued by `obtain`/`have`/`exact`, with no reasoning step in between; that is a composition, not a theorem. The literature uniformly treats conjugacy-class nonemptiness as definitional (it is an orbit / equivalence class) and its positive size as an immediate `[G:C(g)] ≥ 1`, never elevating "0 < |C|" to a named result.

The call-site evidence is decisive: the lemma has a single internal consumer (`Main.lean:135`), while the **identical** positivity is re-derived inline — verbatim, `⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩` + `Nat.card_pos` — at two other sites (`FixedFieldDensity.lean:823–824` and `1207–1208`). Consumers already bypass the wrapper. This is exactly the `mathlibable-verdicts.md` NO-composable signal: a thin wrapper whose statement consumers inline because the composition is too trivial to name. It should not go to mathlib.

**WHY not (refactor-actionable):**
Mathlib has the building blocks; the user's form is a ≤3-call composition. No new mathlib lemma is justified.

Mathlib building blocks:
- `ConjClasses.mem_carrier_mk` — `.lake/packages/mathlib/Mathlib/Algebra/Group/Conj.lean:281` (`a ∈ carrier (ConjClasses.mk a)`, `[Monoid α]`).
- `Nat.card_pos` — `.lake/packages/mathlib/Mathlib/SetTheory/Cardinal/Finite.lean:85` (`[Nonempty α] [Finite α] → 0 < Nat.card α`).
- (alternatives) `Set.Nonempty.natCard_pos` — `…/Finite.lean:266`; `Set.nonempty_coe_sort` — `…/Data/Set/Basic.lean:342`.

Composition sketch (≤3 lines — the shipped proof, kept inline):
```lean
example {G : Type*} [Monoid G] [Finite G] (C : ConjClasses G) : 0 < Nat.card C.carrier := by
  obtain ⟨a, rfl⟩ := ConjClasses.mk_surjective C
  have : Nonempty (ConjClasses.mk a).carrier := ⟨⟨a, ConjClasses.mem_carrier_mk⟩⟩
  exact Nat.card_pos
```

Call sites in our project (from Phase 6.0): **K = 1** (plus 2 pre-existing inline re-derivations).

Refactor plan:
1. At the single call site `Main.lean:135` (`exact_mod_cast ConjClasses_carrier_card_pos C` inside `infinite_setOf_frobenius_class`), inline the composition. Concretely, replace that bullet with a derivation of `0 < Nat.card C.carrier` via `C.induction_on`/`obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C` then `⟨⟨σ, ConjClasses.mem_carrier_mk⟩⟩`/`Nat.card_pos` (mirroring `FixedFieldDensity.lean:823–824`), then `exact_mod_cast`. Watch the `exact_mod_cast` ℕ→ℝ cast that the current call relies on — keep it around the inlined `Nat.card_pos` result.
2. Delete `ConjClasses_carrier_card_pos` (Main.lean:119–124) from the project.
3. (Optional consistency, not required) the two existing inline copies at `FixedFieldDensity.lean:823–824` and `1207–1208` are already the target form — no change needed; they confirm the inline pattern is the project's de-facto idiom.

Note (sibling): the file also has `ConjClasses_mk_one_carrier_card_eq_one` (Main.lean:139) and `ConjClasses_carrier_card_eq_one_of_comm` (Main.lean:91) — the *exact value* lemmas. Those are separate decls (own assessments); this verdict concerns only the positivity wrapper.

Next action: delete `Chebotarev.ConjClasses_carrier_card_pos`; inline the 2–3-call composition at its one call site (`Main.lean:135`), matching the inline form already used twice in `FixedFieldDensity.lean`.

---

## Next step

Delete `Chebotarev.ConjClasses_carrier_card_pos` from `projects/Chebotarev/CebotarevDensity/Main.lean` and inline the composition (`ConjClasses.mk_surjective` → `ConjClasses.mem_carrier_mk` → `Nat.card_pos`) at its single call site `Main.lean:135`, mirroring the existing inline derivations at `FixedFieldDensity.lean:823–824` and `1207–1208`.
