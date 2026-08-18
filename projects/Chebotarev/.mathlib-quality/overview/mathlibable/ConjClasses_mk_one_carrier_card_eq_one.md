# /mathlibable report — `Chebotarev.ConjClasses_mk_one_carrier_card_eq_one`

> Step-9 (overview) full mathlibable assessment, single declaration.
> Run date 2026-06-18. Build is stale (per workflow note); reasoned from source +
> the in-repo mathlib tree at `.lake/packages/mathlib`. `lean_loogle`/`lean_leansearch`/
> `lean_local_search` were not available as deferred tools in this environment; the
> ChatGPT-math MCP was down (stdin error on every call). Mathlib search was therefore
> done directly against the vendored mathlib source, and the literature search via
> WebSearch (4 distinct queries) + ProofWiki/Wikipedia/Groupprops.

---

### Baseline (Phase 0)
- lake build:               not run (workflow note: local build stale); decl read from source
- decl `Chebotarev.ConjClasses_mk_one_carrier_card_eq_one`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/Main.lean:139` (inside `namespace Chebotarev`,
  line 60 … `end Chebotarev` line 528 — qualified name confirmed)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Chebotarev density theorem and its corollaries (abelian case,
  completely-split primes, Dirichlet primes in arithmetic progressions).

---

### Statement (Phase 1)

`Chebotarev.ConjClasses_mk_one_carrier_card_eq_one` is a theorem stating:

> In a finite monoid `G`, the conjugacy class of the identity element has exactly one
> element. Equivalently, the carrier set of `ConjClasses.mk (1 : G)` is the singleton
> `{1}`, so its cardinality is `1`.

This is the standard fact that the identity is central — `1` is conjugate only to itself —
specialised to "the size of its conjugacy class is 1". It is used once, to feed the
completely-split-primes density corollary (`density_split_completely`), where the Chebotarev
density `|C|/[L:K]` for the identity class `C = mk 1` must be simplified to `1/[L:K]`.

Variables / typeclasses (Lean side):
- `G : Type*` — the carrier type
- `[Monoid G]` — multiplicative monoid structure (note: **monoid**, not group)
- `[Finite G]` — finiteness (used only so `Nat.card` of the singleton is the literal `1`;
  the singleton equality itself needs no finiteness)

Hypotheses: none beyond the instances.

Conclusion (math): the conjugacy class of `1` is a singleton; `|{1}| = 1`.
Conclusion (Lean): `Nat.card (ConjClasses.mk (1 : G)).carrier = 1`.

Proof body (verbatim):
```lean
have h : (ConjClasses.mk (1 : G)).carrier = {1} := by
  simp [Set.ext_iff, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
simp [h]
```
The first `simp` reduces `x ∈ carrier (mk 1) ↔ x = 1` via `mem_carrier_iff_mk_eq`,
`mk_eq_mk_iff_isConj`, and the `@[simp]` lemma `isConj_one_left/right`; the second
`simp [h]` rewrites to `Nat.card {1} = 1` and closes with `Nat.card_singleton`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-step helper corollary (carrier of the identity class = singleton), feeding a
single density corollary; not a named theorem, not a new structure, not a `## Main results`
entry. (Literature width was still run EXHAUSTIVE per the protocol.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-liner check **n/a**. (The body is a
2-line tactic proof regardless.) No defeq/diamond/API-anchor considerations apply to a
proposition.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                 | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------|------|-------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | conjugacy class of identity element is singleton trivial group theory | yes  | `Cl(e) = {e}`; identity in singleton class            | ProofWiki "Identity of Group is in Singleton Conjugacy Class"; Wikipedia; MathWorld |
|  2 | WebSearch (general form)         | center of group conjugacy class size one central element              | yes  | `|Cl(g)| = 1 ⟺ g ∈ Z(G)`; `|Cl(g)| = [G : C_G(g)]`    | Groupprops; the identity-singleton fact is the `g = e` special case |
|  3 | WebSearch (named-after / aliases)| (covered by #1/#2: "singleton conjugacy class", "central element")    | yes  | same fact under the class-equation framing            | the fact is unnamed — it is a one-line lemma, not an eponymous theorem |
|  4 | WebSearch (mathlib-specific)     | mathlib4 ConjClasses carrier mk_one center isConj                     | partial | surfaced `ConjClasses.card_carrier`, `noncenter`, `IsConj`/center API | confirmed mathlib has the *general* carrier-card API, not the identity case |
|  5 | ChatGPT MCP                      | standard-form + monoid-vs-group precision (2 attempts)                | n/a  | —                                                     | MCP **down** — Codex stdin error on every call; recorded n/a |
|  6 | Local references                 | `projects/Chebotarev/.mathlib-quality/references/` and `refs/Chebotarev/` | n/a  | (no references dir for this project)                  | both paths absent |
|  7 | nLab                             | "conjugacy class" / "center"                                          | n/a  | trivial-set fact; nLab adds nothing beyond Wikipedia  | not a categorical subtlety |
|  8 | nCatLab / Stacks Project         | —                                                                     | n/a  | not categorical, not algebraic-geometry               | a finite-group/monoid combinatorial fact |
|  9 | MathOverflow / Math.StackExchange| "size of conjugacy class of identity"                                 | yes  | universally "1" — textbook exercise                   | covered by #1/#2; no deeper variant |
| 10 | recent arXiv (last 5 years)      | —                                                                     | n/a  | a 19th-century textbook triviality; no modern variant | nothing to find |

### Literature summary (Phase 3)

Concept identified as: **"the identity element lies in a singleton conjugacy class"** — the
`g = e` case of "`|Cl(g)| = 1 ⟺ g` is central", itself the basis of the class equation.
Sources agree on the standard form: **yes** (ProofWiki, Wikipedia, MathWorld, Groupprops all
state it identically).
Most general standard form: in **any monoid**, `1` is conjugate only to `1` (conjugation is
by units, and `u·1·u⁻¹ = 1`), hence `Cl(1) = {1}`. Finiteness is irrelevant to the singleton
statement; it only makes "cardinality `1`" literal.
Generality dimensions where the literature varies:
  - algebraic structure: stated for groups in textbooks, but the underlying reason (`1`
    central) holds in any monoid; **most general = monoid** — which is exactly the Lean form.
  - output flavour: "is a singleton" vs "has cardinality 1" — trivially interchangeable.
Disagreement with the literature: **none.** The Lean form is the literature fact at (in fact
slightly beyond, via monoids) textbook generality.

---

### Generality analysis — `ConjClasses_mk_one_carrier_card_eq_one`

Literature-standard form (Phase 3): `Cl(1) = {1}` in any monoid; cardinality 1 when finite.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[Monoid G]`           | monoid            | monoid (textbooks: group; mathlib's `isConj_one_right` is `[Monoid α]`) | NO | already the most general — `IsConj` is defined via units, valid in any monoid; can't go below `Monoid` (need `1` and `*`). |
| 2 | `[Finite G]`           | finite            | not needed for the singleton; needed only for literal card `= 1` | partial | The singleton equality `(mk 1).carrier = {1}` needs **no** finiteness. Stating it as the set-equality (or `Nat.card`, which is `1` for any singleton without `Finite`) would drop `[Finite G]`. See 4b/4c. |

### Generality verdict (Phase 4b)

The current form is: **essentially MAXIMALLY GENERAL** in its algebraic typeclass (`Monoid` is
the floor), with **one removable hypothesis** (`[Finite G]`) that is not load-bearing for the
mathematically primitive content.
Number of weakening opportunities found: 1 (drop `[Finite G]`).
Proposed (more primitive) restatement:
```lean
-- the load-bearing content, no finiteness:
theorem ConjClasses.mk_one_carrier (G : Type*) [Monoid G] :
    (ConjClasses.mk (1 : G)).carrier = {1} := by
  ext x; simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
-- Nat.card = 1 then follows for free (Nat.card_singleton), still without [Finite G].
```
Cost of restatement: **CHEAP** (mechanical; the proof already proves the set equality as its
first step). But see the verdict — this is moot because the result is composable.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | bundled hyps → typeclasses? | no | — | already typeclass-driven |
|  2 | sequences/metric → filters/topology? | no | — | finite combinatorial fact, no topology |
|  3 | construction → universal property? | no | — | a set equality, nothing to characterise |
|  4 | set-with-predicate → bundled substructure? | no | — | `carrier` is already mathlib's chosen API |
|  5 | vector-space/field → weaken typeclass? | yes (mild) | drop `[Finite G]`, state as `carrier = {1}` (monoid only) | `Nat.card`/`ncard`/`encard` corollaries all follow; matches `ConjRootClass.carrier_zero` precedent |
|  6 | 1-categorical → higher-categorical? | no | — | n/a |
|  7 | concrete index → general monoid/group? | yes (already done) | already `Monoid G`, not a concrete group | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **marginally** — the only move is the set-equality-without-`Finite`
restatement (row 5), which mirrors mathlib's existing `ConjRootClass.carrier_zero :
(0 : ConjRootClass K L).carrier = {0}`. This is a real but small organisational tidy, **not** a
reason to ship: see Phase 6 — the result is a ≤3-call composition from mathlib primitives, so
the right action is to *inline*, not to add a more-general lemma.

---

### Diamond / defeq risk — Phase 4.5

n/a — declaration kind is `theorem`. No definitional equalities or instance-search paths
introduced.

---

### Mathlib search-status: `ConjClasses_mk_one_carrier_card_eq_one`

[A] Lean-Finder       — n/a: tool not available in this environment.
[B] Loogle            — n/a: tool not available; substituted by direct mathlib-source grep (D).
[C] LeanSearch        — n/a: tool not available; substituted by WebSearch #4 + direct grep.
[D] Grep mathlib src  terms: `carrier`, `mk_one`, `isConj_one`, `noncenter`, `mem_carrier`,
    `mk_eq_mk`, `card_carrier`, `carrier.*= {`, `eq_singleton`
    → KEY HITS (all in the vendored `.lake/packages/mathlib`):
      • `Mathlib/Algebra/Group/Conj.lean:66` `isConj_one_right : IsConj 1 a ↔ a = 1`
        (in `section Monoid`, `variable [Monoid α]`, ends line 77) — **the crux**;
        `@[simp]`, also `isConj_one_left` (line 72).
      • `Mathlib/Algebra/Group/Conj.lean:285` `mem_carrier_iff_mk_eq : a ∈ carrier b ↔
        ConjClasses.mk a = b` (`ConjClasses` namespace, `variable [Monoid α]`).
      • `Mathlib/Algebra/Group/Conj.lean:151` `mk_eq_mk_iff_isConj`.
      • `Mathlib/Algebra/Group/Conj.lean:277` `def carrier` and `:294` `carrier_eq_preimage_mk`.
      • `Mathlib/GroupTheory/GroupAction/Quotient.lean:417` `ConjClasses.card_carrier`
        (Group + Fintype) — the **general** carrier-cardinality-as-index lemma, NOT the
        identity case.
      • `Mathlib/GroupTheory/ClassEquation.lean` — `ConjClasses.noncenter`, the class
        equation; line 72 uses `hg.eq_singleton_of_mem mem_carrier_mk` (the same singleton
        pattern), but there is **no** standalone `(mk 1).carrier = {1}` lemma.
      • `Mathlib/FieldTheory/Minpoly/ConjRootClass.lean:70` `ConjRootClass.carrier_zero :
        (0 : ConjRootClass K L).carrier = {0}` — a **direct analog in a different type**:
        evidence that mathlib names "carrier of the trivial class = singleton" when it earns
        its keep in an API, but for `ConjClasses` it does not exist.
[E] Name pattern      — direct grep for `ConjClasses.*carrier.*one`, `carrier_mk_one`,
    `carrier_one` over `Mathlib/`: **no hits** for `ConjClasses`.

Searched for both: the user's form (`Nat.card (mk 1).carrier = 1`) **and** the general
literature form (`(mk 1).carrier = {1}` over a monoid). Neither exists in mathlib.

Concluded: **not in mathlib as a named lemma**, but mathlib has all the **building blocks**
(`isConj_one_left`/`isConj_one_right`, `mem_carrier_iff_mk_eq`, `mk_eq_mk_iff_isConj`,
`Nat.card_singleton`) and the result is a short composition of them — exactly what the existing
proof body is.

---

### Call sites — `Chebotarev.ConjClasses_mk_one_carrier_card_eq_one`

Internal use count: **1** (within the project, excluding the declaring file's own definition).
External-to-file callers: **0** distinct files (the single use is in the *same* file).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `projects/Chebotarev/CebotarevDensity/Main.lean:157` | `rw [ConjClasses_mk_one_carrier_card_eq_one Gal(L/K), IsGalois.card_aut_eq_finrank K L] at h` |

(The use is inside `density_split_completely`, the Sharifi 7.1.14 completely-split corollary.)

Inline-derivation grep (was the equivalent re-derived elsewhere without this lemma?): **(none)** —
no other site computes the carrier-card of an identity class.

Call-sites signal: **K = 1, single in-file use, no external consumers.** Per the Phase 6.0.1
table this leans **NO-composable** — possibly the wrong abstraction; it could be inlined at its
one call site.

---

### Composition check (Phase 6)

Can `ConjClasses_mk_one_carrier_card_eq_one` be derived from mathlib in ≤3 chained calls? **Yes.**

Attempt 1 (the set-equality, which is the whole content):
```lean
example (G : Type*) [Monoid G] : (ConjClasses.mk (1 : G)).carrier = {1} := by
  ext x
  simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  -- isConj_one_left (@[simp]) closes `IsConj x 1 ↔ x = 1`
```
  - Mathlib decls used: `ConjClasses.mem_carrier_iff_mk_eq`, `ConjClasses.mk_eq_mk_iff_isConj`,
    `isConj_one_left` (all `@[simp]` or simp-driven).
  - Result: **succeeds** — this is verbatim the existing proof's first step.

Attempt 2 (the stated `Nat.card` form):
```lean
example (G : Type*) [Monoid G] [Finite G] :
    Nat.card (ConjClasses.mk (1 : G)).carrier = 1 := by
  rw [show (ConjClasses.mk (1 : G)).carrier = {1} from by
        ext x; simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]]
  exact Nat.card_singleton 1
```
  - Mathlib decls used: the three above + `Nat.card_singleton`.
  - Result: **succeeds** in ≤3 effective calls (the singleton rewrite, then `Nat.card_singleton`).

Conclusion: **COMPOSABLE.** The lemma is a trivial simp/`Nat.card_singleton` composition of
existing mathlib primitives; no new mathematical content. (Bonus: the composition needs no
`[Finite G]` until the very last `Nat.card_singleton`, and even that holds without `Finite`.)

---

## Verdict: `Chebotarev.ConjClasses_mk_one_carrier_card_eq_one`

**Category:** **NO-composable-from-mathlib**

**Evidence:**
- Literature search (Phase 3): the identity's conjugacy class is a singleton — a universal
  textbook one-liner, the `g = e` case of "`|Cl(g)| = 1 ⟺ g` central"; unnamed because trivial.
- Generality analysis (Phase 4): essentially maximally general (`Monoid` is the floor); only a
  removable, non-load-bearing `[Finite G]`. No modernisation that would justify a new lemma.
- Mathlib search (Phase 5): not present as a named `ConjClasses` lemma, but every building block
  is (`isConj_one_left/right`, `mem_carrier_iff_mk_eq`, `mk_eq_mk_iff_isConj`, `Nat.card_singleton`).
- Composition check (Phase 6): **COMPOSABLE** — verbatim the existing 2-line proof.

**Rationale:**

The statement is the most elementary fact about conjugacy classes — the identity sits in its own
singleton class — and mathlib already ships its exact decomposition. `isConj_one_left :
IsConj a 1 ↔ a = 1` (Conj.lean:72, `[Monoid α]`, `@[simp]`) is precisely "1 is conjugate only to
1"; combined with `mem_carrier_iff_mk_eq` and `mk_eq_mk_iff_isConj` it gives
`(ConjClasses.mk 1).carrier = {1}` by a one-line `ext; simp`, and `Nat.card_singleton` finishes.
That is *exactly* the existing proof body. There is no mathematical content here beyond chaining
named mathlib simp lemmas, so it fails the "non-trivial composition" bar for a YES verdict. The
call-sites grep confirms the practical picture: a single in-file use (line 157, feeding
`density_split_completely`) and no external consumers — the classic profile of a local
convenience wrapper that should be inlined rather than upstreamed. (The one mathlib precedent for
naming such a thing, `ConjRootClass.carrier_zero`, lives in a *different* type's API where it
earns repeated use; the `ConjClasses` analog has exactly one consumer here.)

**WHY not (refactor-actionable detail):**
Mathlib has the building blocks; the user's form is a ≤3-call composition. No new lemma needed —
inline at the single call site.

Mathlib building blocks (qualified, with paths):
- `isConj_one_left` — `Mathlib/Algebra/Group/Conj.lean:72` (and `isConj_one_right`:66)
- `ConjClasses.mem_carrier_iff_mk_eq` — `Mathlib/Algebra/Group/Conj.lean:285`
- `ConjClasses.mk_eq_mk_iff_isConj` — `Mathlib/Algebra/Group/Conj.lean:151`
- `Nat.card_singleton` — `Mathlib/SetTheory/Cardinal/Finite.lean`

Composition sketch (≤3 lines), to inline at `Main.lean:157`:
```lean
-- replacing `rw [ConjClasses_mk_one_carrier_card_eq_one Gal(L/K), …] at h`
have hcard : Nat.card (ConjClasses.mk (1 : Gal(L/K))).carrier = 1 := by
  rw [show (ConjClasses.mk (1 : Gal(L/K))).carrier = {1} from by
        ext x; simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]]
  exact Nat.card_singleton 1
rw [hcard, IsGalois.card_aut_eq_finrank K L] at h
```

Call sites in the project (from Phase 6.0): **K = 1** (`Main.lean:157`, same file).

Refactor plan: at the one call site (`projects/Chebotarev/CebotarevDensity/Main.lean:157`,
inside `density_split_completely`), inline the composition above in place of the
`rw [ConjClasses_mk_one_carrier_card_eq_one Gal(L/K), …]` step, then delete the standalone
`ConjClasses_mk_one_carrier_card_eq_one` declaration (lines 138–144). The argument flow is
direct (the lemma was applied to `Gal(L/K)`; the inlined `have` specialises to the same group).

**Caveat / optional upgrade.** If a future audit finds the carrier-of-identity-class fact wanted
in *several* places across the repo, the right move is not to keep this project-local wrapper but
to contribute the **general, finiteness-free** lemma to mathlib next to `carrier`:
`ConjClasses.mk_one_carrier (G) [Monoid G] : (ConjClasses.mk (1 : G)).carrier = {1}` (mirroring
`ConjRootClass.carrier_zero`). That would be a separate, deliberate `YES-add-as-is` decision —
not warranted by the current single in-file consumer.

**Next action:** delete `Chebotarev.ConjClasses_mk_one_carrier_card_eq_one` from the project and
inline the ≤3-line composition at `projects/Chebotarev/CebotarevDensity/Main.lean:157`.

---

## Sources (literature)

- ProofWiki — *Identity of Group is in Singleton Conjugacy Class*:
  https://proofwiki.org/wiki/Identity_of_Group_is_in_Singleton_Conjugacy_Class
- Wikipedia — *Conjugacy class*: https://en.wikipedia.org/wiki/Conjugacy_class
- Groupprops — *Conjugacy class* / *Size of conjugacy class divides index of center*:
  https://groupprops.subwiki.org/wiki/Conjugacy_class
- Wolfram MathWorld — *Conjugacy Class*: https://mathworld.wolfram.com/ConjugacyClass.html
