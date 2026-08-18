# /mathlibable report — `Chebotarev.ConjClasses_carrier_card_eq_one_of_comm`

## Verdict (TL;DR)

**`NO-composable-from-mathlib`** — the statement is a 2-call composition of the
existing mathlib lemma `ConjClasses.mk_injective` (equivalently
`mk_eq_mk_iff_isConj` + `isConj_iff_eq`, both `[CommMonoid]`-level in mathlib) with
`Set.ncard_singleton`/`Nat.card_eq_one_iff_unique`. No new lemma needed; inline at
the single call site.

---

### Baseline (Phase 0)
- lake build:               ⚠ stale locally (per task note); reasoning from source + pinned mathlib `d90090f` grep
- decl `Chebotarev.ConjClasses_carrier_card_eq_one_of_comm`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/Main.lean:91`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Chebotarev's density theorem for finite Galois extensions of number fields (conjugacy-class form), plus its abelian and split-completely corollaries.
- namespace:                 `Chebotarev` (so qualified name = `Chebotarev.ConjClasses_carrier_card_eq_one_of_comm`)

---

### Statement (Phase 1)

`Chebotarev.ConjClasses_carrier_card_eq_one_of_comm` is a **theorem** stating:

> In a finite commutative monoid `G`, the conjugacy class of any element `g` is a
> singleton, hence its carrier set has cardinality 1.

Exact Lean form:

```lean
theorem ConjClasses_carrier_card_eq_one_of_comm
    {G : Type*} [Monoid G] [IsMulCommutative G] [Finite G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier = 1
```

Proof body:
```lean
  letI : CommMonoid G := IsMulCommutative.instCommMonoid
  have h : (ConjClasses.mk g).carrier = {g} := by
    ext a
    simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq]
  simp [h]
```

Variables / typeclasses (Lean side):
- `G : Type*` — the carrier type.
- `[Monoid G]` + `[IsMulCommutative G]` — `G` is a commutative monoid (the
  `IsMulCommutative` mixin on top of `Monoid`; an instance gives `CommMonoid G`).
- `[Finite G]` — finiteness. **Mathematically unnecessary** for the singleton
  fact (see Phase 4); `Nat.card` of a singleton is `1` regardless of ambient
  finiteness. It is present only because the call site happens to have it.
- `(g : G)` — the element whose conjugacy class is taken.

Hypotheses: none beyond the typeclasses.

Conclusion (math): the conjugacy class `{x : x ∼ g}` equals `{g}`, so `|class| = 1`.
Conclusion (Lean): `Nat.card (ConjClasses.mk g).carrier = 1`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a helper lemma — a one-fact specialisation (commutative ⇒ conjugacy
classes are singletons), used once to discharge `Nat.card C.carrier = 1` inside the
abelian-case Chebotarev corollary. Not a named theorem, not a `## Main results`
entry, introduces no new structure.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem` → n/a (the one-liner check targets `def`/`abbrev`/`structure`).
Note: the proof is 4 substantive lines but mathematically a 2-step composition.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                     | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | "conjugacy class abelian group singleton commutative every conjugacy class size one"      | yes  | abelian group ⇒ every conjugacy class is `{g}`, size 1 | Wikipedia / Groupprops / MathWorld all state it as a basic fact |
|  2 | WebSearch (general form)         | "commutative monoid conjugacy class trivial IsConj equality every element central"        | yes  | in a commutative monoid conjugacy collapses to equality → singleton classes | confirms the monoid-level generalisation; "all elements commute → each element only conjugate to itself" |
|  3 | WebSearch (aliases / mathlib)    | "mathlib4 ConjClasses carrier card commutative monoid isConj_iff_eq"                        | yes  | surfaced `ConjClasses.card_carrier`, `mkEquiv` (CommGroup ≃ ConjClasses), `mk_bijective` | the underlying mathlib API is already present (see Phase 5) |
|  4 | ChatGPT MCP                      | standard form + generality + "own lemma vs derive inline?" (high effort)                  | n/a  | —                                                    | MCP server down (Codex exec failed) — task note warned of this; compensated with extra WebSearch + authoritative mathlib-source grep |
|  5 | Local references                 | `projects/Chebotarev/.mathlib-quality/references/`                                         | n/a  | (directory absent; `refs/Chebotarev/` also absent)   | recorded n/a |
|  6 | nLab                             | conjugacy class (WebFetch)                                                                 | yes  | "In an abelian group, conjugacy classes are singletons, one for each element of the group." | explicitly stated; nLab pitches it at **abelian group** level only |
|  7 | nCatLab (if categorical)         | —                                                                                          | n/a  | —                                                    | not a higher-categorical concept; covered by nLab row 6 |
|  8 | Stacks Project (if alg geom)     | —                                                                                          | n/a  | —                                                    | not an algebraic-geometry concept |
|  9 | MathOverflow / Math.StackExchange| (covered by WebSearch rows 1-2; standard undergraduate fact)                               | n/a  | —                                                    | no research-level dispute exists for a fact this elementary |
| 10 | recent arXiv (last 5 years)      | (covered by row 2 arXiv hits on monoid conjugacy: 1703.00027, etc.)                        | n/a  | conjugacy in monoids is studied, but the comm ⇒ trivial direction is folklore | nothing reframes the elementary fact |

### Literature summary (Phase 3)

Concept identified as: **"conjugacy classes in a commutative group/monoid are
singletons"** (equivalently: conjugacy collapses to equality in the commutative case).

Sources agree on the standard form: **yes**. Every source states the same fact.
Most general standard form: in any **commutative monoid**, `IsConj a b ↔ a = b`,
hence every conjugacy class is `{g}` and has cardinality 1. The literature most
commonly states it at the **abelian group** level (nLab, Wikipedia, MathWorld);
the commutative-monoid generalisation is folklore and the *strictly more general*
true statement.

Generality dimensions where the literature varies:
  - structure: abelian **group** (most textbooks/nLab) ⟶ commutative **monoid**
    (the most general form; the project's lemma already uses it). The project is
    AT or ABOVE the literature-standard generality on this axis.
  - finiteness: the literature statement needs **no finiteness** at all; the
    project lemma carries a spurious `[Finite G]`.

Disagreement with the literature: none. The project's form is *more general* than
the typical textbook statement (monoid vs. group), modulo the unnecessary
`[Finite G]`.

---

### Generality analysis — `Chebotarev.ConjClasses_carrier_card_eq_one_of_comm`

Literature-standard form (Phase 3): in a commutative monoid, every conjugacy class
is a singleton; `Nat.card (ConjClasses.mk g).carrier = 1`. No finiteness needed.

| # | Parameter / hypothesis     | Current Lean form          | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|----------------------------|----------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `[Monoid G]`+`[IsMulCommutative G]` | commutative monoid | commutative monoid (or just group) | NO (already at/above standard) | `isConj_iff_eq` needs exactly `[CommMonoid]`; this is the right base |
| 2 | `[Finite G]`               | finite                     | **not required**                  | **yes**             | the carrier is a singleton, and `Nat.card {g} = 1` holds with no finiteness; the proof (`ext`+`simp`, `simp [h]`) never uses `[Finite G]` |
| 3 | `(g : G)`                  | element of `G`             | element of `G`                    | NO                  | the statement is about a specific element; cannot weaken |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD** on one axis — it carries a
redundant `[Finite G]`. Dropping it gives the maximally-general true statement.

Number of weakening opportunities found: **1** (`[Finite G]` is removable).

Proposed (finiteness-free) restatement, were one to ship it:
```lean
theorem ConjClasses.carrier_card_eq_one_of_commMonoid
    {G : Type*} [CommMonoid G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier = 1
```

Cost of restatement: **CHEAP** — the existing proof already does not use `[Finite G]`;
deleting it elaborates unchanged.

Note on bucket: this weakening does NOT push toward `YES-but-generalise-first`,
because (Phase 5/6) mathlib already supplies every building block and the result is
a ≤3-call composition — so the right action is "inline / don't ship a standalone
lemma", not "ship a generalised lemma". The generality observation is recorded so
that *if* it were ever upstreamed, it would go in the finiteness-free form.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1 | bundled-hyp → typeclass? | no | already typeclass-driven (`[CommMonoid]`) | — |
| 2 | sequences/metric → filters/topology? | no | purely algebraic/combinatorial; no topology | — |
| 3 | construction → universal-property class? | no | it's a cardinality fact, nothing to characterise universally | — |
| 4 | set+closure-predicate → bundled substructure? | no | `carrier` is already the mathlib `Set`; fine | — |
| 5 | vector-space/field-specific → weaken typeclass? | partially | drop `[Finite G]` (Phase 4b) — but this is a *removal*, not a modernisation | — |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index (ℕ/ℤ/ℝ) → arbitrary algebraic structure? | no | no concrete index in the statement | — |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (beyond the finiteness removal already captured in
4b). The statement is an elementary cardinality fact; there is no contemporary
mathlib reformulation that organises it better. It is not a modernisation move.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is **theorem** (no definitional equalities or
typeclass-search paths introduced).

---

### Mathlib search-status: `Chebotarev.ConjClasses_carrier_card_eq_one_of_comm`

Search performed by authoritative grep over the pinned mathlib `d90090f`
(`.lake/packages/mathlib/Mathlib/`) — the source of truth — plus WebSearch against
`mathlib4_docs`. (lean_loogle/lean_leansearch were not available as tools in this
environment; the source grep is strictly more reliable for an exact-pin answer.)

```
[A] Lean-Finder       n/a (tool unavailable in env)
[B] Loogle            n/a (tool unavailable in env); type pattern would be
                       `Nat.card (ConjClasses.mk _).carrier = 1` — no such decl exists in mathlib (grep)
[C] LeanSearch        via WebSearch on mathlib4_docs: surfaced ConjClasses.card_carrier,
                       mkEquiv, mk_bijective — none is the singleton-cardinality fact
[D] Grep mathlib src  searched carrier/conj/singleton/card across Mathlib/  → see below
[E] Name pattern      `carrier_eq_singleton`, `carrier_card`, `Subsingleton (ConjClasses`,
                       `Unique (ConjClasses` → ZERO hits
```

What mathlib **does** have (all in `Mathlib/Algebra/Group/Conj.lean`, `[CommMonoid]`):
- `isConj_iff_eq {α} [CommMonoid α] {a b : α} : IsConj a b ↔ a = b` (line 56) — the
  core fact that conjugacy = equality when commutative. `@[simp]`.
- `ConjClasses.mk_eq_mk_iff_isConj : mk a = mk b ↔ IsConj a b`.
- `ConjClasses.mem_carrier_iff_mk_eq : a ∈ carrier b ↔ mk a = b` (line 285).
- `ConjClasses.carrier_eq_preimage_mk : a.carrier = mk ⁻¹' {a}` (line 294).
- `ConjClasses.mk_injective`/`mk_bijective` (lines 226/230) and `mkEquiv : α ≃ ConjClasses α`
  for `[CommMonoid]` — i.e. mathlib *already encodes* "in a commutative monoid the
  classes are exactly the elements".

What mathlib does **NOT** have:
- any lemma asserting `(ConjClasses.mk g).carrier = {g}` for commutative `G`;
- any `Nat.card`/`ncard`/`Fintype.card` `= 1` statement for a commutative conjugacy
  class. The only carrier-cardinality lemma is `ConjClasses.card_carrier`
  (`Mathlib/GroupTheory/GroupAction/Quotient.lean:417`), which requires **`[Group G]`**
  (not a monoid), uses `Fintype.card`, and computes `card(stabilizer of conjugation
  action)` index — a *different, more refined* statement that does not specialise in
  ≤1 line to our `Nat.card … = 1` (it is the orbit–stabiliser count, not the
  commutative-collapse fact).

Searched for both the user's form and the literature-standard (finiteness-free,
monoid-level) form.

Concluded: **not in mathlib as a standalone lemma; building blocks present.**
Mathlib has `isConj_iff_eq` / `mk_injective` / `mem_carrier_iff_mk_eq` (the exact
pieces the proof uses) but no packaged "carrier card = 1 for commutative" lemma.

---

### Call sites — `Chebotarev.ConjClasses_carrier_card_eq_one_of_comm`

Internal use count: **1** (excluding the declaring line).
External-to-file callers: 0 distinct files (used only within `Main.lean`).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `projects/Chebotarev/CebotarevDensity/Main.lean:110` | `simpa [ConjClasses_carrier_card_eq_one_of_comm σ] using chebotarev_abelian K L σ` |

Inline-derivation grep (equivalent re-derived elsewhere without this lemma): (none).

Signal: **K = 1 internal use only** → per the call-sites table, this is the "possibly
the wrong abstraction — could be inlined" pattern. Combined with the Phase 6
composition result, leans **NO-composable-from-mathlib**.

---

### Composition check (Phase 6)

Can the statement be derived from mathlib in ≤3 chained calls? **Yes.**

Attempt 1 — the carrier-is-singleton route (what the existing proof already is):
```lean
example {G : Type*} [CommMonoid G] (g : G) :
    Nat.card (ConjClasses.mk g).carrier = 1 := by
  have h : (ConjClasses.mk g).carrier = {g} := by
    simp [Set.ext_iff, ConjClasses.mem_carrier_iff_mk_eq,
          ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq, eq_comm]
  rw [h, Set.Nat.card_coe_set_eq, Set.ncard_singleton]
```
- Mathlib decls used: `ConjClasses.mem_carrier_iff_mk_eq`, `ConjClasses.mk_eq_mk_iff_isConj`,
  `isConj_iff_eq`, `Set.ncard_singleton` (`Mathlib/Data/Set/Card.lean:667`).
- Result: **succeeds** (this is essentially the current 4-line proof; the `[Finite G]`
  hypothesis is not needed).

Attempt 2 — the even-shorter `mk_injective` route:
Because `ConjClasses.mk` is injective on a `CommMonoid` (`ConjClasses.mk_injective`,
mathlib line 226), the carrier `mk ⁻¹' {mk g}` (`carrier_eq_preimage_mk`) is the
preimage of a point under an injection, i.e. the singleton `{g}`; `Nat.card` of a
singleton is `1`. Same ≤3 building blocks, even more directly tied to existing API.

Conclusion: **COMPOSABLE** — ≤3 mathlib calls (`isConj_iff_eq` /
`mem_carrier_iff_mk_eq` / `mk_eq_mk_iff_isConj` to collapse the carrier to `{g}`,
then `Set.ncard_singleton`). No genuinely new mathematical content; this is the
specialisation `isConj_iff_eq` already packaged, plus "card of a point = 1".

---

## Verdict: `Chebotarev.ConjClasses_carrier_card_eq_one_of_comm`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): elementary, universally-stated fact; nLab/Wikipedia/
  MathWorld at abelian-group level, WebSearch confirms the commutative-monoid
  generalisation. No research-level subtlety.
- Generality analysis (Phase 4): STRICTLY NARROWER on one axis only (redundant
  `[Finite G]`); otherwise already at/above the literature standard. No modern-idiom
  reformulation.
- Mathlib search (Phase 5): not present as a standalone lemma; **building blocks
  present** — `isConj_iff_eq`, `ConjClasses.mk_injective`, `mem_carrier_iff_mk_eq`,
  `Set.ncard_singleton`.
- Composition check (Phase 6): **COMPOSABLE** in ≤3 calls.

**Rationale:**

This is the textbook fact "in a commutative group every conjugacy class is a
singleton", lightly generalised to commutative monoids. Mathlib already contains the
mathematical heart of it: `isConj_iff_eq` (`Mathlib/Algebra/Group/Conj.lean:56`)
proves conjugacy collapses to equality for any `[CommMonoid]`, and mathlib even
packages this as `ConjClasses.mk_injective`/`mk_bijective`/`mkEquiv`. The only thing
the project lemma adds is "...therefore the carrier set is `{g}`, whose `Nat.card`
is `1`" — and that final step is exactly `Set.ncard_singleton`
(`Mathlib/Data/Set/Card.lean:667`) after a two-lemma `simp`. The whole statement is a
≤3-call composition of existing mathlib primitives, so no new lemma is warranted; the
single call site should inline it.

WHY not (refactor-actionable detail): mathlib has the building blocks; the statement
is a 2–3 mathlib-call composition. The building blocks are `isConj_iff_eq`
(`Mathlib/Algebra/Group/Conj.lean:56`), `ConjClasses.mem_carrier_iff_mk_eq`
(`…/Conj.lean:285`), `ConjClasses.mk_eq_mk_iff_isConj` (`…/Conj.lean`), and
`Set.ncard_singleton` (`Mathlib/Data/Set/Card.lean:667`). It is not a packaged mathlib
lemma and there is no mathlib gap/TODO calling for one — the fact is already reachable
in one `simp`-plus-rewrite, so a standalone lemma would be redundant surface area.

Mathlib building blocks:
- `isConj_iff_eq` — `Mathlib/Algebra/Group/Conj.lean:56`
- `ConjClasses.mem_carrier_iff_mk_eq` — `Mathlib/Algebra/Group/Conj.lean:285`
- `ConjClasses.mk_eq_mk_iff_isConj` — `Mathlib/Algebra/Group/Conj.lean`
- `Set.ncard_singleton` — `Mathlib/Data/Set/Card.lean:667` (or `Nat.card_eq_one_iff_unique`)

Composition sketch (≤3 lines):
```lean
-- at the single call site (Main.lean:110), inline:
have hcard : Nat.card (ConjClasses.mk σ).carrier = 1 := by
  have h : (ConjClasses.mk σ).carrier = {σ} := by
    simp [Set.ext_iff, ConjClasses.mem_carrier_iff_mk_eq,
          ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq, eq_comm]
  rw [h, Set.Nat.card_coe_set_eq, Set.ncard_singleton]
```

Call sites in this project (from Phase 6.0): **K = 1** — `Main.lean:110`
(`chebotarev_density_of_comm`).

Refactor plan: at the single call site `Main.lean:110`, inline the composition above
(or fold it directly into the `simpa` set). The argument is `σ : Gal(L/K)` and
`Gal(L/K)` already carries the needed `[IsMulCommutative]`/`[Finite]` instances, so the
composition's `[CommMonoid]` requirement is met via `IsMulCommutative.instCommMonoid`,
exactly as the current proof's `letI` does. Then delete
`ConjClasses_carrier_card_eq_one_of_comm` from `Main.lean`.

Caveat (project policy): this is an AINTLIB `dev` branch where small private helper
lemmas like this are perfectly acceptable WIP convenience. The mathlib verdict ("don't
upstream; inline-able from existing primitives") does **not** mandate deleting it from
the project — it only answers "should mathlib have this?" (no). Whether to inline
locally is a `/cleanup` micro-call, not a correctness issue.

**Next action:** do **not** open a mathlib PR for this lemma. If desired during a
`/cleanup` pass, inline the ≤3-line composition at `Main.lean:110` and delete the
helper. Otherwise leave as harmless local convenience.

---

## Next step

Do not upstream. Optionally inline the composition at the single call site
(`Main.lean:110`) via `isConj_iff_eq` + `mem_carrier_iff_mk_eq` + `Set.ncard_singleton`
and delete the helper; this is a `/cleanup` nicety, not a blocker.
