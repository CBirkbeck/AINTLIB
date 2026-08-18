# `/mathlibable` report — `PadicLFunctions.ExtLogDomain.prod`

**Final verdict: `NO-composable-from-mathlib`** — this is a single `Finset.prod_induction`
call over the project-local predicate `ExtLogDomain p`, using the already-existing binary
closure `ExtLogDomain.mul` and the unit witness already present in the proof's empty case.
It is a wrapper that should be inlined at its one call site, not upstreamed.

---

### Baseline (Phase 0)
- lake build:               build not re-run (per task note: may be stale/slow); reasoned from source. The file `ExtLog.lean` is internally consistent and the decl elaborates against its in-file dependencies.
- decl `PadicLFunctions.ExtLogDomain.prod`:  ✓ resolved at `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:400`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  The extended (Iwasawa-branch) p-adic logarithm `extLog` (RJW §6, decomposition W6a): extends `padicLog` to the rational-valuation domain `ExtLogDomain` (`x^m = p^k·y`, `y` in the exp ball), with `extLog x := m⁻¹·padicLog y` and Iwasawa's branch `log_p(p)=0`.

---

### Statement (Phase 1)

`PadicLFunctions.ExtLogDomain.prod` is a theorem stating the following:

The predicate "lies in the extended-log domain" is closed under finite products. Concretely:
for a finite index set `s` and a family `f : ι → L` of elements of a normed field `L` (a
`ℚ_[p]`-algebra) such that every `f i` (for `i ∈ s`) lies in the extended-log domain
`ExtLogDomain p`, the product `∏ i ∈ s, f i` also lies in `ExtLogDomain p`. Here
`ExtLogDomain p x` means `∃ m > 0, ∃ k : ℤ, ∃ y, x^m = p^k · y` with `y − 1` in the open
exponential ball — i.e. `x` has rational `p`-valuation and a power lands on the principal-unit
ball. The fact is the standard "multiplicatively-closed set ⟹ closed under finite products"
closure, proved by `Finset` induction from the binary closure `ExtLogDomain.mul` and the
membership of `1`.

Variables / typeclasses involved (Lean side):
- `p : ℕ`, `[hp : Fact p.Prime]` — the prime.
- `{L : Type*} [NormedField L] [NormedAlgebra ℚ_[p] L] [IsUltrametricDist L]` — the ambient
  extension field. (Note: `[CompleteSpace L]` is `omit`-ed for this lemma.) A `NormedField`
  is in particular a `Field`, hence a `CommRing`, hence a `CommMonoid` under `*`.
- `{ι : Type*}` — the (arbitrary) index type.
- `s : Finset ι` — the finite index set.
- `f : ι → L` — the family.

Hypotheses (Lean side):
- `hf : ∀ i ∈ s, ExtLogDomain p (f i)` — every factor lies in the domain.

Conclusion (math): the finite product of domain elements is again a domain element.

Conclusion (Lean): `ExtLogDomain p (∏ i ∈ s, f i)`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: It is a routine `Finset`-induction closure lemma (predicate closed under `*` and at
`1` ⟹ closed under `Finset.prod`). It is not a new structure, not named after a person/place,
and not a `## Main results` headline — it is plumbing that feeds `extLog_prod` (the additivity
`extLog(∏ f) = Σ extLog ∘ f`).

(Literature width is EXHAUSTIVE regardless. BIG/SMALL is recorded for framing only.)

### One-line check (Phase 2b)

Body line count: ~6 substantive lines (a `classical` + a two-case `Finset.induction`).
One-liner verdict: n/a — kind is `theorem`, not `def`. (Skipped; no defeq/diamond/API-name
exemption analysis required.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------------------------------------|------|---------------------|-------|
|  1 | WebSearch (specific form)        | "property closed under finite product induction 'closed under multiplication' submonoid"                                              | yes  | "if a set is closed under multiplication (binary closure), then by induction it satisfies closure under finite products" — and "a submonoid is closed under taking finite products, including the empty product" | The exact technique; measure-theory example cited (closed under finite product *as a consequence of* closed under multiplication + induction on cardinality) |
|  2 | WebSearch (general form / context of the *def*) | "p-adic logarithm extended domain rational valuation Iwasawa branch log_p(p)=0"                                                       | yes  | Iwasawa's domain `G = p^ℤ(1+𝔪)`, extended via `x^n ∈ G ⟹ log x := (1/n) log(x^n)` | Confirms `ExtLogDomain` itself is Iwasawa's branch domain (the *definition*'s provenance). Not about the closure lemma per se. |
|  3 | WebSearch (named-after / aliases)| "submonoid closed under finite product list_prod_mem prod_mem nLab multiplicatively closed"                                           | yes  | "A multiplicatively closed set is closed under taking finite products, including the empty product 1, equivalently a submonoid" | Surfaced the exact mathlib API names: `prod_mem`, `list_prod_mem` in `Mathlib.Algebra.Group.Submonoid.Membership` |
|  4 | ChatGPT MCP                      | (intended: "standard form + generality + historical evolution of 'closure under finite products from binary closure'")                | n/a  | —                   | ChatGPT MCP not configured in this environment (no `chatgpt` tool in the deferred-tool list / no `.mcp.json` for it active). Compensated with 3 WebSearch queries + nLab. |
|  5 | Local references                 | grep `.mathlib-quality/references/` and `refs/`                                                                                       | n/a  | (no references dir) | `projects/PadicLFunctions/.mathlib-quality/references/` absent and `refs/` absent — recorded n/a. |
|  6 | nLab                             | WebFetch `ncatlab.org/nlab/show/submonoid`                                                                                            | yes  | "A submonoid of M … is a subset N of M containing 1 which is also a monoid w.r.t. the inherited multiplication" | nLab folds finite-product closure into "is a monoid"; doesn't spell out the induction, but confirms the concept is the textbook submonoid-closure fact. |
|  7 | nCatLab (if categorical)         | (covered by #6, the nLab `submonoid` page)                                                                                            | n/a  | —                   | Not a higher-categorical concept; the relevant nLab page is the `submonoid`/`monoid` one already fetched. No extra categorical content to add. |
|  8 | Stacks Project (if alg geom)     | —                                                                                                                                    | n/a  | —                   | Not an algebraic-geometry statement (it is an elementary monoid-closure fact). |
|  9 | MathOverflow / Math.StackExchange| (subsumed by #1/#3, which surfaced SE/Wikipedia "multiplicatively closed set" hits)                                                   | n/a  | —                   | No distinct content beyond #1/#3; "multiplicatively closed set ⟹ finite products" is uncontroversial and not an MO-level question. |
| 10 | recent arXiv (last 5 years)      | (subsumed by #1/#2 arXiv hits, e.g. 1907.06437 on Iwasawa log)                                                                        | n/a  | —                   | arXiv hits concern the `extLog`/Iwasawa-log *construction*, not the elementary closure lemma. Nothing recent reframes "closed under products". |

### Literature summary (Phase 3)

Concept identified as: **closure of a multiplicatively-closed set (containing 1) under finite
products** — the elementary submonoid-closure fact, proven by induction from binary closure.
Sources agree on the standard form: **yes**.
Most general standard form: *Let `M` be a (commutative) monoid and `P ⊆ M` a subset with `1 ∈ P`
and `P` closed under `·`. Then `P` is closed under all finite products `∏_{i∈s} f i`.* Equivalently,
the `Finset.prod_induction` principle: a predicate that is multiplicative and holds at `1` holds on
any finite product.
Generality dimensions where the literature varies:
  - The carrier: stated for `CommMonoid` in the unbundled/induction form; for `Monoid` in the
    bundled `Submonoid` form. The user's `L` is a `NormedField` ⊆ `CommMonoid`, so the
    `CommMonoid` form applies directly.
  - Index: arbitrary `Finset ι` (the user's form) is the standard generality.
Disagreement with the literature: **none**. The user's lemma is the special case of the standard
closure principle where `P = ExtLogDomain p` and `M = L`.

Note: the substantive mathematics of *this file* (the Iwasawa-branch extended log `extLog` and its
domain) is genuinely in the literature (Washington §5.1; Iwasawa's branch `log_p(p)=0`; arXiv
1907.06437) — but `ExtLogDomain.prod` is **not** that mathematics. It is the generic monoid-closure
plumbing applied to that domain.

---

### Generality analysis — `PadicLFunctions.ExtLogDomain.prod`

Literature-standard form (from Phase 3): `1 ∈ P`, `P` closed under `·`  ⟹  `P` closed under
`∏_{i∈s} f i`, over any `CommMonoid`.

| # | Parameter / hypothesis             | Current Lean form               | Literature-standard form        | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------------------|---------------------------------|----------------------------------|---------------------|----------------------------------|
| 1 | `{ι : Type*}`                       | arbitrary index type            | arbitrary index type             | NO                  | Already maximal. |
| 2 | `(s : Finset ι)`                   | arbitrary finite set            | arbitrary finite set             | NO                  | Already maximal (the universally-quantified `Finset` form). |
| 3 | `(f : ι → L)`                      | arbitrary family into `L`       | arbitrary family                 | NO                  | Already maximal. |
| 4 | predicate `ExtLogDomain p`         | this specific p-adic predicate  | *any* `P` with `1∈P`, `·`-closed | yes (in principle)  | The truly general statement abstracts the predicate to any submonoid-style `P` — but that abstraction **is** `Finset.prod_induction` / `Submonoid.prod_mem`, which mathlib already has. So the "more general form" is not a new lemma to upstream; it is the mathlib lemma this should call. |
| 5 | carrier `L` (`NormedField`)        | normed field                    | `CommMonoid`                     | yes                 | Nothing in the statement uses the norm/field structure; the underlying fact needs only `CommMonoid`. But weakening the carrier just reproduces `Finset.prod_induction`. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL in `ι`, `s`, `f`** for the *fixed* predicate
`ExtLogDomain p`. The only further generalisation (abstracting the predicate / weakening the
carrier to `CommMonoid`) does not yield a new mathlib lemma — it **is** the existing mathlib
lemma `Finset.prod_induction`. So this is not a "generalise-first" situation; it is a
"mathlib already has the general principle, compose with it" situation.
Number of weakening opportunities yielding a *new* upstreamable lemma: **0**.
Cost of restatement: n/a (no new statement to ship).

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
|  1 | "let X be a foo" preambles → typeclasses/instances? | no | — | The hypotheses are already typeclasses; nothing to convert. |
|  2 | sequences/metric → filters/topological? | no | — | No limiting/topological content; it's a finite-product algebra fact. |
|  3 | construct an object → universal-property class? | no | — | No object constructed. |
|  4 | set-with-closure-predicate → **bundled substructure type**? | **yes (but about the *def*, not this lemma)** | Bundle `ExtLogDomain p` as `extLogDomainSubmonoid : Submonoid L` (carrier = `{x | ExtLogDomain p x}`, `one_mem'` = the empty-case witness, `mul_mem'` = `ExtLogDomain.mul`). Then this lemma becomes `S.prod_mem` for free. | `Submonoid` lattice/quotient API; `Submonoid.prod_mem`, `list_prod_mem`, closure lemmas — all auto-available. |
|  5 | vector/metric/field-specific → weaker typeclass? | yes (carrier → `CommMonoid`) | covered in 4a row 5 | reproduces `Finset.prod_induction`. |
|  6 | 1-categorical → higher-categorical? | no | — | n/a. |
|  7 | concrete index (ℕ/ℤ/ℝ) → general additive/ordered? | no | — | Index is already arbitrary `ι`. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes, but it targets the *definition* `ExtLogDomain`, not this lemma.**
The genuine modernisation move would be to make `ExtLogDomain p` a **bundled `Submonoid L`**
(`one_mem'` + `mul_mem'` already exist as `inExpBall_one_sub_one`/the empty witness and
`ExtLogDomain.mul`). If that bundling were done, `ExtLogDomain.prod` would simply be
`Submonoid.prod_mem` and would not exist as a separate lemma at all.
  - Real mathematical improvement: it would give the domain mathlib's whole `Submonoid` API
    (intersections, closures, the lattice, `prod_mem`/`list_prod_mem`) instead of re-deriving
    each closure fact by hand.
  - Cost: MODERATE (a structure definition + re-pointing `extLog_mul`/`extLog_prod` at the bundled
    membership), and it is a **design decision about the project's `ExtLogDomain` definition**, not
    about this product lemma. Either way, the conclusion for *this lemma* is the same: it is
    redundant — either inline `Finset.prod_induction`, or (if bundled) use `Submonoid.prod_mem`.
  - This does **not** make `ExtLogDomain.prod` a `YES-but-generalise-first`: the "generalised"
    target is an existing mathlib lemma (`Submonoid.prod_mem` / `Finset.prod_induction`), so the
    verdict stays in the NO family.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `theorem`. (Theorems introduce no definitional equalities or
typeclass-search paths.)

---

### Mathlib search-status: `PadicLFunctions.ExtLogDomain.prod`

[A] Lean-Finder       (intended: "predicate closed under multiplication is closed under finite product")   n/a: Lean-Finder MCP tool not available in this environment.
[B] Loogle            (intended type pattern: `(∀ a b, ?p a → ?p b → ?p (a*b)) → ?p 1 → ?p (∏ _ ∈ _, _)`)   n/a: Loogle MCP tool not available; substituted by grep of mathlib source (method D below), which found the exact lemma.
[C] LeanSearch        (intended: "property holds on finite product if multiplicative and holds at one")     n/a: LeanSearch MCP tool not available; substituted by web search (Phase 3 #1/#3, which surfaced `prod_mem`).
[D] Grep mathlib src  `prod_induction`, `prod_mem`, `list_prod_mem`, `prod_mem_multiset` over `.lake/packages/mathlib/Mathlib/`   **HITS** (see below)
[E] Name pattern      grep for `Submonoid.prod_mem`, `SubmonoidClass … prod_mem`, `Finset.prod_induction` usages   **HITS**

Method [D]/[E] results (decisive):
- **`Finset.prod_induction`** — `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:600`:
  ```lean
  theorem prod_induction {M : Type*} [CommMonoid M] (f : ι → M) (p : M → Prop)
      (hom : ∀ a b, p a → p b → p (a * b)) (unit : p 1) (base : ∀ x ∈ s, p (f x)) :
      p (∏ x ∈ s, f x)
  ```
  This is *exactly* the principle `ExtLogDomain.prod` instantiates. Real mathlib usages of this
  exact pattern (predicate closed under `*` and at `1` ⟹ closed under `Finset.prod`):
  - `Finset.measurable_prod` / `Finset.measurable_fun_prod` — `Mathlib/MeasureTheory/Group/Arithmetic.lean:830,836`:
    `Finset.prod_induction _ _ (fun _ _ => Measurable.mul) measurable_one hf`
  - `Finset.prod_stronglyMeasurable` — `Mathlib/MeasureTheory/Function/StronglyMeasurable/Basic.lean:642`
  - `ContDiffWithinAt`/`ContMDiffAt` products — `Mathlib/Analysis/Calculus/ContDiff/Operations.lean:469`, `Mathlib/Geometry/Manifold/Algebra/Monoid.lean:347`
- **`Submonoid.prod_mem`** — `Mathlib/Algebra/Group/Submonoid/BigOperators.lean:140` (and the
  `SubmonoidClass` version at line 85): the bundled-substructure route, available if/when
  `ExtLogDomain` is made a `Submonoid`.

Searched for both:
  - the user's current form (`ExtLogDomain p`-specific) — not in mathlib (it is a project-local predicate; correctly so);
  - the literature-standard form (generic "closed under `·` + at `1` ⟹ closed under finite products") — **found**, as `Finset.prod_induction` (unbundled) and `Submonoid.prod_mem` (bundled).

Concluded: **"found the building blocks in mathlib: `Finset.prod_induction` (the exact closure
principle) + the project-local `ExtLogDomain.mul` (binary closure) + the unit witness already in
the proof. A 1-call composition yields the form."** (Not `NO-mathlib-has-it`, because mathlib
cannot have a lemma about the project's bespoke `ExtLogDomain` predicate — but it has the generic
principle that produces it in one call.)

---

### Call sites — `PadicLFunctions.ExtLogDomain.prod`

Internal use count: **1** (within the project, excluding the declaring lines).
External-to-file callers: **0** distinct files (the only use is inside `ExtLog.lean` itself).

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:424 | `extLog_mul p (hf i …) (ExtLogDomain.prod p s f hdom), ih hdom` — inside `extLog_prod`'s `insert` step |

Inline-derivation grep (was the equivalent re-derived elsewhere without `ExtLogDomain.prod`?):
  - (none) — no other file re-derives "domain closed under finite product"; the only consumer is
    `extLog_prod`, which legitimately needs the *membership* (`ExtLogDomain p (∏ …)`) to apply
    `extLog_mul` in its own induction.

What the pattern tells us (per the Phase 6.0.1 table): **K = 1 internal use only → possibly the
wrong abstraction; could be inlined; lean toward NO-composable.** Combined with the Phase 5
finding that the body is a single `Finset.prod_induction` call, this is a textbook
NO-composable-from-mathlib.

---

### Composition check (Phase 6)

Can `ExtLogDomain.prod` be derived from mathlib in ≤3 chained calls? **Yes — 1 call.**

Attempt 1 (term-mode, inlining the same unit witness the current empty-case uses):
```lean
theorem ExtLogDomain.prod {ι : Type*} (s : Finset ι) (f : ι → L)
    (hf : ∀ i ∈ s, ExtLogDomain p (f i)) : ExtLogDomain p (∏ i ∈ s, f i) :=
  Finset.prod_induction f (ExtLogDomain p) (fun _ _ => ExtLogDomain.mul p)
    ⟨1, 0, 1, one_pos, by rw [one_pow, zpow_zero, one_mul], inExpBall_one_sub_one p⟩ hf
```
  - Mathlib decls used: `Finset.prod_induction` (the only mathlib call).
  - Project decls reused: `ExtLogDomain.mul` (binary closure, already proved at line 386) and the
    `1`-membership witness `⟨1,0,1,one_pos,…,inExpBall_one_sub_one p⟩` (verbatim the current
    proof's `empty` case).
  - Result: **succeeds.** `L` is a `NormedField`, hence a `CommMonoid`, so `Finset.prod_induction`
    applies. The `hom` argument is `ExtLogDomain.mul p` η-expanded; the `unit` argument is the
    existing unit witness; `base` is `hf`.
  - This is precisely how mathlib proves the analogous `Finset.measurable_prod` /
    `Finset.prod_stronglyMeasurable` (same one-line `Finset.prod_induction _ _ (fun _ _ => _.mul) _one hf`).

Per the Phase 6b heuristics table, a single function call (`Finset.prod_induction …`) is a genuine
composition, not a proof in disguise — no `rw`/`ring_nf`/`aesop` glue is needed.

Conclusion: **COMPOSABLE** (1 mathlib call).

---

## Verdict: `PadicLFunctions.ExtLogDomain.prod`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): the statement is the textbook "multiplicatively-closed set
  containing `1` is closed under finite products, by induction from binary closure" — confirmed by
  WebSearch ×3 + nLab. The mathematics of the *file* (Iwasawa-branch `extLog`) is real, but *this
  lemma* is generic monoid plumbing, not that mathematics.
- Generality analysis (Phase 4): MAXIMALLY GENERAL in `ι`/`s`/`f`; the only further generalisation
  (abstract the predicate / weaken carrier to `CommMonoid`) **is** the existing mathlib lemma
  `Finset.prod_induction`, so 0 new upstreamable lemmas. Phase 4c notes a real modernisation
  (bundle `ExtLogDomain` as a `Submonoid`) but it targets the *definition* and still removes this
  lemma rather than upstreaming it.
- Mathlib search (Phase 5): found the building block `Finset.prod_induction`
  (`Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:600`), plus `Submonoid.prod_mem`
  (`.../Submonoid/BigOperators.lean:140`). Mathlib itself uses `Finset.prod_induction` in exactly
  this shape for `Measurable`/`StronglyMeasurable`/`ContDiff` products.
- Composition check (Phase 6): COMPOSABLE in **1** mathlib call; only **K = 1** internal call site.

**Rationale:**

`ExtLogDomain.prod` is not new mathematics — it is the universal "closed under `·` and at `1`
⟹ closed under `∏`" principle, specialised to the project's bespoke predicate `ExtLogDomain p`.
Mathlib already owns that principle as `Finset.prod_induction`, and uses it in precisely this
one-line idiom across measure theory and calculus (`Finset.measurable_prod`,
`Finset.prod_stronglyMeasurable`, `ContDiff` finite products). Because mathlib cannot host a lemma
about a downstream project's private predicate, the right move is not "upstream it" but "inline the
mathlib call": the whole proof collapses to
`Finset.prod_induction f (ExtLogDomain p) (fun _ _ => ExtLogDomain.mul p) ⟨unit-witness⟩ hf`,
reusing the already-proved binary closure `ExtLogDomain.mul` and the very unit witness the current
proof spells out in its empty case. The call-site evidence reinforces this: the lemma has exactly
one consumer (`extLog_prod`, line 424), so even keeping it as a named wrapper buys almost nothing.

There is a legitimate adjacent design question — whether `ExtLogDomain p` should be **bundled as a
`Submonoid L`** (its `one_mem'`/`mul_mem'` obligations are already discharged by the empty witness
and `ExtLogDomain.mul`). If the project does that, `ExtLogDomain.prod` becomes `S.prod_mem` and
again disappears. Either way the verdict for this declaration is the same: it does not belong in
mathlib, and locally it should be replaced by the one-line mathlib composition.

**WHY not (refactor-actionable):**
Mathlib has the building block `Finset.prod_induction`; `ExtLogDomain.prod` is a 1-call
composition of it with the project's own `ExtLogDomain.mul`. No new lemma is justified.

Mathlib building blocks:
- `Finset.prod_induction` — `.lake/packages/mathlib/Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean:600`
- (project) `PadicLFunctions.ExtLogDomain.mul` — `projects/PadicLFunctions/PadicLFunctions/ExtLog.lean:386`
- (project) unit witness `⟨1, 0, 1, one_pos, by rw [one_pow, zpow_zero, one_mul], inExpBall_one_sub_one p⟩` — already the `empty` case at lines 404–405.

Composition sketch (≤3 lines):
```lean
example {ι : Type*} (s : Finset ι) (f : ι → L) (hf : ∀ i ∈ s, ExtLogDomain p (f i)) :
    ExtLogDomain p (∏ i ∈ s, f i) :=
  Finset.prod_induction f (ExtLogDomain p) (fun _ _ => ExtLogDomain.mul p)
    ⟨1, 0, 1, one_pos, by rw [one_pow, zpow_zero, one_mul], inExpBall_one_sub_one p⟩ hf
```

Call sites in our project (from Phase 6.0): **K = 1** — `ExtLog.lean:424` (inside `extLog_prod`).

Refactor plan:
1. At the single call site (`ExtLog.lean:424`), the call `ExtLogDomain.prod p s f hdom` can stay
   as-is if the lemma is kept, **or** be replaced inline by the `Finset.prod_induction` composition
   above (it needs the same `s`, `f`, `hdom`).
2. Preferred minimal change: **shrink the proof of `ExtLogDomain.prod` itself** to the one-line
   `Finset.prod_induction` composition (delete the explicit `Finset.induction`), keeping the name
   for the single consumer. This is the smallest, lowest-risk edit and removes the hand-rolled
   induction.
3. Optional larger refactor (a separate design decision, not required by this verdict): bundle
   `ExtLogDomain p` as a `Submonoid L` and replace `ExtLogDomain.prod` with `Submonoid.prod_mem`,
   simultaneously simplifying `ExtLogDomain.mul`'s consumers.

Next action: do **not** upstream this to mathlib. Replace its body with the one-line
`Finset.prod_induction` composition (step 2) — or, if pursuing the `Submonoid` bundling, delete it
in favour of `Submonoid.prod_mem`.

---

## Next step

Do not open a mathlib PR. Inline the mathlib composition: rewrite `ExtLogDomain.prod`'s proof as the
single call `Finset.prod_induction f (ExtLogDomain p) (fun _ _ => ExtLogDomain.mul p) ⟨1,0,1,…⟩ hf`
(reusing the existing `empty`-case unit witness), or — as a separate design choice — bundle
`ExtLogDomain` as a `Submonoid L` and use `Submonoid.prod_mem`. Either way the standalone
hand-rolled induction is redundant with mathlib's `Finset.prod_induction`.
