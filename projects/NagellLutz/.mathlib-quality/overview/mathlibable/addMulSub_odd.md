# Mathlibable assessment: `EllSequence.addMulSub_odd`

**Verdict: YES-but-generalise-first**

- **Qualified name:** `EllSequence.addMulSub_odd` (verified from source)
- **Location:** `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:176`
- **Date:** 2026-06-18
- **Kind:** `lemma` (so Phase 4.5 diamond/defeq risk is n/a)
- **One-line summary:** the *odd-index evaluation lemma* for the project's building-block `def`
  `addMulSub` — it rewrites `addMulSub W (2m+1) (2n+1)` to the clean product `W(m+n+1)·W(m−n)`. It
  is genuine, reused API, but it is **scaffolding for the `EllSequence` elliptic-relation layer**
  and belongs in mathlib only **as part of upstreaming that whole layer** (the standing
  `normEDS satisfies IsEllDivSequence` TODO), inheriting the verdict of its parent `addMulSub`.

## Statement (verified from source)

```lean
namespace EllSequence
variable {R : Type u} [CommRing R] (W : ℤ → R)

/-- The expression `W((m+n)/2) * W((m-n)/2)` is the basic building block of elliptic relations,
where integers `m` and `n` should have the same parity. -/
def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)

lemma addMulSub_even (m n : ℤ) : addMulSub W (2 * m) (2 * n) = W (m + n) * W (m - n) := by
  simp_rw [addMulSub, ← left_distrib, ← mul_sub_left_distrib, Int.mul_tdiv_cancel_left _ two_ne_zero]

lemma addMulSub_odd (m n : ℤ) :
    addMulSub W (2 * m + 1) (2 * n + 1) = W (m + n + 1) * W (m - n) := by
  have h k := Int.mul_tdiv_cancel_left k two_ne_zero
  rw [addMulSub, ← h (m + n + 1), ← h (m - n)]; congr <;> ring
```

The parsed qualified name in the prompt (`EllSequence.addMulSub_odd`) is **correct**: the decl sits
inside `namespace EllSequence` (opened at line 90), and it is a `lemma`.

### Statement (Phase 1) — math prose

`addMulSub_odd` is the **odd-parity specialisation of the half-sum/half-difference building block**.
Recall `addMulSub W m n = W(⌊(m+n)/2⌋) · W(⌊(m−n)/2⌋)` (truncated division `Int.tdiv`). When both
indices are odd — written `2m+1` and `2n+1` — the two halved arguments become exact integers:
`((2m+1)+(2n+1))/2 = m+n+1` and `((2m+1)−(2n+1))/2 = m−n`. The lemma records this evaluation:

> For any commutative ring `R`, any sequence `W : ℤ → R`, and any integers `m, n`:
> `addMulSub W (2m+1) (2n+1) = W(m+n+1) · W(m−n)`.

It is the exact parity-sibling of `addMulSub_even` (line 173):
`addMulSub W (2m) (2n) = W(m+n) · W(m−n)`. Together these two lemmas convert the abbreviation
`addMulSub` into honest products of `W`-values whenever the (same-parity) indices are presented in
`2k` / `2k+1` normal form — which is exactly how the four-index relation `rel₄` is evaluated at
concrete indices.

- Parameters (Lean): `{R}` `[CommRing R]`, `W : ℤ → R`, `(m n : ℤ)`.
- Hypotheses: none (it is an unconditional rewrite, valid for every same-odd-parity pair).
- Conclusion (math): `addMulSub W (2m+1) (2n+1) = W(m+n+1)·W(m−n)`.
- Conclusion (Lean): `addMulSub W (2 * m + 1) (2 * n + 1) = W (m + n + 1) * W (m - n)`.

## Size classification (Phase 2a)

**SMALL.** It is a computational evaluation lemma about a helper `def` — not a new structure, not a
`## Main results` entry, not named after a person. (Literature width was still run EXHAUSTIVE.)

## One-line check (Phase 2b)

n/a — kind is `lemma`, not `def`/`abbrev`/`structure`. The body is a 2-line `rw`/`congr <;> ring`
proof, not a one-line definition. (Recorded for completeness; no exemption analysis needed.)

## 1./3. Literature search (EXHAUSTIVE protocol)

| #  | Channel                          | Query                                                                                               | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | `elliptic divisibility sequence W(m+n)W(m-n) addition formula Ward memoir`                            | yes  | the four-index recurrence `W_{m+n}W_{m−n}W_r²=…`     | Ward 1948; Wikipedia EDS. The *relation* is standard; the 2-arg helper is not named. |
|  2 | WebSearch (general / net form)   | `Stange elliptic nets addition formula building block W product four index relation`                  | yes  | net recurrence `W(p+q+s)W(p−q)W(r+s)W(r)+…=0`        | Stange 0710.1316. Products `W(p±q)` appear inside; no standalone "odd-index product" lemma. |
|  3 | WebSearch (named-after/aliases)  | `mathlib EllSequence addMulSub division polynomial Angdinata elliptic net formalization`              | no   | —                                                    | Only the group-law/division-polynomial formalisation surfaces; no `addMulSub`. |
|  4 | WebSearch (exact symbol)         | `"addMulSub" OR "addMulSub_odd" lean mathlib elliptic sequence`                                       | no   | —                                                    | Surfaced arXiv:2604.05280 *On Elliptic Sequences over Commutative Rings* (the companion paper). No symbol hit. |
|  5 | WebSearch (companion paper)      | `arXiv 2604.05280 "On Elliptic Sequences over Commutative Rings" addMulSub building block relation`   | partial | "elliptic relations" = symmetric quartic relations | Xu's paper underlies this dev; defines the relation algebra, not a named `addMulSub`/odd-index lemma. |
|  6 | ChatGPT MCP                      | (MCP down per environment note) — fallback: WebSearch #1–#5 + parent report `addMulSub.md`            | n/a  | covered by web + companion-paper reading             | MCP unavailable; literature triangulated from arXiv 2604.05280 / 0710.1316 + Ward + the sibling report. |
|  7 | Local references                 | `projects/NagellLutz/.mathlib-quality/references/` — directory absent                                 | n/a  | (no refs dir)                                        | Confirmed absent via `ls`. |
|  8 | nLab                             | "elliptic divisibility sequence" / "elliptic net"                                                    | n/a  | not an nLab topic at this granularity                | nLab has no EDS building-block page; not categorical. |
|  9 | nCatLab (if categorical)         | —                                                                                                   | n/a  | not a categorical concept                            | A ring-valued sequence identity; no categorical content. |
| 10 | Stacks Project (if alg geom)     | —                                                                                                   | n/a  | not a Stacks-style scheme/cohomology concept         | EDS arithmetic, outside Stacks scope. |
| 11 | MathOverflow / Math.StackExchange| "elliptic divisibility sequence even odd index formula"                                              | n/a  | discussion of the recurrence, not this helper        | No canonical "odd-index `addMulSub`" identity exists to cite. |
| 12 | recent arXiv (last 5 years)      | arXiv:2604.05280 (Xu, 2026), arXiv:2109.07050 (elliptic-net algorithm)                                | partial | the elliptic-relation algebra is the studied object | Confirms `rel₄`/`net` are canonical; the parity-evaluation lemma is formalisation glue. |

### Literature summary (Phase 3)

- Concept identified as: **odd-index evaluation of the half-sum/half-difference product** that is the
  atom of the elliptic-net / EDS four-index relation. The *relations* it feeds (`rel₄`, Stange's
  `net`, the three-index `Rel₃`) are **standard and canonical** (Ward 1948; Stange 0710.1316;
  Angdinata–Xu 2604.05280). The 2-argument helper `addMulSub`, and hence its parity-evaluation
  lemmas `addMulSub_even` / `addMulSub_odd`, are a **formalisation convenience** with no textbook
  name — they exist to discharge the `Int.tdiv`-halving bookkeeping so the relation lemmas read
  cleanly.
- Sources agree on the standard form of the *relation*: yes. On a named "odd-index product lemma":
  no such named object exists.
- Disagreement with the literature: none — the lemma is simply true index arithmetic; the literature
  just never isolates it as a citable statement.

**Takeaway:** the mathlib-bound *content* is the `EllSequence` relation layer (`rel₄`/`net` and
"`normEDS` is elliptic"); `addMulSub_odd` is one of the parity-evaluation steps internal to it.

## 4. Generality analysis

### 4a/4b. Generality status + verdict

| # | Parameter / hypothesis | Current Lean form        | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|--------------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]`         | commutative ring         | commutative ring / field | NO                  | `addMulSub` is a product of two `W`-values; `CommRing` is already the weakest sensible carrier (the companion paper 2604.05280 works over a general commutative ring). |
| 2 | `W : ℤ → R`            | arbitrary `ℤ`-sequence   | arbitrary sequence       | NO                  | No structure on `W` is used; fully general. |
| 3 | `(m n : ℤ)`            | arbitrary integers       | arbitrary integers       | NO                  | Holds for all `m, n`; the `2k+1` shape is the *content* (odd parity), not a restriction to weaken. |

**Verdict: MAXIMALLY GENERAL** in the assumption-weakening sense — `K = 0` weakenings. There is
nothing to strengthen: no typeclass to relax, no hypothesis to drop, indices already arbitrary.

The "generalise-first" label here is the **packaging** sense inherited from the parent `addMulSub.md`
(and sibling `isEllSequence_ψ.md`): the right *unit* to upstream is the elliptic-relation development,
not this lone parity-evaluation lemma in isolation.

### 4c. Modern-idiom check (Bourbaki 2.0)

| # | Question | Applies? | Note |
|---|----------|----------|------|
| 1 | "let X be a foo" → typeclass/instance? | no | already typeclass-driven (`CommRing`). |
| 2 | sequences/metric → filters/topology? | no | a finite ring identity; nothing to filter-ise. |
| 3 | construction → universal-property class? | no | it is an equation, not a construction. |
| 4 | set+closure-predicate → bundled substructure? | no | no substructure here. |
| 5 | vector-space/field-specific → weaken typeclasses? | no | already at `CommRing`, the right altitude. |
| 6 | 1-categorical → higher-categorical? | no | no categorical content. |
| 7 | concrete index (ℕ/ℤ/ℝ) → general additive structure? | no | `W` is *defined* on `ℤ` (an integer-indexed EDS); `ℤ`-indexing is intrinsic, and the `2k+1` form is the odd-parity content. The companion paper's generalisation is to *elliptic nets* `ℤⁿ → R`, but that is a different object (the parent layer), not a weakening of this scalar lemma. |

**Modern-idiom verdict:** no contemporary reformulation improves this lemma. It is already at the
right altitude (commutative-ring-valued integer sequence). The only "repackaging" is the granularity
point: ship it with the `EllSequence` layer, not alone.

## 4.5 Diamond / defeq risk

n/a — declaration kind is `lemma` (no definitional equalities or typeclass-search paths introduced).

## 5. Mathlib search (five methods) — forked files checked first

Per project context, NagellLutz **forks** `Mathlib.NumberTheory.EllipticDivisibilitySequence` and
`Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.*`, so the first question is whether this
lemma is already upstream. It is not.

```
[A] Lean-Finder       "odd index elliptic sequence product W(m+n+1) W(m-n)"   no hits (no such named lemma)
[B] Loogle            type pattern `addMulSub _ (2*_+1) (2*_+1) = _ * _`        n/a — `addMulSub` is not a mathlib symbol, so no mathlib type to match
[C] LeanSearch        "evaluate addMulSub at odd indices"                       no hits (concept absent upstream)
[D] Grep mathlib src  `addMulSub` / `addMulSub_odd` / `EllSequence` over .lake/packages/mathlib/Mathlib/**   ZERO hits
[E] Name pattern      `addMulSub_odd`, `addMulSub_even`, `_odd`/`_even` on EDS terms   no mathlib hit; the only hits are intra-AINTLIB
```

Searched for **both** forms:
- the user's current form (`addMulSub W (2m+1)(2n+1) = W(m+n+1)·W(m−n)`) — absent;
- the literature-standard *relation* it feeds (`rel₄` / Stange `net`) — also absent from mathlib (the
  upstream `EllipticDivisibilitySequence.lean` stops at `normEDS`/`complEDS`/`*Rec`/`map_*` and has
  **no `EllSequence` namespace**; it still carries the open TODO *"prove that `normEDS` satisfies
  `IsEllDivSequence`"*, which is exactly the work this layer discharges).

Cross-check on the building block used in the proof: `Int.mul_tdiv_cancel_left` (the one nontrivial
lemma in the proof) lives in Lean **core** (`Init.Data.Int.DivMod`, imported at line 8) — so it does
not appear under `.lake/packages/`, but it exists and is the right primitive.

**Concluded:** *not in mathlib* — all five methods exhausted, plus the literature-standard relation
form. The whole `EllSequence` layer (incl. `addMulSub`, `addMulSub_even`, `addMulSub_odd`, `rel₄`,
`net`) is new, not yet upstream.

## 6. Composition check (+ call-sites)

### 6.0. Call sites of `addMulSub_odd`

Internal use count (NagellLutz `LutzNagell/`, excluding the declaring file and the `…Original.lean`
fork): the lemma is used **inside its own declaring file** at lines 377–378, within
`rel₄_iff_evenRec` (`rw [… rel₄, addMulSub_odd, addMulSub_odd, addMulSub_odd, addMulSub_odd,
addMulSub_odd, addMulSub_odd]`). It is also used across the repo in the **HasseWeil** sibling project.

| Caller file:line                                                              | Usage pattern (one-line excerpt)                                  |
|-------------------------------------------------------------------------------|-------------------------------------------------------------------|
| `LutzNagell/EllipticDivisibilitySequence.lean:377` (same file)                | `rw [iff_comm, EvenRec, … rel₄, addMulSub_odd, addMulSub_odd, …]`  |
| `LutzNagell/EllipticDivisibilitySequence.lean:378` (same file, cont.)         | `addMulSub_odd, addMulSub_odd, addMulSub_odd, addMulSub_odd]`      |
| `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:297`                   | `have h := addMulSub_odd (W := W) 1 0; norm_num at h; exact h`     |
| `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:299`                   | `have h := addMulSub_odd (W := W) k 1`                             |
| `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:303`                   | `have h := addMulSub_odd (W := W) k 0; norm_num at h; exact h`     |
| `HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:304`                   | `simp only [rel₄, addMulSub_odd, e₃₁, e₃, e₁]`                     |
| `LutzNagell/EllipticDivisibilitySequenceOriginal.lean:358` (intra-repo fork)  | `simp_rw [rel₄, addMulSub_odd]; ring_nf; simp only [Nat.rawCast]`  |

Inline-derivation grep (was the same evaluation re-derived without `addMulSub_odd`?): the parity twin
`addMulSub_even` is always used **alongside** it for the even branch; no site re-derives the odd
evaluation by hand. **Signal: real, reused API** (≥3 distinct uses, including cross-project in
HasseWeil), not dead code and not a bypassed wrapper. This reinforces the YES-family leaning — the
lemma earns its name.

### 6a. Composition attempt (≤3 mathlib calls)

Can `addMulSub_odd` be derived from *mathlib* in ≤3 chained mathlib calls? No — because its statement
is **about the project's own `addMulSub`**, a symbol that does not exist in mathlib. There is no
mathlib decl to compose against. (Its *proof* is short — `rw [addMulSub]` then two applications of the
core lemma `Int.mul_tdiv_cancel_left` and `congr <;> ring` — but that is a proof of a statement over a
project-local definition, not a composition of mathlib results yielding a mathlib-expressible fact.)

**Conclusion: NOT-COMPOSABLE** (in the mathlib sense — the statement is not even expressible without
first having `addMulSub` upstream). This rules out NO-composable-from-mathlib.

## 7. Verdict

## Verdict: `EllSequence.addMulSub_odd`

**Category: YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): the elliptic-net / EDS four-index relation is canonical (Ward 1948;
  Stange 0710.1316; Angdinata–Xu 2604.05280), but the half-sum/half-difference helper `addMulSub` and
  its parity-evaluation lemmas are unnamed formalisation glue — no standalone citation.
- Generality analysis (Phase 4): MAXIMALLY GENERAL (`CommRing`, arbitrary `W`, arbitrary `m,n`;
  `K = 0` weakenings); no modern-idiom reformulation improves it.
- Mathlib search (Phase 5): *not in mathlib* — zero grep hits for `addMulSub`/`EllSequence`; upstream
  `EllipticDivisibilitySequence.lean` lacks the whole relation layer and still carries the
  `normEDS`-is-elliptic TODO.
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (statement is about the project-local
  `addMulSub`, absent upstream); call-sites show real reuse (in-file + cross-project HasseWeil).

**Rationale.** `addMulSub_odd` is true, maximally general, genuinely reused (≥3 sites, incl.
cross-project), and absent from mathlib — so it is neither NO-mathlib-has-it nor (in the mathlib
sense) NO-composable-from-mathlib. But it is **not the right unit to ship on its own**: it is a
parity-evaluation lemma for the helper `def addMulSub`, whose own assessment (`addMulSub.md`, same
directory) is **YES-but-generalise-first → upstream as part of the `EllSequence` relation layer**.
Per the verdict-inheritance/re-aim rule, a lemma whose statement is *about* a parent def that is
itself "ship only with its layer" inherits that packaging verdict: `addMulSub_odd` belongs in
mathlib **inside the same PR** that introduces `addMulSub`, `addMulSub_even`, `rel₄`, `net`, and
culminates in "`normEDS` is an `IsEllSequence` / `IsEllDivSequence`" — closing the standing upstream
TODO. It should travel as the named odd-index simp/rewrite lemma for `addMulSub`, paired with its
even twin, not as an independent public declaration assessed alone.

Note: the "generalise-first" here is **packaging/repackaging**, not assumption-weakening — Phase 4b
found nothing to weaken. The action is *re-grain to the layer*, not *re-prove more generally*. (Cost
is not invoked as a downgrade reason; this is not a BORDERLINE cost punt.)

**Reason for the generalisation:** MODERN-IDIOM / packaging — the correct mathlib unit is the
`EllSequence` elliptic-relation layer, of which this is an internal evaluation lemma; shipping it
standalone is the wrong granularity (it is meaningless without `addMulSub` and `rel₄`/`net`).

**Proposed restatement / re-grain (no statement change to the lemma itself):**
```lean
-- Upstream as part of the EllSequence layer in
-- Mathlib/NumberTheory/EllipticDivisibilitySequence.lean, paired with addMulSub_even:
namespace EllSequence
variable {R : Type*} [CommRing R] (W : ℤ → R)

def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)

@[simp] lemma addMulSub_even (m n : ℤ) :
    addMulSub W (2 * m) (2 * n) = W (m + n) * W (m - n) := …

@[simp] lemma addMulSub_odd (m n : ℤ) :          -- ← this lemma, unchanged
    addMulSub W (2 * m + 1) (2 * n + 1) = W (m + n + 1) * W (m - n) := …
end EllSequence
```
Estimated cost of re-graining: **CHEAP** (mechanical — it moves verbatim with the layer; the proof is
already a 2-line core-lemma rewrite).

**Mathlib downstream this enables (as part of the layer):** the parity-evaluation pair
(`addMulSub_even`/`addMulSub_odd`) is what lets `rel₄`/`net` be reduced to explicit `W`-products at
concrete same-parity indices — the mechanism behind `rel₄_iff_evenRec` (line 377) and the HasseWeil
EDS-recurrence proofs (lines 297–304), and ultimately behind discharging the upstream
`normEDS satisfies IsEllDivSequence` TODO in
`Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.

**Next action:** run `/generalise EllSequence.addMulSub` (the parent) first; this lemma rides along in
the same upstreaming PR as the named odd-index rewrite. Do **not** open a standalone PR for
`addMulSub_odd`. Also resolve the intra-AINTLIB triplication (HasseWeil + `…Original.lean`) via
`/cleanup` before upstreaming.

### Verdict-gate self-check
- Not NO-mathlib-has-it: Phase 5 = "not in mathlib" (no decl to cite). ✓ gate ok.
- Not NO-composable: Phase 6 = NOT-COMPOSABLE (statement not mathlib-expressible). ✓ gate ok.
- Not YES-add-as-is: Phase 4b MAXIMALLY GENERAL, but granularity is wrong (internal evaluation lemma
  for a def whose own verdict is "ship with the layer") → YES-but-generalise-first per inheritance. ✓
- YES-but-generalise-first: restatement target given (the layer); reason = MODERN-IDIOM/packaging with
  concrete downstream (`rel₄_iff_evenRec`, HasseWeil recurrences, the `normEDS`-is-elliptic TODO). ✓
- Call-sites table present (≥1 row per caller, inline-derivation grep filled). ✓
- Cost not used as a downgrade reason. ✓

## Notes / cross-refs

- Parent def assessment (drives the inherited verdict): `addMulSub.md` (same directory) —
  **YES-but-generalise-first**, "upstream as part of the `EllSequence` layer; closes the
  `normEDS`-is-elliptic TODO."
- Even twin: `addMulSub_even` (line 173) — same packaging verdict; the two ship together.
- Upstream mathlib EDS file (no `EllSequence` layer; open TODOs):
  `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`.
- Intra-AINTLIB duplicates (a `/cleanup` dedup chore, **not** mathlibability):
  `projects/HasseWeil/HasseWeil/Auxiliary/EllipticDivisibilitySequence.lean:104`,
  `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:168`.
- Build/env note: local Lean build is stale (could not run `lake build`/`#synth`); assessment reasons
  from the source statement + grep over the pinned mathlib checkout + live web. ChatGPT MCP was down;
  literature triangulated via WebSearch + the companion paper arXiv:2604.05280 + the sibling reports.

## Sources

- Ward, *Memoir on Elliptic Divisibility Sequences*, Amer. J. Math. 70 (1948) 31–74 —
  https://www.sciepub.com/reference/247378
- Stange, *Elliptic nets and elliptic curves* — https://arxiv.org/abs/0710.1316
- Angdinata–Xu, *On Elliptic Sequences over Commutative Rings* — https://arxiv.org/pdf/2604.05280
- *Elliptic divisibility sequence* (four-index recurrence) —
  https://en.wikipedia.org/wiki/Elliptic_divisibility_sequence
- Mathlib4 docs, `Mathlib.NumberTheory.EllipticDivisibilitySequence` (open TODOs; no `EllSequence`
  layer) —
  https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/EllipticDivisibilitySequence.html
