# /mathlibable report — `EllSequence.rel₄_same₁₂`

> Step-9 (overview) mathlibable assessment, single declaration.
> Repo: `aintlib-main` · Project: `NagellLutz` (Nagell–Lutz / division polynomials / EDS).
> mathlib pin: `d90090f647ca` (lean `v4.31.0-rc2`).

---

### Baseline (Phase 0)
- lake build:               not run (local build stale per task); reasoning from source + upstream docs
- decl `EllSequence.rel₄_same₁₂`: ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:557`
- qualified name:           `EllSequence.rel₄_same₁₂`  (inside `namespace EllSequence`, opened at line 90; **VERIFIED** — matches the assumed name)
- kind:                     lemma (`theorem`-class; not a `def`)
- has sorry:                no
- module docstring summary: Elliptic divisibility sequences — defines EDS and constructs normalised EDSs (`normEDS`); a **fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence` extended with the new `addMulSub`/`rel₄`/`net`/`relFin4` "elliptic relation" algebra (copyright David Kurniadi Angdinata, the mathlib EDS author).

Exact source:
```lean
omit neg in
lemma rel₄_same₁₂ (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring
```
where the supporting definitions/lemmas (same file) are:
```lean
def addMulSub (m n : ℤ) : R := W ((m + n).tdiv 2) * W ((m - n).tdiv 2)         -- line 94
def rel₄ (a b c d : ℤ) : R :=                                                    -- line 103
  addMulSub W a b * addMulSub W c d
    - addMulSub W a c * addMulSub W b d + addMulSub W a d * addMulSub W b c
lemma addMulSub_same (zero : W 0 = 0) (m : ℤ) : addMulSub W m m = 0 := by ...    -- line 181
```
Context variable in scope: `(zero : W 0 = 0)` (line 547). `omit neg in` drops the odd-function hypothesis (unused here).

---

### Statement (Phase 1)

`EllSequence.rel₄_same₁₂` states: for a sequence `W : ℤ → R` over a commutative ring `R` with `W 0 = 0`, the four-index elliptic relation `rel₄ W` vanishes when its **second and third** indices coincide:
$$`\mathrm{rel}_4(W; m, n, n, s) = 0.`$$

Here `rel₄` is the alternating ("Plücker-/determinant-like") 3-term expression built from `addMulSub W m n = W(\lfloor (m+n)/2\rfloor)\,W(\lfloor (m-n)/2\rfloor)`:
$$`\mathrm{rel}_4(a,b,c,d) = b(a,b)\,b(c,d) - b(a,c)\,b(b,d) + b(a,d)\,b(b,c),\quad b(m,n):=\mathrm{addMulSub}(m,n).`$$
Since `addMulSub W m m = 0` whenever `W 0 = 0` (because `b(m,m)=W(0)\,W(0)`), setting `c=b` (here the 2nd/3rd index both `n`) makes the first and third products carry a factor `b(n,n)=0` and the middle product becomes `b(a,n)b(n,d)` against `+b(a,n)b(n,d)`… concretely the three terms cancel: this is the **diagonal-vanishing of an alternating form**.

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — the coefficient ring.
- `(W : ℤ → R)` — the sequence.
- `(m n s : ℤ)` — the three free indices (2nd and 3rd forced equal to `n`).

Hypotheses (Lean side):
- `(zero : W 0 = 0)` — the sequence vanishes at 0 (a defining EDS normalisation). This is the *only* hypothesis the proof uses (`neg` is `omit`-ted).

Conclusion (math): the alternating 4-index relation is zero on the `(m,n,n,s)` diagonal.
Conclusion (Lean): `rel₄ W m n n s = 0`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: a one-line helper lemma (a degenerate/diagonal case of `rel₄`), not a named theorem, not a `## Main statements` entry, not a new structure. It exists to feed the sorting argument in `rel₄_of_oddRec_evenRec`.

(Literature width run EXHAUSTIVE regardless, per skill.)

### One-line check (Phase 2b)

Kind is `lemma` (not `def`/`abbrev`/`structure`) → the def one-liner exemption machinery is **n/a**. Recorded as: this is a one-line *lemma*, a strong "helper not headline" signal that feeds Phase 6/7 (a lemma whose entire body is `simp_rw [rel₄, addMulSub_same W zero]; ring`).

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel | Query | Hit? | Standard form found | Notes |
|----|---------|-------|------|---------------------|-------|
| 1 | WebSearch (specific form) | "Stange elliptic nets four-index relation alternating vanishes equal indices division polynomial" | partial | elliptic nets generalise EDS (Stange 2008); net/relation polynomials | no source names the *diagonal-vanishing* as a theorem — it is treated as elementary |
| 2 | WebSearch (general/source form) | "elliptic divisibility sequence Mathlib rel₄ addMulSub EllSequence Angdinata" | yes | arXiv **2604.05280** "On Elliptic Sequences over Commutative Rings" (2026) — the paper behind THIS exact `rel₄`/`net`/`EllSequence` development | confirms the framework is new & being formalised; the diagonal case is an internal step |
| 3 | WebSearch (named-after / aliases) | "mathlib4 EllipticDivisibilitySequence rel4 net Stange elliptic net pull request" | partial | mathlib4 EDS docs (only `IsEllSequence`/`preNormEDS`/`normEDS`); Stange "Elliptic nets and elliptic curves" (0710.1316) | no PR/decl named `rel₄`; alternating-3-term form is Plücker-/Stange-standard but unnamed at this granularity |
| 4 | ChatGPT MCP | self-contained "is diagonal-vanishing of this rel₄ a named theorem; does mathlib have an alternating-vanishes-on-diagonal lemma" | **DOWN** | — | Codex MCP failed (environment, as warned). Compensated by channels 1–3, 6–10 and mathlib-source reasoning. |
| 5 | Local references | `ls projects/NagellLutz/.mathlib-quality/references/` | n/a | — | directory absent — recorded n/a |
| 6 | nLab | "alternating form vanishes on diagonal" / "alternating multilinear map" | yes (concept) | alternating ⇒ vanishes when two arguments agree; over a general ring *vanishing-on-diagonal* is the **primitive** (stronger) notion, antisymmetry is derived | confirms this is a definitional/elementary fact, not a citable theorem |
| 7 | nCatLab | (same as nLab) | n/a | — | not a distinct categorical concept here |
| 8 | Stacks Project | "alternating" / "determinant" diagonal vanishing | n/a | — | not an algebraic-geometry/scheme statement; the relevant fact is linear-algebra-elementary, not in Stacks at this grain |
| 9 | MathOverflow / Math.SE | "alternating form f(x,x)=0 vs antisymmetric characteristic 2" generality | yes (folklore) | over rings where 2 is a zero-divisor, "f(...,x,...,x,...)=0" is *defined* as alternating; it is the right primitive | matches the `tdiv`/`addMulSub_same` design choice in the file |
| 10 | recent arXiv (≤5 yr) | elliptic nets / division polynomials over commutative rings 2025–2026 | yes | 2604.05280 (source), 2503.15428, 2512.09601 — elliptic-net relations over general rings | the framework is current research; individual diagonal lemmas are never stated as results |

The protocol passed: WebSearch ran 3 distinct generality levels (specific / source / named-after); ChatGPT MCP attempted (down — documented); local refs n/a with reason; nLab/nCatLab/Stacks/MathOverflow/arXiv each checked with reason.

### Literature summary (Phase 3)

Concept identified as: the **diagonal-vanishing of the alternating four-index elliptic relation** `rel₄` (Stange-style elliptic-net relation; the alternating 3-term Plücker-like expression). Source development: arXiv 2604.05280, "On Elliptic Sequences over Commutative Rings" (Angdinata), of which `rel₄`/`net`/`relFin4_perm` are the Lean rendering.
Sources agree on the standard form: yes — `rel₄(a,b,c,d)=b(a,b)b(c,d)-b(a,c)b(b,d)+b(a,d)b(b,c)` is the alternating relation; the literature treats "two indices equal ⇒ 0" as an immediate definitional consequence (over a general ring, vanishing-on-diagonal is the primitive notion of *alternating*, which is exactly why the file builds `addMulSub_same` and uses `Int.tdiv`).
Most general standard form: for any `b : ℤ×ℤ → R` with `b(m,m)=0`, the determinant-like expression vanishes on any repeated index — pure (multi)linear-algebra triviality.
Generality dimensions where the literature varies: the *interesting* content is the full permutation-antisymmetry `relFin4_perm` and the recursion `rel₄_of_oddRec_evenRec`; the diagonal case is never an isolated named result.
Disagreement with the literature: none. The lemma is correct and standard; it simply is not the kind of statement the literature elevates to a named theorem.

---

### Generality analysis — `EllSequence.rel₄_same₁₂`

Literature-standard form (Phase 3): "an alternating form vanishes when two arguments coincide", instantiated at `rel₄`'s 2nd/3rd slots.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason |
|---|------------------------|-------------------|--------------------------|---------------------|--------|
| 1 | `[CommRing R]` | commutative ring | commutative ring (need `+`,`*`,`0`, and `addMulSub_same`) | NO (already minimal here) | `rel₄`/`addMulSub` are defined over `CommRing`; `ring` needs commutativity. Matches the whole file's base. |
| 2 | `(zero : W 0 = 0)` | `W 0 = 0` | the alternating/diagonal hypothesis | NO | this *is* the minimal hypothesis; it is precisely what makes `b(m,m)=0`. Cannot be weakened. |
| 3 | indices `(m n s : ℤ)` | three free integers, slot 2=slot 3 | the `(·, x, x, ·)` diagonal | NO | this is one of three sibling lemmas (`rel₄_same₀₁/₁₂/₂₃`) covering each adjacent diagonal; already at the natural grain. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL** (within its own API — no parameter can be weakened; it already lives over `CommRing` with only `W 0 = 0`).
Number of weakening opportunities found: 0.
Proposed restatement: none needed for generality.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Downstream |
|----|----------|----------|------------------------|------------|
| 1 | bundled hyp → typeclass? | no | `W 0 = 0` is a genuine per-sequence fact, not a typeclass | — |
| 2 | sequences/metric → filters/topology? | no | purely algebraic identity | — |
| 3 | construction → universal property? | no | it's an equation, not a construction | — |
| 4 | set+closure-pred → bundled substructure? | no | n/a | — |
| 5 | vector-space/field-specific → weaken typeclass? | no | already `CommRing`-level | — |
| 6 | 1-categorical → higher-categorical? | no | n/a | — |
| 7 | concrete index ℤ → general monoid? | **no (with note)** | `rel₄` is intrinsically ℤ-indexed (uses `(m±n).tdiv 2`, parity); generalising the index is not meaningful for EDS | — |

Real *modernisation* available here is at the **API level, not the lemma level**: the genuinely idiomatic move (not specific to this decl) would be to express `rel₄` as an honest `Mathlib`-style **alternating map** (`MultilinearMap`/`AlternatingMap`-flavoured), after which "vanishes on repeated index" would come *for free* from the general mathlib alternating-map API rather than from three hand-written `rel₄_same₀₁/₁₂/₂₃` lemmas. That is a redesign of the *whole* `rel₄` development, not a restatement of this one lemma — so it does not convert this decl into a YES-but-generalise; it reinforces that the lemma is scaffolding that a better abstraction would absorb.

### Modern-idiom verdict (Phase 4c)

Modern idiom available: no (for this single lemma). The only modernisation is the file-wide "make `rel₄` an alternating map" redesign, which would *delete* these helpers rather than restate them — recorded as context for Phase 7, not as a generalise-first target for `rel₄_same₁₂` itself.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (a `Prop`-valued proof; introduces no definitional equalities or typeclass-search paths).

---

### Mathlib search-status: `EllSequence.rel₄_same₁₂`

[A] Lean-Finder       — (no dedicated MCP available)        n/a: tool not present in this environment
[B] Loogle            `rel₄`, `addMulSub`, `?a*?b-?a*?c+?a*?d = 0`   no dedicated MCP; substituted by source grep [D]
[C] LeanSearch        "elliptic relation four index vanishes equal" via WebSearch on mathlib docs   no hits — concept absent from mathlib
[D] Grep mathlib src  `grep -rn "def rel₄\|def addMulSub\|rel₄_same\|EllSequence.rel₄" .lake/packages/mathlib/Mathlib/`   **no hits** — the entire `addMulSub`/`rel₄`/`net`/`relFin4`/`EllSequence` API is ABSENT from the pinned mathlib EDS file (which has only `IsEllSequence`/`preNormEDS`/`normEDS`/`complEDS₂`)
[E] Mathlib master docs | WebFetch of `mathlib4_docs/.../EllipticDivisibilitySequence.html` | **none of** `rel₄`, `addMulSub`, `EllSequence`, `rel₄_same₁₂`, `relFin4`, `net`, `Rel₃` appear — confirms absence from **current mathlib master**, not just the pin |

Searched for both:
- the user's form (`rel₄ W m n n s = 0`) — not in mathlib.
- the literature-standard form ("alternating form vanishes on diagonal") — mathlib *does* have the general principle for genuine alternating maps (`AlternatingMap.map_eq_zero_of_eq` and friends), but `rel₄` is **not** typed as an alternating map, so that lemma does not apply to it directly.

Concluded: **not in mathlib** (all available methods exhausted, plus the literature-standard form). The whole containing `rel₄` API is a new, not-yet-upstreamed development (arXiv 2604.05280); `rel₄_same₁₂` is an internal helper within it.

---

### Call sites — `EllSequence.rel₄_same₁₂`

Internal use count (NagellLutz `EllipticDivisibilitySequence.lean`, excluding the declaring line): **1**
- `EllipticDivisibilitySequence.lean:582` — inside `rel₄_of_oddRec_evenRec`: `by_cases h₂₁ : t (σ 2) = t (σ 1); · rw [h₂₁, rel₄_same₁₂ zero, smul_zero]` (the sorting/permutation argument: when the sorted indices collide in the middle slot, discharge via the diagonal-vanishing).

External-to-file callers: the other two grep hits are **duplicates of the same forked file**, not independent consumers:
| Caller file:line | Usage |
|------------------|-------|
| `projects/HasseWeil/.../Auxiliary/EllipticDivisibilitySequence.lean:499` | same `rw [h₂₁, rel₄_same₁₂ zero, smul_zero]` — a second copy of the identical fork |
| `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequenceOriginal.lean:557` | same usage — an `…Original.lean` copy of the same fork |

So across the whole repo the lemma has **exactly one genuine call site, replicated verbatim in three copies of one forked file**. No site uses it other than as the middle-collision branch of the same sorting proof.

Inline-derivation grep (was the equivalent re-derived elsewhere without `rel₄_same₁₂`?): (none) — but note `rel₄_same₀₁` (line 553) and `rel₄_same₂₃` (line 561) are its two siblings, each used once in the same `by_cases` cascade (lines 581, 583).

Call-sites signal: **K = 1** genuine internal use (the duplicates don't count), used purely as scaffolding for one proof. Per the skill's table, "K = 1 internal use only" leans toward NO-composable / could-be-inlined.

---

### Composition check (Phase 6)

Can `rel₄_same₁₂` be derived in ≤3 chained calls?

Attempt 1 (from the local `rel₄` API — its actual proof):
```lean
example (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring
```
- Decls used: `rel₄` (unfold), `addMulSub_same` (the `b(m,m)=0` workhorse), `ring`.
- Result: **succeeds** — this is verbatim the 1-line body.
- It is a 2-rewrite + `ring` composition over the *project-local* `rel₄`/`addMulSub_same`; carries no content beyond `addMulSub_same`.

Attempt 2 (from *mathlib* primitives directly): mathlib has the general "alternating map vanishes on repeated argument" lemma (`AlternatingMap.map_eq_zero_of_eq`), but `rel₄` is not an `AlternatingMap`, so mathlib's lemma does not fire without first building that abstraction.
- Result: **partial** — composable from mathlib *only after* the `rel₄`-as-alternating-map redesign (a whole-API change), not as a 1–3 call inline today.

Conclusion: **COMPOSABLE** from the local `rel₄` API in 2 calls + `ring`; **NOT-COMPOSABLE** from *mathlib-as-pinned* solely because `rel₄` itself is not yet in mathlib. The lemma adds nothing over `addMulSub_same` + `ring`.

---

## Verdict: `EllSequence.rel₄_same₁₂`

**Category:** `NO-composable-from-mathlib`

**Evidence:**
- Literature search (Phase 3): diagonal-vanishing of an alternating relation; never a named theorem; the only citable object is the *whole* `rel₄`/`relFin4_perm` framework (arXiv 2604.05280).
- Generality analysis (Phase 4): MAXIMALLY GENERAL in its own API; no weakening; the only "modernisation" is a file-wide alternating-map redesign that would *delete* this helper, not restate it.
- Mathlib search (Phase 5): not in mathlib (pin or master); the containing `rel₄` API is entirely absent upstream.
- Composition check (Phase 6): COMPOSABLE in 2 calls + `ring` over the local `rel₄`/`addMulSub_same`; carries no content beyond `addMulSub_same`.

**Rationale:**

`rel₄_same₁₂` is a one-line helper lemma — `simp_rw [rel₄, addMulSub_same W zero]; ring` — asserting the diagonal-vanishing of the alternating four-index relation `rel₄` at its middle slots. Mathematically it is the textbook "alternating form is zero when two arguments coincide", which the literature (and every channel searched) treats as an immediate definitional consequence, never a named result. It is one of three identical siblings (`rel₄_same₀₁/₁₂/₂₃`), each used exactly once, as the three collision branches of the `by_cases` cascade inside the single theorem `rel₄_of_oddRec_evenRec`. Across the entire repo it has one genuine call site, replicated only because the host file is forked into three copies (NagellLutz, HasseWeil, `…Original`). The honest classification is **NO-composable-from-mathlib**: relative to the project's own `rel₄`/`addMulSub_same` it is a 2-call-plus-`ring` inline with no independent content; it is "not in mathlib" only because the parent `rel₄` API is not in mathlib.

The competing reading is "this belongs to a coherent new API (the `rel₄` elliptic-relation algebra) that is itself plausibly mathlib-bound, so the helper should ride along." That is true but does **not** make *this declaration* a standalone mathlib contribution: it is scaffolding for `relFin4_perm`/`rel₄_of_oddRec_evenRec`, and the mathlib-idiomatic version of the whole development (typing `rel₄` as an `AlternatingMap`) would obtain "vanishes on a repeated index" for free from mathlib's existing alternating-map API and **delete** these three hand-written `rel₄_same` lemmas. So under either path the right home for this fact is "absorbed into the `rel₄` API", never "a standalone `feat` PR adding `rel₄_same₁₂`".

**WHY not (refactor-actionable):**
Mathlib has the building blocks for the *general* statement (`AlternatingMap.map_eq_zero_of_eq` for genuine alternating maps); relative to the *project's* API the proof is the 2-line composition above. No standalone lemma is warranted.
Building blocks / local primitives:
- `EllSequence.addMulSub_same` (`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:181`) — `addMulSub W m m = 0`.
- `EllSequence.rel₄` (def, line 103) — unfolded by `simp_rw`.
- `ring`.
- (mathlib general principle, applicable only post-redesign) `AlternatingMap.map_eq_zero_of_eq`.
Composition sketch (≤3 lines):
```lean
example (m n s : ℤ) : rel₄ W m n n s = 0 := by
  simp_rw [rel₄, addMulSub_same W zero]; ring
```
Call sites in the project (Phase 6.0): K = 1 genuine (`EllipticDivisibilitySequence.lean:582`), plus 2 fork-duplicate copies.
Refactor plan:
1. **Do not** PR `rel₄_same₁₂` to mathlib as a standalone lemma.
2. **Keep it as-is locally** as a named helper while the `rel₄` development lives in the project — it makes `rel₄_of_oddRec_evenRec` readable, and three explicit diagonal lemmas are clearer than three inline `simp_rw … ; ring` blocks. (Equivalently, the single call site at line 582 could inline `by simp_rw [rel₄, addMulSub_same W zero]; ring`, but the readability win is negligible and the helper is harmless.)
3. **When/if the `rel₄` API is upstreamed** (it accompanies arXiv 2604.05280 and is plausibly mathlib-bound), this fact should ride along *as part of that API* — preferably by typing `rel₄` as a mathlib `AlternatingMap` so that "vanishes on a repeated index" comes from `AlternatingMap.map_eq_zero_of_eq` and the three `rel₄_same*` lemmas disappear; or, if `rel₄` stays a bare `def`, the three `rel₄_same*` lemmas go in the same PR as `rel₄`/`relFin4_perm`, never as their own PR.

Next action: delete-or-inline is optional (harmless helper); do **not** open a standalone mathlib PR for `rel₄_same₁₂`. Its mathlib fate is bound to the parent `rel₄` API — assess `EllSequence.rel₄` / `EllSequence.relFin4_perm` (the real candidates) to decide the whole-development upstreaming, and let this helper follow that decision.

---

## Next step

Do not PR `rel₄_same₁₂` standalone. Keep it as a local helper (or inline its single use). Its upstreaming is bound to the parent `EllSequence.rel₄` API — run `/mathlibable` on `EllSequence.rel₄` and `EllSequence.relFin4_perm` to assess the *development as a whole*; if that API is upstreamed (ideally as a mathlib `AlternatingMap`), this diagonal fact rides along or is obtained for free from `AlternatingMap.map_eq_zero_of_eq`.
