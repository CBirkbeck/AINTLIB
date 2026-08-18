# /mathlibable report — `EllSequence.net_eq_rel₄`

> Step-9 mathlibable assessment (NagellLutz project). Single declaration.
> Local Lean build is stale; verdict reasoned from source + literature + mathlib-source grep.

### Baseline (Phase 0)
- lake build:                stale (not run; reasoned from source per task constraints)
- decl `EllSequence.net_eq_rel₄`:  ✓ resolved at `projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:121`
- kind:                      lemma
- has sorry:                 no
- module docstring summary:  Elliptic divisibility sequences (EDS); defines EDS and constructs normalised EDSs from initial terms. **Extended fork** of `Mathlib.NumberTheory.EllipticDivisibilitySequence` — adds Stange elliptic-net / four-index-relation API (`addMulSub`, `rel₄`, `net`, `invarNum`, …) absent from mathlib.

Namespace confirmed: the decl sits inside `namespace EllSequence` (opened line 90), so the qualified name is **`EllSequence.net_eq_rel₄`**.

---

### Statement (Phase 1)

`EllSequence.net_eq_rel₄` is a **theorem** (algebraic identity) stating:

> For a sequence `W : ℤ → R` into a commutative ring `R` and any integers `p, q, r, s`, Stange's elliptic-net recurrence value `net W p q r s` equals the symmetric four-index relation `rel₄ W` evaluated at the affine-reindexed arguments `(2p+s, 2q+s, 2r+s, s)`.

Here (all defined in the same file):
- `addMulSub W m n := W ((m+n).tdiv 2) * W ((m-n).tdiv 2)` — the building block `A(m,n) = W((m+n)/2)·W((m-n)/2)` (truncated division so it behaves well off the equal-parity locus).
- `rel₄ W a b c d := A(a,b)·A(c,d) − A(a,c)·A(b,d) + A(a,d)·A(b,c)` — the symmetric four-index relation, the three partitions of `{a,b,c,d}` into two pairs.
- `net W p q r s := W(p+q+s)W(p−q)W(r+s)W(r) − W(p+r+s)W(p−r)W(q+s)W(q) + W(q+r+s)W(q−r)W(p+s)W(p)` — Stange's elliptic-net defining polynomial (docstring: "The defining property of Stange's elliptic nets ... two signs are swapped compared to Stange's paper to make the equivalence with elliptic relations unconditional").

Variables / typeclasses (Lean side):
- `{R : Type u} [CommRing R]` — arbitrary commutative ring.
- `(W : ℤ → R)` — the sequence (implicit in the lemma via `variable {W}`).
- `{p q r s : ℤ}` — the four integer indices.

Hypotheses: **none** (no `W 0 = 0`, no oddness, no parity condition).

Conclusion (math): `net(p,q,r,s) = rel₄(2p+s, 2q+s, 2r+s, s)`.
Conclusion (Lean): `net W p q r s = rel₄ W (2 * p + s) (2 * q + s) (2 * r + s) s`.

Proof: `simp_rw [net, rel₄, addMulSub, …, Int.mul_tdiv_cancel_left _ two_ne_zero]; ring` — i.e. unfold both sides and close by ring arithmetic. **Pure polynomial identity in the values of `W`.**

---

### Size classification (Phase 2a)

Verdict: **SMALL** (leans BIG-adjacent).
Reason: It is a helper/bridge lemma, not a `## Main statement`. But it is *foundational* — it is the identity that ties Stange's `net` form to the symmetric `rel₄` form and lets the entire `rel₄` symmetry theory (`rel₄_transf`, permutation invariance, recurrence equivalences) transfer to `net`. Its mathlibability is **contingent on its two parent defs `net` and `rel₄` being mathlib-bound** (a bridge between two project-local defs only belongs in mathlib if both defs do).

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Body line count: 2 substantive lines (a `simp_rw` list + `ring`).
One-liner verdict: **n/a — kind is `lemma`/theorem, not `def`.** The one-liner penalty applies to `def`/`abbrev`/`structure`, not to proof terms. Skipped.

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                   | Hit? | Standard form found | Notes |
|----|----------------------------------|---------------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | Stange elliptic nets definition net polynomial four-index elliptic relation                             | yes  | `W(p+q+s)W(p−q)W(r+s)W(r) + … = 0` — **exactly the project's `net`** | Stange, *Elliptic nets and elliptic curves*, arXiv 0710.1316; the rank-1 net recurrence |
| 2  | WebSearch (general / Ward form)  | EDS Ward recurrence "W(m+n)W(m−n)" three-term / four-term relation                                       | yes  | Ward symmetric 3-term `W_{h−m}W_{h+m}W_n² + … = 0`; 4-term specialisations | Wikipedia EDS; Ward 1948. The `rel₄`/`net` 4-index relation is the homogenised four-index version |
| 3  | WebSearch (partition / pairs)    | elliptic net "three partitions" four indices "two pairs" symmetric relation                              | yes  | "four factors … three ways to partition into two pairs" — **exactly `rel₄`** | Surfaced Xu, *On Elliptic Sequences over Commutative Rings*, arXiv 2604.05280; Stange formulary |
| 4  | ChatGPT MCP                      | Is `net = rel₄∘reindex` a pure ring identity / standard bridge? generality?                              | n/a  | — | **MCP/Codex down** (command failed twice); compensated by reading the proof body (`simp_rw … ; ring`, no `W` hyps ⇒ pure ring identity) + channels 1–3,6,9 |
| 5  | Local references                 | grep `projects/NagellLutz/.mathlib-quality/references/` and `refs/`                                     | n/a  | (no references dir present for this project) | recorded n/a |
| 6  | nLab                             | elliptic divisibility sequence / elliptic net recurrence                                                | yes (weak) | EDS = integer recurrence from division polynomials; nets = higher-dim generalisation | no dedicated nLab page; concept confirmed via arXiv mirrors. Not a categorical concept |
| 7  | nCatLab (if categorical)         | —                                                                                                       | n/a  | — | not a categorical concept |
| 8  | Stacks Project (if alg geom)     | —                                                                                                       | n/a  | — | not in scope; Stacks has no EDS/elliptic-net recurrence material |
| 9  | MathOverflow / arXiv             | "On Elliptic Sequences over Commutative Rings" + Angdinata/Xu formalisation                              | yes  | **elliptic sequences over a commutative ring; 4-parameter symmetric homogeneous quartic "elliptic relations"** | **Xu, arXiv 2604.05280 (2026)** — defines exactly `rel₄`-style relations over `CommRing`; Xu+Angdinata are the mathlib group-law / EDS authors. This is the upstream reference the file follows |
| 10 | recent arXiv (last 5 yrs)        | elliptic net algorithm / recurrence over rings                                                          | yes  | confirms net-vs-partition transformation rules (product invariant under repartition) | arXiv 2109.07050 (Elliptic Net Algorithm Revisited); 2102.07573; 2503.15428 |

The protocol passes: ≥3 WebSearch queries at different generality levels (specific Stange net form, general Ward relation, partition form); ChatGPT MCP attempted (down — substituted by direct proof-body analysis); local refs checked (absent → n/a); nLab checked; Stacks/nCatLab recorded n/a with reason; MathOverflow/arXiv hit (the load-bearing Xu reference).

### Literature summary (Phase 3)

Concept identified as: the **four-index elliptic / elliptic-net defining relation**, in two literature-standard guises — (A) **Stange's net recurrence** (`net`, arXiv 0710.1316) and (B) the **symmetric "three partitions into two pairs" elliptic relation** (`rel₄`, Ward-style; formalised over commutative rings in Xu arXiv 2604.05280).

Sources agree on the standard form: yes. Stange's net relation and the symmetric four-index relation are both well-established; the affine reindexing connecting them (`a=2p+s, b=2q+s, c=2r+s, d=s`, equivalently `net W p q r s = rel₄ W` at those args) is exactly the "transformation rule" the literature describes ("one partition transforms four factors … leaving the product invariant", arXiv 2503.15428 / formulary).

Most general standard form: stated over an **arbitrary commutative ring** `R` for `W : ℤ → R` (Xu 2604.05280 is explicitly "over commutative rings"). No oddness / `W(0)=0` needed for the *identity* itself (those enter only the divisibility/EDS half).

Generality dimensions where the literature varies:
  - **coefficient ring**: ℤ (classical Ward/Stange) → integral domain → field → **arbitrary commutative ring** (the most general; Xu's setting, and the file's setting). The file is at the maximum.
  - **index group**: ℤ (rank 1 / EDS) → ℤⁿ (general elliptic nets). The file is rank-1 (`net : ℤ→ℤ→ℤ→ℤ→R`), matching EDS scope; the ℤⁿ generalisation is a *separate, larger* development, not a weakening of this lemma.

Disagreement with the literature: none. The file deliberately swaps two signs vs. Stange's paper so the `net`↔`rel₄` equivalence is **unconditional** (docstring) — a formalisation-quality choice, not a deviation from the math.

---

### Generality analysis — `EllSequence.net_eq_rel₄`

Literature-standard form (Phase 3): the identity holds for `W : ℤ → R` over any commutative ring, with no constraints on `W`.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|------------------------|-------------------|--------------------------|---------------------|----------------------------------|
| 1 | `[CommRing R]` | arbitrary comm. ring | arbitrary comm. ring (Xu 2604.05280) | NO | `ring` needs commutativity + subtraction; `net`/`rel₄` are differences of products. `CommRing` is the natural floor. Could in principle be `CommRing`→`CommRing` only (no Field/Domain assumed — already maximal). Dropping to `CommSemiring` fails: both sides contain genuine subtractions. |
| 2 | `(W : ℤ → R)` | sequence on ℤ | sequence on ℤ (rank-1 net / EDS) | NO (not a weakening) | The ℤⁿ generalisation is a *different, larger* object; it does not weaken this lemma's hypotheses. |
| 3 | indices `{p q r s : ℤ}` | four integers | four integers | NO | intrinsic to a four-index relation |
| 4 | constraints on `W` | **none** | none (for the identity) | already none | The lemma is hypothesis-free — strictly stronger than any version gated on `W(0)=0`/oddness. Maximal. |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL.**
Number of weakening opportunities found: 0. `[CommRing R]`, `W : ℤ → R`, zero hypotheses on `W` — this is exactly the generality at which Xu (arXiv 2604.05280) states elliptic relations over commutative rings, and the hypothesis-free identity is strictly stronger than any `W(0)=0`-gated variant. No restatement needed.
Cost of restatement: n/a.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | "let W be a foo" → typeclass/instance? | no | — | `W` is a plain function argument; `IsEllSequence`/`Rel₃` already carry the predicate side. No bundling gain for this *identity*. |
| 2  | sequences/metric → filters/topology? | no | — | finite algebraic identity; no limit/topology content |
| 3  | construction → universal property? | no | — | it is an equation between two explicit polynomials, not a construction |
| 4  | set-with-closure → bundled substructure? | no | — | no substructure |
| 5  | vector-space/field-specific → module/(semi)ring weakening? | no | — | already at `CommRing`, the relevant floor |
| 6  | 1-categorical → higher-categorical? | no | — | not categorical |
| 7  | concrete index ℕ/ℤ/ℝ → general additive group/monoid? | **partially (out of scope)** | the ℤⁿ elliptic-net generalisation indexes by a f.g. free abelian group | This is the genuine future generalisation (Stange's full nets). But it is a *separate development*, not a restatement of this rank-1 lemma; it does not flip the verdict and is not "generalise first" for *this* decl. |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **no** (for this decl as scoped).
One-line reason: it is a hypothesis-free finite ring identity already at the maximal `CommRing` generality; the only "more general" object (ℤⁿ nets) is a separate larger formalisation, not an idiomatic restatement of this rank-1 identity.

---

### Diamond / defeq risk (Phase 4.5)

n/a — declaration kind is `lemma` (a proof of a `Prop`/equation). No definitional equalities or typeclass-search paths introduced. Skipped.

---

### Mathlib search-status: `EllSequence.net_eq_rel₄`

[A] Lean-Finder       (index unavailable locally; substituted by grep over mathlib source)  n/a
[B] Loogle            pattern `net _ _ _ _ = rel₄ _ _ _ _` / `EllSequence.*`                no hits (names absent from mathlib)
[C] LeanSearch        "Stange net equals symmetric four-index elliptic relation"            no hits
[D] Grep mathlib src  `def net` / `rel₄` / `addMulSub` / `Stange` / `EllSequence` / `net_eq_rel` over `.lake/packages/mathlib/Mathlib/`  **no hits** (all "net" matches are topological nets, ε-nets, or `kerodon.net`/`mathoverflow.net` URLs — unrelated)
[E] Name pattern      grep `net_eq_rel₄`, `namespace EllSequence` in mathlib                **no hits**

Searched for both:
  - the user's current form (`net = rel₄ ∘ reindex`) — absent.
  - the literature-standard forms — mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (547 lines) has `IsEllSequence`, `IsDivSequence`, `IsEllDivSequence`, `preNormEDS`, `normEDS`, the `*.smul` lemmas — and **explicitly lists as a TODO** (line 44) "prove that `normEDS` satisfies `IsEllDivSequence`". It has **none** of `net`/`rel₄`/`addMulSub`/`invarNum`/the four-index relation machinery. `Mathlib/AlgebraicGeometry/EllipticCurve/DivisionPolynomial/{Basic,Degree}.lean` likewise have no `net`/`rel₄`.

Concluded: **not in mathlib** (all methods exhausted, plus both literature-standard forms). The `net`/`rel₄` API and this bridge lemma appear in exactly three project files (`NagellLutz/…/EllipticDivisibilitySequence.lean`, its `…Original.lean`, and `HasseWeil/…/EllipticDivisibilitySequence.lean`) and **zero** mathlib files.

---

### Call sites — `EllSequence.net_eq_rel₄`

Internal use count: **3** within the NagellLutz current file (excluding the declaring line 121), all external to the declaring lemma.
External-to-file callers: the same lemma is independently re-declared (not imported) in 2 sibling files (`…Original.lean`, HasseWeil), each with its own call sites — evidence the lemma is a genuine, repeatedly-needed primitive across the EDS forks.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `…/EllipticDivisibilitySequence.lean:224` | `rw [net_eq_rel₄, h, h, h]; …` — inside `HaveSameParity₄.rel₄_eq_net` (the *inverse* bridge `rel₄ = net ∘ reindex`) |
| `…/EllipticDivisibilitySequence.lean:695` | `rw [net_eq_rel₄]` — rewriting a `net` goal into `rel₄` form to apply the relation theory |
| `…/EllipticDivisibilitySequence.lean:1170` | `simp_rw [net_eq_rel₄, map_rel₄]` — inside `map_net`, transporting `net` across a ring hom via the already-proven `map_rel₄` |

Inline-derivation grep (was the equivalent re-derived inline elsewhere without using `net_eq_rel₄`?): none — every `net ↔ rel₄` transit in the file routes through this lemma. It is the single chokepoint connecting the two formulations.

Call-sites signal: **K = 3 internal uses, no inline re-derivation ⇒ real API; consumers depend on it** → YES-* leaning.

---

### Composition check (Phase 6)

Can `EllSequence.net_eq_rel₄` be derived from mathlib in ≤3 chained calls?

Attempt 1: any mathlib lemma relating `net` and `rel₄`.
  - Mathlib decls used: none exist — mathlib has neither `net` nor `rel₄` nor `addMulSub`.
  - Result: **fails.** There is nothing in mathlib to compose; both sides of the identity are project-defined.

Conclusion: **NOT-COMPOSABLE.** (The proof is `simp_rw`-unfold-then-`ring` over *project* definitions; it is not a composition of mathlib primitives — it is the defining bridge between two project notions mathlib does not yet have.)

---

## Verdict: `EllSequence.net_eq_rel₄`

**Category:** YES-add-as-is

**Evidence:**
- Literature search (Phase 3): `net` = Stange's elliptic-net recurrence (arXiv 0710.1316); `rel₄` = symmetric "three partitions into two pairs" elliptic relation over commutative rings (Xu arXiv 2604.05280). The `net`↔`rel₄` reindexing is the literature's standard transformation rule. Hypothesis-free pure ring identity.
- Generality analysis (Phase 4): **MAXIMALLY GENERAL** — `[CommRing R]`, `W : ℤ → R`, zero hypotheses on `W`. Phase 4c: no modern-idiom restatement (already at the `CommRing` floor; ℤⁿ nets are a separate development).
- Mathlib search (Phase 5): **not in mathlib** — mathlib's EDS file lacks the entire `net`/`rel₄` API and lists the downstream goal (`normEDS` is an EDS) as a TODO.
- Composition check (Phase 6): **NOT-COMPOSABLE** — both sides are project-defined; nothing in mathlib to compose.

**Rationale:**

`net_eq_rel₄` is the foundational identity bridging the two literature-standard formulations of the four-index elliptic-net defining relation: Stange's net-recurrence form (`net`) and the symmetric three-partition form (`rel₄`). It is mathematically real (not bookkeeping in the pejorative sense): it is the chokepoint through which the entire `rel₄` symmetry/permutation/recurrence theory (`rel₄_transf`, `HaveSameParity₄.perm`, the `Rel₃`/`EvenRec` equivalences) is transported onto Stange's `net`, and through which `net` is shown to commute with ring homomorphisms (`map_net` via `map_rel₄`). It is stated at maximal generality — an arbitrary commutative ring, no constraints on `W` — exactly matching the generality of Junyan Xu's "elliptic sequences over commutative rings" (arXiv 2604.05280), the very reference this development tracks. The whole file is an extended, upstream-destined formalisation by David Angdinata (file copyright) — the original author of mathlib's EDS file — building precisely the API mathlib is currently missing (mathlib still lists "prove `normEDS` is an EDS" as a TODO).

**Important contingency (carry into PR planning).** This is a bridge lemma between two *project-local* defs `net` and `rel₄`. A bridge belongs in mathlib **iff both endpoints do.** It must therefore ship **as part of the same PR(s) that introduce `EllSequence.net` and `EllSequence.rel₄`** (and `addMulSub`) — not standalone. Independently, the lemma is correct, maximal, and non-composable, so conditional on that API landing, it is a clean add-as-is.

WHY add it (refactor-actionable):
- **Named mathlib gap it fills:** `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:44` carries the explicit TODO *"prove that `normEDS` satisfies `IsEllDivSequence`"* and *"prove that a normalised sequence satisfying `IsEllDivSequence` can be given by `normEDS`."* Discharging those is exactly what the `net`/`rel₄` theory in this file is for; `net_eq_rel₄` is a load-bearing lemma on that path (it is what lets `net = 0` ⇔ the symmetric elliptic relation, feeding `invar_of_net` and the `Rel₃`/`EvenRec` characterisations).
- **New content:** mathlib currently has the EDS *predicate* (`IsEllSequence`) and the *construction* (`normEDS`) but **none of the relational calculus** (`addMulSub`, `rel₄`, `net`, their permutation symmetry, their compatibility with ring homs). This identity is the hinge of that calculus.
- **Composes with existing mathlib API:** once `net`/`rel₄` land, `map_net`/`map_rel₄` make the relation a natural object under `RingHom`, and `Rel₃`/`IsEllSequence` (already in mathlib) become provable-equivalent to the four-index form via this lemma — closing the loop toward the TODO.

Proposed mathlib location: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (or a new `Mathlib/NumberTheory/EllipticDivisibilitySequence/Relations.lean` if the file is split — the existing file is 547 lines, this development adds ~1000+).

Proposed PR title: `feat(NumberTheory): elliptic-net four-index relation (net = rel₄) for EDS`

PR grouping (REQUIRED — right grain): ship together as ONE coherent API PR with its definitional dependencies and immediate companions, in this order —
  1. `EllSequence.addMulSub` (+ `addMulSub_even`/`_odd`/`_same`/`_neg₀`/`_neg₁`/`_swap`/…),
  2. `EllSequence.rel₄`, `EllSequence.net`,
  3. **`EllSequence.net_eq_rel₄`** (this decl) and its inverse `HaveSameParity₄.rel₄_eq_net`,
  4. `map_addMulSub` / `map_rel₄` / `map_net`.
  These are inseparable: the bridge lemma is meaningless without both defs, and `map_net` is *proven via* this lemma. Splitting them produces orphan defs / unprovable companions.

Pre-PR checklist before opening:
  - [ ] `/generalise EllSequence.net_eq_rel₄` — confirm no further weakening (expected: none; already `CommRing` + hypothesis-free).
  - [ ] `/cleanup …/EllipticDivisibilitySequence.lean EllSequence.net_eq_rel₄` — full audit + diff gates.
  - [ ] Coordinate with the upstream author (David Angdinata / Junyan Xu) — this file *is* their in-progress upstream of arXiv 2604.05280; the right move is to land it via their effort, not a parallel PR. Deduplicate the 3 in-repo copies (NagellLutz current, NagellLutz Original, HasseWeil) into `Common/` first.

---

## Next step

Treat as **YES-add-as-is, conditional on shipping with its parent defs `net`/`rel₄`/`addMulSub`**. Do not PR standalone. Before any mathlib PR: dedupe the three in-repo copies into a shared module, run `/generalise` (expect no change) and `/cleanup`, and coordinate with the upstream EDS author (Angdinata/Xu) since this file is the in-progress upstream of arXiv 2604.05280 and directly targets the existing mathlib TODO at `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:44`.
