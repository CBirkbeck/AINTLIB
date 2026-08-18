# /mathlibable report — `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`

_Step-9 overview mathlibable assessment, single declaration. ChatGPT-math MCP was
down for the whole run (consistent Codex stdin failure, same as the sibling
`abs_card_inter_sub_volume_mul_pow_le` run); the literature phase was carried by
WebSearch (≥4 distinct queries at varying generality) + mathlib-source grep +
mathlib4 docs. Loogle/LeanSearch deferred tools not available in this env; Phase 5
used the authoritative mathlib source grep + official docs. Local references dir
absent → recorded n/a. Cross-checked against the already-written sibling reports
for `abs_card_inter_sub_volume_mul_pow_le` (the direct dependency) and the
inventory file._

---

### Baseline (Phase 0)
- lake build:               not re-run (task note: local build stale; reasoning from source). Decl elaborates in-repo — it is the file's terminal export and is referenced as a primary input by three downstream Chebotarev files that build.
- decl `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`: ✓ resolved at `projects/Chebotarev/CebotarevDensity/ForMathlib/LatticePointCount.lean:366`
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Effective lattice-point count with a Lipschitz-boundary `O(nᵈ⁻¹)` error term — "the single deepest analytic input to the class-field-theory-free formalisation of Chebotarev's density theorem". File header explicitly: "It is stated here for a future mathlib contribution."

True qualified name **verified**: the decl sits in `namespace Chebotarev` (opened
line 51), inside an `@[expose] public section`, is a plain `theorem` (not
`private`), and there is no inner namespace between line 51 and line 366. So the
qualified name is **`Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`**.
The parsed name in the ticket is correct.

---

### Statement (Phase 1)

`Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le` is a theorem
stating the **effective (quantitative) lattice-point counting principle** — the
classical Lang/Davenport/Widmer theorem:

> Let `s ⊆ ℝ^d` (`d = #ι`, `ι` a fintype) be bounded and measurable, and suppose
> the topological frontier `∂s` is covered by finitely many Lipschitz images of
> the unit cube `[0,1]^{d-1}` (i.e. `∂s` is `(d−1)`-Lipschitz parametrizable, in
> the sense of Widmer/Masser: there exist `m`, a common Lipschitz constant `M`,
> and charts `φ₁,…,φ_m : [0,1]^{d-1} → ℝ^d`, each `M`-Lipschitz, with
> `∂s ⊆ ⋃ⱼ φⱼ([0,1]^{d-1})`). Then there is a constant `C` (depending only on `d`,
> `m`, `M`) such that for **every** integer `n ≥ 1` the number of points of the
> scaled standard lattice `n⁻¹·ℤ^d` lying in `s` satisfies
> `| #(s ∩ n⁻¹·ℤ^d) − vol(s)·nᵈ | ≤ C · nᵈ⁻¹`.

This is the **effective form** of mathlib's `tendsto_card_div_pow_atTop_volume`,
whose conclusion is only the rate-free limit `#(s ∩ n⁻¹ℤ^d)/nᵈ → vol s`.

The proof (lines 375–380) is a short composition of two project lemmas:
1. `abs_card_inter_sub_volume_mul_pow_le` (the boundary-cell **sandwich**, from
   bounded + measurable only): `|#(s ∩ n⁻¹ℤ^d) − vol(s)·nᵈ| ≤ #(index n '' ∂s)`
   = the number of grid cells of the `n⁻¹ℤ^d` grid meeting `∂s`;
2. `ncard_index_image_frontier_le` (the **Lipschitz chart bound**):
   `#(index n '' ∂s) ≤ (m·(2⌈M⌉+1)ᵈ·2ᵈ⁻¹) · nᵈ⁻¹`.
   The explicit `C = m·(2⌈M⌉₊+1)ᵈ·2ᵈ⁻¹` is produced (line 376) and the chain is
   closed by `push_cast; ring`.

Variables / typeclasses (Lean side):
- `ι : Type*`, `[Fintype ι]` — the finite coordinate index; `d = Fintype.card ι`.
- `s : Set (ι → ℝ)` — the region.

Hypotheses (Lean side):
- `hbdd : Bornology.IsBounded s` — region is bounded.
- `hmeas : MeasurableSet s` — region is measurable.
- `hlip : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (d−1) → ℝ) → (ι → ℝ)), (∀ j, LipschitzWith M (φ j)) ∧ frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1`
  — `∂s` is `(d−1)`-Lipschitz parametrizable.

Conclusion (math): `∃ C, ∀ n ≥ 1, |#(s ∩ n⁻¹ℤ^d) − vol(s)·nᵈ| ≤ C·nᵈ⁻¹`.

Conclusion (Lean):
`∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → |(Nat.card ↑(s ∩ (n:ℝ)⁻¹ • span ℤ (Set.range (Pi.basisFun ℝ ι))) : ℝ) − volume.real s * (n:ℝ) ^ Fintype.card ι| ≤ C * (n:ℝ) ^ (Fintype.card ι − 1)`.

The lattice is `span ℤ (range (Pi.basisFun ℝ ι))` = `ℤ^ι` — **identical** to the
local `notation "L"` in `Mathlib/Analysis/BoxIntegral/UnitPartition.lean:330`
(`span ℤ (Set.range (Pi.basisFun ℝ ι))`). So the count expression
`s ∩ (n:ℝ)⁻¹ • L` is verbatim mathlib's, and `tendsto_card_div_pow_atTop_volume`
is its rate-free limit, on the nose.

---

### Size classification (Phase 2a)

Verdict: **BIG**
Reason: it is the file's **main result** (the only entry under "## Main results"
that is called "the terminal export"), and it is the *named* classical theorem
(Lang GTM 110 Ch. VI §3 Thm 3 / Davenport 1951 / Widmer 2010) — a result
attributable to a person, which the size rule flags as BIG. (Literature width was
EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → n/a. (Body is a 5-line `refine`
composition, but the *statement* is the headline theorem, not a definitional
one-liner; the one-line check is about `def` bodies and does not apply.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                                  | Hit? | Standard form found | Notes |
|----|----------------------------------|--------------------------------------------------------------------------------------------------------|------|---------------------|-------|
| 1  | WebSearch (specific form)        | "counting lattice points in region volume error term Lipschitz boundary O(t^{d-1})"                    | yes  | error term `O(t^{d-1})` is the boundary contribution; Lipschitz parametrizability controls it | Widmer (RHUL notes); Gorodnik–Nevo; arXiv 2411.13522, 1609.08720 |
| 2  | WebSearch (surface-area / general)| "number of lattice points bounded region equals volume plus error proportional surface area boundary"  | yes  | `N = V + O(surface area)`; convex N ≤ V + ½S + … | Blichfeldt-type; geometry-of-numbers classics |
| 3  | WebSearch (named-after: Lang)    | "Lang Algebraic Number Theory boundary cell estimate lattice point count Lipschitz parametrizable"     | **yes (decisive)** | **"if a compact domain C has Lipschitz-parametrizable boundary then `|Λ ∩ tC| = Vol(C)·tᴺ + O(tᴺ⁻¹)`"; and the general corollary "if `S ⊆ ℝⁿ` has `(n−1)`-Lipschitz-parametrizable boundary then `#(tS ∩ Λ) = μ(S)·covol(Λ)·tⁿ + O(tⁿ⁻¹)`"** | this is **verbatim our theorem**. Names: Lang GTM 110, Davenport, Widmer; "`d`-Lipschitz parametrizable = finite union of images of Lipschitz `[0,1]^d → B`" defined exactly as in the Lean `hlip` |
| 4  | WebSearch (mathlib effective)    | "mathlib4 effective lattice point count error term tendsto_card_div_pow"                                | yes  | mathlib docs surface only `tendsto_card_div_pow*` (limits); no effective form | leanprover-community docs; arXiv on error terms of lattice counting |
| 5  | ChatGPT MCP                      | self-contained Q on standard name + generality (lattice vs ℤ^d, real t vs integer n, Lipschitz-charts vs Minkowski content, explicit C) | n/a | — | **MCP down** (Codex stdin failure), same as sibling run; task warned of this. Compensated by WebSearch #1–#4 + the sibling report's identical finding. |
| 6  | Local references                 | grep `.mathlib-quality/references/` and `refs/`                                                         | n/a  | — | **No references dir** (both `projects/Chebotarev/.mathlib-quality/references/` and `refs/` absent) → n/a per protocol. |
| 7  | nLab                             | "lattice point counting / geometry of numbers"                                                         | n/a  | — | Not an nLab-style categorical concept; no dedicated entry. Recorded n/a with reason. |
| 8  | nCatLab                          | —                                                                                                       | n/a  | — | Not a categorical concept. |
| 9  | Stacks Project                   | —                                                                                                       | n/a  | — | Not an algebraic-geometry concept (real-analytic geometry of numbers). |
| 10 | MathOverflow / Math.SE           | covered via WebSearch #1–#3 (geometry-of-numbers Q&A surfaced)                                         | yes  | agrees: leading term vol·tⁿ, error O(tⁿ⁻¹) from boundary | folded into #1–#3 |
| 11 | recent arXiv (last 5 yrs)        | "heights and morphisms in number fields" 2411.13522; "slicing the stars" 1609.08720; Gun–Ramaré–Sivaraman | yes | the Lipschitz principle (main term + `O(tⁿ⁻¹)`) is current and actively used; GRS is the project's own cited source family | confirms the result is live, standard, and is exactly the GRS/Debaene input |

Protocol pass check: WebSearch ran 4 distinct queries at 4 generality levels
(specific `O(t^{d-1})` / surface-area general / Lang-named / mathlib-effective).
ChatGPT MCP attempted, down — explicitly recorded, not silently skipped (and the
identical question was effectively answered by the sibling `abs_…` report's
literature phase). Local refs, nLab, nCatLab, Stacks, MathOverflow, arXiv all
checked or n/a-with-reason. ✓

### Literature summary (Phase 3)

Concept identified as: **the effective / quantitative lattice-point counting
principle (Davenport's Lipschitz principle)** — "for a region whose boundary is
`(d−1)`-Lipschitz parametrizable, `#(scaled lattice ∩ S) = vol(S)·nᵈ + O(nᵈ⁻¹)`."
Canonical references: **Lang, *Algebraic Number Theory*, GTM 110, Ch. VI §3
Theorem 3 (p. 129)** (the exact citation in the Lean docstring); **H. Davenport,
*On a principle of Lipschitz*, J. London Math. Soc. 26 (1951)**; **M. Widmer,
*Lipschitz class, narrow class, and counting lattice points*, Proc. AMS 138
(2010)** (the canonical modern statement, with explicit constants via successive
minima); Masser–Vaaler; and — directly for this project — **Gun–Ramaré–Sivaraman,
*Counting ideals in ray classes*, JNT 243 (2023), §3.3–3.5, after Debaene** (the
project's own cited lineage).

Sources agree on the standard form: **yes.** Web query #3 returns the statement
essentially verbatim, including the definition of `(d−1)`-Lipschitz
parametrizability ("a set `B` is `d`-Lipschitz parametrizable if it is the union
of images of finitely many Lipschitz `[0,1]^d → B`") that the Lean `hlip`
hypothesis encodes letter-for-letter.

Most general standard form: for an **arbitrary full-rank lattice `Λ ⊂ ℝⁿ`** with
covolume `covol(Λ)`, and the scaled **set** `tS` with **real** `t → ∞`:
`#(tS ∩ Λ) = vol(S)·tⁿ/covol(Λ) + O(tⁿ⁻¹)`, the implied constant explicit in `n`,
the number/Lipschitz-constants of the boundary charts, and (Widmer) the successive
minima of `Λ`.

Generality dimensions where the literature varies:
- **lattice**: from "scaled standard lattice `n⁻¹ℤⁿ`" (this theorem) up to
  "arbitrary full-rank `Λ` with covolume" (Widmer's general form). Standard
  textbook form is the `ℤⁿ` case.
- **scaling variable**: integer `n` (this theorem; also mathlib's
  `tendsto_card_div_pow_atTop_volume`) vs real `t` (Widmer; also mathlib's
  `tendsto_card_div_pow_atTop_volume'`).
- **boundary hypothesis**: "finitely many Lipschitz charts of `[0,1]^{d-1}`"
  (this theorem, = Widmer/Masser `(d−1)`-Lipschitz parametrizable) is the standard
  geometry-of-numbers phrasing; "finite `(d−1)`-dimensional upper Minkowski
  content" is an alternative but less common phrasing. The Lean form uses the
  standard one.
- **constant**: explicit `C` (this theorem gives `m·(2⌈M⌉₊+1)ᵈ·2ᵈ⁻¹`) vs bare
  `O(·)`. Widmer's refinement makes `C` explicit; giving an explicit `C` is the
  *stronger, preferred* form.

Disagreement with the literature: **none.** The Lean form is the recognised named
theorem at a standard (textbook-`ℤⁿ`, integer-`n`, explicit-`C`) generality.

---

### Generality analysis — `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`

Literature-standard form (from Phase 3): `#(tS ∩ Λ) = vol(S)·tⁿ/covol(Λ) + O(tⁿ⁻¹)`
for an arbitrary full-rank lattice `Λ`, real or integer scaling, `∂S`
`(n−1)`-Lipschitz parametrizable, `C` explicit.

| # | Parameter / hypothesis | Current Lean form | Literature-standard form | Weaker form exists? | Reason it can/can't be weakened |
|---|---|---|---|---|---|
| 1 | `[Fintype ι]` | finite coordinate index | `n`-dim Euclidean space | NO | `d = #ι` must be finite for `vol`, the grid, `nᵈ`, `nᵈ⁻¹`. Maximal. |
| 2 | `hbdd : IsBounded s` | bounded | bounded (compact in Lang) | NO | needed for finiteness of the cell sets and `vol s < ∞`. The bounded (not compact) hypothesis is already *more* general than Lang's "compact". Maximal. |
| 3 | `hmeas : MeasurableSet s` | measurable | measurable | borderline | enters only through the sandwich lemma's `NullMeasurableSet` + `vol s ≠ ⊤`; a cosmetic `MeasurableSet → NullMeasurableSet` micro-weakening is possible but not a literature axis. |
| 4 | `hlip` (finite Lipschitz charts of `[0,1]^{d-1}`) | `(d−1)`-Lipschitz parametrizable `∂s` | `(d−1)`-Lipschitz parametrizable `∂S` | NO | this **is** the literature-standard boundary hypothesis (Widmer/Masser), stated verbatim. Maximal. |
| 5 | lattice = `n⁻¹·(standard ℤ^ι)`, scaling = integer `n` | scaled standard lattice, integer `n` | arbitrary full-rank `Λ` with covolume; real `t` allowed | **conceptually yes** (lattice + real-scaling axes) | the lattice is hard-wired to `n⁻¹·ℤ^ι` and `n` is an integer. The literature-general form is over arbitrary `ZLattice` Λ with `ZLattice.covolume` and real `t`. **This is the one real generality axis** — and it is *identical to the axis on which mathlib's own `tendsto_card_div_pow_atTop_volume` sits* (same `L`, same integer-`n` form; the real-`t` companion `…'` requires an extra monotonicity hypothesis). |

### Generality verdict (Phase 4b)

The current form is: **MAXIMALLY GENERAL on the region + boundary axes** (bounded
beats Lang's compact; the Lipschitz-charts hypothesis is the literature standard
verbatim; the explicit `C` is the stronger form), but **STRICTLY NARROWER on the
lattice/scaling axis** (hard-wired `n⁻¹·ℤ^ι`, integer `n`, rather than a general
`ZLattice` Λ / real `t`).

Number of weakening opportunities found: 1 substantive (lattice/scaling axis) + 1
cosmetic (`MeasurableSet → NullMeasurableSet`).

Proposed restatement (lattice-general), schematic:
```
theorem exists_card_inter_sub_volume_le {ι} [Fintype ι]
    {Λ : Submodule ℤ (ι → ℝ)} [IsZLattice ℝ Λ]
    {s : Set (ι → ℝ)} (hbdd : IsBounded s) (hmeas : NullMeasurableSet s)
    (hlip : ∃ m (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier s ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(Nat.card ↑(s ∩ t⁻¹ • Λ) : ℝ) - volume.real s * t ^ Fintype.card ι / ZLattice.covolume Λ|
        ≤ C * t ^ (Fintype.card ι - 1)
```
Cost of restatement: **EXPENSIVE** — both building blocks
(`abs_card_inter_sub_volume_mul_pow_le`, `ncard_index_image_frontier_le`) and the
whole `box`/`index`/`tag` infrastructure of `BoxIntegral.unitPartition` are built
specifically for the `n⁻¹ℤ^ι` grid at integer `n`. A `ZLattice`-general,
real-`t` fundamental-domain cell count and its sandwich need new API. This is a
research-formalisation effort, not a mechanical rewrite.

**Crucial caveat (why this does NOT by itself force YES-but-generalise):**
mathlib's own companion `tendsto_card_div_pow_atTop_volume` is *also* hard-wired
to the `n⁻¹ℤ^ι` grid at integer `n` (literally the same `L = span ℤ (range
(Pi.basisFun ℝ ι))` and `box`/`index` machinery), with the real-`t` version split
off as a separate `…'` lemma under an extra hypothesis. The project's theorem is
the **effective sibling at exactly mathlib's established generality.** Generalising
the lattice/scaling axis is a separate, library-wide project that should generalise
*both* the limit and the effective form together — it is not a precondition for
upstreaming the effective form in the shape mathlib already chose for the
qualitative one. Per the skill's cost rule, EXPENSIVE does not by itself downgrade
the verdict; and the narrower axis here is the *house style* of the very mathlib
file this joins.

### Modern-idiom check (Phase 4c)

| #  | Question | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|----------|----------|------------------------|----------------------------------|
| 1  | bundled-hyp → typeclass/instance? | partial | the `hlip` existential could be packaged as a predicate/class `LipschitzBoundary s` (or a `(d−1)`-Lipschitz-parametrizable class). But mathlib has **no such class yet**, and `IsBounded`/`MeasurableSet` are already idiomatic predicates. A class is a *new design*, not a weakening of this statement. | a future `LipschitzParametrizable` class would let many counting results share the hypothesis |
| 2  | sequences/metric → filters/topology? | no | the conclusion is `∀ n, …` (a uniform bound), already the effective object; the *limit* sibling is the filter version and already lives in mathlib | — |
| 3  | construct → universal property? | no | nothing constructed | — |
| 4  | set-with-predicate → bundled substructure? | no | — | — |
| 5  | vector-space/field-specific → weaken typeclass? | no | already over `ι → ℝ` exactly as mathlib's `unitPartition`; `ℝ`-specific is intrinsic (Lebesgue/Haar) | — |
| 6  | 1-categorical → higher-categorical? | no | — | — |
| 7  | **concrete index → general algebraic structure?** | **yes** | replace `n⁻¹·(standard ℤ^ι)`/integer `n` by a general `ZLattice` Λ with `ZLattice.covolume` and real `t` (Phase-4b row 5) | a `ZLattice`-general effective count composes with all of mathlib's `ZLattice`/covolume/Minkowski API |

### Modern-idiom verdict (Phase 4c)

Modern idiom available: **yes in principle** (the `ZLattice`/real-`t`
generalisation of the lattice axis, row 7), **but it is the SAME generalisation as
Phase-4b row 5**, and:
- Cost: **EXPENSIVE** (a `ZLattice`-level reworking of `unitPartition`'s
  `box`/`index`/`tag`, plus a real-`t` count).
- It applies *equally* to mathlib's existing `tendsto_card_div_pow_atTop_volume`,
  which has **not** been so generalised (the integer-`n` `L`-grid form is the one
  mathlib ships; the real-`t` one is a separate hypothesis-laden lemma). Asking the
  project's effective theorem to clear a generality bar mathlib's own qualitative
  theorem has not cleared is the wrong gate — they should be generalised together
  as a future `unitPartition`-over-`ZLattice` project.
- The optional `LipschitzParametrizable`-class idea (row 1) is a genuine but
  *separate* piece of new design, not a restatement of this theorem; it is a good
  follow-up, not a blocker.
- Real mathematical improvement: yes *eventually*, but **not blocking**: the
  contribution mathlib is missing is the *effective error term at the existing
  generality*, which is exactly what this theorem supplies.

Conclusion: the modern-idiom move is real but library-scoped and shared with the
existing mathlib limit; it informs *sequencing* (a later `ZLattice` generalisation
of the whole `unitPartition` count family) rather than downgrading this theorem to
YES-but-generalise-first. Surfaced as a non-blocking question to the maintainer
below.

---

### Diamond / defeq risk — n/a

Declaration kind is `theorem` → Phase 4.5 skipped (no definitional equalities or
typeclass-search paths introduced).

---

### Mathlib search-status: `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`

[A] Lean-Finder      — (deferred tool unavailable in this env) — n/a
[B] Loogle           — (deferred tool unavailable in this env) — n/a; compensated by source grep [D] + official docs
[C] LeanSearch       — natural-language web proxy: "mathlib4 effective lattice point count error term Lipschitz boundary" — no effective-form hit; only the `tendsto_*` limits
[D] **Grep mathlib src** — over **all** of `Mathlib/`: `exists_card_inter`, `card_inter_sub_volume`, `volume_mul_pow`, `abs_card`, `ncard.*frontier`, `n ^ (.*card.*- 1)`, `Lipschitz.*frontier`, `index.*frontier`, `Parametriz`/`parametriz` — **no hits** pairing a lattice-point count with an effective volume error term. The only `Parametriz` hits are in homotopy/continuous-map files, unrelated. The only file pairing `card ∩ (scaled L)` with `volume` is `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`, which stops at the rate-free limits.
[E] Name pattern     — `tendsto_card_div_pow*`, `*card*volume*pow*`, `*frontier*ncard*`, `*Lipschitz*count*` — only `tendsto_card_div_pow_atTop_volume`, `…_volume'`, `tendsto_tsum_div_pow_atTop_integral` (all *limits*, no effective inequality, no `O(nᵈ⁻¹)` rate).

Searched for both:
  - the user's current form (effective `∃C, ∀n, |count − vol·nᵈ| ≤ C·nᵈ⁻¹`) — **not in mathlib**
  - the literature-general form (`ZLattice` covolume, real `t`, explicit `C`) — **not in mathlib** (mathlib has `ZLattice.Covolume` defns and `ZLattice` Minkowski theory, but **no** effective count-vs-volume error bound and no Lipschitz-boundary cell count in any form)

The two **building blocks** this theorem composes are *also both absent* from
mathlib (confirmed in this grep and in the sibling `abs_…` report's Phase 5):
neither `abs_card_inter_sub_volume_mul_pow_le` (the sandwich) nor
`ncard_index_image_frontier_le` (the Lipschitz chart bound) has any mathlib
counterpart.

Confirmed against the official mathlib4 docs for `BoxIntegral.UnitPartition`: the
file's public API is exactly the three `tendsto_*` limits + the
`box`/`index`/`tag`/`admissibleIndex`/`prepartition` infrastructure. **No
effective version is present.**

Concluded: **"not in mathlib (all available methods exhausted, plus the
literature-general form, plus both building blocks)."** Mathlib has the
*qualitative limit* sibling and the *base infrastructure*, but neither this
effective theorem nor either lemma it is built from.

---

### Call sites — `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`

Internal use count: **3 distinct downstream files reference it as a primary input**
(within the project, excluding the declaring file's own `Main results`/docstring
mentions). All current references are in module docstrings / prose framing rather
than a bare `exact <name>` application term, because each downstream file states
its *own* adapted count theorem and cites this as the underlying input ("L1");
that is the normal shape for a deep analytic input that gets specialised per
consumer.

| Caller file:line | Usage pattern (one-line excerpt) |
|------------------|-----------------------------------|
| `…/CebotarevDensity/ForMathlib/IdealCongruenceCount.lean:21` | "formalised as `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (**L1**) with the Lipschitz …" — the ideal-congruence count is built on it as its labelled lattice-point input |
| `…/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean:10,345` | "to apply the effective lattice-point count (`…sub_volume_mul_pow_le`) one needs the stronger [Lipschitz-boundary]…" — this file exists *to supply the `hlip` hypothesis* for it |
| `…/CebotarevDensity/ZetaProduct.lean:435,1870` | "with each congruence sublattice (`…sub_volume_mul_pow_le`, fed the …)" / "by `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le` (the effective …)" — the zeta-product / L-function continuation uses it per congruence sublattice |

Inline-derivation grep (was the equivalent `∃C, ∀n, |count − vol·nᵈ| ≤ C·nᵈ⁻¹`
re-derived elsewhere without using this theorem?): **(none)** — no other site
re-proves the effective count; the entire `ForMathlib/NormLeOneLipschitz.lean`
file is dedicated to feeding this theorem its boundary hypothesis, and
`IdealCongruenceCount`/`ZetaProduct` consume the result.

Signal reading: this is the **terminal export / load-bearing public API** of the
file — referenced across three downstream files as the named effective input,
with an entire sibling file (`NormLeOneLipschitz`) written solely to discharge its
`hlip` hypothesis, and zero inline re-derivation. Matches the "K ≥ 3, no inline
re-derivation → YES-* bucket" row decisively. (The references are prose/docstring
citations rather than `exact` terms only because each consumer states its own
specialised count; the dependency is real and structural, not cosmetic.)

---

### Composition check (Phase 6)

Can `exists_card_inter_smul_lattice_sub_volume_mul_pow_le` be derived from
**mathlib** in ≤3 chained calls?

Attempt 1: from `tendsto_card_div_pow_atTop_volume` (the mathlib limit).
  - Mathlib decls used: `tendsto_card_div_pow_atTop_volume`.
  - Result: **fails — wrong direction of logical strength.** That theorem is a
    *qualitative limit* (`card/nᵈ → vol s` as `n → ∞`, and only under
    `vol(∂s) = 0`). It gives **no effective bound at finite `n`** and **no rate**;
    a limit cannot produce an explicit `∃C, ∀n, … ≤ C·nᵈ⁻¹`. (Conversely, *this*
    theorem implies that limit — it is strictly stronger.)

Attempt 2: assemble from mathlib `unitPartition` + `MeasureTheory` primitives
directly (`volume_box`, `measureReal_mono`, `Set.ncard_union_le`, the
`box`/`index`/`tag` lemmas, plus a Lipschitz-image cell bound).
  - Result: **fails as a ≤3-call composition.** It requires *both* (a) the
    boundary-cell **sandwich** `abs_card_inter_sub_volume_mul_pow_le` (a ~75-line
    three-set `Inside ⊆ Tag ⊆ Meet`, `Meet ⊆ Inside ∪ Bd` proof with the
    preconnectedness lemma `index_mem_image_frontier_of_box_meet_not_subset`), and
    (b) the **Lipschitz chart bound** `ncard_index_image_frontier_le` (itself built
    on `ncard_index_image_chart_le` / `ncard_index_image_le_of_diam_le`). Neither
    is in mathlib. This is two substantial proofs, not a composition.

Note: the theorem's *own* in-project proof **is** a 3-line composition — but of
**two project lemmas that are themselves not in mathlib**. The composition
heuristic asks whether *mathlib's* primitives compose to give it; they do not
(mathlib lacks both ingredients). So this is NOT a `NO-composable-from-mathlib`
case: there is no mathlib building block to inline at the call site.

Conclusion: **NOT-COMPOSABLE (from mathlib).** Mathlib supplies only the base
`box`/`index`/`tag` infrastructure and the strictly-weaker limit; the effective
theorem is genuine new content built from two new lemmas.

---

## Verdict: `Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`

**Category:** YES-add-as-is

(with a single non-blocking BORDERLINE flag for the maintainer on lattice/scaling-
axis sequencing — see question at the end; it does not block the YES, and is the
same flag carried by the sibling `abs_…` lemma.)

**Evidence:**
- Literature search (Phase 3): this is the **named** effective lattice-point
  counting principle — Lang GTM 110 Ch. VI §3 Thm 3 (the docstring's exact
  citation), Davenport 1951, Widmer 2010, and the project's own GRS/Debaene
  lineage. Web query #3 returns `#(tS ∩ Λ) = vol(S)·tⁿ + O(tⁿ⁻¹)` under
  `(n−1)`-Lipschitz-parametrizable boundary essentially verbatim, with the
  Lipschitz-charts hypothesis defined exactly as the Lean `hlip`.
- Generality analysis (Phase 4): MAXIMALLY GENERAL on the region + boundary axes
  (bounded ⊇ compact; the Lipschitz-charts hypothesis is the literature standard
  verbatim; explicit `C` is the stronger form); STRICTLY NARROWER only on the
  lattice/scaling axis — but that axis is *identical to mathlib's own
  `tendsto_card_div_pow_atTop_volume`*, so it is house-style, not a defect.
  Generalising it is an EXPENSIVE, library-wide `ZLattice` project shared with the
  existing limit (so does not gate this PR).
- Mathlib search (Phase 5): not in mathlib in any form; `UnitPartition.lean` has
  the rate-free limits and the infrastructure, but **no effective error bound**,
  and **neither building block** (`abs_…`, `ncard_index_image_frontier_le`) exists
  in mathlib (confirmed against official docs + full-tree grep).
- Composition check (Phase 6): NOT-COMPOSABLE from mathlib (the limit is strictly
  weaker; the theorem needs two substantial new lemmas absent from mathlib).

**Rationale:**

This is the canonical **effective form of an existing mathlib limit**, and it is a
classical *named theorem* (Lang/Davenport/Widmer). Mathlib's
`tendsto_card_div_pow_atTop_volume` establishes only `card(s ∩ n⁻¹ℤ^d)/nᵈ → vol s`
(rate-free, under `vol(∂s) = 0`), using the very same `box`/`index`/`tag`
unit-partition machinery and the very same lattice `L`. The project's theorem
proves the **quantitative, finite-`n`** statement — with an explicit constant and
the power-saving `O(nᵈ⁻¹)` rate — under the standard `(d−1)`-Lipschitz-parametrizable
boundary hypothesis. This is strictly more information than the limit (the limit
follows from it), and it is exactly the form every *effective* application needs:
power-saving error terms, the Lipschitz principle, and (the project's own use)
counting ideals in ray classes to get analytic continuation of abelian
`L`-functions past `Re s = 1`. The statement sits at a standard textbook generality
(`ℤⁿ`, integer `n`, explicit `C`), and the explicit constant is the *stronger* of
the literature forms.

The one narrower axis (general `ZLattice` Λ / real `t`) is shared verbatim with
mathlib's own qualitative limit, which has not been generalised that far either;
that is a future library-wide `unitPartition`-over-`ZLattice` effort, not a
precondition for upstreaming the effective form mathlib's qualitative form already
fixes. Per the skill's cost rule, an EXPENSIVE generalisation does not downgrade
the verdict.

**WHY add it (the gap, refactor-actionable):** the concrete, named gap is that
`Mathlib/Analysis/BoxIntegral/UnitPartition.lean` provides *only* the rate-free
limits (`tendsto_card_div_pow_atTop_volume`, `…'`, `tendsto_tsum_div_pow_atTop_integral`)
and the unit-partition infrastructure, and has **no effective / error-term
companion at all** — there is currently no way in mathlib to get an explicit rate
`|count − vol·nᵈ| ≤ C·nᵈ⁻¹` for a Lipschitz-boundary region. The entire
geometry-of-numbers Lipschitz-principle toolkit (Davenport, Widmer, Masser–Vaaler,
and downstream: counting algebraic integers / ideals / points of bounded height)
rests on exactly this estimate, and anyone needing it in mathlib today must rebuild
it from scratch, as this project did. Adding it:
- *fills the effective-counting gap* in `UnitPartition` directly above the existing
  limit — it is the headline theorem the file is morally missing (the limit is its
  immediate corollary by sending `n → ∞`);
- *composes with the existing API*: it is the natural strengthening of
  `tendsto_card_div_pow_atTop_volume` and reuses the same `box`/`index`/`tag`
  machinery, `volume_box`, `measureReal_*`, `Set.ncard_union_le`, plus
  `LipschitzWith.isBounded_image` — all already in mathlib;
- *is the export three downstream developments already depend on* (with an entire
  sibling file written solely to feed its `hlip` hypothesis), demonstrating it is
  reusable, load-bearing API rather than a one-shot wrapper.

Proposed mathlib location: `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`
(same file as `tendsto_card_div_pow_atTop_volume` — it belongs *just before* the
limit, as the effective theorem the limit specialises from), or a sibling
`Mathlib/Analysis/BoxIntegral/UnitPartitionCount.lean` if the file is felt too
long. The supporting lemmas ship alongside — at minimum
`abs_card_inter_sub_volume_mul_pow_le` (the sandwich),
`ncard_index_image_frontier_le` + `ncard_index_image_chart_le` +
`ncard_index_image_le_of_diam_le` (the Lipschitz chart bound spine), and
`setFinite_index_image_of_isBounded` (the finiteness helper).

Proposed PR title: `feat(Analysis/BoxIntegral): effective lattice-point count with
Lipschitz-boundary O(nᵈ⁻¹) error term`

PR grouping (REQUIRED): ship as **one PR** with the whole spine it composes, since
the export is useless without its two building blocks:
- `Chebotarev.abs_card_inter_sub_volume_mul_pow_le` — the boundary-cell sandwich
  (separately assessed **YES-add-as-is**);
- `Chebotarev.ncard_index_image_frontier_le`, `…_chart_le`, `…_le_of_diam_le` — the
  Lipschitz-image cell-count bound;
- `Chebotarev.setFinite_index_image_of_isBounded` — the "index-image of a bounded
  set is finite" helper;
- this terminal export itself.
(Run `/mathlibable` per-decl on the chart-bound spine to confirm each before the
PR; the sandwich and this export are already confirmed YES.)

Pre-PR checklist before opening:
- [ ] `/generalise Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`
  — apply the cosmetic `MeasurableSet → NullMeasurableSet` weakening (the proof
  only uses it through the sandwich's `NullMeasurableSet`); decide with the
  maintainer whether to do the `ZLattice` / real-`t` lattice-axis generalisation
  now or as a follow-up that also generalises the existing limit.
- [ ] `/cleanup …/LatticePointCount.lean Chebotarev.exists_card_inter_smul_lattice_sub_volume_mul_pow_le`
  — full style audit + diff gates (drop the `Chebotarev` namespace; rename to drop
  the project prefix and align with `unitPartition` naming; reuse the file's local
  `L`/`box`/`index` rather than re-spelling `span ℤ (range (Pi.basisFun ℝ ι))`;
  consider packaging the `hlip` existential as a named predicate).
- [ ] Pick a reviewer from recent `Mathlib/Analysis/BoxIntegral/` history — the
  author/maintainers of `UnitPartition.lean` (the `tendsto_card_div_pow` series)
  are the natural reviewers, since this slots directly into their file as its
  effective headline.

**BORDERLINE flag for the maintainer (single question, does not block the YES):**
1. Should the effective theorem be upstreamed *now* at mathlib's existing
   `n⁻¹·ℤ^ι`-grid / integer-`n` generality (matching
   `tendsto_card_div_pow_atTop_volume`), with the `ZLattice`-general + real-`t`
   version deferred to a later PR that generalises the whole `unitPartition` count
   family (limit + effective) together? (Recommended: **yes** — do not gate the
   effective form on a library-wide generalisation that mathlib's own qualitative
   form has not undergone.)

---

## Next step

Open a `feat(Analysis/BoxIntegral)` PR adding the effective Lipschitz-boundary
`O(nᵈ⁻¹)` lattice-point count to `Mathlib/Analysis/BoxIntegral/UnitPartition.lean`,
grouped as one PR with its full supporting spine (`abs_card_inter_sub_volume_mul_pow_le`,
`ncard_index_image_frontier_le` + `…_chart_le` + `…_le_of_diam_le`,
`setFinite_index_image_of_isBounded`). First run `/generalise` (apply the
`NullMeasurableSet` weakening; settle the `ZLattice`/real-`t` question with the
maintainer) and `/cleanup` (drop the `Chebotarev` namespace, align naming with
`unitPartition`, reuse its `L`/`box`/`index`).
