# /mathlibable report — `Chebotarev.cyclic_subgroup_meets_G_times_one_trivially`

### Baseline (Phase 0)
- lake build:               ⚠ not run (local build stale per task note; reasoning from source — statement reread char-accurate)
- decl `Chebotarev.cyclic_subgroup_meets_G_times_one_trivially`: ✓ resolved at
  `projects/Chebotarev/CebotarevDensity/Abelian.lean:90` (inside `namespace Chebotarev`, lines 56–1595)
- kind:                      theorem
- has sorry:                 no
- module docstring summary:  Chebotarev's density theorem, abelian case — reduces to the cyclotomic
  case by crossing with cyclotomic extensions (Sharifi §7.2.2 Step 2).

True qualified name confirmed: **`Chebotarev.cyclic_subgroup_meets_G_times_one_trivially`**
(the parsed guess was correct).

---

### Statement (Phase 1)

`cyclic_subgroup_meets_G_times_one_trivially` is a theorem stating:

> Let `G`, `H` be finite groups, `σ ∈ G`, `τ ∈ H`. If `|G|` divides the order of `τ`, then the
> cyclic subgroup `⟨(σ,τ)⟩` of the direct product `G × H` intersects the "first-factor" subgroup
> `G × {1}` only in the identity: `⟨(σ,τ)⟩ ∩ (G × {1}) = {1}`.

This is Sharifi 7.2.2 Step 2 sub-lemma (i) (p. 144): "if `|G|` divides the order of `τ`, then
`⟨(σ,τ)⟩ ∩ (G × {1}) = 1`". It is the only place in Step 2 where the `|G| ∣ ord τ` hypothesis is used.

Variables / typeclasses (Lean side):
- `G H : Type*`, `[Group G] [Group H]` — two groups.
- `[Finite G] [Finite H]` — both assumed finite.
- `σ : G`, `τ : H` — the two components of the generator.

Hypotheses (Lean side):
- `_hn : Nat.card G ∣ orderOf τ` — `|G|` divides the order of `τ`. (Note the leading underscore:
  the name signals it is consumed, but it *is* used in the proof.)

Conclusion (math): `⟨(σ,τ)⟩ ∩ (G × {1}) = {1}` in `G × H`.
Conclusion (Lean): `(Subgroup.zpowers (σ, τ)) ⊓ ((⊤ : Subgroup G).prod (⊥ : Subgroup H)) = ⊥`.

Proof (verbatim, lines 95–103): take `(g,h) ∈` the meet; membership in `⊤.prod ⊥` forces `h = 1`;
membership in `zpowers (σ,τ)` gives `k` with `(σ,τ)^k = (g,h)`, so `τ^k = 1`, hence `ord τ ∣ k`;
since `ord σ ∣ |G| ∣ ord τ ∣ k` we get `σ^k = 1`, so `g = σ^k = 1`; thus `(g,h) = 1`.
Spelled with `orderOf_dvd_natCard σ`, `orderOf_dvd_iff_zpow_eq_one`, `Prod.mk_eq_one`.

---

### Size classification (Phase 2a)

Verdict: **SMALL**
Reason: helper sub-lemma (a `theorem`, not a `def`/structure; not a `## Main results` entry; not
named after a person/place — it is an internal Step-2 sub-lemma). Pure finite-group-theory fact
with a 9-line elementary proof.

(Literature width run EXHAUSTIVE regardless.)

### One-line check (Phase 2b)

Kind is `theorem`, not `def`/`abbrev`/`structure` → one-line def check is **n/a**. (The body is a
9-line tactic proof, not a one-line definitional unfolding.)

---

### Literature search table — EXHAUSTIVE protocol

| #  | Channel                          | Query                                                                                   | Hit? | Standard form found                                  | Notes |
|----|----------------------------------|-----------------------------------------------------------------------------------------|------|------------------------------------------------------|-------|
|  1 | WebSearch (specific form)        | cyclic subgroup of G×H intersection with G×{1} trivial, order condition                  | partial | `S₁ = S ∩ (G×1)` is the standard "subdirect" notation; no named theorem for the trivial-meet specialisation | Wikipedia *Direct product of groups*; arXiv *Maximal subgroups of direct products* |
|  2 | WebSearch (general form / lcm)   | "order of (a,b)" direct product = lcm; cyclic subgroup intersection factor trivial       | yes  | `ord(a,b) = lcm(ord a, ord b)` — the fundamental fact; trivial-meet is a routine corollary | LSU FiniteAbelianGroup notes; Princeton "structure of groups" 6.1; LibreTexts/Judson 9.2; Conrad |
|  3 | WebSearch (named-after / aliases)| Keith Conrad "orders of elements" direct product; lcm of orders; factor intersection     | yes  | Conrad *Orders of Elements in a Group*: `o(a,b)=lcm(o(a),o(b))`; exercise-level, unnamed | kconrad.math.uconn.edu/blurbs/grouptheory/order.pdf (fetch ECONNREFUSED; identified via search snippets) |
|  4 | ChatGPT MCP                      | standard form / minimal hypothesis / finiteness — asked twice (high + medium effort)     | n/a  | — (server down: Codex `exec` failed both calls)      | task note warned MCP may be down; used WebSearch + nLab + own analysis as fallback |
|  5 | Local references                 | grep `.mathlib-quality/references/` for the concept                                      | n/a  | (no `references/` dir; no `refs/` dir on this machine) | recorded n/a — directory absent |
|  6 | nLab                             | direct product of groups — subgroup/intersection structure                               | no   | nLab page covers only the categorical definition + irreps of products; nothing on cyclic-subgroup factor intersections | ncatlab.org/nlab/show/direct+product+of+groups (fetched) |
|  7 | nCatLab (categorical)            | (same as #6)                                                                             | n/a  | not a categorical concept beyond the product itself  | — |
|  8 | Stacks Project (alg geom)        | is this an algebraic-geometry concept? cyclic subgroup / direct product factor           | n/a  | not an algebraic-geometry concept — pure finite group theory | confirmed via WebSearch: query is fundamentally abstract algebra |
|  9 | MathOverflow / Math.SE           | (covered by #1–#3; standard direct-product / lcm-of-orders material surfaced)            | yes  | uniformly treated as elementary; `ord(a,b)=lcm`      | LibreTexts/Judson, course PDFs (Princeton, KSU, LSU, USC) |
| 10 | recent arXiv (last 5 years)      | direct product subgroup intersection; maximal intersections in finite groups             | no   | arXiv hits (*Maximal subgroups of direct products*, *Maximal intersections in finite groups*) concern far harder questions; our fact is below their threshold | math/9703201; arXiv:2012.07018 |

The protocol passes: WebSearch ran ≥3 distinct queries at three generality levels (specific
trivial-meet form, the general lcm-of-orders form, named-after/Conrad). ChatGPT MCP attempted
(down — fallbacks used). Local refs checked (absent). nLab checked. Stacks/nCatLab/MathOverflow/
arXiv each checked or recorded n/a with reason.

### Literature summary (Phase 3)

Concept identified as: **order of an element in a direct product** — `ord(a,b) = lcm(ord a, ord b)`
— and its immediate corollary that `⟨(a,b)⟩ ∩ (G × {1})` is trivial when `ord a ∣ ord b`.
Sources agree on the standard form: **yes**. The lcm formula is universal textbook content; the
trivial-intersection statement is an unnamed exercise-level consequence.
Most general standard form: in **any** group `G × H` (no finiteness needed), if `ord(σ)` is finite
and `ord(σ) ∣ ord(τ)`, then `⟨(σ,τ)⟩ ∩ (G × {1}) = {1}`. Proof: `(σ,τ)^k ∈ G×{1} ⟺ τ^k = 1 ⟺
ord(τ) ∣ k`, and `ord(σ) ∣ ord(τ) ∣ k ⟹ σ^k = 1`.
Generality dimensions where the literature varies:
  - finiteness of `G`: literature needs none — only `ord σ` finite (automatic if `G` finite).
  - finiteness of `H`: never needed — `ord τ` may even be `0` (infinite), in which case `ord(σ) ∣ 0`
    holds trivially for any finite-order `σ`, and the statement still holds.
  - the hypothesis: literature-natural is **`ord(σ) ∣ ord(τ)`**; `|G| ∣ ord(τ)` is a *sufficient
    specialisation* (since `ord σ ∣ |G|`). The user's own docstring (lines 390–392) states exactly
    this: "the *correct* meet `⟨g⟩ ⊓ (G×{1})` is trivial iff `ord σ ∣ ord τ`, which `ord σ ∣ |G| ∣
    ord τ` DOES give."
Disagreement with the literature: the Lean form is **strictly narrower** than the literature-standard
form on two axes (finiteness assumptions; `|G| ∣ ord τ` vs `ord σ ∣ ord τ`).

---

### Generality analysis — `cyclic_subgroup_meets_G_times_one_trivially`

Literature-standard form (Phase 3): for any groups `G, H`, `σ ∈ G`, `τ ∈ H` with `orderOf σ ∣
orderOf τ` (and `σ` of finite order — automatic when `orderOf τ ≠ 0`), `⟨(σ,τ)⟩ ⊓ (⊤.prod ⊥) = ⊥`.

| # | Parameter / hypothesis        | Current Lean form       | Literature-standard form          | Weaker form exists? | Reason it can/can't be weakened |
|---|-------------------------------|-------------------------|-----------------------------------|---------------------|----------------------------------|
| 1 | `[Finite G]`                  | `G` finite              | `orderOf σ` finite (or `≠ 0`)     | **yes**             | proof uses only `orderOf σ ∣ orderOf τ`; `Finite G` is invoked solely via `orderOf_dvd_natCard σ` to get `ord σ ∣ |G|`. Drop it. |
| 2 | `[Finite H]`                  | `H` finite              | (none)                            | **yes**             | `H`/`τ` finiteness is never used. The proof only needs `τ^k = 1`. Drop entirely. |
| 3 | `_hn : Nat.card G ∣ orderOf τ`| `|G| ∣ ord τ`           | `orderOf σ ∣ orderOf τ`           | **yes**             | `ord σ ∣ |G|` always, so `|G| ∣ ord τ ⟹ ord σ ∣ ord τ`; the converse fails. The weaker hypothesis `ord σ ∣ ord τ` is what the proof actually consumes (and matches the literature + the file's own line-391 remark). |

### Generality verdict (Phase 4b)

The current form is: **STRICTLY NARROWER THAN STANDARD**
Number of weakening opportunities found: **3** (drop `Finite G`, drop `Finite H`, weaken hypothesis to `orderOf σ ∣ orderOf τ`).

Proposed restatement (general form):

```lean
theorem zpowers_inf_top_prod_bot_eq_bot
    {G H : Type*} [Group G] [Group H] {σ : G} {τ : H}
    (h : orderOf σ ∣ orderOf τ) :
    Subgroup.zpowers (σ, τ) ⊓ (⊤ : Subgroup G).prod (⊥ : Subgroup H) = ⊥ := by
  sorry -- the existing 9-line proof goes through verbatim after replacing
        -- `(orderOf_dvd_natCard σ).trans _hn` with `h`
```

Cost of restatement: **CHEAP** — mechanical. The body changes by one token: replace
`((orderOf_dvd_natCard σ).trans _hn)` with the hypothesis `h`, and the `Finite` instances drop out
unused. At the project's single call-pattern (Step 2, where `|G| ∣ ord τ` is in hand), the caller
supplies `(orderOf_dvd_natCard σ).trans hn` to recover the specialised hypothesis.

### Modern-idiom check (Phase 4c) — Bourbaki 2.0

| #  | Question                                                                                   | Applies? | Proposed reformulation | Mathlib downstream this enables |
|----|--------------------------------------------------------------------------------------------|----------|------------------------|----------------------------------|
|  1 | bundled-hypothesis preambles → typeclasses?                                                 | no       | hypotheses are genuine order facts, not class-shaped | — |
|  2 | sequences/metric → filters/topology?                                                        | no       | finite combinatorial/order statement; no analysis | — |
|  3 | construct an object → universal-property class?                                             | no       | it is an equation between subgroups, nothing to characterise universally | — |
|  4 | set-with-closure-predicate → bundled substructure?                                          | partly   | already stated with bundled `Subgroup` + `⊓`/`⊥` lattice ops — already idiomatic | — |
|  5 | vector-space/metric/field → weaken typeclass to module/(semi)ring?                          | no       | already at the `Group` level, the natural home | — |
|  6 | 1-categorical → higher-categorical?                                                          | no       | — | — |
|  7 | concrete index (ℕ/ℤ/ℝ) → arbitrary additive/ordered structure?                              | partly   | the cleaner mathlib idiom is **`Disjoint (zpowers (σ,τ)) (MonoidHom.snd G H).ker`** — see note | unifies with `Subgroup.disjoint_def`, `MonoidHom.ker` API |

Modern-idiom verdict: **yes (mild)** — the most idiomatic mathlib spelling replaces `⊓ … = ⊥`
with `Disjoint`, and replaces `(⊤ : Subgroup G).prod ⊥` with `(MonoidHom.snd G H).ker` (mathlib
proves `Subgroup.ker_snd : ker (snd G G') = .prod ⊤ ⊥`, Mathlib/Algebra/Group/Subgroup/Basic.lean:715).
That reframes the lemma as "the second projection is injective on `⟨(σ,τ)⟩`", which is the real
content. Cost: CHEAP. But this is a *cosmetic* improvement, not an organisational one — it enables no
blocked downstream proof; it is `Subgroup.disjoint_def`/`ker_snd`-rewriting away from the current
form. The substantive modernisation that *does* matter is the generality weakening from Phase 4b,
not this reskin. Real mathematical improvement: marginal (readability), so this does not by itself
drive the verdict — the Phase 4b weakening does.

---

### Diamond / defeq risk — (Phase 4.5)

n/a — declaration kind is `theorem` (no definitional equalities or typeclass-search paths introduced).

---

### Mathlib search-status: `cyclic_subgroup_meets_G_times_one_trivially`

Note: project-aware lean index tools (Loogle / LeanSearch / Lean-Finder) were **not available** as
deferred tools in this environment (only LSP surfaced), and the local build is stale, so the search
was done by **grep over the vendored mathlib tree** `.lake/packages/mathlib/Mathlib/` plus reasoning.

[A] Lean-Finder       n/a — tool unavailable in this environment
[B] Loogle            n/a — tool unavailable; substituted by typed grep over mathlib src (below)
[C] LeanSearch        n/a — tool unavailable; substituted by WebSearch concept identification
[D] Grep mathlib src  `zpowers.*⊓`, `⊓.*prod.*bot`, `Prod.orderOf`, `ker_snd`, `mrange_inl`,
                      `disjoint_def`, `prod_eq_bot_iff`, `mem_zpowers_iff`, `orderOf_dvd_*`
                      → **no exact hit** for the composite statement; **all building blocks present**
[E] Name pattern      grep `cyclic_subgroup_meets`, `zpowers_inf.*prod`, `zpowers.*top_prod_bot`
                      → no hit (no mathlib lemma named for this composite)

Searched for both:
  - the user's current form (`zpowers (σ,τ) ⊓ ⊤.prod ⊥ = ⊥` with `|G| ∣ ord τ`) — not present;
  - the literature-standard general form (`ord σ ∣ ord τ`, no finiteness) — not present either.

Building blocks found in mathlib (all by qualified name):
  - `Subgroup.ker_snd` — `ker (snd G G') = .prod ⊤ ⊥`  (Basic.lean:715) — *the* idiomatic spelling of `G × {1}`.
  - `Prod.orderOf` / `Prod.orderOf_mk` — `orderOf (a,b) = Nat.lcm (orderOf a) (orderOf b)` (OrderOfElement.lean:1353/1381).
  - `orderOf_dvd_iff_zpow_eq_one` (OrderOfElement.lean:757), `orderOf_dvd_natCard` (1153).
  - `Subgroup.mem_zpowers_iff`, `Subgroup.mem_prod` (Basic.lean:101), `Subgroup.mem_bot`, `Prod.mk_eq_one`.
  - `Subgroup.disjoint_def` (Lattice.lean:666), `Subgroup.prod_eq_bot_iff` (Basic.lean:144), `bot_prod_bot`.
  - `MonoidHom.mker_snd`/`mrange_inl` (submonoid analogues, Operations.lean:835/887).

Concluded: **not in mathlib** (all available methods exhausted, both the user's form and the
literature-standard general form) — but mathlib has every building block.

---

### Call sites — `Chebotarev.cyclic_subgroup_meets_G_times_one_trivially`

Internal use count: **0** (within the project, excluding the declaring file — and in fact 0 even
*including* the declaring file: there is no term-mode application anywhere).
External-to-file callers: **0 files**.

All six occurrences of the name in the repo:

| Site (file:line)                  | Kind            | Usage                                                                 |
|-----------------------------------|-----------------|----------------------------------------------------------------------|
| Abelian.lean:90                   | declaration     | the theorem itself                                                   |
| Abelian.lean:140                  | docstring       | prose mention ("`(cyclic_subgroup_meets_G_times_one_trivially)`, so `M = F(μ_m)`") |
| Abelian.lean:187                  | docstring       | prose mention (C3 decomposition note, "needs `|G| ∣ ord τ`")        |
| Abelian.lean:392                  | docstring       | prose mention ("matching `cyclic_subgroup_meets_G_times_one_trivially`") |
| Abelian.lean:399                  | docstring       | prose mention ("transported across the `Gal(M/K) ≅ G × H` splitting") |
| Abelian.lean:680                  | docstring       | "Concrete realisation of `cyclic_subgroup_meets_G_times_one_trivially` inside `Gal(M/K)`" |

Inline-derivation grep (re-derived elsewhere without using it?):
  - **YES — `Chebotarev.zpowers_inf_fixingSubgroup_eq_bot_aux`** (`Abelian.lean:685`, `private theorem`).
    This is the *concrete realisation* that the actual Step-2 assembly uses: it re-proves the same
    trivial-meet fact directly inside `Gal(M/K)` against `(adjoin K {b | b^m=1}).fixingSubgroup`
    (the `G × {1}` factor identified as `Gal(M/K(μ_m))`), with its own 30-line proof
    (`orderOf_dvd_iff_zpow_eq_one`, `orderOf_dvd_natCard`, `autToPow`, `restrictNormalHom`). It does
    **not** call `cyclic_subgroup_meets_G_times_one_trivially`; the abstract lemma is only
    *referenced in prose* as the fact being realised.

Call-sites signal: **K = 0 internal uses, AND the same statement is re-derived inline** at
`zpowers_inf_fixingSubgroup_eq_bot_aux`. Per the heuristic table this leans
NO-composable / wrapper-that-consumers-bypass. The abstract lemma is currently a documentation
anchor: it states the clean group-theoretic core that the concrete `_aux` lemma realises, but the
two are not wired together. (This is consistent with the file's WIP decomposition status — the
master leaf was "intended to be discharged from … `cyclic_subgroup_meets_G_times_one_trivially`
transported across the `G × H` splitting", line 399, but the concrete `_aux` route was taken instead.)

---

### Composition check (Phase 6)

Can `cyclic_subgroup_meets_G_times_one_trivially` be derived from mathlib in ≤3 chained calls?

Attempt 1 (via `ker_snd` + injectivity): rewrite `⊤.prod ⊥` as `(MonoidHom.snd G H).ker`
(`Subgroup.ker_snd`), reducing the goal to `Disjoint (zpowers (σ,τ)) (snd G H).ker`
(`Subgroup.disjoint_def`). This is "`snd` injective on `⟨(σ,τ)⟩`".
  - Mathlib decls used: `Subgroup.ker_snd`, `Subgroup.disjoint_def`, `Subgroup.mem_zpowers_iff`.
  - Result: **partial** — after the rewrites you still must show `(σ,τ)^k ∈ ker snd ⟹ (σ,τ)^k = 1`,
    i.e. `τ^k = 1 ⟹ σ^k = 1`, which needs the order-divisibility argument (`τ^k=1 ⟹ ord τ ∣ k ⟹
    ord σ ∣ k ⟹ σ^k=1`). That is the real 3–4-step content; not eliminated by the reframe.

Attempt 2 (via `Prod.orderOf_mk`): not shorter — characterising the meet still needs the elementwise
`τ^k=1 ⟹ σ^k=1` implication.

Conclusion: **NOT-COMPOSABLE** in ≤3 mathlib calls. After the cosmetic `ker_snd`/`disjoint_def`
rewrites, the load-bearing step is the order-divisibility chain (`orderOf_dvd_iff_zpow_eq_one` twice
+ `orderOf_dvd_natCard`/the `ord σ ∣ ord τ` hypothesis), with `have`s and reasoning between — that
is a genuine (small) proof, not a 1–3-call inline. So this is a real lemma, but a *small, general,
reusable* one whose right home is mathlib's `GroupTheory/OrderOfElement.lean` next to `Prod.orderOf`.

---

## Verdict: `Chebotarev.cyclic_subgroup_meets_G_times_one_trivially`

**Category:** **YES-but-generalise-first**

**Evidence:**
- Literature search (Phase 3): standard form is `ord(σ) ∣ ord(τ)` (and no finiteness); the lcm-of-
  orders fact is universal textbook content (Conrad, Princeton/LSU/USC notes, Judson). Unnamed,
  exercise-level — but genuinely general and reusable.
- Generality analysis (Phase 4): **STRICTLY NARROWER THAN STANDARD** — 3 weakenings (drop
  `[Finite G]`, drop `[Finite H]`, weaken `|G| ∣ ord τ` to `ord σ ∣ ord τ`).
- Mathlib search (Phase 5): **not in mathlib** in either the user's or the general form; all building
  blocks present (`Prod.orderOf`, `Subgroup.ker_snd`, `orderOf_dvd_iff_zpow_eq_one`).
- Composition check (Phase 6): **NOT-COMPOSABLE** in ≤3 calls — the order-divisibility chain is real
  (small) content.

**Rationale.**
The mathematical content — `⟨(σ,τ)⟩ ∩ (G × {1})` is trivial once `ord σ ∣ ord τ` — is a clean,
fully general finite-order fact that sits exactly alongside mathlib's existing `Prod.orderOf`
(`orderOf (a,b) = lcm`) in `GroupTheory/OrderOfElement.lean`, yet mathlib has no lemma for it
(grep over the vendored tree finds the lcm formula and `ker_snd` but no statement about
`zpowers (a,b)` meeting a factor). It is not a ≤3-call composition: after the cosmetic
`ker_snd`/`disjoint_def` reframe, the `τ^k = 1 ⟹ σ^k = 1` implication still has to be proved via the
order chain. So mathlib *would* benefit from it — but **not in the form written here**. The Lean
statement carries two unnecessary `[Finite]` instances (only `orderOf σ ∣ orderOf τ` is used; `H`
finiteness is never touched) and the non-minimal hypothesis `|G| ∣ ord τ` where `ord σ ∣ ord τ`
suffices — a gap the project's *own* docstring flags (line 391: "trivial iff `ord σ ∣ ord τ`").
Mathlib's iron rule (most general form: groups not finite groups, the weakest divisibility
hypothesis) makes this a generalise-first, not add-as-is. The generalisation is CHEAP (one-token
proof edit; instances drop out). The verdict is *not* downgraded to NO by the K=0 call count: the
fact's home is mathlib (general, reusable), and the reason it is unused locally is that the project
took the concrete `zpowers_inf_fixingSubgroup_eq_bot_aux` route — the general lemma is exactly the
kind of API mathlib should carry so such concrete proofs can cite it.

Reason for the generalisation: **LITERATURE-WEAKENING** (Phase 4b found the user's form strictly
narrower than the literature-standard form on three axes). The Phase-4c modern-idiom reskin
(`Disjoint`/`ker_snd`) is a minor secondary readability win, not the driver.

Proposed restatement (the form to upstream):

```lean
/-- In a product of groups, if `orderOf σ ∣ orderOf τ` then the cyclic subgroup
generated by `(σ, τ)` meets the first factor `G × {1}` trivially. -/
theorem zpowers_inf_top_prod_bot_eq_bot
    {G H : Type*} [Group G] [Group H] {σ : G} {τ : H}
    (h : orderOf σ ∣ orderOf τ) :
    Subgroup.zpowers (σ, τ) ⊓ (⊤ : Subgroup G).prod (⊥ : Subgroup H) = ⊥ := by
  sorry  -- existing proof survives: replace `(orderOf_dvd_natCard σ).trans _hn` with `h`;
         -- `[Finite G]`, `[Finite H]` are no longer needed.
```

Estimated cost of regeneralisation: **CHEAP**.

Mathlib downstream this enables: lives next to `Prod.orderOf` in `Mathlib/GroupTheory/OrderOfElement.lean`;
gives a reusable "projection is injective on a cyclic subgroup when the orders are compatible" fact
that any direct-product Galois/`ZMod`-character argument (exactly the Chebotarev use) can cite
instead of re-deriving — e.g. the project's own `zpowers_inf_fixingSubgroup_eq_bot_aux` would, after
identifying `G × {1}` with `(snd …).ker` via `ker_snd`, reduce to one application of it. An optional
`Disjoint`-phrased corollary (`Disjoint (zpowers (σ,τ)) (MonoidHom.snd G H).ker`) composes with the
`MonoidHom.ker` API.

Next action: run `/generalise Chebotarev.cyclic_subgroup_meets_G_times_one_trivially` (it will
tension against both the literature-standard `ord σ ∣ ord τ` form and the `Disjoint`/`ker_snd`
modern idiom), confirm the proof survives the weakening, then upstream as
`feat(GroupTheory/OrderOfElement): cyclic subgroup of a product meets a factor trivially`.
Within the project, supply `(orderOf_dvd_natCard σ).trans hn` at the (eventual) call site to recover
the `|G| ∣ ord τ` specialisation.

---

## Next step

Run `/generalise Chebotarev.cyclic_subgroup_meets_G_times_one_trivially` to weaken to
`orderOf σ ∣ orderOf τ` (dropping both `[Finite]` instances), verify the proof survives, then open a
mathlib PR placing it next to `Prod.orderOf` in `Mathlib/GroupTheory/OrderOfElement.lean`.
