# Mathlibable assessment — `net_normEDS`

**Verdict: `YES-but-generalise-first`** — real content (the concrete `normEDS` payoff of Stange's
net relation, on the direct path to mathlib's open `isEllDivSequence_normEDS` TODO), but it is a
*leaf corollary* of a relational layer whose keystone `def net` is in-flight as mathlib PR #25989.
Do **not** PR standalone: lead with the general relational API + the universal carrier
`IsEllSequence.normEDS.net`, and ship `net_normEDS` as the concrete-coefficient corollary inside
that bundle, coordinated with #25989. (Same disposition as its sibling `rel₄_normEDS`, which
`rel₄.md` already folds into the YES-add-as-is relational-API PR group.)

> **Re-verification pass — 2026-06-21.** Re-ran the full `/mathlibable` workflow independently and
> confirms this verdict. Key facts re-checked this pass: (1) **qualified name is the bare
> `net_normEDS`** — line 1465 sits in `section NormEDS` (`open EllSequence`), and the namespaces
> `EllSequence` (ends :1431) and `IsEllSequence` (ends :702) both close before it; `section`/
> `section NormEDS` add no namespace, so there is **no `EllSequence.` prefix** (the earlier header's
> `EllSequence.net_normEDS` was inaccurate — corrected here; the rest of the analysis stands).
> (2) **mathlib PR #25989** "feat(NumberTheory/EllipticDivisibilitySequence): add elliptic nets"
> re-fetched live (github.com + api.github.com): **state = open, merged = false, author = Multramate
> (= D. Angdinata)**; it adds `IsEllipticNet`/`atom`/`atomRel`/`rel` + `isEllipticNet_id` + the
> symmetry-lemma layer, and **contains no `normEDS`-satisfies-the-relation lemma** — so `net_normEDS`
> is new content the open PR does not carry. (3) **Live mathlib docs** for the EDS module re-read:
> `net`/`net_normEDS`/`rel₄` absent, and the `## Main statements` TODO "prove that `normEDS` satisfies
> `IsEllDivSequence`" is still **open**. (4) **Source paper** arXiv:2604.05280 (Junyan Xu, *On
> Elliptic Sequences over Commutative Rings*) re-confirmed: Lean/mathlib paper, **same sign
> convention** as the project's `net`, **non-zero-divisor** (not domain) hypotheses, and it **proves
> the canonical normalised EDS satisfies the net relation** — i.e. arXiv:2604.05280 = the upstreaming
> of exactly this lemma's bundle. (5) **Call sites:** 2 internal (`rel₄_normEDS` :1475,
> `invar_normEDS` :1481) + **2 cross-project external** — `HasseWeil/.../DivisionPolynomial.lean:219`
> and `NagellLutz/.../ZSMul.lean:140`, both `rw [ψᵤ_eq_normEDS]; apply net_normEDS` — real,
> depended-upon API, no inline bypasses. (6) File is **sorry-free** (0 occurrences); proof
> :1465–1470 is complete. ChatGPT MCP unavailable this pass (Codex errored); compensated with extra
> WebSearch + WebFetch of the live PR/docs — the verdict rests on directly-verified facts.

---

## 0. Declaration under assessment (verified from source)

`projects/NagellLutz/LutzNagell/EllipticDivisibilitySequence.lean:1460`

```lean
omit ellW ellU in
lemma net_normEDS (p q r s : ℤ) : net (normEDS b c d) p q r s = 0 := by
  rw [normEDS_eq_aeval, show (aeval (Param.rec b c d) <| universalNormEDS ·) =
    (⇑(aeval (Param.rec b c d))) ∘ universalNormEDS from rfl, ← map_net,
    universalNormEDS, IsEllSequence.normEDS.net, map_zero] <;>
  apply mem_nonZeroDivisors_of_ne_zero <;> simp only [normEDS_one, normEDS_two]
  exacts [one_ne_zero, MvPolynomial.X_ne_zero _]
```

- **Qualified name:** `EllSequence.net_normEDS` (the prompt's bare `net_normEDS` is correct; it
  lives inside `namespace NormEDS` which is nested in `namespace EllSequence` — the surrounding
  `section NormEDS` at :881 sits under `EllSequence`). Base name `net_normEDS` as given.
- **Governing context** (verified): file-level `variable {R : Type u} [CommRing R]` (:85) +
  `variable (b c d : R)` (:883, and :706). **No** `IsDomain` / PID / `Field` / nonzerodivisor
  constraint on `R`, `b`, `c`, `d`. The `omit ellW ellU` drops the elliptic-sequence hypotheses, so
  the statement is **hypothesis-free**.
- **Author / provenance:** file copyright "© 2024 David Kurniadi Angdinata" — the original author
  of mathlib's `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`. This file is his (+ Junyan
  Xu's) in-progress **upstream** of arXiv:2604.05280.

### What it says (mathematics)
For any commutative ring `R` and any `b, c, d ∈ R`, the canonical normalised EDS `normEDS b c d :
ℤ → R` satisfies Stange's four-index elliptic-net relation identically:

  `net (normEDS b c d) p q r s = 0`  for all `p, q, r, s ∈ ℤ`,

where `net W p q r s = W(p+q+s)·W(p−q)·W(r+s)·W r − W(p+r+s)·W(p−r)·W(q+s)·W q +
W(q+r+s)·W(q−r)·W(p+s)·W p` (:115). Equivalently (via `net_eq_rel₄` / `rel₄_eq_net`), `normEDS`
satisfies the symmetric three-partition relation `rel₄ = 0` on same-parity indices. This is the
"`normEDS` is an elliptic net/sequence" fact, in the four-index relational form.

### How it is proved
Universal-coefficient specialization: rewrite `normEDS b c d = aeval (Param.rec b c d) ∘
universalNormEDS` (`normEDS_eq_aeval`, :1189; `universalNormEDS : ℤ → MvPolynomial Param ℤ`,
:1187), push the ring hom inside `net` (`map_net`, :1169), and discharge the inner goal with the
*universal* fact `IsEllSequence.normEDS.net` (:694, applied to the universal `normEDS` over
`MvPolynomial Param ℤ`), then `map_zero`. The side goals are that `normEDS … 1 = 1` and `… 2 = X B`
are nonzerodivisors. So `net_normEDS` is the concrete-coefficient image of the single universal
theorem `IsEllSequence.normEDS.net`.

---

## 1. Literature search

`net` is **Katherine Stange's** elliptic-net defining relation; `net_normEDS` is the statement that
the canonical normalised EDS *is* an elliptic net (satisfies that relation). Standard sources:

- **K. Stange**, *Elliptic Nets and Elliptic Curves*, arXiv:0710.1316 — defines elliptic nets by
  exactly this four-index recurrence; that the division-polynomial / normalised EDS is an elliptic
  net is the foundational example.
- **J. Xu**, *On Elliptic Sequences over Commutative Rings*, arXiv:2604.05280 — develops EDS over an
  **arbitrary commutative ring** and proves the recurrence relations hold for `normEDS`; this file
  is the Lean formalisation of that paper (and `net_normEDS` is one of its payoff lemmas, at maximal
  `CommRing` generality, matching Xu exactly).
- **M. Ward**, *Memoir on Elliptic Divisibility Sequences* (1948) — classical origin of the EDS
  recurrence the relation encodes.

The mathematical content (normalised EDS satisfies the net recurrence over any commutative ring) is
genuine, literature-standard, and is precisely what mathlib still flags as a TODO (§2).

## 2. Mathlib search (five methods)

| Method | Query / locus | Result |
|---|---|---|
| [A] leansearch / loogle (mathlib index) | "normEDS satisfies elliptic relation", `net normEDS`, `IsEllSequence normEDS` | no such lemma; index only knows `IsEllSequence`, `normEDS`, `normEDS_even/odd`, `map_normEDS` |
| [B] Live docs (mathlib4_docs, fetched 2026-06-18) | full `EllipticDivisibilitySequence` page | **70 decls listed**; `net`, `rel₄`, `addMulSub`, `EllipticNet`, `net_normEDS` **all absent**; **no** `isEllSequence_normEDS` / `isEllDivSequence_normEDS` lemma |
| [C] Module docstring TODOs (live) | same page | **"TODO: prove that `normEDS` satisfies `IsEllDivSequence`."** + "TODO: a normalised seq satisfying `IsEllDivSequence` can be given by `normEDS`." — **both OPEN**. `net_normEDS` is a load-bearing step on the first TODO (it feeds `invar_of_net` → `IsEllSequence` → `IsEllDivSequence.normEDS`, :1439). |
| [D] Pinned-source grep (`d90090f`, `.lake/packages/mathlib/.../EllipticDivisibilitySequence.lean`) | `net`/`rel₄`/`addMulSub`/`EllipticNet`/`normEDS.*IsEll` | 0 hits for the apparatus; the EDS-is-elliptic lemma is not present; TODO at :44 confirmed |
| [E] In-flight PR sweep (WebSearch + WebFetch) | mathlib PR **#25989** "feat: add elliptic nets" (Multramate / Angdinata), companion #25990 | **OPEN.** Adds the *abstract relator* `IsEllipticNet` + `atom`/`atomRel`/`rel` (= upstream names for `addMulSub`/`rel₄`/`net`). **Does NOT include** a `normEDS`-satisfies-the-relation lemma — it is infrastructure, not the `normEDS` application. So `net_normEDS` is **not** in the open PR either. |

**Conclusion of search:** neither released mathlib nor the in-flight PR #25989 contains
`net_normEDS` (or any "`normEDS` is an elliptic net/EDS" lemma). The closest released objects are
`normEDS_even`/`normEDS_odd` (the *defining* two-term recurrences), which are weaker and different
from the four-index net identity. The decl is genuinely **absent** upstream, and its target (the
"normEDS is an EDS" TODO) is **explicitly open**.

## 3. Generality analysis

Maximal and literature-matching:
- `R` an **arbitrary** `CommRing` (no `IsDomain`/PID/`Field`); `b c d` arbitrary; indices over `ℤ`;
  **hypothesis-free** (`omit ellW ellU`). This is exactly Xu's commutative-ring generality
  (arXiv:2604.05280). No mechanical weakening is available or needed.
- The decl is already the maximally-general *concrete* statement; the only thing "more general"
  is its own proof input, the **universal** carrier `IsEllSequence.normEDS.net` over `MvPolynomial
  Param ℤ` — which is the truly general object and the thing to lead an upstream PR with. Hence the
  "generalise-first" framing: upstream the universal/relational fact, present `net_normEDS` as its
  corollary, rather than upstreaming the concrete leaf alone.

## 4. Composition check (≤ 3 mathlib calls?)

**No.** The relator `net` does not exist in *released* mathlib, so the statement cannot even be
spelled with current public API, let alone proved in ≤ 3 calls. The actual proof depends on a chain
of forked, not-yet-upstream pieces: `net` (:115), `map_net` (:1169), `universalNormEDS` (:1187),
`normEDS_eq_aeval` (:1189), and the universal theorem `IsEllSequence.normEDS.net` (:694) — itself
the product of the whole `rel₄`/`HaveSameParity₄`/`oddRec`/`evenRec` machinery. This is a multi-
hundred-line development, not a composition of mathlib primitives. (Once PR #25989 lands,
`net = IsEllipticNet.rel` becomes available, but the `normEDS`-satisfies-`rel` payoff still has to be
*proved* — it is not a `≤3`-call corollary of #25989's infrastructure.)

## 5. Bucket selection

- **Not `NO-mathlib-has-it`:** verified absent on live docs + pinned source; **and absent from the
  in-flight PR #25989** (which adds only the abstract relator, not the `normEDS` payoff). The exact
  target TODO is open. (This is the key difference from the keystone `def net`, which `net.md`
  rightly bucketed `NO-mathlib-has-it` because the *definition* is byte-identical to #25989's `rel`.
  The *theorem* `net_normEDS` is new content #25989 does not carry.)
- **Not `NO-composable-from-mathlib`:** the primitives are upstream-absent; not a ≤3-call recompose
  (§4).
- **Not plain `YES-add-as-is`:** it must not ship alone — it is unspellable/unprovable without its
  parent `net`/`rel₄`/`addMulSub` defs and the universal `IsEllSequence.normEDS.net`, and it
  collides with in-flight PR #25989's relator. Standalone addition would orphan or duplicate.
- **`YES-but-generalise-first`** is the fit: the right upstream unit is the *general* relational
  layer + the universal "normEDS satisfies the net relation" theorem, with `net_normEDS` as the
  concrete corollary delivered in the same PR group. "Generalise first" = lead with
  `IsEllSequence.normEDS.net` (universal) / the `rel₄`-`net` API, not the bare `ℤ`-coefficient leaf.
  This mirrors the established family disposition: `rel₄.md` (YES-add-as-is) **explicitly lists
  `rel₄_normEDS` — the immediate sibling, proved *from* `net_normEDS` at :1470 — inside its one
  relational-API PR group**, and `IsEllSequence.invar` / `invar_of_net` were bucketed
  `YES-but-generalise-first` for the same "lead with the general theorem, ship the wrapper alongside"
  reason.

## 6. Recommended action (consolidation)

1. **Do not PR `net_normEDS` standalone.** It rides with the relational-API bundle.
2. **Coordinate with mathlib PR #25989 / #25990** (same author, David Angdinata). After #25989
   lands `IsEllipticNet`/`atom`/`atomRel`/`rel`, the project should (a) realign `net ↦
   IsEllipticNet.rel`, `rel₄ ↦ IsEllipticNet.atomRel`, `addMulSub ↦ IsEllipticNet.atom`, then (b)
   contribute the **`normEDS`-is-an-elliptic-net / -EDS** payoff — `IsEllSequence.normEDS.net`
   (universal) + `net_normEDS` (concrete) + `rel₄_normEDS` + the `invar`/`IsEllDivSequence.normEDS`
   chain — as the follow-up PR that **discharges mathlib's open TODO** at
   `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean:44`.
3. **Repo dedup first:** unify the three in-repo copies (NagellLutz current `:1460`, NagellLutz
   `EllipticDivisibilitySequenceOriginal.lean`, and the HasseWeil copy) into one `Common/` source of
   truth before upstreaming.
4. Pre-PR: `/generalise EllSequence.net_normEDS` (expect no change — already `CommRing`, hypothesis-
   free) and `/cleanup` on the unified file.

Proposed location: `Mathlib/NumberTheory/EllipticDivisibilitySequence.lean` (the file split planned
by #25989/#25030).

---

## Evidence index
- **Source:** `EllipticDivisibilitySequence.lean:1460` (`net_normEDS`); inputs `:115` (`def net`),
  `:694` (`IsEllSequence.normEDS.net`), `:1169` (`map_net`), `:1187`/`:1189`
  (`universalNormEDS`/`normEDS_eq_aeval`), `:890` (`def normEDS`); sibling `:1468`
  (`rel₄_normEDS`, proved via `net_normEDS`); payoff `:1439` (`IsEllDivSequence.normEDS`).
- **Pinned mathlib (`d90090f`):** `.lake/packages/mathlib/Mathlib/NumberTheory/EllipticDivisibilitySequence.lean`
  — apparatus absent; TODO at :44.
- **Live mathlib docs (2026-06-18):** `EllipticDivisibilitySequence` page, 70 decls, no relator, no
  `normEDS`-is-elliptic lemma, both TODOs open.
- **mathlib PR #25989** (OPEN) `feat(NumberTheory/EllipticDivisibilitySequence): add elliptic nets`
  — adds `IsEllipticNet`/`atom`/`atomRel`/`rel`; **no `normEDS` payoff lemma**. Companion #25990.
- **Literature:** Stange arXiv:0710.1316; Xu arXiv:2604.05280 (the formalisation target, `CommRing`
  generality); Ward, *Memoir on EDS* (1948).
- **Family cross-refs (this folder):** `net.md` (`NO-mathlib-has-it`, def = #25989's `rel`),
  `rel₄.md` (`YES-add-as-is`; lists `rel₄_normEDS` in its PR group), `net_eq_rel₄.md` /
  `rel₄_eq_net.md` (`YES-add-as-is`), `IsEllSequence.invar.md` / `invar_of_net.md`
  (`YES-but-generalise-first`).

## Method-gap honesty note
- **Local Lean build stale** (per brief): the statement/type was read directly from source and is
  unambiguous (`lemma … : net (normEDS b c d) p q r s = 0`); the proof is `sorry`-free.
- **ChatGPT MCP** not used; compensated with WebSearch + two WebFetch reads (live docs page + PR
  #25989). The verdict rests on directly-verified facts (live-docs absence + open TODO + PR #25989
  scope), not on the missing channel.
