# AINTLIB — Atlas of Formalised Number Theory in Lean

- **Date:** 2026-06-08
- **Owner:** Chris Birkbeck (GitHub `CBirkbeck`)
- **Status:** Approved design → ready for implementation planning
- **Repo:** `CBirkbeck/AINTLIB` (private). Built blueprint published publicly.

---

## 1. Summary

AINTLIB ("AI Number Theory Library") is a single **Verso blueprint** that serves as an
**atlas of formalised number theory in Lean**. It collects the *main* (Wikipedia-level)
results of number theory as they exist in Lean today — across **mathlib**, the user's
**local number-theory repos**, and **external projects** (PNT+, Imperial FLT, and others
discovered on GitHub) — and presents each with:

1. a human-readable **unformalised statement** (prose + KaTeX), and
2. a paragraph-level **proof sketch**,

all wired into **one interactive dependency graph** so the connections between results
(and between projects) are visible at a glance.

The repo is **private**; the built HTML blueprint is published **publicly** so the link can
be shared.

## 2. Goals / Non-goals

**Goals**
- One place to *see all the number theory we have in Lean right now* and how it connects.
- Human-readable unformalisation of the main results and their proofs.
- A cross-project dependency graph (the "connections" are the point).
- Show the **frontier**: results currently in open mathlib PRs, tagged as in-review.
- Private source repo; public, shareable blueprint URL.

**Non-goals**
- Not a single buildable monorepo of every project (impossible — see §3).
- Not every lemma. Curated to named/Wikipedia-level results plus the load-bearing
  definitions and lemmas needed to connect them.
- Not a re-formalisation effort. We *describe and link* existing Lean; we don't re-prove it.

## 3. The hard constraint that shapes everything

The source repos span **Lean v4.7 → v4.31** (e.g. `LocalClassFieldTheory` on 4.7,
`FLT` on 4.9, `EulerProducts` on 4.12, `chebotarev-density` on 4.31). A single `lake`
project pins exactly one mathlib, so **these repos cannot all compile together**. Therefore
AINTLIB is an **atlas**, not a unified build:

- The **mathlib number-theory core is live-built** (AINTLIB depends on one recent mathlib),
  giving automatic sorry-free status for every `Mathlib.NumberTheory.*` reference.
- Every **other repo is represented as linked blueprint chapters** — real nodes in the
  dependency graph, but referenced by declaration name + hyperlinks rather than compiled
  in-tree.

## 4. Architecture — the atlas model

- **One Lean project**, pinned to a recent mathlib. **Target: Lean v4.31** (matches the
  user's `chebotarev-density` / `mathlib4-up1`). Revisit to "latest stable" at scaffold time.
- **Live-built backbone = mathlib's number theory.** `(lean := "Mathlib.NumberTheory.…")`
  references resolve against the build and get auto sorry-free status. This is the verified core.
- **Local/external repos = linked chapters.** Each main result becomes a Verso node carrying:
  - unformalised statement + proof sketch,
  - a `(lean := …)` pointer to the declaration name in that repo,
  - hyperlinks to the repo and (where it exists) its own blueprint,
  - status *"formalised externally (repo @ commit)."*
  These are not compiled inside AINTLIB but are woven into the **same graph** via `{uses}` edges.
- **Provenance tags** on every node (`mathlib`, `flt-regular-bernoulli`, `LeanModularForms`,
  `FLT`, `PNT+`, …) so the graph can be **filtered / colour-coded by source**.
- **Sources manifest** (`sources/`): one entry per repo — URL, pinned commit, Lean version,
  blueprint URL, and the declarations we cite. Repos tracked as **git submodules** for stable
  links; cloned locally for mining, but mathlib-sized trees are not vendored into AINTLIB.

## 5. Organisation — by topic, not by repo

Chapters are mathematical areas so cross-repo connections surface. Proposed top-level parts
(each a recognisable area of number theory):

| Chapter | Sample contents | Primary sources |
|---|---|---|
| Elementary NT | primes, arithmetic functions, congruences, quadratic reciprocity | mathlib |
| Analytic NT | ζ/L-functions, PNT, Dirichlet non-vanishing, sieves, Bombieri–Vinogradov | PNT+, EulerProducts, DirichletNonvanishing, mathlib |
| Algebraic NT | number fields, rings of integers, ramification, class groups, units, cyclotomic | LocalClassFieldTheory, QuadraticIntegers, mathlib |
| Class field theory & Galois | Chebotarev density, local/global CFT, reciprocity | chebotarev-density, LocalClassFieldTheory |
| p-adic & adic spaces | ℚ_p, valuations, adic spaces | Adic spaces, mathlib (Padics) |
| Modular & automorphic forms | modular/Hecke/Eisenstein, **valence formula**, **strong multiplicity one**, dimension formulas | LeanModularForms(-hecke), ModFormDims, mathlib |
| Elliptic curves & arithmetic geometry | Weierstrass, division polynomials, heights, Nagell–Lutz, Hasse–Weil, Weil conjectures | Nagel--Lutz, Hasse-Weil, WeilConjectures, mathlib |
| Fermat's Last Theorem & regular primes | FLT, FLT-regular, Bernoulli/regularity | FLT, flt-regular, flt-regular-bernoulli |
| Diophantine & transcendence | Gelfond–Schneider, Lindemann–Weierstrass, Newton polygons | NewtonPolys, mathlib |
| Additive / combinatorial NT (lighter) | sumsets, PFR-adjacent | formal-conjectures, PFR (if in scope) |

`{uses}` edges cross chapter **and** source boundaries — that is the "see the connections" payoff.

## 6. Curation rule

A result is **included** if it is:
- a *named / Wikipedia-level* theorem, **or**
- a key structural **definition**, **or**
- a **load-bearing lemma** needed to connect two included results.

Not every lemma. Rule of thumb: *if it has a Wikipedia page, it should be in the blueprint.*

## 7. Node format

Each node is a Verso directive authored via the `/blueprint` (mathlib-quality:blueprint) skill:

```
:::theorem "chebotarev-density" (lean := "Chebotarev.density_eq")
Statement in prose with inline $`…`$ and display $$`…`$$ KaTeX.
:::

:::proof
Paragraph-level human-readable sketch (the "unformalisation"). {uses "frobenius"}[] …
:::
```

- Statements and sketches are authored by **mining each repo's existing LaTeX blueprint and
  docstrings** as raw material — we don't reinvent prose that already exists.
- Lean status is **auto-computed** from the `(lean := …)` reference for the mathlib core;
  external nodes carry a manual "formalised externally" status + commit pin.

## 8. Forthcoming in mathlib

Results currently in **open mathlib PRs** (label `t-number-theory`; 58 open as of 2026-06-08)
appear as nodes tagged *"in review (PR #…)"*, so the atlas shows the frontier, not just the
merged state. Examples spotted today: Gelfond–Schneider transcendence, AKS primality test,
three-gap (Steinhaus) theorem, Farey sequences, Newton polygons, Selberg sieve, L-series of a
modular form, Robin's & Lagarias' RH-equivalent inequalities, Chebyshev's primorial bound,
Northcott property, ramification/inertia refactors, Amice transform (p-adic).

## 9. Discovery & sync (Phase 0)

- **Pull every local repo to latest** (fetch + pull); record each HEAD commit + Lean version
  into the manifest.
- **Clone external repos not present locally**: PNT+, Imperial FLT, and every GitHub-discovered
  NT project.
- **Thorough GitHub search + mathlib open-PR scan.**
- Present the **full source catalogue for user sign-off** before mining begins.

## 10. Deployment

- **Private** `CBirkbeck/AINTLIB` — source, manifest, Verso blueprint sources, CI.
- **Public** site (separate public repo `CBirkbeck/AINTLIB-blueprint`, or a `gh-pages` branch)
  hosting only the built HTML → **public blueprint URL, private source**. Works on a free plan;
  clean separation. GitHub Actions in the private repo builds the Verso blueprint and pushes
  HTML to the public site on each commit to `main`.

## 11. Phasing

- **Phase 0 — Discovery & sync:** pull/clone everything, GitHub search, PR scan, finalise the
  source catalogue (user approves).
- **Phase 1 — Scaffold:** create the private repo + remote, Verso blueprint project on mathlib
  v4.31, CI + public Pages site, chapter skeleton, sources manifest.
- **Phase 2 — Core:** author the live-built mathlib number-theory backbone, chapter by chapter.
- **Phase 3 — Repos:** fold each local/external repo's main results in as linked chapters,
  wiring cross-source `{uses}` edges.
- **Phase 4 — Frontier & polish:** forthcoming-in-mathlib nodes, source colouring, cross-link
  validation, README / landing page.

The blueprint is useful from Phase 2 onward; each phase splits into per-chapter tickets.

## 12. Preliminary source catalogue (finalised in Phase 0)

**Local repos found** (`/Users/mcu22seu/Documents/GitHub`, with Lean version; ✦ = has own blueprint):

- `Adic spaces` (4.29) — adic spaces / p-adic geometry
- `chebotarev-density` (4.31) ✦ — Chebotarev density theorem
- `flt-regular-bernoulli` (4.30) ✦ — Bernoulli numbers, regular primes
- `LeanModularForms` (4.30) ✦ — modular forms; valence formula; strong multiplicity one
- `LeanModularForms-hecke` (4.30) ✦ — Hecke operators
- `FLT` (4.9) ✦ — Fermat's Last Theorem (local copy)
- `flt-regular` (4.30) ✦ — FLT for regular primes
- `Hasse-Weil` (4.29) — Hasse–Weil bound / zeta of curves
- `WeilConjectures` (4.28) — Weil conjectures
- `EulerProducts` (4.12) — Euler products, L-series
- `DirichletNonvanishing` (4.13) ✦ — Dirichlet L non-vanishing / Dirichlet's theorem
- `LocalClassFieldTheory` (4.7) ✦ — local class field theory
- `Nagel--Lutz` (4.29) — Nagell–Lutz theorem
- `NewtonPolys` (4.28) — Newton polygons
- `power_reside_symbols` (4.7) — power residue symbols
- `GLn_F_q` (4.8) — GL_n(F_q)
- `ModFormDims` — modular form dimensions
- *To triage:* AACConjecture, formal-conjectures(NEW), UEA_primes, ETH_FLT, FLF, WeilConverse,
  DnDLean4, and other NT-adjacent folders.

**External (clone in Phase 0):**
- `AlexKontorovich/PrimeNumberTheoremAnd` (PNT+) ✦
- `ImperialCollegeLondon/FLT` ✦ (upstream, newer than local copy)

**GitHub-discovered (verify in Phase 0):**
- `pitmonticone/QuadraticIntegers` — ring of integers of quadratic fields
- `amellendijk/lean-bombieri-vinogradov` — Bombieri–Vinogradov
- upstream `LocalClassFieldTheory`, `google-deepmind/formal-conjectures`, `teorth/pfr`,
  perfectoid/adic-space projects, and others surfaced by the search.

**mathlib:** `Mathlib.NumberTheory.*` (+ valuation/p-adic/L-series namespaces) as the live-built
backbone; 58 open `t-number-theory` PRs for the frontier section.

## 13. Decisions made

- Atlas model with live-built mathlib core (vs. monorepo build, vs. pure docs). **Chosen: atlas.**
- Tooling: **Verso** (`/blueprint` skill), not leanblueprint LaTeX.
- Coverage: **everything, phased** — comprehensive, built outward from a core.
- Target mathlib **v4.31** (revisit to latest stable at scaffold).
- Deployment via a **separate public site repo** (avoids paid Pages-on-private).

## 14. Success criteria

- A public blueprint URL showing one cross-project dependency graph of formalised number theory.
- Every main/Wikipedia-level result present, with an unformalised statement + proof sketch.
- Nodes filterable/colourable by source; cross-source `{uses}` edges render.
- mathlib core auto-tracked sorry-free; external nodes pinned to commits and linked out.
- Forthcoming-in-mathlib results visible as in-review nodes.
- Source repo private, build reproducible via CI.

## 15. Open questions (carry into planning)

- Exact final source list (resolved in Phase 0 with user sign-off).
- Whether to attempt forward-porting select repos into the live build later (deferred).
- Depth of the "additive/combinatorial NT" chapter (lighter touch by default).
